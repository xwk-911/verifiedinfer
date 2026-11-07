"""Finite CUDA execution evidence, separate from Lean and PTX assembly checks.

Only the standard library and a functioning CUDA driver/JIT are required.
Outputs and guard words are compared byte-for-byte, with no float tolerance.
Small f32 inputs have explicit exact expected values; these are not a claim
that hardware rounding/approximation implements the exact-real model generally.
"""

import argparse
import ctypes as C
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import sys
import threading

ROOT = Path(__file__).resolve().parent.parent
U64, U32 = C.c_uint64, C.c_uint32
PTR = C.c_void_p


def words(kind, values):
    return struct.pack("<" + kind * len(values), *values)


def matmul_reference(a, b, m, n, k):
    return [sum(Fraction(a[row*k+t]) * b[t*n+col] for t in range(k))
            for row in range(m) for col in range(n)]


def attention_reference(q, keys, values, scale):
    if not keys:
        return Fraction(0)
    scores = [Fraction(scale) * sum(Fraction(x)*y for x, y in zip(q, key)) for key in keys]
    if any(score.denominator != 1 for score in scores):
        raise ValueError("This exact host reference uses integer base-2 scores")
    weights = [Fraction(2)**int(score) for score in scores]
    return sum(weight*value for weight, value in zip(weights, values))/sum(weights)


def shuffle_reference(mode, index, b, c, mask, inputs):
    lane, warp_base = index % 32, index // 32 * 32
    offset, segment, clamp = b & 31, c >> 8 & 31, c & 31
    lower = lane & segment
    bound = lower | (clamp & (~segment & 31))
    source = {"up": lambda: lane - offset, "down": lambda: lane + offset,
              "bfly": lambda: lane ^ offset,
              "idx": lambda: lower | (offset & (~segment & 31))}[mode]()
    valid = source >= bound if mode == "up" else source <= bound
    source = source if valid else lane
    if not (0 <= source < 32 and mask >> lane & 1 and mask >> source & 1
            and warp_base + source < len(inputs)):
        raise ValueError("Undefined shuffle input is outside finite GPU evidence")
    return inputs[warp_base + source], int(valid)


class Driver:
    def __init__(self, ordinal):
        self.library = os.environ.get("CUDA_DRIVER_LIBRARY", "libcuda.so.1")
        self.lib = C.CDLL(self.library)
        self.context = PTR()
        self.buffers = []
        self.modules = {}
        self.on_launch = lambda _: None
        signatures = {
            "cuInit": [U32], "cuDriverGetVersion": [C.POINTER(C.c_int)],
            "cuDeviceGet": [C.POINTER(C.c_int), C.c_int],
            "cuDeviceGetName": [PTR, C.c_int, C.c_int],
            "cuDeviceComputeCapability": [C.POINTER(C.c_int), C.POINTER(C.c_int), C.c_int],
            "cuCtxCreate_v2": [C.POINTER(PTR), U32, C.c_int], "cuCtxDestroy_v2": [PTR],
            "cuModuleLoadData": [C.POINTER(PTR), PTR],
            "cuModuleGetFunction": [C.POINTER(PTR), PTR, C.c_char_p], "cuModuleUnload": [PTR],
            "cuMemAlloc_v2": [C.POINTER(U64), C.c_size_t], "cuMemFree_v2": [U64],
            "cuMemcpyHtoD_v2": [U64, PTR, C.c_size_t], "cuMemcpyDtoH_v2": [PTR, U64, C.c_size_t],
            "cuLaunchKernel": [PTR, U32, U32, U32, U32, U32, U32, U32, PTR,
                               C.POINTER(PTR), C.POINTER(PTR)],
            "cuCtxSynchronize": [],
            "cuGetErrorName": [C.c_int, C.POINTER(C.c_char_p)],
            "cuGetErrorString": [C.c_int, C.POINTER(C.c_char_p)],
        }
        for name, args in signatures.items():
            fn = getattr(self.lib, name)
            fn.argtypes, fn.restype = args, C.c_int
        self.call("cuInit", 0)
        device, major, minor, version = C.c_int(), C.c_int(), C.c_int(), C.c_int()
        self.call("cuDeviceGet", C.byref(device), ordinal)
        label = C.create_string_buffer(128)
        self.call("cuDeviceGetName", label, len(label), device)
        self.call("cuDeviceComputeCapability", C.byref(major), C.byref(minor), device)
        self.call("cuDriverGetVersion", C.byref(version))
        self.info = {"ordinal": ordinal, "name": label.value.decode(),
                     "compute_capability": [major.value, minor.value], "driver_api_version": version.value,
                     "driver_library": self.library}
        if (major.value, minor.value) < (7, 0):
            raise RuntimeError("The current fixtures require a device supporting PTX target sm_70")
        self.call("cuCtxCreate_v2", C.byref(self.context), 0, device)

    def call(self, name, *args):
        result = getattr(self.lib, name)(*args)
        if result:
            label, detail = C.c_char_p(), C.c_char_p()
            self.lib.cuGetErrorName(result, C.byref(label))
            self.lib.cuGetErrorString(result, C.byref(detail))
            raise RuntimeError(f"{name}: {result} {label.value!r}: {detail.value!r}")

    def upload(self, data):
        address = U64()
        self.call("cuMemAlloc_v2", C.byref(address), len(data))
        self.buffers.append(address)
        host = C.create_string_buffer(data)
        self.call("cuMemcpyHtoD_v2", address, host, len(data))
        return address.value

    def download(self, address, size):
        host = C.create_string_buffer(size)
        self.call("cuMemcpyDtoH_v2", host, address, size)
        return host.raw

    def preload(self, fixture):
        """Load/JIT before dependent launches, without inserting waits between them."""
        if fixture not in self.modules:
            source = (ROOT / "examples" / f"{fixture}.ptx").read_bytes()
            entry = re.search(rb"\.entry\s+(\w+)", source).group(1)
            image, module, function = C.create_string_buffer(source), PTR(), PTR()
            self.call("cuModuleLoadData", C.byref(module), image)
            self.modules[fixture] = (module, function, hashlib.sha256(source).hexdigest())
            self.call("cuModuleGetFunction", C.byref(function), module, entry)
    def launch(self, fixture, args, block=(1, 1, 1), grid=(1, 1, 1), synchronize=True):
        self.on_launch(fixture)
        self.preload(fixture)
        _, function, _ = self.modules[fixture]
        pointers = (PTR * len(args))(*(C.addressof(arg) for arg in args)) if args else None
        self.call("cuLaunchKernel", function, *grid, *block, 0, None, pointers, None)
        if synchronize:
            self.call("cuCtxSynchronize")

    def close(self):
        # Best-effort cleanup must not mask the original CUDA/byte mismatch.
        for buffer in reversed(self.buffers):
            self.lib.cuMemFree_v2(buffer)
        for module, _, _ in self.modules.values():
            self.lib.cuModuleUnload(module)
        if self.context:
            self.lib.cuCtxDestroy_v2(self.context)


def run_cases(driver, results):
    def compare(case, fixture, address, expected, block, grid):
        actual = driver.download(address, len(expected))
        if actual != expected:
            raise AssertionError(f"{case}: expected {expected.hex()}, got {actual.hex()}")
        results.append({"case": case, "fixture": fixture, "status": "passed", "evidence": "exact_bytes",
                        "block": block, "grid": grid, "bytes_compared": len(expected),
                        "expected_hex": expected.hex(), "actual_hex": actual.hex()})
        print(f"GPU exact bytes: {case} ({len(expected)} bytes)", flush=True)

    shuffle_cases = [
        (mode, "full_warp", 1, 0 if mode == "up" else 31, 0xffffffff, 100, (32, 1, 1))
        for mode in ("up", "down", "bfly", "idx")
    ] + [
        ("up", "underflow", 31, 0, 0xffffffff, 0xfffffff5, (32, 1, 1)),
        ("up", "offset_high_bits_two_warps", 33, 0, 0xffffffff, 100, (8, 8, 1)),
        ("up", "segmented", 1, 0x1000, 0xffffffff, 100, (8, 4, 1)),
        ("down", "overflow", 31, 31, 0xffffffff, 0xfffffff5, (32, 1, 1)),
        ("down", "offset_high_bits_3d", 65, 31, 0xffffffff, 100, (4, 4, 4)),
        ("down", "segmented", 1, 0x100f, 0xffffffff, 100, (8, 4, 1)),
        ("bfly", "two_warps", 17, 31, 0xffffffff, 100, (64, 1, 1)),
        ("bfly", "upper_clamp_allows_lower_segment", 16, 0x100f, 0xffffffff, 100, (32, 1, 1)),
        ("bfly", "segmented", 1, 0x100f, 0xffffffff, 100, (8, 4, 1)),
        ("idx", "segment_source", 20, 0x100f, 0xffffffff, 100, (32, 1, 1)),
        ("idx", "clamp_falls_back", 31, 15, 0xffffffff, 100, (32, 1, 1)),
        ("idx", "offset_high_bits_3d", 39, 31, 0xffffffff, 100, (4, 4, 4)),
        ("idx", "reserved_c_bits", 7, 0xffffe0ff, 0xffffffff, 100, (32, 1, 1)),
    ] + [
        (mode, "partial_warp", 1, 0 if mode == "up" else 15, 0xffff, 100, (16, 1, 1))
        for mode in ("up", "down", "bfly", "idx")
    ]
    for mode, label, offset, clamp, mask, base, block in shuffle_cases:
        count = block[0] * block[1] * block[2]
        inputs = [(base + index) & 0xffffffff for index in range(count)]
        expected = [0xa5a5a5a5] * 2
        for index in range(count):
            expected.extend(shuffle_reference(mode, index, offset, clamp, mask, inputs))
        expected.extend([0xa5a5a5a5] * 2)
        destination = driver.upload(words("I", [0xa5a5a5a5] * len(expected)))
        fixture = f"shuffle_{mode}"
        driver.launch(fixture, [U64(destination + 8), U32(offset), U32(clamp), U32(mask), U32(base)], block=block)
        compare(f"shuffle_{mode}_{label}", fixture, destination, words("I", expected), block, (1, 1, 1))

    arena = driver.upload(words("I", [0xa5a5a5a5, 0, 0, 99, 0xa5a5a5a5]))
    driver.launch("release_acquire_message", [U64(arena + 4), U64(arena + 8), U64(arena + 12)], block=(2, 1, 1))
    compare("release_acquire_payload_flag_output_and_guards", "release_acquire_message", arena,
            words("I", [0xa5a5a5a5, 42, 1, 42, 0xa5a5a5a5]), (2, 1, 1), (1, 1, 1))

    src = driver.upload(words("I", [7, 4294967295, 42]))
    dst = driver.upload(words("I", [165] * 5))
    driver.launch("copy", [U64(src), U64(dst), U32(3)], block=(5, 1, 1))
    compare("copy_mask_and_frame", "copy", dst, words("I", [7, 4294967295, 42, 165, 165]), (5, 1, 1), (1, 1, 1))

    src = driver.upload(words("I", [13, 4294967295]))
    dst = driver.upload(words("I", [165] * 3))
    driver.launch("shared_swap", [U64(src), U64(dst)], block=(2, 1, 1))
    compare("shared_swap", "shared_swap", dst, words("I", [4294967295, 13, 165]), (2, 1, 1), (1, 1, 1))

    driver.launch("loop", [])
    results.append({"case": "loop", "fixture": "loop", "status": "passed", "evidence": "completion_only",
                    "block": [1, 1, 1], "grid": [1, 1, 1], "bytes_compared": 0})
    print("GPU completion only: loop (no exported result)", flush=True)

    dst = driver.upload(words("I", [0, 165]))
    driver.launch("barrier_publish", [U64(dst), U32(4294967295)], block=(2, 1, 1))
    compare("barrier_publish_global_and_frame", "barrier_publish", dst, words("I", [4294967295, 165]), (2, 1, 1), (1, 1, 1))

    src = driver.upload(words("f", [2, 3, 5]))
    dst = driver.upload(words("f", [999, 999]))
    driver.launch("float_fma", [U64(src), U64(dst)])
    compare("float_fma", "float_fma", dst, words("f", [11, 999]), (1, 1, 1), (1, 1, 1))
    driver.launch("float_literals", [U64(dst)])
    compare("float_literals", "float_literals", dst, words("f", [9, 999]), (1, 1, 1), (1, 1, 1))

    if tuple(driver.info["compute_capability"]) >= (8, 0):
        copied = [7, 4294967295, 42, 99]
        src = driver.upload(words("I", copied))
        dst = driver.upload(words("I", [165] * 5))
        driver.launch("cp_async_copy", [U64(src), U64(dst)])
        compare("cp_async_wait_shared_and_frame", "cp_async_copy", dst,
                words("I", copied + [165]), (1, 1, 1), (1, 1, 1))
    else:
        results.append({"case": "cp_async_wait_shared_and_frame", "fixture": "cp_async_copy",
                        "status": "skipped_unsupported_device", "evidence": "none",
                        "reason": "requires sm_80 or higher"})

    if tuple(driver.info["compute_capability"]) >= (8, 0):
        # Independent host matrices, serialized into NVIDIA's per-lane f16x2
        # fragment layout. All products/sums are exactly representable in f32.
        a_values = [(row + 2*k) % 3 - 1 for row in range(16) for k in range(16)]
        b_values = [(3*k + col) % 7 - 3 for k in range(16) for col in range(8)]
        a_fragments = [a_values[(lane//4 + 8*((slot//2) % 2))*16
                               + 2*(lane % 4) + slot % 2 + 8*(slot//4)]
                       for lane in range(32) for slot in range(8)]
        b_fragments = [b_values[(2*(lane % 4) + slot % 2 + 8*(slot//2))*8 + lane//4]
                       for lane in range(32) for slot in range(4)]
        a = driver.upload(words("e", a_fragments))
        b = driver.upload(words("e", b_fragments))
        dst = driver.upload(words("f", [999]*132))
        driver.launch("mma_probe", [U64(a), U64(b), U64(dst)], block=(32, 1, 1))
        matrix = matmul_reference(a_values, b_values, 16, 8, 16)
        expected = [matrix[(lane//4 + 8*(slot//2))*8 + 2*(lane % 4) + slot % 2]
                    for lane in range(32) for slot in range(4)]
        compare("mma_m16n8k16_full_warp_fragment_layout_and_frame", "mma_probe", dst,
                words("f", expected + [999]*4), (32, 1, 1), (1, 1, 1))
        results[-1].update({"shape": [16, 8, 16], "inputs": "exact small f16 integers",
                           "reference": "independent rational matmul, per-lane f32 output and guards"})
    else:
        results.append({"case": "mma_m16n8k16_full_warp_fragment_layout_and_frame", "fixture": "mma_probe",
                        "status": "skipped_unsupported_device", "evidence": "none",
                        "reason": "requires sm_80 or higher"})

    if tuple(driver.info["compute_capability"]) >= (8, 0):
        for label, m, n, k, grid in [
            ("single_tile", 16, 8, 16, (1, 1, 1)),
            ("multi_cta_reuse_three_k_tiles", 32, 16, 48, (2, 2, 1)),
            ("zero_k_unused_inputs_alias_c", 16, 8, 0, (1, 1, 1)),
            ("uniform_mask_and_reuse_two_k_tiles", 16, 8, 32, (2, 2, 1)),
        ]:
            a_values = [(2*row + 3*t) % 5 - 2 for row in range(m) for t in range(k)]
            b_values = [(3*t + 2*col) % 7 - 3 for t in range(k) for col in range(n)]
            dst = driver.upload(words("f", [999]*(m*n+4)))
            if k:
                a_bytes = words("e", a_values)
                # Kernel contract stores B column-major, independent of host ref.
                b_bytes = words("e", [b_values[t*n+col] for col in range(n) for t in range(k)])
                a, b = driver.upload(a_bytes), driver.upload(b_bytes)
            else:
                a = b = dst
            driver.launch("ampere_tiled_matmul", [U64(a), U64(b), U64(dst), U32(m), U32(n), U32(k)],
                          block=(4, 8, 1), grid=grid)
            expected = matmul_reference(a_values, b_values, m, n, k)
            compare("ampere_tiled_"+label, "ampere_tiled_matmul", dst,
                    words("f", expected+[999]*4), (4, 8, 1), grid)
            if k:
                if driver.download(a, len(a_bytes)) != a_bytes or driver.download(b, len(b_bytes)) != b_bytes:
                    raise AssertionError("Ampere tiled matmul changed an input buffer")
            results[-1].update({"shape": [m,n,k], "input_layout": "A row-major f16; B column-major f16",
                               "reference": "independent rational matmul; exact f32 results and guards",
                               "input_frame": "all input bytes unchanged" if k else "unused A/B alias C",
                               "k_tiles": k//16})
    else:
        results.append({"case": "ampere_tiled_matmul", "fixture": "ampere_tiled_matmul",
                        "status": "skipped_unsupported_device", "evidence": "none",
                        "reason": "requires sm_80 or higher"})

    a = driver.upload(words("f", [2, 5, 7, 11]))
    b = driver.upload(words("f", [3, 4, 5, 7, 8, 9]))
    dst = driver.upload(words("f", [999] * 8))
    driver.launch("scalar_matmul", [U64(a), U64(b), U64(dst), U32(2), U32(3), U32(2)], block=(2, 2, 1), grid=(2, 1, 1))
    expected = matmul_reference([2, 5, 7, 11], [3, 4, 5, 7, 8, 9], 2, 3, 2)
    compare("matmul_2x3x2_mask_frame", "scalar_matmul", dst, words("f", expected + [999, 999]), (2, 2, 1), (2, 1, 1))
    driver.launch("scalar_matmul", [U64(dst), U64(dst), U64(dst), U32(2), U32(3), U32(0)], block=(2, 2, 1), grid=(2, 1, 1))
    compare("matmul_zero_k_alias_frame", "scalar_matmul", dst, words("f", [0] * 6 + [999, 999]), (2, 2, 1), (2, 1, 1))

    # Both modules were already loaded above. Queue dependent launches on the
    # same default stream, with one completion wait after both and no host wait
    # or JIT/module loading between them. A/B/C and their guards share an arena.
    arena = driver.upload(words("f", [999, 999, 2, 999, 999, 999]))
    driver.launch("float_literals", [U64(arena)], synchronize=False)
    driver.launch("scalar_matmul", [U64(arena), U64(arena + 8), U64(arena + 16),
                  U32(1), U32(1), U32(1)], synchronize=False)
    driver.call("cuCtxSynchronize")
    literal_result = (1 + 2) * 3
    result = matmul_reference([literal_result], [2], 1, 1, 1)[0]
    compare("stream_literal_then_matmul", "scalar_matmul", arena,
            words("f", [literal_result, 999, 2, 999, result, 999]), (1, 1, 1), (1, 1, 1))
    results[-1].update({"launches": ["float_literals", "scalar_matmul"], "stream": "default",
                        "intermediate_host_synchronize": False})

    dst = driver.upload(words("I", [0, 165, 165, 165]))
    driver.launch("atomic_dispatch", [U64(dst), U64(dst + 4), U64(dst + 8)], grid=(2, 1, 1))
    compare("atomic_dispatch_two_ctas", "atomic_dispatch", dst, words("I", [2, 1, 2, 165]), (1, 1, 1), (2, 1, 1))

    scale = driver.upload(words("f", [1]))
    key = driver.upload(words("f", [0, 1]))
    value = driver.upload(words("f", [4, 10]))
    for name, q_value in [("changed_maximum", 1), ("equal_scores", 0)]:
        q = driver.upload(words("f", [q_value]))
        dst = driver.upload(words("f", [999, 999]))
        driver.launch("scalar_flash_attention", [U64(q), U64(key), U64(value), U64(dst), U64(scale), U32(1), U32(2), U32(1)])
        expected = attention_reference([q_value], [[0], [1]], [4, 10], 1)
        compare("attention_" + name, "scalar_flash_attention", dst, words("f", [expected, 999]), (1, 1, 1), (1, 1, 1))
    q_data, key_data, value_data = [1] * 9, [0] * 6, [7] * 6
    q, key, value = [driver.upload(words("f", data)) for data in (q_data, key_data, value_data)]
    dst = driver.upload(words("f", [999] * 11))
    driver.launch("scalar_flash_attention", [U64(q), U64(key), U64(value), U64(dst), U64(scale),
                  U32(3), U32(2), U32(3)], block=(2, 2, 1), grid=(2, 2, 1))
    expected = [attention_reference(q_data[row*3:(row+1)*3],
                [key_data[item*3:(item+1)*3] for item in range(2)],
                [value_data[item*3+col] for item in range(2)], 1)
                for row in range(3) for col in range(3)]
    compare("attention_3x3x2_mask_frame", "scalar_flash_attention", dst,
            words("f", expected + [999, 999]), (2, 2, 1), (2, 2, 1))
    dst = driver.upload(words("f", [999, 999]))
    driver.launch("scalar_flash_attention", [U64(dst)] * 5 + [U32(1), U32(0), U32(1)])
    compare("attention_empty_keys_alias_frame", "scalar_flash_attention", dst, words("f", [0, 999]), (1, 1, 1), (1, 1, 1))

    # Actual normalized top-1 MoE, three preloaded kernels on one default
    # stream. Compare the entire arena: gates/X/W, routes, both expert planes,
    # final output and a guard after every segment. No intermediate host wait.
    for fixture in ("moe_route", "moe_experts", "moe_combine"):
        driver.preload(fixture)

    def moe_case(name, gates, x, weights, m, n, k, alias_unused=False):
        routes = [int(gates[2*row+1] > gates[2*row]) for row in range(m)]
        outputs = [sum(Fraction(x[row*k+t]) * weights[(routes[row]*k+t)*n+col]
                       for t in range(k)) for row in range(m) for col in range(n)]
        expert_values = [999] * (2*m*n)
        for row in range(m):
            for col in range(n):
                expert_values[(routes[row]*m+row)*n+col] = outputs[row*n+col]
        initial, expected, offsets = bytearray(), bytearray(), {}
        for label, kind, before, after in (
            ("G", "f", gates, gates), ("X", "f", x, x), ("W", "f", weights, weights),
            ("R", "I", [165]*m, routes), ("H", "f", [999]*(2*m*n), expert_values),
            ("Y", "f", [999]*(m*n), outputs),
        ):
            offsets[label] = len(initial)
            initial.extend(words(kind, before) + words("I", [0xDEADBEEF]))
            expected.extend(words(kind, after) + words("I", [0xDEADBEEF]))
        arena = driver.upload(bytes(initial))
        addresses = {label: arena+offset for label, offset in offsets.items()}
        if alias_unused:
            # K=0 or N=0 avoids X/W reads; M=0 masks all data accesses.
            for label in (("G", "X", "W", "R", "H", "Y") if m == 0 else ("X", "W")):
                addresses[label] = arena+offsets["H"]
        route_block, route_grid = (2, 1, 1), (max(1, (m+1)//2), 1, 1)
        block, grid = (2, 2, 1), (max(1, (n+1)//2), max(1, (m+1)//2), 1)
        driver.launch("moe_route", [U64(addresses["G"]), U64(addresses["R"]), U32(m)],
                      block=route_block, grid=route_grid, synchronize=False)
        driver.launch("moe_experts", [U64(addresses[label]) for label in ("X", "W", "R", "H")]
                      + [U32(m), U32(n), U32(k)], block=block, grid=grid, synchronize=False)
        driver.launch("moe_combine", [U64(addresses[label]) for label in ("R", "H", "Y")]
                      + [U32(m), U32(n)], block=block, grid=grid, synchronize=False)
        driver.call("cuCtxSynchronize")
        compare("moe_"+name, "moe_combine", arena, bytes(expected), block, grid)
        results[-1].update({"launches": ["moe_route", "moe_experts", "moe_combine"],
                            "stream": "default", "intermediate_host_synchronize": False,
                            "route_block": route_block, "route_grid": route_grid,
                            "dimensions_mnk": [m, n, k], "selected_experts": routes,
                            "unused_input_alias": alias_unused,
                            "arena_segments": offsets})

    moe_case("mixed_ties_mask_frame", [4, 1, -2, 3, 7, 7], [1, 2, 3, 4, 5, 6],
             list(range(1, 13)), 3, 3, 2)
    subnormal = struct.unpack("<f", words("I", [1]))[0]
    moe_case("negative_and_subnormal_gates", [-3, -2, 0, subnormal], [2, -3],
             [1, 2, 3, 4], 2, 2, 1)
    moe_case("zero_k_alias_frame", [1, 0, 0, 1], [], [], 2, 3, 0, alias_unused=True)
    moe_case("empty_columns_alias_frame", [1, 0, 0, 1], [], [], 2, 0, 2, alias_unused=True)
    moe_case("empty_rows_alias_frame", [], [], list(range(1, 13)), 0, 3, 2, alias_unused=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--device", type=int, default=0)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--timeout", type=float, default=60, help="Whole-run watchdog in seconds; timeout fails")
    args = parser.parse_args()
    report = {"schema_version": 1, "timestamp_utc": datetime.now(timezone.utc).isoformat(), "status": "failed",
              "scope": "finite GPU execution; exact bytes without float tolerance; separate from formal proofs",
              "reference": "independent integer shuffle selection/value/predicate and exact rational host matrix/direct-attention/top-1 MoE specs on small selected inputs",
              "limits": ["loop exports no result; completion only",
                         "barrier_publish exports only the producer write; its unused consumer load may be optimized away",
                         "shuffle probes use defined active sources; no proof of general TTGIR/PTX lowering",
                         "no universal IEEE/approximation or performance claim"], "cases": []}
    if args.timeout <= 0:
        parser.error("--timeout must be positive")

    report_lock = threading.Lock()

    def persist():
        if args.report:
            with report_lock:
                args.report.parent.mkdir(parents=True, exist_ok=True)
                temporary = args.report.with_suffix(args.report.suffix + ".tmp")
                temporary.write_text(json.dumps(report, indent=2) + "\n")
                temporary.replace(args.report)

    def expired():
        report["status"] = "failed_timeout"
        report["error"] = f"GPU watchdog expired after {args.timeout}s at {report.get('active_fixture', 'initialization')}"
        try:
            persist()
            print(report["error"], file=sys.stderr, flush=True)
        finally:
            os._exit(124)

    def started(fixture):
        report["active_fixture"] = fixture
        persist()

    watchdog = threading.Timer(args.timeout, expired)
    watchdog.daemon = True
    watchdog.start()
    driver = None
    try:
        driver = Driver(args.device)
        driver.on_launch = started
        report["device"] = driver.info
        print(f"GPU: {driver.info['name']} sm_{''.join(map(str, driver.info['compute_capability']))}", flush=True)
        run_cases(driver, report["cases"])
        report["source_sha256"] = {name: data[2] for name, data in driver.modules.items()}
        report.pop("active_fixture", None)
        report["status"] = "passed"
    except (OSError, RuntimeError, AssertionError, ValueError) as error:
        report["error"] = str(error)
        print(str(error), file=sys.stderr)
    finally:
        if driver is not None:
            driver.close()
        watchdog.cancel()
        persist()
    if report["status"] != "passed":
        return 1
    compared = sum(item["evidence"] == "exact_bytes" for item in report["cases"])
    print(f"GPU checks passed: {compared} exact-byte comparisons, 1 completion-only smoke check")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

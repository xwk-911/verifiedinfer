# PTX Verify

Translate a PTX kernel into Lean program data, then check its Lean specification
and proof. Translation alone does not prove correctness.

## Environment

From the repository root on the host:

```sh
./dev build ptx
```

The tool's own [Dockerfile](Dockerfile) installs Rust, Python, Lean **4.35.0**,
CUDA tools, pinned Iris and Mathlib dependencies during the image build.
Runtime commands below run offline and require no bootstrap or host toolchain.
Run them from the repository root; PTX input/output paths are relative to
`tools/ptx-verify/`. Generated files remain in your checkout; compilation caches
use Docker volumes. Rebuild the image after changing dependency versions.

## 1. Translate

```sh
./dev run --rm ptx translate examples/copy.ptx lean/Ptx/Generated/Copy.lean
```

This reads PTX and writes typed Lean program data. Unsupported syntax or
instructions return an error. It does not generate a correctness proof.

## 2. Verify

For the Copy example, the repository already contains a specification and proofs:

```sh
./dev run --rm ptx verify Ptx.Kernels.CopyEventWitness \
    Ptx.CopyEvent.correct Ptx.CopyEvent.nonvacuous
```

The first argument is the Lean proof module; remaining arguments name the
proof theorems to check. This step builds that module, checks the selected proofs
and their transitive axiom dependencies, and prints the proved statements.
Temporary `sorry` is allowed in ordinary proof files during development;
any selected theorem that depends on it, including through a helper lemma, fails
verification as unfinished. It does not
translate PTX again, run other cases, or execute GPU tests.

For a new kernel, use your own PTX/generated module in step 1. Before step 2,
write its specification and proof in `lean/Ptx/Kernels/`, importing the generated
program, then pass that module and its theorem names to `ptx verify`. The checker
checks a supplied proof; it does not automatically prove arbitrary kernels.

To use this tool separately from the engine, run `docker compose build` from
`tools/ptx-verify/`, then use `docker compose run --rm ptx translate ...` and
`docker compose run --rm ptx verify ...`. For a host UID/GID other than 1000,
export `HOST_UID=$(id -u)` and `HOST_GID=$(id -g)` first; `./dev` sets them for you.

## Scope and documentation

Proofs apply to their stated model and preconditions. Floating-point proofs use
exact-real models; IEEE behavior and physical compiler/runtime conformance remain
outside those proofs. GPU tests provide separate finite execution evidence.

- [Supported instructions](instructions.toml) and [coverage limits](coverage.toml).
- [Example kernels and proofs](lean/Ptx/Kernels/).
- [Memory model](docs/memory-model.md) and [developer notes](docs/development-notes.md).

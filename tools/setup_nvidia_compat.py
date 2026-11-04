"""Extract matching NVIDIA userspace libraries locally; never install a driver."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import urllib.request


LIBRARIES = (
    "libcuda.so.*",
    "libnvidia-ml.so.*",
    "libnvidia-ptxjitcompiler.so.*",
    "libnvidia-nvvm.so.*",
    "libnvidia-gpucomp.so.*",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--archive", type=Path, help="Already downloaded official .run archive"
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    version = Path("/sys/module/nvidia/version").read_text().strip()
    if not re.fullmatch(r"\d+\.\d+\.\d+", version):
        parser.error("cannot identify active NVIDIA module version")
    archive = args.archive or root / "build" / f"NVIDIA-Linux-x86_64-{version}.run"
    url = (
        f"https://us.download.nvidia.com/XFree86/Linux-x86_64/{version}/"
        f"NVIDIA-Linux-x86_64-{version}.run"
    )
    archive.parent.mkdir(parents=True, exist_ok=True)
    if not archive.is_file():
        partial = archive.with_suffix(".part")
        urllib.request.urlretrieve(url, partial)
        partial.rename(archive)
    extracted = root / "build" / f"nvidia-driver-{version}"
    if not extracted.is_dir():
        subprocess.run(
            ["sh", str(archive.resolve()), "--extract-only", "--target", str(extracted)],
            check=True,
        )
    destination = root / "build" / "nvidia-compat" / version
    destination.mkdir(parents=True, exist_ok=True)
    for pattern in LIBRARIES:
        for source in extracted.glob(pattern):
            target = destination / source.name
            target.unlink(missing_ok=True)
            target.symlink_to(source)
            dynamic = subprocess.check_output(["readelf", "-d", str(source)], text=True)
            soname = re.search(r"SONAME.*\[(.+?)\]", dynamic)
            if soname and soname[1] != source.name:
                link = destination / soname[1]
                link.unlink(missing_ok=True)
                link.symlink_to(source.name)
    link = destination / "nvidia-smi"
    link.unlink(missing_ok=True)
    link.symlink_to(extracted / "nvidia-smi")
    with archive.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    manifest = {
        "active_module": version,
        "source": url,
        "archive_sha256": digest,
    }
    (destination / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Compatibility libraries: {destination}")
    firmware = Path("/lib/firmware/nvidia") / version / "gsp_ga10x.bin"
    if not firmware.is_file():
        print(
            "The running kernel module also needs missing firmware. "
            "An administrator may restore it with:"
        )
        print(shlex.join([
            "sudo", "install", "-D", "-m", "0644",
            str(extracted / "firmware/gsp_ga10x.bin"), str(firmware),
        ]))
    print("Run: sh tools/with_nvidia.sh nvidia-smi")


if __name__ == "__main__":
    main()

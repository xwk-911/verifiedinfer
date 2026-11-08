#!/usr/bin/env python3
"""Image-build-only dependency installation from the committed Lake manifest."""

import json
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IRIS_REV = "956f5482cf6f3970bb34d68e3813c73b0f9b1245"


def checkout(url, revision, destination):
    destination.mkdir(parents=True)
    subprocess.run(["git", "init", "--quiet", str(destination)], check=True)
    subprocess.run(["git", "-C", str(destination), "remote", "add", "origin", url], check=True)
    command = ["git", "-C", str(destination), "-c", "http.version=HTTP/1.1",
               "fetch", "--depth=1", "origin", revision]
    for attempt in range(4):
        try:
            subprocess.run(command, check=True)
            break
        except subprocess.CalledProcessError:
            if attempt == 3:
                raise
            time.sleep(2 ** attempt)
    subprocess.run(["git", "-C", str(destination), "checkout", "--detach", "FETCH_HEAD"], check=True)


checkout("https://github.com/leanprover-community/iris-lean.git", IRIS_REV, ROOT / "vendor/iris-lean")
manifest = json.loads((ROOT / "lean/lake-manifest.json").read_text())
for package in manifest["packages"]:
    if package["type"] == "git":
        checkout(package["url"], package["rev"], ROOT / "lean/.lake/packages" / package["name"])

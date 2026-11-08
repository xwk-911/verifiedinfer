# Tools

从仓库根目录通过 Compose 使用工具：

```bash
./dev run --rm qcp check
./dev run --rm ptx translate examples/copy.ptx lean/Ptx/Generated/Copy.lean
./dev run --rm ptx verify Ptx.Kernels.CopyEventWitness Ptx.CopyEvent.correct
./dev run --rm engine make compile-commands
```

- [QCP](QCP/README.md)：C 符号执行及验证；镜像复用 `coq` 工具链，在构建时编译上游 Rocq 基础库。首次构建前运行 `git submodule update --init --recursive tools/QCP`；启动时不下载。验证具体 C 模块时遵循其工作流，项目的 `proof/` 规则单独管理。
- [PTX Verify](ptx-verify/README.md)：自有镜像提供 PTX 翻译和 Lean 证明检查；Iris、Mathlib 依赖在镜像构建时准备，翻译和验证分两步运行。
- `download_model.py`、`check_model.py`：模型下载和独立参考检查。常用模型由 `engine generate` 自动准备；高级选项见脚本 `--help`。
- `setup_nvidia_compat.py`、`with_nvidia.sh`：已有的宿主机驱动兼容工具。Compose 入口自动使用与当前内核模块匹配的本地库。

环境与常用运行命令见 [项目说明](../README.md)。

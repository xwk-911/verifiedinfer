# Tools

从仓库根目录通过 Compose 使用工具：

```bash
./dev run --rm qcp check
./dev run --rm ptx check
./dev run --rm engine make compile-commands
```

- [QCP](QCP/README.md)：C 内存与状态验证；`check` 自动初始化子模块并构建 Rocq 基础库。验证具体 C 模块时遵循其工作流。
- [PTX Verify](ptx-verify/README.md)：PTX 翻译及 Lean kernel 规约检查；`check` 自动准备依赖并运行现有检查。
- `download_model.py`、`check_model.py`：模型下载和独立参考检查。常用模型由 `engine generate` 自动准备；高级选项见脚本 `--help`。
- `setup_nvidia_compat.py`、`with_nvidia.sh`：已有的宿主机驱动兼容工具。Compose 入口自动使用与当前内核模块匹配的本地库。

环境与常用运行命令见 [项目说明](../README.md)。

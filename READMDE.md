# VerifiedInfer

最小 C/CUDA 推理引擎及验证实验。模型前向、KV 状态与 greedy 采样在 C/CUDA 中执行；Python 负责 tokenizer、chat template 和独立参考检查。

需要 Linux、NVIDIA GPU/驱动、Docker Engine、NVIDIA Container Toolkit 和 Docker Compose v2.30+。`./dev` 是项目的 Compose 入口：将当前仓库挂载到容器内相同的绝对路径，并使用宿主机用户身份运行。代码、模型、构建产物和缓存均保留在宿主机工作目录。

```bash
./dev build

# Mock 示例
./dev run --rm engine make demo mock

# 真实模型：首次运行自动准备模型并编译 CUDA 引擎
./dev run --rm engine generate --model smollm2 \
    --prompt "What is the capital of France?" --max-new-tokens 32
./dev run --rm engine generate --model qwen \
    --prompt "法国的首都是哪里？" --max-new-tokens 32

# C 回归及模型兼容性测试
./dev run --rm engine make test model-test

# QCP 的 Rocq 基础库；PTX 翻译器和 Lean 检查
./dev run --rm qcp check
./dev run --rm ptx check

# 导出自有 CUDA 算子的 PTX
./dev run --rm engine make cuda-ptx
```

测试与形式证明分别报告：模型测试检查固定执行方案下的精确一致性；QCP/PTX 命令检查各自已有的基础库或示例，不代表已证明整个推理引擎。cuBLAS、CUDA runtime、编译器及跨证明器连接仍属于证明边界。

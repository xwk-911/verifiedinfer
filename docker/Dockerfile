ARG CUDA_IMAGE=nvcr.io/nvidia/cuda:12.8.1-devel-ubuntu24.04@sha256:520292dbb4f755fd360766059e62956e9379485d9e073bbd2f6e3c20c270ed66
FROM ${CUDA_IMAGE} AS base
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
    bash build-essential ca-certificates curl git libgmp-dev pkg-config \
    python3 python3-venv unzip zstd \
    && rm -rf /var/lib/apt/lists/*
ENV CUDA_HOME=/usr/local/cuda CUDA_HOST_CXX=/usr/bin/g++
ENTRYPOINT ["/opt/verifiedinfer/entrypoint.sh"]
CMD ["bash"]

FROM base AS engine
RUN python3 -m venv /opt/venv
COPY requirements.txt /opt/verifiedinfer/requirements.txt
RUN /opt/venv/bin/pip install --no-cache-dir --upgrade pip \
    && /opt/venv/bin/pip install --no-cache-dir --retries 8 --timeout 60 \
        -r /opt/verifiedinfer/requirements.txt
ENV PATH=/opt/venv/bin:$PATH PYTHON=/opt/venv/bin/python VI_SERVICE=engine \
    CUDA=1 VI_DEVICE=cuda
COPY --chmod=755 entrypoint.sh infer.py /opt/verifiedinfer/
CMD ["bash"]

# Optional CPU inference target; intentionally disabled and absent from Compose.
# FROM engine AS cpu
# ENV CUDA=0 VI_DEVICE=cpu

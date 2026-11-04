ARG CUDA_IMAGE=nvcr.io/nvidia/cuda:12.8.1-devel-ubuntu24.04@sha256:520292dbb4f755fd360766059e62956e9379485d9e073bbd2f6e3c20c270ed66
ARG RUST_IMAGE=public.ecr.aws/docker/library/rust:1.90.0-slim-bookworm@sha256:64232e656c058f4468e8d024e990acff04f0fd5a5c0a88a574dc37773d7325c9

FROM ${RUST_IMAGE} AS rust

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

# Optional CPU inference target; intentionally disabled and absent from Compose.
# FROM engine AS cpu
# ENV CUDA=0 VI_DEVICE=cpu

FROM base AS qcp
RUN apt-get update && apt-get install -y --no-install-recommends opam libgmp-dev rsync \
    && rm -rf /var/lib/apt/lists/*
RUN python3 -m venv /opt/venv \
    && /opt/venv/bin/pip install --no-cache-dir uv==0.12.15 pytest==9.1.1
ENV OPAMROOT=/opt/opam OPAMJOBS=4
RUN opam init --disable-sandboxing --bare --yes \
    && opam switch create /opt/coq ocaml-base-compiler.4.14.1 --yes
RUN opam install --switch=/opt/coq --yes coq.8.20.1 dune.3.17.2 \
    && opam clean --all-switches --download-cache --logs --yes \
    && chmod -R a+rX /opt/opam /opt/coq
ENV PATH=/opt/coq/_opam/bin:/opt/venv/bin:$PATH VI_SERVICE=qcp
RUN coqc --version && dune --version
COPY --chmod=755 entrypoint.sh /opt/verifiedinfer/
CMD ["check"]

FROM base AS ptx
COPY --from=rust /usr/local/cargo /opt/cargo
COPY --from=rust /usr/local/rustup /opt/rustup
ARG LEAN_VERSION=4.35.0
RUN curl --fail --location --retry 3 \
    "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst" \
    -o /tmp/lean.tar.zst \
    && mkdir -p /opt/lean \
    && tar --zstd -xf /tmp/lean.tar.zst --strip-components=1 -C /opt/lean \
    && rm /tmp/lean.tar.zst
ENV PATH=/opt/lean/bin:/opt/cargo/bin:$PATH RUSTUP_HOME=/opt/rustup \
    LEAN_TOOLCHAIN_DIR=/opt/lean VI_SERVICE=ptx
RUN rustup component add rustfmt clippy
RUN rustc --version && cargo --version && lean --version && ptxas --version
COPY --chmod=755 entrypoint.sh ptx-check.sh /opt/verifiedinfer/
CMD ["check"]

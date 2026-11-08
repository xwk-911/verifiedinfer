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

FROM base AS toolchain
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
    LEAN_TOOLCHAIN_DIR=/opt/lean PTXAS=/usr/local/cuda/bin/ptxas
RUN rustup component add rustfmt clippy
RUN apt-get update && apt-get install -y --no-install-recommends rsync \
    && rm -rf /var/lib/apt/lists/*

FROM toolchain AS dependencies
WORKDIR /opt/ptx-verify
COPY lean/lean-toolchain lean/lakefile.toml lean/lake-manifest.json ./lean/
COPY docker/install-deps.py ./docker/install-deps.py
# Fetch exact manifest revisions; cache retrieval is a build step, never startup.
RUN python3 docker/install-deps.py && cd lean && lake exe cache get \
    && chmod -R a+rX .lake/packages ../vendor
RUN cd lean && lake build @iris

FROM dependencies AS ptx
COPY . .
COPY --chmod=755 docker/entrypoint.sh /usr/local/bin/ptx-entrypoint
RUN cargo build --locked --offline \
    && cd lean && lake build Ptx.Kernels.CopyEventWitness PtxPrototype.Audit
# Lake lazily regenerates small hash/trace files even for cached Mathlib modules.
# Allow arbitrary container UIDs to maintain metadata without duplicating the
# multi-gigabyte compiled libraries in another image layer.
RUN find vendor lean/.lake/packages -type d -exec chmod a+rwx {} + \
    && find vendor lean/.lake/packages -type f \
        \( -name '*.hash' -o -name '*.trace' -o -name '*.log' \) -exec chmod a+rw {} +
RUN find . -path ./vendor -prune -o -path ./lean/.lake/packages -prune \
    -o -exec chmod a+rwX {} +
ENV CARGO_TARGET_DIR=/opt/ptx-verify/target CARGO_NET_OFFLINE=true
ENTRYPOINT ["/usr/local/bin/ptx-entrypoint"]
CMD ["help"]

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

FROM base AS coq
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
ENV PATH=/opt/coq/_opam/bin:/opt/venv/bin:$PATH VI_SERVICE=coq
RUN coqc --version && dune --version
COPY --chmod=755 docker/entrypoint.sh /opt/verifiedinfer/

FROM coq AS qcp
COPY tools/QCP /opt/qcp
ARG MAKE_JOBS=4
RUN test -x /opt/qcp/bin/linux/symexec \
    && make -C /opt/qcp/Rocq -j${MAKE_JOBS} core
ENV UV_PROJECT_ENVIRONMENT=/opt/venv UV_PYTHON_DOWNLOADS=never
RUN uv sync --frozen --project /opt/qcp
ENV UV_OFFLINE=true
ENV PATH=/opt/qcp/bin/linux:$PATH VI_SERVICE=qcp QCP_IMAGE_ROOT=/opt/qcp
CMD ["check"]

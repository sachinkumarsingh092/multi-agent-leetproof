# syntax=docker/dockerfile:1

FROM ghcr.io/astral-sh/uv:0.11.28 AS uv

FROM python:3.13-slim-trixie

RUN python -c "import sqlite3; value = sqlite3.connect(':memory:').execute(\"SELECT unixepoch('subsec')\").fetchone()[0]; assert value is not None, sqlite3.sqlite_version"

RUN apt-get update \
    && apt-get install --yes --no-install-recommends \
        build-essential \
        ca-certificates \
        curl \
        git \
        libgmp-dev \
        unzip \
        zstd \
    && rm -rf /var/lib/apt/lists/*

RUN useradd --create-home --uid 10001 worker \
    && mkdir -p /opt/leetproof /workspace \
    && chown -R worker:worker /opt/leetproof /workspace

COPY --from=uv /uv /uvx /usr/local/bin/

USER worker
ENV HOME=/home/worker \
    ELAN_HOME=/home/worker/.elan \
    PATH=/home/worker/.elan/bin:/opt/leetproof/leetproof/.venv/bin:${PATH} \
    PYTHONDONTWRITEBYTECODE=1 \
    UV_NO_PROGRESS=1

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none

WORKDIR /opt/leetproof
COPY --chown=worker:worker lean-worker/lean-toolchain ./lean-toolchain
RUN LEAN_TOOLCHAIN="$(tr -d '\n' < lean-toolchain)" \
    && if ! elan toolchain list | grep -Fq "${LEAN_TOOLCHAIN}"; then \
        for attempt in 1 2 3; do \
            if elan toolchain install "${LEAN_TOOLCHAIN}"; then break; fi; \
            if [ "${attempt}" -eq 3 ]; then exit 1; fi; \
            sleep 5; \
        done; \
    fi

COPY --chown=worker:worker leetproof ./leetproof
RUN --mount=type=cache,target=/home/worker/.cache/uv,uid=10001,gid=10001 \
    uv sync --project /opt/leetproof/leetproof --frozen --no-dev

WORKDIR /workspace
COPY --chown=worker:worker lean-worker ./
RUN lake exe cache get \
    && lake build Extensions \
    && rm -rf /home/worker/.cache/mathlib

ENTRYPOINT ["lloom-agent"]

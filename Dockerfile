# Multi-stage Dockerfile for erdos-ai.
# Stage 1 caches elan, Lean, and the Mathlib oleans (~6 GB) so that subsequent
# builds only recompile changed .lean files.
#
# Build:   docker build -t erdos-ai .
# Run:     docker run --rm -it erdos-ai lake build conjectures/13.lean
# Shell:   docker run --rm -it erdos-ai bash

# ---------------------------------------------------------------------------
# Stage 1: toolchain + Mathlib cache (rebuilds only when lean-toolchain,
# lakefile.toml, or lake-manifest.json change)
# ---------------------------------------------------------------------------
FROM ubuntu:24.04 AS base

RUN apt-get update && apt-get install -y --no-install-recommends \
    curl git ca-certificates python3 \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
ENV ELAN_HOME="/root/.elan"
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

WORKDIR /workspace

# Copy only the files Lake needs to resolve deps + fetch cache.
COPY lean-toolchain lakefile.toml lake-manifest.json ./

# Fetch Lean toolchain (triggered by lean-toolchain) and Mathlib oleans.
RUN lake exe cache get

# ---------------------------------------------------------------------------
# Stage 2: full repo on top of the cached environment
# ---------------------------------------------------------------------------
FROM base AS workspace

COPY . .

# Build project targets so subsequent container runs reuse compiled oleans.
RUN lake build

# Default: drop into a shell. Override with e.g. `lake build conjectures/13.lean`
CMD ["bash"]

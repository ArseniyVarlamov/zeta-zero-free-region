#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
if [ ! -x .venv/bin/python ]; then
    python3 -m venv .venv
fi
if ! .venv/bin/python -c 'import flint; assert flint.__version__ == "0.8.0"' >/dev/null 2>&1; then
    PIP_CACHE_DIR="$PWD/.pip-cache" .venv/bin/python -m pip install --disable-pip-version-check python-flint==0.8.0 >&2
fi
.venv/bin/python verify.py "$@"

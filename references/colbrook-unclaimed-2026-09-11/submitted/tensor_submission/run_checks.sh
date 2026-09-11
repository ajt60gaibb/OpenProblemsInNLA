#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
python3 code/verify_results.py

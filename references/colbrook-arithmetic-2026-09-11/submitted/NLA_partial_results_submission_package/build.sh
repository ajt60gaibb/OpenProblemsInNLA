#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
CXX="${CXX:-g++}"
"$CXX" -O3 -std=c++17 src/find_min.cpp -o build/find_min
"$CXX" -O3 -std=c++17 -pthread src/verify_permanent.cpp -o build/verify_permanent
"$CXX" -O3 -std=c++17 src/spectrum.cpp -o build/spectrum
"$CXX" -O3 -std=c++17 src/check_range.cpp -o build/check_range
"$CXX" -O3 -std=c++17 src/extend_upper.cpp -o build/extend_upper

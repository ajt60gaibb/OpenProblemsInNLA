#!/usr/bin/env bash
# Run the preserved three-case probe against the prepared Comparator tool.
set -euo pipefail
replay_checks_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
replay_lean_root="$(cd -- "$replay_checks_dir/../.." && pwd)"
source "$replay_lean_root/.tools/env.sh"
cd -- "$replay_lean_root/.tools/comparator"
# Comparator and lean4export both name their executable module Main.
replay_lean_path="$PWD/.lake/build/lib/lean:$(lake env printenv LEAN_PATH)"
printf '%s\n' 'Replay probe: RestrictAddressFamilies=~AF_UNIX (deny AF_UNIX sockets).'
exec systemd-run --user --quiet --wait --pipe \
  -p 'RestrictAddressFamilies=~AF_UNIX' --working-directory="$PWD" \
  /usr/bin/env "PATH=$PATH" "LEAN_PATH=$replay_lean_path" \
  /bin/bash --noprofile --norc -c '
set -euo pipefail
lean --version | sed "s/, commit [^,)]*//"
lean --deps "$1"
exec lean "$1"
' replay-probe "$replay_checks_dir/PinnedReplayProbe.lean"

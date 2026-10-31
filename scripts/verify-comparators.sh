#!/usr/bin/env bash
set -euo pipefail

# Judge each Solution against its Challenge the way the Palomar registry does:
# with the `lake comparator` that ships in this project's own toolchain,
# replaying the proof through Lean's kernel and the toolchain's bundled
# independent kernels (NanoDa and con-ron). No separately installed comparator
# is used: everything that judges comes from `lean-toolchain`.
#
# Usage: scripts/verify-comparators.sh [NAME ...]
# Without arguments every configuration Audit/<NAME>/comparator.json is checked,
# one after the other; otherwise only the named ones. Build the project first
# (`lake build`).
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

if [ "$#" -eq 0 ]; then
  [ -d Audit ] || { echo "error: no Audit/ directory" >&2; exit 1; }
  mapfile -t names < <(find Audit -mindepth 2 -maxdepth 2 -name comparator.json -printf '%h\n' \
    | sed 's|^Audit/||' | sort)
else
  names=("$@")
fi
[ "${#names[@]}" -gt 0 ] || { echo "error: no Audit/<NAME>/comparator.json found" >&2; exit 1; }

workdir=$(mktemp -d "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -rf "$workdir"' EXIT

failed=()
for name in "${names[@]}"; do
  source_config="Audit/$name/comparator.json"
  [ -f "$source_config" ] || { echo "error: $source_config not found" >&2; exit 1; }
  # Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted
  # comparator.json: it registers the toolchain's bundled kernels itself. This
  # generated copy does the same, so the local check judges as the registry does.
  config="$workdir/$name.json"
  python3 - "$source_config" "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field; Palomar rejects it", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
  echo "=== comparator: $name"
  # Each configuration exports its own environments; give it its own temporary
  # directory and delete it as soon as the configuration is done.
  mkdir -p "$workdir/$name"
  if TMPDIR="$workdir/$name" lake comparator --config "$config"; then
    echo "=== $name: PASS"
  else
    echo "=== $name: FAIL"
    failed+=("$name")
  fi
  rm -rf "${workdir:?}/$name"
done

if [ "${#failed[@]}" -gt 0 ]; then
  echo "comparators failed: ${failed[*]}" >&2
  exit 1
fi
echo "all ${#names[@]} comparators passed"

#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

# Fetch the compiled dependencies imported by this project.
mapfile -t modules < <(awk '$1 == "import" && $2 ~ /^Mathlib\./ {print $2}' SU2WignerNegativity/*.lean | sort -u)
lean --version
lake exe cache get "${modules[@]}"
lake build
lake env lean Audit.lean

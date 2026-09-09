#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p build output/pdf
if [ -n "${TECTONIC:-}" ]; then
  "$TECTONIC" --keep-logs --keep-intermediates --outdir build main.tex
elif command -v latexmk >/dev/null 2>&1; then
  latexmk -xelatex -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build main.tex
elif command -v tectonic >/dev/null 2>&1; then
  tectonic --keep-logs --keep-intermediates --outdir build main.tex
else
  echo 'Install latexmk with XeLaTeX, or set TECTONIC to a Tectonic executable.' >&2
  exit 1
fi
cp build/main.pdf output/pdf/resonance_kinetic_en.pdf

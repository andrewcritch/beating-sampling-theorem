#!/bin/sh
# Build main.pdf from main.tex.
#
#   ./make-pdf.sh          compile main.tex
#   ./make-pdf.sh --all    first regenerate the Lean appendix from groups.py and
#                          check that the groups cover every Lean module
#   ./make-pdf.sh --watch  recompile whenever a source file changes
set -e
cd "$(dirname "$0")"

case "$1" in
  --all)
    python3 gen_appendix.py
    python3 check_coverage.py
    ;;
  --watch)
    last=""
    while true; do
      now=$(stat -f %m main.tex *.tex 2>/dev/null | tr '\n' ' ')
      if [ "$now" != "$last" ]; then
        last="$now"
        tectonic -X compile main.tex && echo "$(date '+%H:%M:%S') wrote main.pdf"
      fi
      sleep 1
    done
    ;;
esac

tectonic -X compile main.tex
echo "wrote $(pwd)/main.pdf"

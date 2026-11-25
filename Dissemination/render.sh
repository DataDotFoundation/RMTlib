#!/usr/bin/env bash
# Render one Dissemination video and stitch its scenes into <folder>/<folder>.mp4.
#   ./render.sh 01_some_video          720p30 (default)
#   ./render.sh 01_some_video -ql      480p15 preview
#   ./render.sh 01_some_video -qh      1080p60
# MEDIA_DIR=/elsewhere ./render.sh …  renders outside the tree.
# Canonical copy: DataDotFoundation/MeaningLib, Dissemination/render.sh (byte-identical copies
# downstream, checked by scripts/check_pins.py).
# The scene list is the SCENES list at the end of the folder's single .py file.
# Needs manim (pip install manim mpmath), LaTeX (texlive-latex-extra, dvisvgm) and ffmpeg.
set -euo pipefail
cd "$(dirname "$0")"
DIR="${1:?usage: ./render.sh <video-folder> [-ql|-qm|-qh|-qk]}"
QUALITY="${2:--qm}"
SRC="$(ls "$DIR"/*.py | head -n1)"
MOD="$(basename "$SRC" .py)"
MEDIA="${MEDIA_DIR:-$DIR/media}"
mapfile -t SCENES < <(python3 -I - "$SRC" <<'PY'
import ast, sys
tree = ast.parse(open(sys.argv[1]).read())
for node in tree.body:
    if isinstance(node, ast.Assign) and any(getattr(t, "id", None) == "SCENES" for t in node.targets):
        for elt in node.value.elts:
            print(elt.id)
PY
)
for s in "${SCENES[@]}"; do
  manim "$QUALITY" --media_dir "$MEDIA" "$SRC" "$s"
done
case "$QUALITY" in
  -ql) RES=480p15 ;; -qm) RES=720p30 ;; -qh) RES=1080p60 ;; -qk) RES=2160p60 ;; *) RES=720p30 ;;
esac
LIST="$MEDIA/scenes.txt"; : > "$LIST"
for s in "${SCENES[@]}"; do echo "file 'videos/$MOD/$RES/$s.mp4'" >> "$LIST"; done
ffmpeg -loglevel error -y -f concat -safe 0 -i "$LIST" -c copy "$DIR/$MOD.mp4"
rm -f "$LIST"
echo "wrote $PWD/$DIR/$MOD.mp4"

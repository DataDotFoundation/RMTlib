# Dissemination

Short Manim videos that explain RMTlib's mathematics to a wider audience. Nothing here is imported by
the Lean library. The videos use published mathematics and what RMTlib proves or states as a
conjecture in `docs/`, and they flag readings and heuristics as such. On screen, each claim carries
one of four tags: **proved** (in RMTlib, with the Lean name), **exact** (elementary, not yet
formalised), **reading** (our language, not a theorem), **conjecture**.

| folder | video | about |
|---|---|---|
| [`01_string_insertion/`](01_string_insertion/) | *The string-insertion law* | a partition as particles on a line (Maya diagram) under its Russian-notation profile, the padding as a gauge; the hook product in Frobenius form as a one-body `ℓ!` energy over the pair Vandermonde; inserting a string: `Hset(L ⊔ S)·Mut(L,S) = Hset(L)·Hset(S)`, self-energy minus mutual energy, and the Pauli obstruction; telescoping along a sequence; a commuting square as a growth-diagram cell, and the defect as a diagnostic; the place reading (`ℓ!` at ∞ versus `T^ℓ` at `p`); the string-insertion law, stated as a conjecture with what would refute it. Source: [`docs/string-insertion.md`](../docs/string-insertion.md), RMTlib#49 |

## Layout

- `common/style.py`: colours, titles, footers, and drawing helpers (Young diagrams, Russian
  notation, the light cone, corners), shared by every video. It is a copy of RH-Dual's
  `Dissemination/common/style.py`, so that the two repositories' videos look alike; keep the two in
  step until it moves to a shared place.
- One folder per video, each holding one `.py` file whose `SCENES` list gives the scene order.
- `render.sh`: renders one video and stitches its scenes (also copied from RH-Dual).

## Rendering

Needs [Manim Community](https://www.manim.community/) (0.22 was used), `mpmath`, a LaTeX
installation (`texlive-latex-extra`, `dvisvgm`) and `ffmpeg`.

```bash
pip install manim mpmath          # in a virtualenv if your Python is externally managed
```

```bash
./render.sh 01_string_insertion        # 720p30, writes 01_string_insertion/string_insertion.mp4
./render.sh 01_string_insertion -ql    # quick 480p preview
manim -ql 01_string_insertion/string_insertion.py OneInsertion   # one scene
```

Rendered videos and Manim's `media/` folders are not committed (see `.gitignore`).

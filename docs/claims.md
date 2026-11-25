# RMTlib's claims, at the maturity the evidence licenses

RMTlib owns two "hedgehog" topics, the **places** reading (our reading of Scholze's programme, not
a claim of Scholze's) and **boson–fermion**, together with their **junction**, and the duty to
communicate them (RMTlib#56; MeaningLib#45). This register lists each claim with its scope and
maturity. Notes and videos quote a claim **at this maturity, never above it**. Once MeaningLib's
`Claim` data lands (MeaningLib#45), these entries move into Lean and the corpus-readable part of the
maturity is computed rather than declared.

**Maturity ladder** (MeaningLib#45, with RMTlib's addition): idea → conjecture → checked on examples
→ exact on paper → stated in Lean → proved → pinned. **Reading** is a separate flag: an
interpretation of a statement, never a rung.

## Hedgehogs

| id | claim | maturity | evidence |
|---|---|---|---|
| H1 | **Places.** Every place, ∞ included, is one kind of object; a statement at one place has a counterpart at the others, and the counterpart moves content, support (the wall) or the one-body potential. | programme (frame `RMT.Frames.places`, hosted here since #58) | the frame's rules; reports below |
| H2 | **Boson–fermion.** `s_λ ↔` Maya diagram (`Fermion.ofRows`, `occ_ofRows_rowLen`), with ω as particle–hole conjugation (`ofRows_transpose`, `Maya.conj`). Statements that are one-body in the fermions are the uniform ones. | classical (lit), the correspondence's pieces **proved**; the "one-body ⇒ uniform" part a **conjecture** (#52) | #11, #12, #52 |

## Junctions

| id | claim | maturity | statements |
|---|---|---|---|
| J1 | **Places × boson–fermion: the place enters only through a one-body potential on Maya sites**, affine at `p`, not at ∞. | **proved for BDTW pattern A**; **pinned** for the potential roles; otherwise a conjecture | `det_mul_diagonal_mul_transpose`, `bdtw_inf`/`bdtw_fin` (instances, twin witnessed), `isExpLinear_rhoFin`, `not_isExpLinear_rhoInf` (REFUTED row pinned) |
| J2 | **ω × places: ω is the same particle–hole swap at ∞ and at every `p`.** At ∞ the hook product is a two-species log-gas in Frobenius coordinates; at `p` its valuations are core statistics. | **checked on examples** (#53: 271 and 3,348 exact checks) | none in Lean yet (#53 targets) |

## Foxes (specific results the hedgehogs rest on)

| id | claim | maturity | statement |
|---|---|---|---|
| F1 | The boson's wall is the ω-image of the fermion's: `s_λ(m vars) = 0` for `ℓ(λ) > m`, via `e_k = 0` for `k > m`. | proved | `schurV_eq_zero_of_length` |
| F2 | `L₁^{(a)}` removes one box from `s_μ` with weight `a + c` (in `Λ`, every charge). | proved | `L1_eDetP`, `L1_eP` |
| F3 | String insertion: `Hset(L ⊔ S)·Mut(L,S) = Hset(L)·Hset(S)`; a translation by `Δ` contributes `∏(ℓ+1)_Δ`. | identity **proved** (Vandermonde form); translation factor **exact on paper** | `vd_union`, `fac_union`; `docs/string-insertion.md` |
| F4 | String-insertion **law** along theta lifts (slack = one-body + two-body increments, telescoping, exact squares). | **checked on one example** (RH-Dual #39); otherwise a conjecture | `docs/string-insertion.md` |
| F5 | The moment measure puts its mass at the wall (`N·P(λ₁ = N) → k²`); the wall is a hard edge. | **checked on examples** (Loop 3); "hard edge / Bessel" a **reading** | `scripts/wall_moments.py` |
| F6 | Hook products at every place: `H(λ) ∣ |λ|!`, `v_p H + v_p f^λ = v_p |λ|!`. | proved; tagged as transfers | `hookProd_dvd_factorial`, `padicValNat_hookProd_add_fSYT` |

## What may not be said

- That the places programme **is** boson–fermion: J1 is proved for one pattern, not as an equivalence.
- That the string-insertion law **holds along the lifts**: one worked example (F4).
- That the wall's fluctuations **are** Bessel: a reading of computed data (F5).

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
| F4 | String-insertion **law** along theta lifts (slack = one-body + two-body increments, telescoping, exact squares). | **checked**: exceptionless on all admissible parameter sets in two windows (RH-Dual #48: 23,744 and 1,268,736 cases); exact split `Δ log H = T + S + V` (now an identity, F9) (translation, string self-energy, Vandermonde): the one-body translation share `T/Δ` **overshoots 1 and decays with `t`** (1.117, 1.081, 1.062, 1.046 at `t` = 3, 7, 11, 17, down to 1.019 at `t` = 51; the decay is now **proved** in the form `T/Δ ≤ 1/(1 − 2/Δe)`, at most `1 + 2/(t+1)` once `Δe ≥ t+3`, F10's `translation_le_step`), the Vandermonde share `|V|/Δ` decays, closer to `1/t` than to `1/√t` for `t ≥ 21` (inferred from three points; the earlier `1/√t` fit is withdrawn, RH-Dual #83) and does not depend on `k`, and `Δ log H > 0` on every step; no family cancellation. The worked example (`t = 17`, `T/Δ` = 1.045) matches the family mean at its `t` (RH-Dual #54) | `docs/string-insertion.md`; `RMT.Claims.stringInsertionLaw` |
| F5 | The moment measure puts its mass at the wall (`N·P(λ₁ = N) → k²`); the wall is a hard edge. | **checked on examples** (Loop 3); "hard edge / Bessel" a **reading** | `scripts/wall_moments.py` |
| F6 | Hook products at every place: `H(λ) ∣ |λ|!`, `v_p H + v_p f^λ = v_p |λ|!`. | proved; tagged as transfers | `hookProd_dvd_factorial`, `padicValNat_hookProd_add_fSYT` |
| F7 | Rankin–Selberg by rows: the one-row series (the unfolding's Mellin step) and the full Cauchy kernel differ exactly by the second-row factor `1 − x y x′ y′ c² X²` (the Eisenstein `ζ(2s)`). Both occur in the proof, in different nodes (RH-Dual #66). | proved | `oneRow_cauchy_two`, `cauchy_powerSeries` |
| F8 | One wall breaks ω, two walls restore it. Over an ω-closed family with an ω-even weight: no wall, an ω-odd statistic (`λ₁ − ℓ`, odd content moments) sums to zero; behind the boson's wall `ℓ ≤ N` its sum is carried exactly by the shapes with `λ₁ > N`; on the `N × N` box it is zero again. For a family that is not ω-closed, the box bias is carried by the ω-defect of its weight, `2 Σ m f = Σ (m − m∘ω) f`; confirmed exactly on the theta-lift shapes (RH-Dual #72, #73: rows win on every shape with `λ₁ > p`; 100 % of the box asymmetry comes from shapes whose transpose is absent). | proved; **checked** on the proof's shapes | `sum_bosonWall_odd`, `sum_box_odd_eq_zero`, `sum_bosonWall_transpose`, `two_mul_sum_odd_eq_sum_defect` |
| F9 | One lift is one step: translating a Maya set by `Δ` and inserting the crossing charge `ℓ` gives `Δ log H = T + S + V` exactly (translation `Σ log (x+Δ)!/x!`, self-energy `log ℓ!`, Vandermonde `−Σ log|x+Δ−ℓ|`). The identity behind F4's computed split, for every finite Maya set. **Draining**: on the hole side (remove the lowest hole, translate down by `Δ ≥ 1`) `H` never increases, factor by factor: each remaining hole's distance to the removed one is at most its position, which the translation divides out (RH-Dual: no exception in 2.56 M steps). | proved | `log_hset_step`, `hset_step`, `vd_shift`, `hset_drain` |
| F10 | The theta tower at one place is one object (`RMT.Tower`: configuration `X`, levels `e i`, band `c`). Each level is the cut `(a⁺_i, a⁻_i)` of `X + e_i` through the band. With the band empty and exactly one crossing per lift: `a⁺` gains the crossing point (F9's `T + S + V`), `a⁻` loses it and drains while `a⁺` grows (`hset_above_le_succ`), `|a⁺| + |a⁻| = |X|`; the move `X ↦ −X` swaps the sides and keeps `H(a⁺)H(a⁻)`. **At every place**: the step has the same `T + S + V` split for `v_p` at each prime (`padicValRat_above_succ`), and `log H(a⁺)H(a⁻) = Σ_p v_p · log p` (`log_factorInf_eq_sum`); draining is an inequality at `∞` only. Merging two lifts (M6) adds exactly one cross term `−log|ℓ₁−ℓ₂|` between the two newcomers (`log_hset_above_succ_succ`; RH-Dual #102 computed it). Changing the spacing (M4): in tower coordinates the two-body part `V` does **not** depend on the gap `Δ`, and the step is monotone in `Δ` (`log_hset_step_gap`, `log_hset_step_gap_mono`). **The overshoot is `O(1/Δ)`**: `|V| ≤ (2/Δ)·T` for every Maya set (pairing `(x+Δ)^Δ ≤ ((x+Δ)!/x!)²`), so `(1 − 2/Δ)·T ≤ Δ log H` (`translation_le_step`); with `Δ ≥ t+3` (RH-Dual #128) the overshoot is at most `2/(t+1)`. Changing the band (M5) translates both sides, so the band width enters `H(a⁺)H(a⁻)` through one-body terms only (`hset_cut_narrow`). The formal degree's Vandermonde is constant along the tower (`vdZ_level`; RH-Dual #88: the proof writes it as `∏|λ_a−λ_b|/∏(b−a)`). That one crossing follows from the proof's `HCParam` is RH-Dual's identification (lane C). | proved | `RMT.Tower.cut_succ_fst`, `hset_below_succ_le`, `log_hset_above_succ`, `card_cut`, `cut_reflectTower`, `padicValRat_above_succ`, `log_factorInf_eq_sum`, `vdZ_level`, `log_hset_above_succ_succ`, `hset_cut_narrow`, `log_hset_step_gap_mono`, `translation_le_step` |
| F11 | The proof uses ω (`λ ↦ λ′`) as a duality at **no** place. At finite places there is no Aubert/Zelevinsky, Alvis–Curtis or Iwahori–Matsumoto. At ∞ the Fock model is bosonic only and `transpose` is never called. Its dualities are contragredients (`ν ↦ ν⁻¹`, `−w₀`): on Maya diagrams, the reflection (`RMT.Tower.reflectTower`) without the particle–hole complement that would make it ω. *Corrected*: an earlier version said "at ∞ only" (RH-Dual #101). | **checked** (RH-Dual #89, #95, #101) | `omega-finite-places.md`, `omega-infinite-places.md` (RH-Dual) |
| F12 | The proof is bosonic throughout. Every truncated partition sum is behind the boson wall at the rank, none behind a fermion wall. The ω-images of its sums (dual Cauchy, vertical-strip Pieri) are absent from the closure. Its kernel positivities fail under the fermionic twin: the Jacquet–Shalika coefficients become `(−1)^{k+1}\|p_k\|²/k`, negative at `k = 2`. No summand is ω-even or ω-odd, so F8 applies to derived statistics (rows against columns), not to these sums directly. | **checked** (RH-Dual #86, #92, #98) | `bridge/links/wall-sums.md`, `positivity-census.md` (RH-Dual) |
| F13 | The vacuum character splits as **point ⊗ charge**. `mu = χV(x)` is one global character, the same at every place (point). At ∞, `muInf = mu_∞ · j` with `j = ∏ det(k₊)^m det(k₋)^{−m}`, `m = rk V/2`, fixed by the signature (charge); the charge is absent at the finite places. ω (`m ↦ −m`) inverts `j` and fixes `mu`, so its asymmetry is purely archimedean charge. | **checked** (RH-Dual #122: read; the factorisation inferred from the closed form) | `vacuum-character-places.md` (RH-Dual) |

## What may not be said

- That the places programme **is** boson–fermion: J1 is proved for one pattern, not as an equivalence.
- That the string-insertion law **holds along the lifts in general**: it is exceptionless on two small windows (F4), not proved.
- That the wall's fluctuations **are** Bessel: a reading of computed data (F5).

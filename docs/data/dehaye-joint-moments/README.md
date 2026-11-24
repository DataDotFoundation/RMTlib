# Joint moments of derivatives of characteristic polynomials: data

The source of the mixed moments taken as given in `main/PROGRAMME.md`'s Hall toy model
("Hall's ladder: a second toy model").

**Reference.** P.-O. Dehaye, *Joint moments of derivatives of characteristic polynomials*,
Algebra & Number Theory **2** (2008), 31–68; arXiv:math/0703440 (v3). The files here are copied
unchanged from the data attached to the arXiv source (v3, Sep 2007):

| File | Contents |
|---|---|
| `NumeratorsComplexM` | `X_r(u)` for `r = 1..60`: numerators of `(ℳ)(2k,r)` |
| `NumeratorsNormedM` | `X̂_{2h}(u)` for `h = 1..30`: numerators of `|ℳ|(2k,2h)` |
| `NumeratorsNormedV` | `X̃_{2h}(u)` for `h = 1..30`: numerators of `|𝒱|(2k,2h)` (Hardy's real version: **Hall's inputs**) |
| `MagmaCode` | the paper's Magma implementation |

## Definitions and normalisation (paper, §1 and Theorems 1, 16)

- `Z_U(θ) = ∏_j (1 − e^{i(θ_j − θ)})`, and `V_U(θ) = e^{iN(θ+π)/2} e^{−iΣθ_j/2} Z_U(θ)`, which is
  real for real `θ`.
- `|ℳ|_N(2k,r) = ⟨|Z_U(0)|^{2k} |Z'_U(0)/Z_U(0)|^r⟩_{U(N)}`, and `|𝒱|_N` is the same with `V`. The
  limits are taken after dividing by `N^{k²+r}`.
- `(ℳ)(2k,r) = (−i/2)^r g(k) X_r(2k)/Y_r(2k)` (Theorem 1), with `g(k) = G(k+1)²/G(2k+1)`.
- `|ℳ|(2k,2h) = 2^{−2h} g(k) X̂_{2h}(2k)/Y_{2h}(2k)`.
- `|𝒱|(2k,2h) = C̃(h) g(k) X̃_{2h}(2k)/Y_{2h}(2k)` with `C̃(h) = (2h)!/(h! 2^{3h})`.
  - The monic normalisation of `X̂` and `X̃` is stated as conjectural in Theorem 16.
- `Y_r(u) = ∏_{a odd, 1≤a≤r−1} (u² − a²)^{α_a(r)}`, `α_a(r) = ⌊(−a + √(a²+4r))/2⌋`.
- Conjecturally, `∫_0^T |ζ|^{2k−2h}|ζ'|^{2h} ~ a(k)|ℳ|(2k,2h) T (log T/2π)^{k²+2h}`, and the same
  with Hardy's `Z` and `|𝒱|`. Here `a(k)` is the arithmetic factor.

## What Hall uses

The ratios `β_h(k) = |𝒱|(2k,2h)/|𝒱|(2k,0) = C̃(h) X̃_{2h}(2k)/Y_{2h}(2k)`; `g(k)` and `a(k)` cancel.
`toy_examples/scripts/dehaye_joint_moments.py` loads the files, exposes `beta(h, k)` exactly, and checks:
- that `β₁` and `β₂` agree with Hughes's form as quoted in `hall-theta-dictionary.md`;
- that every `X̃_{2h}` is monic and even;
- Theorem 16's degree relation `deg Y_{2h} − deg X̃_{2h} = 2h`, for `h ≤ 30`.

The Hughes normalisation used so far (#189) therefore agrees with the paper's on the cases
checked. The paper is the authority.

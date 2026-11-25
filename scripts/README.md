# Scripts

Checks that accompany the combinatorics library: `growth_rules.py` (growth diagrams, below),
`fischer_class_functions.py` (the Fock pairing on class functions, `RMTlib/Fock/ClassFunction.lean`)
`q_whittaker_check.py` (`RMT.Symmetric.qWhittV`, `RMTlib/Symmetric/QWhittaker.lean`)
and `multiset_hook_check.py` (Dehaye–Han's multiset hook length formula, `RMTlib/Tableaux/MultisetHook*.lean`:
the paper's examples, every `t`-core of size ≤ 14 for `t ≤ 6`, the residue identity in every charge, and
bijectivity by counting).

## `growth_rules.py`: which super RSK the growth rules encode

`growth_rules.py` gives one local growth rule for each parity type of square: (b,b), (b,f),
(f,b), (f,f). Rows are recording letters `i`, columns are inserted letters `j`. Its insertion
check (c) was described as Berele–Regev insertion. That label is wrong.

**What the script's insertion is.** The insertion `insertion(A, rp, cp)` is exactly the
super-RSK of N. Hage, *A super Robinson–Schensted–Knuth correspondence with symmetry and the
super Littlewood–Richardson rule*, arXiv:2206.15451 (Algorithm `A:RSkalgo`).
- Pairs are ordered by the recording letter. For an even recording letter the inserted letters
  are read in increasing order; for an odd one, in decreasing order (conditions `E:Order1`,
  `E:Order2`). Equal pairs are allowed only when both letters have the same parity, so
  mixed-parity entries are 0 or 1.
- Every letter is inserted by the super *row* insertion of La Scala, Nardozza and Senato,
  *Super RSK-algorithms and super plactic monoid*, IJAC 16 (2006), arXiv:0904.0605 (Def.
  `row-insertion`). An even letter bumps the first entry `> x`, an odd letter the first entry
  `≥ x`.
- The tableau conventions are the script's: even letters are row-weak and column-strict, odd
  letters are row-strict and column-weak.

The script reproduces Hage's worked Example `Ex:RSKExample1` exactly, both P and Q. Hage proves
this correspondence has the symmetry property, using a matrix-ball construction. That matches
the growth rules being symmetric: the (f,f) cap is symmetric in μ and ν, and (b,f) and (f,b)
are transposes of each other. Hage remarks that when all even letters are smaller than all odd
letters, the correspondence reduces to Berele–Remmel's super-RSK (JPAA 35, 1985). I have not
read that paper.

**Other super RSKs, implemented and compared.** `literature_checks()` implements three other
insertions. It checks each against the worked examples in the source papers, then computes the
growth grid of each one (shape of P restricted to letters `< j` after rows `< i`). For words of
length ≤ 3 on both sides and entry sum ≤ 4, every grid obeys a local rule. In the table,
"conj" means the script's rule for the parity-flipped type, applied to conjugate shapes:
`conj(fwd_{flip t}(ρ', μ', ν', x))`.

| insertion | (b,b) | (b,f) | (f,b) | (f,f) | symmetric |
|---|---|---|---|---|---|
| script = Hage 2022 (LNS row insertion) | script | script | script | **script** | yes |
| Muth 2019, arXiv:1711.00420 (Haiman mixed insertion) | script | conj | conj | **script** | yes |
| Bonetti–Senato–Venezia 1998, as stated in LNS 2006 | script | script | conj | **conj** (= `FF_CONJ`) | no |

- **Muth.** R. Muth, *Super RSK correspondence with symmetry*, arXiv:1711.00420 (Sec. 3.1
  ε-insertion; Sec. 5.2 sRSK). Pairs are ordered by the recording letter, then odd inserted
  letters in decreasing order, then even ones in increasing order. With ε the parity of the
  recording letter, a letter of parity p is row-inserted if ε + p = 0 and column-inserted
  otherwise, bumping the first entry `> x` (ε = 0) or `≥ x` (ε = 1).
- **BSV.** For an even recording letter, row insertion. For an odd recording letter, super
  column insertion, with the inserted letters read in increasing order (LNS Def. `S ↦ (T,U)`).
- Both implementations reproduce Muth's Example `bigex`, for w and for w^inv. That example also
  contains the BSV outputs Muth quotes, which show BSV is not symmetric. On the same biword the
  script gives a third answer, of shape (3,2,2,1).

**Berele–Regev 1987.** I could not access A. Berele and A. Regev, *Hook Young diagrams with
applications to combinatorics and to representations of Lie superalgebras*, Adv. Math. 64
(1987) 118–175. ScienceDirect and the AMS Bulletin announcement (1983) both refused automated
download. Their (k,l)-RSK is known to me only through two descriptions:
- Shimozono–White, *Shuffle invariance of the super-RSK algorithm*, arXiv:math/0103206, Sec. 1:
  "the usual RSK insertion algorithm is applied to the t_i's, and the conjugate correspondence
  is applied to the u_j's".
- Muth's Remark `insertinLitH`.

On words (all recording letters even, so Q is standard), this is Muth's ε = 0 mixed insertion:
even letters are row-inserted and odd letters column-inserted. `literature_checks()` reproduces
Shimozono–White's example with it. So, as far as these secondary sources describe it:
- Berele–Regev's correspondence involves only (b,b) and (b,f) squares, and puts no constraint
  on the (f,f) rule.
- It already differs from the script on (b,f) squares. On the word u₂ t₁ t₂ u₁ it gives
  P = t₁ t₂ u₂ / u₁, while the script gives t₁ t₂ u₁ / u₂.

**Conclusion for the (f,f) rule.**
- The script's (f,f) rule, cap `ρ_k + 1 − max(μ_k, ν_k)`, is forced by Hage's super-RSK. Muth's
  super-RSK forces the same rule, although Muth differs from Hage on mixed squares.
- The conjugated bosonic rule (`FF_CONJ`) is the (f,f) rule of Bonetti–Senato–Venezia. It is
  part of an asymmetric correspondence: there, (f,b) is the conjugate of (b,f), not its
  transpose.
- Both families give bijections with the same super Cauchy counts, so the choice is a
  convention. Hage's convention is the one that is both symmetric and row-insertion based.

Not checked: Remmel's papers on (k,l)-hook Schur functions; Berele–Remmel 1985; Fomin's
"Schur operators and Knuth correspondences" (1995) and Krattenthaler (2006), beyond the bosonic
rule already cross-checked in the script; any treatment of super RSK by growth diagrams. My arXiv
searches ("super RSK", "Berele-Regev", "growth diagram" with "super") found none.


## `super_schensted_omega.py`: Schensted's ω for the super-RSK (RMTlib#74)

Schensted: reversing a permutation transposes its insertion tableau. For the super-RSK of
`growth_rules.py` (Hage 2022), the exact statement found here is

> reverse the biword **and** flip every parity (rows and letters): P transposes.

This is checked exhaustively on fillings up to 3 × 3 with entries ≤ 2 and sum ≤ 4: 35,130 of 35,130
cases. Each partial version fails:

| variant | P(reversed) = Pᵀ |
|---|---|
| reverse only | 5,272 / 35,130 |
| reverse, flip rows only | 8,320 / 20,320 |
| reverse, flip letters only | 11,212 / 20,320 |

The local rule is **not** ω-equivariant square by square in a fixed orientation (`conj ∘ fwd_flip ∘
conj ≠ fwd` on most squares of every type, already at `ρ = ∅`, `μ = ν = (1)`). BSV's rule is locally equivariant at (f,f) by construction (`FF_CONJ`), but it is not symmetric. Among the
three rules implemented, each has local ω-equivariance or the P↔Q symmetry, never both (an
observation, not a theorem). So the ω-symmetry of
super-RSK (Hage) is a reflection of the whole grid (reversal) combined with the parity flip, not a
property of one square. A Lean proof should therefore go through the grid reflection, as for
Schensted's theorem, not through a local equivariance lemma.

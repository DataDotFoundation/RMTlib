import Mathlib

/-!
# The residue identity: the algebraic heart of the multiset hook length formula

This file is about divisors on `ℤ`, i.e. elements of the free abelian group `ℤ^(ℤ) = ℤ →₀ ℤ`, and
says nothing about partitions. Write `[x]` (`pt x`) for the point divisor.

Fix `t ≥ 1` and a **complete residue system** `V ⊆ ℤ`: `t` integers, pairwise incongruent mod
`t`. For two of them, `a > b`, write `d = a − b = q·t + r` (`0 < r < t`). The *pair divisor*

  `pairHooks d = ∑_{n=1}^{q} ray(r, n)`,   `ray(r, n) = [r] + [r + t] + ⋯ + [r + (n−1)t]`,

is the hook multiset that the runners `a` and `b` of a `t`-abacus contribute (that link is made in
`RMTlib.Tableaux.MultisetHook.Maya`). The **folded Laplacian** `lap` sends `[h]` to
`[|h − t|] + [h + t] − 2[h]`.

## Main results

* `lap_pairHooks`: `lap (pairHooks d) = [d] − Φ(d)`, by telescoping a ray. Here
  `Φ(e) = [e mod t] + ⌊e/t⌋·([e mod t] − [t − e mod t])` depends only on `e`, is even
  (`phi_neg`), and is *affine in the abacus coordinate*: `Φ(e + n·t) = Φ(e) + n·σ(e mod t)`
  (`phi_add_mul`), with `σ(s) = [s] − [t − s]`.
* `sum_phi`: `∑_{b < a in V} Φ(a − b) = ∑_{i=1}^{t−1} (t − i)·[i]`, for every complete residue
  system `V`. The proof: `Φ` is affine in the runner positions, and the linear part sums to zero
  because the differences `a − b`, `b ≠ a`, run once through every nonzero residue, where
  `∑_s σ(s) = 0` (reflection `s ↦ t − s`). So the sum only depends on the residues, and for
  `V = {0, …, t − 1}` it is the count of the differences `x − y`.
* `residue_identity`: `∑_{a, b ∈ V} lap (pairHooks (a − b)) + ∑_{i=1}^{t−1} (t − i)·[i]
  = ∑_{b < a in V} [a − b]`. This is the folded, β-free form of Dehaye–Han's Eq. (2), for every
  `t`-abacus at once (every charge, not just charge `0`).
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

/-- The point divisor `[x] ∈ ℤ^(ℤ)`. -/
abbrev pt (x : ℤ) : ℤ →₀ ℤ := Finsupp.single x 1

/-- A multiset of integers as a divisor: `m ↦ ∑_{x ∈ m} [x]`. -/
def toDiv (m : Multiset ℤ) : ℤ →₀ ℤ := (m.map pt).sum

theorem toDiv_apply (m : Multiset ℤ) (x : ℤ) : toDiv m x = m.count x := by
  induction m using Multiset.induction_on with
  | empty => rw [toDiv, Multiset.map_zero, Multiset.sum_zero, Finsupp.zero_apply,
      Multiset.count_zero, Nat.cast_zero]
  | cons a m ih =>
    rw [toDiv, Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ← toDiv, ih,
      Multiset.count_cons, Finsupp.single_apply]
    by_cases h : x = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]

/-- Multisets embed in divisors. -/
theorem toDiv_injective : Function.Injective toDiv := by
  intro m m' h
  ext x
  have h1 := toDiv_apply m x
  have h2 := toDiv_apply m' x
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

theorem toDiv_add (m m' : Multiset ℤ) : toDiv (m + m') = toDiv m + toDiv m' := by
  simp [toDiv]

theorem toDiv_nsmul (n : ℕ) (m : Multiset ℤ) : toDiv (n • m) = n • toDiv m := by
  simp [toDiv, Multiset.map_nsmul, Multiset.sum_nsmul]

theorem toDiv_singleton (x : ℤ) : toDiv {x} = pt x := by simp [toDiv]

theorem toDiv_sum {ι : Type*} (s : Finset ι) (f : ι → Multiset ℤ) :
    toDiv (∑ i ∈ s, f i) = ∑ i ∈ s, toDiv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [toDiv]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, toDiv_add, ih]

theorem toDiv_map {α : Type*} (m : Multiset α) (g : α → ℤ) :
    toDiv (m.map g) = (m.map fun x => pt (g x)).sum := by
  simp [toDiv, Multiset.map_map]

/-- The folded Laplacian of one point: `[|h − t|] + [h + t] − 2[h]`. -/
def lapPt (t : ℕ) (h : ℤ) : ℤ →₀ ℤ := pt |h - t| + pt (h + t) - 2 • pt h

/-- **The folded Laplacian** on divisors, the linear extension of `lapPt`. -/
def lap (t : ℕ) : (ℤ →₀ ℤ) →+ (ℤ →₀ ℤ) :=
  Finsupp.liftAddHom fun h => zmultiplesHom _ (lapPt t h)

theorem lap_single (t : ℕ) (h n : ℤ) : lap t (Finsupp.single h n) = n • lapPt t h := by
  simp [lap]

theorem lap_pt (t : ℕ) (h : ℤ) : lap t (pt h) = lapPt t h := by
  rw [lap_single, one_smul]

/-! ### Rays and pair divisors -/

/-- A ray on one runner: `[r] + [r + t] + ⋯ + [r + (n − 1)t]`. -/
def ray (t : ℕ) (r : ℤ) (n : ℕ) : ℤ →₀ ℤ := ∑ j ∈ range n, pt (r + t * j)

/-- **A ray telescopes under `lap`.** -/
theorem lap_ray (t : ℕ) {r : ℤ} (h0 : 0 < r) (ht : r < t) (n : ℕ) :
    lap t (ray t r (n + 1)) = pt (t - r) - pt r + (pt (r + t * (n + 1)) - pt (r + t * n)) := by
  induction n with
  | zero =>
    have : |r - t| = t - r := by rw [abs_of_neg (by omega)]; ring
    simp only [ray, sum_range_one, Nat.cast_zero, mul_zero, add_zero, lap_pt, lapPt, this,
      zero_add, mul_one]
    abel
  | succ n ih =>
    rw [ray, sum_range_succ, map_add, ← ray, ih, lap_pt, lapPt]
    have hn : (0 : ℤ) ≤ t * n := by positivity
    have : |r + t * ((n + 1 : ℕ) : ℤ) - t| = r + t * n := by
      push_cast; rw [abs_of_nonneg (by nlinarith)]; ring
    rw [this]
    push_cast
    rw [show r + (t : ℤ) * (n + 1) + t = r + t * (n + 1 + 1) by ring]
    abel

/-- `⌊d/t⌋` as a natural number (zero when `d < t`). -/
def quo (t : ℕ) (d : ℤ) : ℕ := (d / t).toNat

/-- **The pair divisor** of two runners at distance `d`: `∑_{n=1}^{⌊d/t⌋} ray(d mod t, n)`. -/
def pairHooks (t : ℕ) (d : ℤ) : ℤ →₀ ℤ := ∑ n ∈ range (quo t d), ray t (d % t) (n + 1)

theorem pairHooks_of_nonpos (t : ℕ) (ht : 0 < t) {d : ℤ} (hd : d ≤ 0) : pairHooks t d = 0 := by
  have : quo t d = 0 := by
    unfold quo; have := Int.ediv_nonpos_of_nonpos_of_neg hd (by exact_mod_cast ht : (0 : ℤ) < t); omega
  simp [pairHooks, this]

/-! ### `Φ`: the defect of one pair -/

/-- `σ(s) = [s] − [t − s]`, the antisymmetric part under the reflection `s ↦ t − s`. -/
def sig (t : ℕ) (s : ℤ) : ℤ →₀ ℤ := pt s - pt (t - s)

/-- `Φ(e) = [e mod t] + ⌊e/t⌋·σ(e mod t)`. -/
def phi (t : ℕ) (e : ℤ) : ℤ →₀ ℤ := pt (e % t) + (e / t) • sig t (e % t)

theorem emod_pos_of_not_dvd' {t : ℕ} (ht : 0 < t) {e : ℤ} (he : ¬ (t : ℤ) ∣ e) : 0 < e % t := by
  rcases Int.emod_pos_of_not_dvd he with h | h
  · omega
  · exact h

theorem emod_lt' {t : ℕ} (ht : 0 < t) (e : ℤ) : e % t < t := Int.emod_lt_of_pos e (by omega)

/-- `(−e) mod t = t − e mod t` and `⌊−e/t⌋ = −⌊e/t⌋ − 1` when `t ∤ e`. -/
theorem neg_divmod {t : ℕ} (ht : 0 < t) {e : ℤ} (he : ¬ (t : ℤ) ∣ e) :
    -e / t = -(e / t) - 1 ∧ -e % t = t - e % t := by
  have h1 := emod_pos_of_not_dvd' ht he
  have h2 := emod_lt' ht e
  have h3 := Int.emod_add_mul_ediv e t
  rw [Int.ediv_emod_unique (by omega)]
  refine ⟨by linarith, by omega, by omega⟩

/-- **`Φ` is even** away from multiples of `t`. -/
theorem phi_neg {t : ℕ} (ht : 0 < t) {e : ℤ} (he : ¬ (t : ℤ) ∣ e) : phi t (-e) = phi t e := by
  obtain ⟨hq, hr⟩ := neg_divmod ht he
  rw [phi, phi, hq, hr, sig, sig, sub_sub_cancel]
  module

/-- **`Φ` is affine in the abacus coordinate.** -/
theorem phi_add_mul {t : ℕ} (ht : 0 < t) (e n : ℤ) :
    phi t (e + t * n) = phi t e + n • sig t (e % t) := by
  rw [phi, phi, Int.add_mul_emod_self_left, Int.add_mul_ediv_left _ _ (by omega)]
  module

/-- **One pair under `lap`**: `lap (pairHooks d) = [d] − Φ(d)` for `d > 0`, `t ∤ d`. -/
theorem lap_pairHooks {t : ℕ} (ht : 0 < t) {d : ℤ} (hd : 0 < d) (hdt : ¬ (t : ℤ) ∣ d) :
    lap t (pairHooks t d) = pt d - phi t d := by
  have h0 := emod_pos_of_not_dvd' ht hdt
  have h1 := emod_lt' ht d
  have hq : ((quo t d : ℕ) : ℤ) = d / t := by
    unfold quo; have := Int.ediv_nonneg hd.le (by omega : (0 : ℤ) ≤ t); omega
  rw [pairHooks, map_sum]
  simp_rw [lap_ray t h0 h1]
  rw [sum_add_distrib, sum_const, card_range]
  have tel := Finset.sum_range_sub (fun n : ℕ => pt (d % t + t * (n : ℤ))) (quo t d)
  push_cast at tel
  rw [tel]
  have hd' : d % t + t * ((quo t d : ℕ) : ℤ) = d := by rw [hq]; exact Int.emod_add_mul_ediv d t
  simp only [mul_zero, add_zero, hd', phi, sig, ← hq]
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  module

/-! ### Summing `Φ` over a complete residue system -/

/-- A complete residue system mod `t`: `t` integers, pairwise incongruent. -/
structure Complete (t : ℕ) (V : Finset ℤ) : Prop where
  /-- Incongruent. -/
  inj : ∀ a ∈ V, ∀ b ∈ V, a % t = b % t → a = b
  /-- `t` of them. -/
  card : V.card = t

/-- Congruence as divisibility. -/
theorem emod_eq_iff {n a b : ℤ} : a % n = b % n ↔ n ∣ a - b := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]

theorem Complete.not_dvd {t : ℕ} {V : Finset ℤ} (hV : Complete t V) {a b : ℤ} (ha : a ∈ V)
    (hb : b ∈ V) (hab : a ≠ b) : ¬ (t : ℤ) ∣ a - b := fun h =>
  hab (hV.inj a ha b hb (emod_eq_iff.mpr h))

/-- The residues of a complete system are `{0, …, t − 1}`. -/
theorem Complete.image_emod {t : ℕ} (ht : 0 < t) {V : Finset ℤ} (hV : Complete t V) :
    V.image (· % (t : ℤ)) = (range t).image (fun n : ℕ => (n : ℤ)) := by
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_image, mem_range] at hx ⊢
    obtain ⟨a, -, rfl⟩ := hx
    refine ⟨(a % t).toNat, ?_, ?_⟩
    · have := emod_lt' ht a; have := Int.emod_nonneg a (by omega : (t : ℤ) ≠ 0); omega
    · have := Int.emod_nonneg a (by omega : (t : ℤ) ≠ 0); omega
  · rw [card_image_of_injective _ Nat.cast_injective, card_range,
      card_image_of_injOn (fun a ha b hb h => hV.inj a ha b hb h), hV.card]

/-- **Summing over a complete residue system**: for `k = ±1`, `b ↦ (k·b + c) mod t` is a bijection
from `V` onto `{0, …, t − 1}`. -/
theorem Complete.sum_emod {t : ℕ} (ht : 0 < t) {V : Finset ℤ} (hV : Complete t V) {k : ℤ}
    (hk : k = 1 ∨ k = -1) (c : ℤ) {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ b ∈ V, f ((k * b + c) % t) = ∑ n ∈ range t, f n := by
  have hT : (t : ℤ) ≠ 0 := by omega
  have hdvd : ∀ x y : ℤ, (t : ℤ) ∣ (k * x + c) - (k * y + c) → (t : ℤ) ∣ x - y := by
    intro x y h
    rw [show k * x + c - (k * y + c) = k * (x - y) by ring] at h
    rcases hk with rfl | rfl
    · simpa using h
    · rw [neg_one_mul, dvd_neg] at h; exact h
  have hinj : ∀ x ∈ V, ∀ y ∈ V, (k * x + c) % (t : ℤ) = (k * y + c) % t → x = y :=
    fun x hx y hy h => hV.inj x hx y hy (emod_eq_iff.mpr (hdvd x y (emod_eq_iff.mp h)))
  rw [← sum_image (f := f) (g := fun x => (k * x + c) % (t : ℤ)) hinj,
    ← sum_image (f := f) (g := fun n : ℕ => (n : ℤ)) (fun x _ y _ h => Nat.cast_injective h)]
  congr 1
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_image, mem_range] at hx ⊢
    obtain ⟨a, -, rfl⟩ := hx
    have := emod_lt' ht (k * a + c); have := Int.emod_nonneg (k * a + c) hT
    exact ⟨(((k * a + c) % t)).toNat, by omega, by omega⟩
  · rw [card_image_of_injOn hinj, hV.card, card_image_of_injective _ Nat.cast_injective,
      card_range]

/-- The case `k = 1`, `c = 0` of `Complete.sum_emod`. -/
theorem Complete.sum_emod' {t : ℕ} (ht : 0 < t) {V : Finset ℤ} (hV : Complete t V)
    {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ b ∈ V, f (b % t) = ∑ n ∈ range t, f n := by
  rw [← hV.sum_emod ht (Or.inl rfl) 0 f]; simp

/-- Cancelling `2` in `ℤ^(ℤ)`. -/
theorem two_nsmul_inj {X Y : ℤ →₀ ℤ} (h : 2 • X = 2 • Y) : X = Y := by
  ext x
  have := DFunLike.congr_fun h x
  simp only [Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
  omega

/-- `Φ(e) = [|e|]` for `|e| < t`. -/
theorem phi_small {t : ℕ} (ht : 0 < t) {e : ℤ} (h1 : -t < e) (h2 : e < t) : phi t e = pt |e| := by
  rcases le_or_gt 0 e with he | he
  · obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique (a := e) (b := t) (q := 0) (r := e) (by omega)).mpr
      ⟨by ring, he, h2⟩
    rw [phi, hq, hr, abs_of_nonneg he, zero_smul, add_zero]
  · obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique (a := e) (b := t) (q := -1) (r := e + t) (by omega)).mpr
      ⟨by ring, by omega, by omega⟩
    rw [phi, hq, hr, abs_of_neg he, sig, show (t : ℤ) - (e + t) = -e by ring]
    module

/-- Splitting a sum over `V` at `a`: below, at, above. -/
theorem sum_split (V : Finset ℤ) (a : ℤ) (ha : a ∈ V) {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ b ∈ V, f b = ∑ b ∈ V.filter (· < a), f b + f a + ∑ b ∈ V.filter (a < ·), f b := by
  rw [← sum_filter_add_sum_filter_not V (· < a), ← sum_filter_add_sum_filter_not
    (V.filter fun b => ¬ b < a) (a < ·)]
  have hgt : (V.filter fun b => ¬ b < a).filter (a < ·) = V.filter (a < ·) := by
    ext b; simp only [mem_filter]; constructor
    · rintro ⟨⟨h, -⟩, h2⟩; exact ⟨h, h2⟩
    · rintro ⟨h, h2⟩; exact ⟨⟨h, by omega⟩, h2⟩
  have heq : (V.filter fun b => ¬ b < a).filter (fun b => ¬ a < b) = {a} := by
    ext b; simp only [mem_filter, mem_singleton]; constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; omega
    · rintro rfl; exact ⟨⟨ha, lt_irrefl _⟩, lt_irrefl _⟩
  rw [hgt, heq, sum_singleton]
  abel

/-- **Folding a symmetric double sum**: for `F(−e) = F(e)` on differences,
`∑_{a,b} F(a − b) = #V·F(0) + 2·∑_{b < a} F(a − b)`. -/
theorem sum_sym (V : Finset ℤ) (F : ℤ → ℤ →₀ ℤ)
    (hF : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → F (b - a) = F (a - b)) :
    ∑ a ∈ V, ∑ b ∈ V, F (a - b) =
      V.card • F 0 + 2 • ∑ a ∈ V, ∑ b ∈ V.filter (· < a), F (a - b) := by
  have h1 : ∑ a ∈ V, ∑ b ∈ V, F (a - b) = ∑ a ∈ V, (∑ b ∈ V.filter (· < a), F (a - b) + F 0 +
      ∑ b ∈ V.filter (a < ·), F (a - b)) :=
    sum_congr rfl fun a ha => by rw [sum_split V a ha, sub_self]
  have h2 : ∑ a ∈ V, ∑ b ∈ V.filter (a < ·), F (a - b) =
      ∑ a ∈ V, ∑ b ∈ V.filter (· < a), F (a - b) := by
    rw [sum_comm' (t' := V) (s' := fun b => V.filter (· < b))]
    · refine sum_congr rfl fun b hb => sum_congr rfl fun a ha => ?_
      rw [mem_filter] at ha
      exact hF b hb a ha.1 (by omega)
    · intro a b; simp only [mem_filter]; tauto
  rw [h1, sum_add_distrib, sum_add_distrib, h2, sum_const, two_nsmul]
  abel

/-- `∑_{s=0}^{t−1} σ(s)` is the same for every residue system, so the linear part cancels. -/
theorem sum_range_abs (t : ℕ) :
    ∑ n ∈ range t, ∑ m ∈ range t, pt |(n : ℤ) - m| =
      t • pt 0 + 2 • ∑ i ∈ Ico 1 t, ((t : ℤ) - i) • pt i := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hrefl : ∑ m ∈ range t, pt ((t : ℤ) - m) = ∑ i ∈ Ico 1 (t + 1), pt i := by
      rw [← sum_range_reflect, sum_Ico_eq_sum_range]
      refine sum_congr (by simp) fun m hm => ?_
      rw [mem_range] at hm; congr 1; push_cast [Nat.sub_sub, show t - (1 + m) + 1 = t - m by omega]
      omega
    have row : ∑ m ∈ range t, pt |(t : ℤ) - m| = ∑ i ∈ Ico 1 (t + 1), pt i := by
      rw [← hrefl]; refine sum_congr rfl fun m hm => ?_
      rw [mem_range] at hm; rw [abs_of_nonneg (by omega)]
    have col : ∑ n ∈ range t, pt |(n : ℤ) - t| = ∑ i ∈ Ico 1 (t + 1), pt i := by
      rw [← row]; refine sum_congr rfl fun m _ => ?_; rw [abs_sub_comm]
    have top : ∑ i ∈ Ico 1 (t + 1), ((t : ℤ) - i) • pt i = ∑ i ∈ Ico 1 t, ((t : ℤ) - i) • pt i := by
      rcases Nat.eq_zero_or_pos t with rfl | htp
      · simp
      · rw [sum_Ico_succ_top (by omega), sub_self, zero_smul, add_zero]
    simp only [sum_range_succ, sum_add_distrib, ih, row, col, sub_self, abs_zero]
    push_cast
    simp only [add_sub_right_comm _ (1 : ℤ), add_smul, one_smul, sum_add_distrib, top]
    rw [succ_nsmul]
    abel

/-- **`∑ Φ` over a complete residue system**: `∑_{b < a in V} Φ(a − b) = ∑_{i=1}^{t−1} (t − i)·[i]`.
The abacus coordinates of `V` drop out. -/
theorem sum_phi {t : ℕ} (ht : 0 < t) {V : Finset ℤ} (hV : Complete t V) :
    ∑ a ∈ V, ∑ b ∈ V.filter (· < a), phi t (a - b) = ∑ i ∈ Ico 1 t, ((t : ℤ) - i) • pt i := by
  have hT : (t : ℤ) ≠ 0 := by omega
  -- the full double sum, computed two ways
  have hsym := sum_sym V (phi t) fun a ha b hb hab => by
    rw [← neg_sub, phi_neg ht (hV.not_dvd ha hb hab)]
  -- split each difference into residues and abacus coordinates
  have hsplit : ∀ a b : ℤ, phi t (a - b) =
      phi t (a % t - b % t) + (a / t - b / t) • sig t ((-1 * b + a) % t) := by
    intro a b
    have := phi_add_mul ht (a % t - b % t) (a / t - b / t)
    rw [show a % t - b % t + t * (a / t - b / t) = a - b by
      have := Int.emod_add_mul_ediv a t; have := Int.emod_add_mul_ediv b t; linarith] at this
    rw [this, show -1 * b + a = a - b by ring, ← Int.sub_emod]
  have hlin : ∑ a ∈ V, ∑ b ∈ V, (a / t - b / t) • sig t ((-1 * b + a) % t) = 0 := by
    simp only [sub_smul, sum_sub_distrib, ← smul_sum]
    rw [sum_comm (s := V) (t := V) (f := fun a b => (b / (t : ℤ)) • sig t ((-1 * b + a) % t))]
    simp only [← smul_sum]
    have e1 : ∀ a : ℤ, ∑ b ∈ V, sig t ((-1 * b + a) % t) = ∑ n ∈ range t, sig t n :=
      fun a => hV.sum_emod ht (Or.inr rfl) a _
    have e2 : ∀ b : ℤ, ∑ a ∈ V, sig t ((-1 * b + a) % t) = ∑ n ∈ range t, sig t n := fun b => by
      rw [← hV.sum_emod ht (Or.inl rfl) (-1 * b) (sig t)]
      exact sum_congr rfl fun a _ => by ring_nf
    simp only [e1, e2, sub_self]
  have hres : ∑ a ∈ V, ∑ b ∈ V, phi t (a % t - b % t) =
      ∑ n ∈ range t, ∑ m ∈ range t, pt |(n : ℤ) - m| := by
    rw [hV.sum_emod' ht (fun x => ∑ b ∈ V, phi t (x - b % t))]
    refine sum_congr rfl fun n hn => ?_
    rw [hV.sum_emod' ht (fun x => phi t ((n : ℤ) - x))]
    refine sum_congr rfl fun m hm => ?_
    rw [mem_range] at hn hm
    exact phi_small ht (by omega) (by omega)
  have hfull : ∑ a ∈ V, ∑ b ∈ V, phi t (a - b) =
      ∑ n ∈ range t, ∑ m ∈ range t, pt |(n : ℤ) - m| := by
    rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => hsplit a b]
    simp only [sum_add_distrib]
    rw [hlin, add_zero, hres]
  rw [hfull, sum_range_abs, hV.card, phi_small ht (by omega) (by omega), abs_zero] at hsym
  exact (two_nsmul_inj (add_left_cancel hsym)).symm

/-- **The residue identity** (folded, β-free): for every complete residue system `V`,
`∑_{a,b ∈ V} lap (pairHooks (a − b)) + ∑_{i=1}^{t−1} (t − i)·[i] = ∑_{b < a in V} [a − b]`. -/
theorem residue_identity {t : ℕ} (ht : 0 < t) {V : Finset ℤ} (hV : Complete t V) :
    ∑ a ∈ V, ∑ b ∈ V, lap t (pairHooks t (a - b)) + ∑ i ∈ Ico 1 t, ((t : ℤ) - i) • pt i =
      ∑ a ∈ V, ∑ b ∈ V.filter (· < a), pt (a - b) := by
  have h : ∀ a ∈ V, ∑ b ∈ V, lap t (pairHooks t (a - b)) =
      ∑ b ∈ V.filter (· < a), (pt (a - b) - phi t (a - b)) := by
    intro a ha
    rw [← sum_filter_add_sum_filter_not V (· < a)]
    rw [sum_eq_zero (s := V.filter fun b => ¬ b < a) fun b hb => by
      rw [mem_filter] at hb; rw [pairHooks_of_nonpos t ht (by omega), map_zero], add_zero]
    refine sum_congr rfl fun b hb => ?_
    rw [mem_filter] at hb
    exact lap_pairHooks ht (by omega) (hV.not_dvd ha hb.1 (by omega))
  rw [sum_congr rfl h]
  simp only [sum_sub_distrib]
  rw [sum_phi ht hV]
  abel

end

end RMT.MultisetHook

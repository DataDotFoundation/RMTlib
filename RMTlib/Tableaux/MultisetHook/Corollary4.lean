import RMTlib.Tableaux.MultisetHook.Bijection

/-!
# Dehaye–Han, Corollary 4: the class-sorted coding and the sign `C`

For a weight `τ` that is even or odd, Eq. (2) can be written with the coding `u` sorted by
congruence class instead of by size: `u_i ≡ i + t₀ (mod t)` (the paper's convention), that is
`u_i ≡ i + ⌊t/2⌋` for the unshifted coding (`uCoding`). Then

  `∏_h τ(h − t)τ(h + t)/τ(h)² = C / ∏_{k<t} τ(k)^{t−k} · ∏_{i<j} τ(u_i − u_j)`   (Eq. (19))

with `C = −1` if `t ≡ 3 (mod 4)` and `τ` is odd, and `C = 1` otherwise (`corollary4`).

## Proof

Write `τ(x) = ε^{[x<0]} τ(|x|)` (`ε = ±1`). The folded identity (N5), evaluated on `τ`, has no
signs. Going back to the paper's form costs `ε^{N}` with `N = #{h < t} + inv(u)`. The parity of
`N` depends only on `t` (`sign_parity`):

* `#{h < t} = ∑_{b<a in V} ⌊(a − b)/t⌋`: each pair divisor contributes one hook `< t` per ray.
* `⌊(a − b)/t⌋ = a/t − b/t − [a mod t < b mod t]`. The abacus coordinates `a/t` add up to the
  charge `−t`, so they contribute `(t − 1)(−t)`, which is even.
* What remains depends only on the residues, and counts the pairs whose order is changed by the
  rotation `x ↦ x − ⌊t/2⌋` of `ℤ/t`. That gives `(t choose 2) − ⌊t/2⌋⌈t/2⌉ ≡ [t ≡ 3 mod 4]`.
-/

open Finset

namespace RMT.MultisetHook

noncomputable section

open Classical

/-! ### Residue bookkeeping -/

theorem Complete.exists_emod {t : ℕ} (ht : 0 < t) {V : Finset ℤ} (hV : Complete t V) (x : ℤ) :
    ∃ a ∈ V, a % t = x % t := by
  have : x % (t : ℤ) ∈ V.image (· % (t : ℤ)) := by
    rw [hV.image_emod ht, mem_image]
    have := emod_lt' ht x; have := Int.emod_nonneg x (by omega : (t : ℤ) ≠ 0)
    exact ⟨(x % t).toNat, mem_range.mpr (by omega), by omega⟩
  obtain ⟨a, ha, hax⟩ := mem_image.mp this
  exact ⟨a, ha, hax⟩

/-- **The class-sorted coding**: `u_i` is the element of `V` congruent to `i + ⌊t/2⌋` (the paper's
`u_i ≡ i + t₀` for the shifted coding). -/
def uCoding (t : ℕ) (μ : YoungDiagram) (i : Fin t) : ℤ :=
  ∑ a ∈ (vSet t μ).filter (fun a => a % t = ((i : ℤ) + (t / 2 : ℕ)) % t), a

theorem uCoding_spec {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hV : Complete t (vSet t μ))
    (i : Fin t) :
    uCoding t μ i ∈ vSet t μ ∧ uCoding t μ i % t = ((i : ℤ) + (t / 2 : ℕ)) % t := by
  obtain ⟨a, ha, har⟩ := hV.exists_emod ht ((i : ℤ) + (t / 2 : ℕ))
  have : (vSet t μ).filter (fun a => a % t = ((i : ℤ) + (t / 2 : ℕ)) % t) = {a} := by
    ext b; simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hb, hbr⟩; exact hV.inj b hb a ha (hbr.trans har.symm)
    · rintro rfl; exact ⟨ha, har⟩
  rw [uCoding, this, sum_singleton]
  exact ⟨ha, har⟩

/-- The class of `x`: `(x − ⌊t/2⌋) mod t`, so that `cls (u_i) = i`. -/
def cls (t : ℕ) (x : ℤ) : ℤ := (x - (t / 2 : ℕ)) % t

theorem cls_uCoding {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hV : Complete t (vSet t μ))
    (i : Fin t) : cls t (uCoding t μ i) = i := by
  unfold cls
  rw [Int.sub_emod, (uCoding_spec ht hV i).2, ← Int.sub_emod, add_sub_cancel_right,
    Int.emod_eq_of_lt (by omega) (by omega)]

theorem uCoding_injective {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hV : Complete t (vSet t μ)) :
    Function.Injective (uCoding t μ) := fun i j h => by
  have := congrArg (cls t) h
  rw [cls_uCoding ht hV, cls_uCoding ht hV] at this
  exact Fin.ext (by exact_mod_cast this)

theorem uCoding_surj {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hV : Complete t (vSet t μ))
    {a : ℤ} (ha : a ∈ vSet t μ) : ∃ i, uCoding t μ i = a := by
  have h0 := Int.emod_nonneg (a - (t / 2 : ℕ)) (by omega : (t : ℤ) ≠ 0)
  have h1 := emod_lt' ht (a - (t / 2 : ℕ))
  refine ⟨⟨(cls t a).toNat, by unfold cls; omega⟩, ?_⟩
  have hs := uCoding_spec ht hV ⟨(cls t a).toNat, by unfold cls; omega⟩
  apply hV.inj _ hs.1 a ha
  rw [hs.2]
  simp only [cls]
  rw [Int.toNat_of_nonneg h0, Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.add_emod,
    sub_add_cancel]

/-! ### Sums over pairs -/

/-- For a symmetric `F`, the double sum is the diagonal plus twice the sum over `b < a`. -/
theorem sum_pairs_symm {α : Type*} [LinearOrder α] (V : Finset α) (F : α → α → ℤ)
    (hF : ∀ a b, F a b = F b a) :
    ∑ a ∈ V, ∑ b ∈ V, F a b = ∑ a ∈ V, F a a + 2 * ∑ a ∈ V, ∑ b ∈ V.filter (· < a), F a b := by
  have split : ∀ a ∈ V, ∑ b ∈ V, F a b =
      ∑ b ∈ V.filter (· < a), F a b + F a a + ∑ b ∈ V.filter (a < ·), F a b := by
    intro a ha
    rw [← sum_filter_add_sum_filter_not V (· < a), ← sum_filter_add_sum_filter_not
      (V.filter fun b => ¬ b < a) (a < ·)]
    have hgt : (V.filter fun b => ¬ b < a).filter (a < ·) = V.filter (a < ·) := by
      ext b; simp only [mem_filter]; constructor
      · rintro ⟨⟨h, -⟩, h2⟩; exact ⟨h, h2⟩
      · rintro ⟨h, h2⟩; exact ⟨⟨h, not_lt.mpr h2.le⟩, h2⟩
    have heq : (V.filter fun b => ¬ b < a).filter (fun b => ¬ a < b) = {a} := by
      ext b; simp only [mem_filter, mem_singleton]; constructor
      · rintro ⟨⟨-, h1⟩, h2⟩; exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      · rintro rfl; exact ⟨⟨ha, lt_irrefl _⟩, lt_irrefl _⟩
    rw [hgt, heq, sum_singleton]; ring
  have swap : ∑ a ∈ V, ∑ b ∈ V.filter (a < ·), F a b = ∑ a ∈ V, ∑ b ∈ V.filter (· < a), F a b := by
    rw [sum_comm' (t' := V) (s' := fun b => V.filter (· < b))]
    · exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => hF a b
    · intro a b; simp only [mem_filter]; tauto
  rw [sum_congr rfl split, sum_add_distrib, sum_add_distrib, swap]; ring

/-- `∑_{b<a} (f a + f b) = (#V − 1) ∑ f`. -/
theorem sum_pairs_add {α : Type*} [LinearOrder α] (V : Finset α) (f : α → ℤ) :
    ∑ a ∈ V, ∑ b ∈ V.filter (· < a), (f a + f b) = ((V.card : ℤ) - 1) * ∑ a ∈ V, f a := by
  have h := sum_pairs_symm V (fun a b => f a + f b) (fun a b => by ring)
  have h2 : ∑ a ∈ V, ∑ b ∈ V, (f a + f b) = 2 * V.card * ∑ a ∈ V, f a := by
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]; ring
  have h3 : ∑ a ∈ V, (f a + f a) = 2 * ∑ a ∈ V, f a := by rw [sum_add_distrib]; ring
  have : (2 : ℤ) * ∑ a ∈ V, ∑ b ∈ V.filter (· < a), (f a + f b) =
      2 * (((V.card : ℤ) - 1) * ∑ a ∈ V, f a) := by linear_combination -h + h2 - h3
  exact mul_left_cancel₀ two_ne_zero this

/-! ### The parity of the sign -/

/-- `⌊(a − b)/t⌋ = a/t − b/t − [a mod t < b mod t]`. -/
theorem ediv_sub {t : ℕ} (ht : 0 < t) (a b : ℤ) :
    (a - b) / t = a / t - b / t - if a % t < b % t then 1 else 0 := by
  have h1 := Int.emod_add_mul_ediv a t; have h2 := Int.emod_add_mul_ediv b t
  have h3 := emod_lt' ht a; have h4 := emod_lt' ht b
  have h5 := Int.emod_nonneg a (by omega : (t : ℤ) ≠ 0)
  have h6 := Int.emod_nonneg b (by omega : (t : ℤ) ≠ 0)
  split_ifs with h
  · exact ((Int.ediv_emod_unique (b := t) (by omega)).mpr
      ⟨show a % t - b % t + t + t * (a / t - b / t - 1) = a - b by linarith, by omega, by omega⟩).1
  · exact ((Int.ediv_emod_unique (b := t) (by omega)).mpr
      ⟨show a % t - b % t + t * (a / t - b / t - 0) = a - b by linarith, by omega, by omega⟩).1

/-- `(z − s) mod t` for `0 ≤ z < t`, `s ≤ t`. -/
theorem rot_eq {t s : ℕ} (hs : s ≤ t) {z : ℤ} (h0 : 0 ≤ z) (hz : z < t) :
    (z - s) % t = if (s : ℤ) ≤ z then z - s else z + t - s := by
  split_ifs with h
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [show z - s = (z + t - s) + t * (-1) by ring, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by omega)]

/-- The rotation `x ↦ (x − s) mod t` keeps the order of `y < x` unless `y < s ≤ x`. -/
theorem rot_count {t s : ℕ} (hs : s ≤ t) (x : ℕ) (hx : x < t) :
    ∑ y ∈ range x, (if ((y : ℤ) - s) % t < ((x : ℤ) - s) % t then (1 : ℤ) else 0) =
      x - if s ≤ x then (s : ℤ) else 0 := by
  have key : ∀ y ∈ range x, (if ((y : ℤ) - s) % t < ((x : ℤ) - s) % t then (1 : ℤ) else 0) =
      1 - if y < s ∧ s ≤ x then 1 else 0 := by
    intro y hy
    rw [mem_range] at hy
    have hyt : (y : ℤ) < t := by exact_mod_cast (show y < t by omega)
    rw [rot_eq hs (by positivity) hyt, rot_eq hs (by positivity) (by exact_mod_cast hx)]
    by_cases h1 : s ≤ y <;> by_cases h2 : s ≤ x <;> simp [h1, h2] <;> omega
  rw [sum_congr rfl key, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  congr 1
  split_ifs with h
  · rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have : (range x).filter (fun y => y < s ∧ s ≤ x) = range s := by
      ext y; simp only [mem_filter, mem_range]; omega
    rw [this, card_range]
  · exact sum_eq_zero fun y _ => if_neg (by omega)

/-- **The rotation count is `[t ≡ 3 mod 4]` mod 2**: `∑_{y<x<t} [(y − s) mod t < (x − s) mod t]`
with `s = ⌊t/2⌋` is `(t choose 2) − s(t − s)`. -/
theorem rot_parity (t : ℕ) :
    Even ((∑ x ∈ range t, ∑ y ∈ range x,
      (if ((y : ℤ) - (t / 2 : ℕ)) % t < ((x : ℤ) - (t / 2 : ℕ)) % t then (1 : ℤ) else 0)) -
        if t % 4 = 3 then 1 else 0) := by
  have hs : t / 2 ≤ t := Nat.div_le_self t 2
  rw [sum_congr rfl fun x hx => rot_count hs x (mem_range.mp hx), sum_sub_distrib]
  have h2 : 2 * ∑ x ∈ range t, (x : ℤ) = t * (t - 1 : ℤ) := by
    have := Finset.sum_range_id_mul_two t
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · simp
    have := congrArg (fun z : ℕ => (z : ℤ)) this; push_cast [Nat.cast_sub htp] at this
    linarith
  have h3 : ∑ x ∈ range t, (if t / 2 ≤ x then ((t / 2 : ℕ) : ℤ) else 0) =
      (t / 2 : ℕ) * (t - t / 2 : ℕ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    have : (range t).filter (fun x => t / 2 ≤ x) = Ico (t / 2) t := by
      ext x; simp only [mem_filter, mem_range, mem_Ico]; tauto
    rw [this, Nat.card_Ico]
  rw [h3]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' t
  · subst hm
    rw [show 2 * m / 2 = m by omega, show 2 * m - m = m by omega, if_neg (by omega), sub_zero]
    have : ∑ x ∈ range (2 * m), (x : ℤ) - m * m = m * (m - 1) := by push_cast at h2; linarith
    rw [this]; exact Int.even_mul_pred_self m
  · subst hm
    rw [show (2 * m + 1) / 2 = m by omega, show 2 * m + 1 - m = m + 1 by omega]
    have : ∑ x ∈ range (2 * m + 1), (x : ℤ) - m * ((m + 1 : ℕ) : ℤ) = m * m := by
      push_cast at h2 ⊢; linarith
    rw [this]
    rcases Nat.even_or_odd m with hme | hmo
    · rw [if_neg (by obtain ⟨k, hk⟩ := hme; omega), sub_zero]
      exact (Int.even_mul.mpr (Or.inl (by exact_mod_cast hme.natCast)))
    · rw [if_pos (by obtain ⟨k, hk⟩ := hmo; omega)]
      obtain ⟨k, hk⟩ := hmo
      subst hk; push_cast
      exact ⟨2 * k * k + 2 * k, by ring⟩


/-! ### Hooks shorter than `t`, and inversions of `u` -/

/-- The part of a divisor in `[1, t)`. -/
def cntLt (t : ℕ) : (ℤ →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun k => zmultiplesHom ℤ (if 1 ≤ k ∧ k < t then 1 else 0)

theorem cntLt_pt (t : ℕ) (k : ℤ) : cntLt t (pt k) = if 1 ≤ k ∧ k < t then 1 else 0 := by
  simp [cntLt]

theorem cntLt_ray {t : ℕ} {r : ℤ} (h0 : 0 < r) (h1 : r < t) (n : ℕ) :
    cntLt t (ray t r (n + 1)) = 1 := by
  rw [ray, map_sum, sum_range_succ', sum_eq_zero, zero_add]
  · rw [cntLt_pt, if_pos (by push_cast; omega)]
  · intro j _
    rw [cntLt_pt, if_neg]
    have : (0 : ℤ) ≤ t * j := by positivity
    rintro ⟨-, h⟩; push_cast at h; nlinarith

theorem cntLt_pairHooks {t : ℕ} (ht : 0 < t) {d : ℤ} (_hd : 0 < d) (hdt : ¬ (t : ℤ) ∣ d) :
    cntLt t (pairHooks t d) = quo t d := by
  rw [pairHooks, map_sum]
  simp only [cntLt_ray (emod_pos_of_not_dvd' ht hdt) (emod_lt' ht d)]
  simp

theorem sum_map_ite_one (H : Multiset ℤ) (p : ℤ → Prop) [DecidablePred p] :
    (H.map fun h => if p h then (1 : ℤ) else 0).sum = (H.filter p).card := by
  induction H using Multiset.induction_on with
  | empty => simp
  | cons a H ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.filter_cons]
    by_cases hp : p a
    · rw [if_pos hp, if_pos hp]; simp; ring
    · rw [if_neg hp, if_neg hp]; simp

/-- **The hooks shorter than `t`**: one per ray, so `∑_{b<a in V} ⌊(a − b)/t⌋`. -/
theorem card_hooks_lt {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hs : Stable t μ) :
    (((hooks μ).filter (· < (t : ℤ))).card : ℤ) =
      ∑ a ∈ vSet t μ, ∑ b ∈ (vSet t μ).filter (· < a), (quo t (a - b) : ℤ) := by
  have hV := complete ht hs
  have e := congrArg (cntLt t) (hooks_eq_pairHooks ht hs)
  rw [toDiv, map_multiset_sum, Multiset.map_map] at e
  have hH : (hooks μ).map (cntLt t ∘ pt) =
      (hooks μ).map fun h : ℤ => if h < (t : ℤ) then (1 : ℤ) else 0 :=
    Multiset.map_congr rfl fun h hh => by
      show cntLt t (pt h) = _
      rw [cntLt_pt]
      have := one_le_of_mem_hooks hh
      split_ifs <;> first | rfl | omega
  rw [hH, sum_map_ite_one] at e
  rw [e, map_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [map_sum, ← sum_filter_add_sum_filter_not (vSet t μ) (· < a)]
  rw [sum_eq_zero (s := (vSet t μ).filter fun b => ¬ b < a) fun b hb => by
    rw [mem_filter] at hb; rw [pairHooks_of_nonpos t ht (by omega), map_zero], add_zero]
  refine sum_congr rfl fun b hb => ?_
  rw [mem_filter] at hb
  exact cntLt_pairHooks ht (by omega) (hV.not_dvd ha hb.1 (by omega))

/-- **The inversions of the class-sorted coding**, as pairs `b < a` in `V` with `cls b < cls a`. -/
theorem card_inv {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hV : Complete t (vSet t μ)) :
    (((univ : Finset (Fin t × Fin t)).filter
        fun p => p.1 < p.2 ∧ uCoding t μ p.1 < uCoding t μ p.2).card : ℤ) =
      ∑ a ∈ vSet t μ, ∑ b ∈ (vSet t μ).filter (· < a), if cls t b < cls t a then 1 else 0 := by
  have e : ∑ a ∈ vSet t μ, ∑ b ∈ (vSet t μ).filter (· < a),
      (if cls t b < cls t a then (1 : ℤ) else 0) =
      (((vSet t μ ×ˢ vSet t μ).filter fun q => q.2 < q.1 ∧ cls t q.2 < cls t q.1).card : ℤ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter, sum_product]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_filter]
    refine sum_congr rfl fun b _ => ?_
    by_cases h1 : b < a <;> by_cases h2 : cls t b < cls t a <;> simp [h1, h2]
  rw [e]
  congr 1
  refine card_nbij (fun p => (uCoding t μ p.2, uCoding t μ p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, mem_product, Set.mem_ofPred_eq] at hp ⊢
    refine ⟨⟨(uCoding_spec ht hV _).1, (uCoding_spec ht hV _).1⟩, hp.2, ?_⟩
    rw [cls_uCoding ht hV, cls_uCoding ht hV]; exact_mod_cast hp.1
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (uCoding_injective ht hV h.2) (uCoding_injective ht hV h.1)
  · rintro ⟨a, b⟩ hq
    simp only [coe_filter, mem_product] at hq
    obtain ⟨⟨ha, hb⟩, hlt, hcl⟩ := hq
    obtain ⟨j, rfl⟩ := uCoding_surj ht hV ha
    obtain ⟨i, rfl⟩ := uCoding_surj ht hV hb
    refine ⟨(i, j), ?_, rfl⟩
    simp only [coe_filter, mem_univ, true_and]
    rw [cls_uCoding ht hV, cls_uCoding ht hV] at hcl
    exact ⟨by exact_mod_cast hcl, hlt⟩

/-- **The sign is `[t ≡ 3 mod 4]`**: `#{h < t} + inv(u) ≡ [t ≡ 3 (mod 4)] (mod 2)`. -/
theorem sign_parity {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hs : Stable t μ) :
    Even ((((hooks μ).filter (· < (t : ℤ))).card : ℤ) +
      (((univ : Finset (Fin t × Fin t)).filter
        fun p => p.1 < p.2 ∧ uCoding t μ p.1 < uCoding t μ p.2).card : ℤ) -
      if t % 4 = 3 then 1 else 0) := by
  have hV := complete ht hs
  set V := vSet t μ
  set s := t / 2
  have hT : (t : ℤ) ≠ 0 := by omega
  rw [card_hooks_lt ht hs, card_inv ht hV]
  have hmerge : ∑ a ∈ V, ∑ b ∈ V.filter (· < a), (quo t (a - b) : ℤ) +
      ∑ a ∈ V, ∑ b ∈ V.filter (· < a), (if cls t b < cls t a then (1 : ℤ) else 0) =
      ∑ a ∈ V, ∑ b ∈ V.filter (· < a),
        ((quo t (a - b) : ℤ) + if cls t b < cls t a then 1 else 0) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun a _ => sum_add_distrib.symm
  rw [hmerge]
  -- residue part `K`, symmetric in the pair
  let K : ℤ → ℤ → ℤ := fun x y => if (min x y - s) % t < (max x y - s) % t then 1 else 0
  have hcls : ∀ a, cls t a = (a % t - s) % t := fun a => by
    unfold cls
    conv_lhs => rw [Int.sub_emod]
    conv_rhs => rw [Int.sub_emod, Int.emod_emod]
  have hterm : ∀ a ∈ V, ∀ b ∈ V.filter (· < a),
      (quo t (a - b) : ℤ) + (if cls t b < cls t a then 1 else 0) =
        (a / t + b / t) - 2 * (b / t) + K (a % t) (b % t) -
          2 * ((if a % t < b % t then 1 else 0) * K (a % t) (b % t)) := by
    intro a ha b hb
    rw [mem_filter] at hb
    have hq : (quo t (a - b) : ℤ) = (a - b) / t := by
      unfold quo; have := Int.ediv_nonneg (by omega : (0 : ℤ) ≤ a - b) (by omega : (0 : ℤ) ≤ t)
      omega
    rw [hq, ediv_sub ht, hcls a, hcls b]
    have hne : a % t ≠ b % t := fun h => by have := hV.inj a ha b hb.1 h; omega
    have hne' : (b % t - s) % t ≠ (a % t - s) % t := fun h => hne (by
      have := emod_eq_iff.mp h
      have : (t : ℤ) ∣ b % t - a % t := by rw [show b % t - a % t = b % t - s - (a % t - s) by ring]; exact this
      have h1 := emod_lt' ht a; have h2 := emod_lt' ht b
      have h3 := Int.emod_nonneg a hT; have h4 := Int.emod_nonneg b hT
      obtain ⟨k, hk⟩ := this
      have : k = 0 := by
        by_contra hk0
        rcases lt_or_gt_of_ne hk0 with h | h
        · have : (t : ℤ) * k ≤ -t := by nlinarith
          omega
        · have : (t : ℤ) * k ≥ t := by nlinarith
          omega
      subst this; omega)
    simp only [K]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le, if_pos hlt]
      by_cases h : (a % t - s) % t < (b % t - s) % t
      · rw [if_pos h, if_neg (by omega)]; ring
      · rw [if_neg h, if_pos (by omega)]; ring
    · rw [min_eq_right hgt.le, max_eq_left hgt.le, if_neg (by omega)]
      by_cases h : (b % t - s) % t < (a % t - s) % t
      · rw [if_pos h]; ring
      · rw [if_neg h]; ring
  have hterm' : ∀ a ∈ V, ∀ b ∈ V.filter (· < a),
      (quo t (a - b) : ℤ) + (if cls t b < cls t a then 1 else 0) =
        ((a / t + b / t) + K (a % t) (b % t)) +
          2 * (-(b / t) - (if a % t < b % t then 1 else 0) * K (a % t) (b % t)) := by
    intro a ha b hb; rw [hterm a ha b hb]; ring
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => hterm' a ha b hb]
  have hsplit2 : ∑ a ∈ V, ∑ b ∈ V.filter (· < a), (((a / (t : ℤ) + b / t) + K (a % t) (b % t)) +
      2 * (-(b / (t : ℤ)) - (if a % t < b % t then 1 else 0) * K (a % t) (b % t))) =
      (∑ a ∈ V, ∑ b ∈ V.filter (· < a), (a / (t : ℤ) + b / t) +
        ∑ a ∈ V, ∑ b ∈ V.filter (· < a), K (a % t) (b % t)) +
      2 * ∑ a ∈ V, ∑ b ∈ V.filter (· < a),
        (-(b / (t : ℤ)) - (if a % t < b % t then 1 else 0) * K (a % t) (b % t)) := by
    simp only [mul_sum, ← sum_add_distrib]
  rw [hsplit2, sum_pairs_add V (fun a => a / (t : ℤ)), hV.card]
  -- the abacus coordinates sum to the charge
  have hcharge : ∑ a ∈ V, a / (t : ℤ) = -t := by
    have hQ := charge ht hs
    have hr : ∑ a ∈ V, a % (t : ℤ) = ∑ n ∈ range t, (n : ℤ) := hV.sum_emod' ht (fun x => x)
    have h2 : 2 * ∑ n ∈ range t, (n : ℤ) = t * (t - 1 : ℤ) := by
      have := Finset.sum_range_id_mul_two t
      rcases Nat.eq_zero_or_pos t with rfl | htp
      · simp
      have := congrArg (fun z : ℕ => (z : ℤ)) this; push_cast [Nat.cast_sub htp] at this
      linarith
    have hsplit : ∑ a ∈ V, a = ∑ a ∈ V, a % (t : ℤ) + t * ∑ a ∈ V, a / (t : ℤ) := by
      rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun a _ => (Int.emod_add_mul_ediv a t).symm
    have : (t : ℤ) * (2 * ∑ a ∈ V, a / (t : ℤ)) = t * (-2 * t) := by
      unfold Charge at hQ; nlinarith
    linarith [mul_left_cancel₀ hT this]
  rw [hcharge]
  -- the residue part is the rotation count
  have hK : ∑ a ∈ V, ∑ b ∈ V.filter (· < a), K (a % t) (b % t) =
      ∑ x ∈ range t, ∑ y ∈ range x,
        (if ((y : ℤ) - s) % t < ((x : ℤ) - s) % t then (1 : ℤ) else 0) := by
    have hsym : ∀ x y, K x y = K y x := fun x y => by simp only [K, min_comm, max_comm]
    have hdiag : ∀ x, K x x = 0 := fun x => by simp [K]
    have h1 := sum_pairs_symm V (fun a b => K (a % t) (b % t)) (fun a b => hsym _ _)
    have h2 := sum_pairs_symm (range t) (fun x y => K x y) (fun x y => hsym _ _)
    have h3 : ∑ a ∈ V, ∑ b ∈ V, K (a % t) (b % t) = ∑ x ∈ range t, ∑ y ∈ range t, K x y := by
      rw [hV.sum_emod' ht (fun x => ∑ b ∈ V, K x (b % t))]
      exact sum_congr rfl fun x _ => hV.sum_emod' ht (fun y => K x y)
    have h4 : ∑ x ∈ range t, ∑ y ∈ (range t).filter (· < x), K x y =
        ∑ x ∈ range t, ∑ y ∈ range x,
          (if ((y : ℤ) - s) % t < ((x : ℤ) - s) % t then (1 : ℤ) else 0) := by
      refine sum_congr rfl fun x hx => ?_
      rw [mem_range] at hx
      have : (range t).filter (· < x) = range x := by
        ext y; simp only [mem_filter, mem_range]; omega
      rw [this]
      refine sum_congr rfl fun y hy => ?_
      rw [mem_range] at hy
      simp only [K, min_eq_right (show (y : ℤ) ≤ x by exact_mod_cast hy.le),
        max_eq_left (show (y : ℤ) ≤ x by exact_mod_cast hy.le)]
    simp only [hdiag, sum_const_zero, zero_add] at h1 h2
    have : (2 : ℤ) * ∑ a ∈ V, ∑ b ∈ V.filter (· < a), K (a % t) (b % t) =
        2 * ∑ x ∈ range t, ∑ y ∈ (range t).filter (· < x), K x y := by
      rw [← h1, ← h2, h3]
    rw [← h4]; exact mul_left_cancel₀ two_ne_zero this
  rw [hK]
  have hrot := rot_parity t
  have hev : Even (((t : ℤ) - 1) * -t) := by
    rw [show ((t : ℤ) - 1) * -t = -(t * (t - 1)) by ring]; exact (Int.even_mul_pred_self t).neg
  have key : ∀ A R Z c : ℤ, Even A → Even (R - c) → Even (A + R + 2 * Z - c) := by
    intro A R Z c hA hR
    have := (hA.add hR).add (even_two_mul Z)
    rwa [show A + R + 2 * Z - c = A + (R - c) + 2 * Z by ring]
  exact key _ _ _ _ hev hrot

/-! ### Corollary 4 -/

/-- Evaluating a divisor on a weight `τ` with values in a commutative group. -/
def evalU {G : Type*} [CommGroup G] (τ : ℤ → G) : (ℤ →₀ ℤ) →+ Additive G :=
  Finsupp.liftAddHom fun k => zmultiplesHom _ (Additive.ofMul (τ k))

theorem evalU_zsmul_pt {G : Type*} [CommGroup G] (τ : ℤ → G) (n k : ℤ) :
    (evalU τ (n • pt k)).toMul = τ k ^ n := by
  simp [evalU]

theorem evalU_pt {G : Type*} [CommGroup G] (τ : ℤ → G) (k : ℤ) : (evalU τ (pt k)).toMul = τ k := by
  simpa using evalU_zsmul_pt τ 1 k

/-- **N5 evaluated on a weight**: the folded Eq. (2), multiplicatively, with no signs. -/
theorem folded_eval {G : Type*} [CommGroup G] (τ : ℤ → G) {t : ℕ} {μ : YoungDiagram}
    (hF : Folded t μ) :
    (∏ c ∈ μ.cells, τ |hook μ c - t| * τ (hook μ c + t) / τ (hook μ c) ^ 2) *
        ∏ k ∈ Ico 1 t, τ k ^ ((t : ℤ) - k) =
      ∏ a ∈ vSet t μ, ∏ b ∈ (vSet t μ).filter (· < a), τ (a - b) := by
  have e := congrArg (fun D => (evalU τ D).toMul) hF
  have hH : toDiv (hooks μ) = ∑ c ∈ μ.cells, pt (hook μ c) := by rw [hooks, toDiv_map]; rfl
  simp only [hH, map_sum, map_add, toMul_add, toMul_sum, lap_pt, lapPt, map_sub, toMul_sub,
    map_nsmul, toMul_nsmul, evalU_pt, evalU_zsmul_pt] at e
  simpa using e

/-- A product of signs. -/
theorem prod_map_ite_pow {G : Type*} [CommGroup G] (H : Multiset ℤ) (p : ℤ → Prop)
    [DecidablePred p] (ε : G) :
    (H.map fun h => if p h then ε else 1).prod = ε ^ (H.filter p).card := by
  induction H using Multiset.induction_on with
  | empty => simp
  | cons a H ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.filter_cons]
    split_ifs <;> simp [pow_succ, mul_comm]

/-- Rearranging in a commutative group. -/
theorem rearrange_sign {G : Type*} [CommGroup G] {n1 n2 C X P E : G} (hX : X * P = E)
    (hN : n1 = C * n2) : n1 * X = C / P * (n2 * E) := by
  subst hN; rw [← hX]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

/-- **Dehaye–Han, Corollary 4 (Eq. (19))**: for `τ` even (`ε = 1`) or odd (`ε = −1`),
`∏_h τ(h − t)τ(h + t)/τ(h)² = C / ∏_{k<t} τ(k)^{t−k} · ∏_{i<j} τ(u_i − u_j)`,
with `C = −1` if `τ` is odd and `t ≡ 3 (mod 4)`, `C = 1` otherwise. -/
theorem corollary4 {t : ℕ} (ht : 0 < t) {μ : YoungDiagram} (hμ : IsTCore t μ) {R : Type*}
    [CommRing R] (τ : ℤ → Rˣ) (ε : Rˣ) (hε : ε = 1 ∨ ε = -1) (hτ : ∀ x, x ≠ 0 → τ (-x) = ε * τ x) :
    ((hooks μ).map fun h => τ (h - t) * τ (h + t) / τ h ^ 2).prod =
      (if ε = -1 ∧ t % 4 = 3 then -1 else 1) / (∏ k ∈ Ico 1 t, τ k ^ (t - k)) *
        ∏ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
          τ (uCoding t μ p.1 - uCoding t μ p.2) := by
  have hs := stable_of_core ht hμ
  have hV := complete ht hs
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have habs : ∀ x : ℤ, τ x = (if x < 0 then ε else 1) * τ |x| := fun x => by
    split_ifs with h
    · rw [abs_of_neg h, hτ x (by omega), ← mul_assoc, hεε, one_mul]
    · rw [abs_of_nonneg (not_lt.mp h), one_mul]
  -- left side: `ε^{#{h<t}}` times the folded product
  have hL : ((hooks μ).map fun h => τ (h - t) * τ (h + t) / τ h ^ 2).prod =
      ε ^ ((hooks μ).filter (· < (t : ℤ))).card *
        ∏ c ∈ μ.cells, τ |hook μ c - t| * τ (hook μ c + t) / τ (hook μ c) ^ 2 := by
    have hcells : ∏ c ∈ μ.cells, τ |hook μ c - t| * τ (hook μ c + t) / τ (hook μ c) ^ 2 =
        ((hooks μ).map fun h => τ |h - t| * τ (h + t) / τ h ^ 2).prod := by
      rw [hooks, Multiset.map_map]; rfl
    rw [hcells, ← prod_map_ite_pow, ← Multiset.prod_map_mul]
    show _ = (((hooks μ).map fun h : ℤ => (if h < (t : ℤ) then ε else 1) *
      (τ |h - t| * τ (h + t) / τ h ^ 2))).prod
    congr 1
    refine Multiset.map_congr rfl fun h hh => ?_
    have hne : h ≠ t := fun e => hμ h hh (e ▸ dvd_refl _)
    rw [habs (h - t)]
    simp only [sub_neg, mul_assoc, mul_div_assoc]
  -- right side: `ε^{inv(u)}` times the product over pairs of `V`
  have hR : ∏ p ∈ (univ : Finset (Fin t × Fin t)).filter (fun p => p.1 < p.2),
      τ (uCoding t μ p.1 - uCoding t μ p.2) =
      ε ^ ((univ : Finset (Fin t × Fin t)).filter
          fun p => p.1 < p.2 ∧ uCoding t μ p.1 < uCoding t μ p.2).card *
        ∏ a ∈ vSet t μ, ∏ b ∈ (vSet t μ).filter (· < a), τ (a - b) := by
    rw [prod_congr rfl fun p _ => habs _, prod_mul_distrib, prod_ite, prod_const_one, mul_one,
      prod_const, filter_filter]
    congr 1
    · congr 2; ext p; simp only [sub_neg]
    have e2 : ∏ a ∈ vSet t μ, ∏ b ∈ (vSet t μ).filter (· < a), τ (a - b) =
        ∏ q ∈ (vSet t μ ×ˢ vSet t μ).filter (fun q => q.2 < q.1), τ (q.1 - q.2) := by
      rw [prod_filter, prod_product]
      exact prod_congr rfl fun a _ => by rw [prod_filter]
    rw [e2]
    refine prod_nbij (fun p => (max (uCoding t μ p.1) (uCoding t μ p.2),
      min (uCoding t μ p.1) (uCoding t μ p.2))) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      have hne : uCoding t μ p.1 ≠ uCoding t μ p.2 := fun h =>
        (ne_of_lt hp) (uCoding_injective ht hV h)
      simp only [mem_filter, mem_product]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rcases le_total (uCoding t μ p.1) (uCoding t μ p.2) with h | h
        · rw [max_eq_right h]; exact (uCoding_spec ht hV _).1
        · rw [max_eq_left h]; exact (uCoding_spec ht hV _).1
      · rcases le_total (uCoding t μ p.1) (uCoding t μ p.2) with h | h
        · rw [min_eq_left h]; exact (uCoding_spec ht hV _).1
        · rw [min_eq_right h]; exact (uCoding_spec ht hV _).1
      · exact min_lt_max.mpr hne
    · intro p hp q hq h
      simp only [coe_filter, mem_univ, true_and] at hp hq
      simp only [Prod.mk.injEq] at h
      have inj := uCoding_injective ht hV
      rcases le_total (uCoding t μ p.1) (uCoding t μ p.2) with h1 | h1 <;>
        rcases le_total (uCoding t μ q.1) (uCoding t μ q.2) with h2 | h2 <;>
        simp only [max_eq_right, max_eq_left, min_eq_left, min_eq_right, h1, h2] at h
      · exact Prod.ext (inj h.2) (inj h.1)
      · exfalso
        have e1 := congrArg Fin.val (inj h.1); have e2 := congrArg Fin.val (inj h.2)
        have := Fin.lt_def.mp hp; have := Fin.lt_def.mp hq; omega
      · exfalso
        have e1 := congrArg Fin.val (inj h.1); have e2 := congrArg Fin.val (inj h.2)
        have := Fin.lt_def.mp hp; have := Fin.lt_def.mp hq; omega
      · exact Prod.ext (inj h.1) (inj h.2)
    · rintro ⟨a, b⟩ hq
      simp only [coe_filter, mem_product] at hq
      obtain ⟨⟨ha, hb⟩, hlt⟩ := hq
      obtain ⟨j, rfl⟩ := uCoding_surj ht hV ha
      obtain ⟨i, rfl⟩ := uCoding_surj ht hV hb
      have hij : i ≠ j := fun h => by subst h; exact lt_irrefl _ hlt
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨(i, j), by simpa using h, by simp [max_eq_right hlt.le, min_eq_left hlt.le]⟩
      · exact ⟨(j, i), by simpa using h, by simp [max_eq_left hlt.le, min_eq_right hlt.le]⟩
    · intro p _
      rcases le_total (uCoding t μ p.1) (uCoding t μ p.2) with h | h
      · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by omega), neg_sub]
      · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by omega)]
  -- the folded identity, with `npow` exponents
  have hX := folded_eval τ (folded ht hs)
  have hP : ∏ k ∈ Ico 1 t, τ k ^ ((t : ℤ) - k) = ∏ k ∈ Ico 1 t, τ k ^ (t - k) :=
    prod_congr rfl fun k hk => by
      rw [mem_Ico] at hk; rw [← zpow_natCast, Nat.cast_sub hk.2.le]
  rw [hP] at hX
  -- the sign
  have hsign : ε ^ ((hooks μ).filter (· < (t : ℤ))).card =
      (if ε = -1 ∧ t % 4 = 3 then -1 else 1) *
        ε ^ ((univ : Finset (Fin t × Fin t)).filter
          fun p => p.1 < p.2 ∧ uCoding t μ p.1 < uCoding t μ p.2).card := by
    set N1 := ((hooks μ).filter (· < (t : ℤ))).card
    set N2 := ((univ : Finset (Fin t × Fin t)).filter
          fun p => p.1 < p.2 ∧ uCoding t μ p.1 < uCoding t μ p.2).card
    have hsq : ε ^ N2 * ε ^ N2 = 1 := by rw [← mul_pow, hεε, one_pow]
    suffices ε ^ (N1 + N2) = if ε = -1 ∧ t % 4 = 3 then -1 else 1 by
      calc ε ^ N1 = ε ^ (N1 + N2) * ε ^ N2 := by rw [pow_add, mul_assoc, hsq, mul_one]
        _ = _ := by rw [this]
    rcases hε with rfl | rfl
    · rw [one_pow]; split_ifs with h
      · exact h.1
      · rfl
    · have hpar := sign_parity ht hs
      rw [← zpow_natCast, show ((N1 + N2 : ℕ) : ℤ) = (if t % 4 = 3 then 1 else 0) +
        ((N1 : ℤ) + N2 - if t % 4 = 3 then 1 else 0) by push_cast; ring, zpow_add,
        hpar.neg_one_zpow, mul_one]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd ⟨rfl, h1⟩ h2
      · exact absurd h2.2 h1
      · simp
  rw [hL, hR]
  exact rearrange_sign hX hsign


end

end RMT.MultisetHook

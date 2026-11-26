import RMTlib.Growth.Maya

/-!
# The piecewise-linear local rule (horizontal strips)

Fomin's local rule for growth diagrams of `ℕ`-matrices: from the corner `κ` of a square, its two
neighbours `μ, l` (each a horizontal strip over `κ`) and the entry `x` of the square,

  `ν_0 = max(μ_0, l_0) + x`,  `ν_{i+1} = max(μ_{i+1}, l_{i+1}) + (min(μ_i, l_i) − κ_i)` (`plRule`):

each row takes the larger neighbour, and the overlap of the two strips in row `i` is passed to
row `i + 1`. This is the rule of the original export's Gelfand–Tsetlin Pieri bijection
`Pieri.toggle_sum` (its map `bw`, RH-Dual's computation in #129), so a column of a PL growth
diagram is one `Pieri.up` step (#143).

* `plRule_none`, `plRule_left`, `plRule_right`, `plRule_two`, `plRule_bump`: the single-box cases
  (`box κ a = κ + e_a`). In the bump the overlap `1` passes to the next row.
* `localRule_two_eq_plRule`, `localRule_bump_eq_plRule`, `localRule_left_eq_plRule`,
  `localRule_none_eq_plRule`: **on single boxes the PL rule is `RMT.Growth.localRule`**, the 0/1
  rule that computes RSK (`RMTlib.Growth.Maya`, #130).
* `sum_plRule`, `sum_plRule_eq`: size conservation, `|ν| + |κ| = x + |μ| + |l|`.
* On the Maya diagram (`site f i = f_i − i − 1`): `site_plRule_zero`, `site_plRule_succ`: each
  particle takes the farther of its two positions and moves on by the overlap passed from the
  particle above; `hStrip_iff_site`: a horizontal strip is a set of non-overtaking right hops.
-/

open Finset

namespace RMT.Growth

/-- **The piecewise-linear local rule** (Fomin's rule for `ℕ`-matrices, horizontal strips):
from the corner `κ`, the two neighbours `μ, l` and the entry `x` of the square,
`ν_0 = max(μ_0, l_0) + x` and `ν_{i+1} = max(μ_{i+1}, l_{i+1}) + (min(μ_i, l_i) − κ_i)`:
row `i + 1` receives the overlap of the two strips in row `i`. -/
def plRule (κ μ l : ℕ → ℕ) (x : ℕ) : ℕ → ℕ
  | 0 => max (μ 0) (l 0) + x
  | i + 1 => max (μ (i + 1)) (l (i + 1)) + (min (μ i) (l i) - κ i)

/-- `κ + e_a`: one box added in row `a`. -/
def box (κ : ℕ → ℕ) (a : ℕ) : ℕ → ℕ := Function.update κ a (κ a + 1)

theorem box_apply (κ : ℕ → ℕ) (a i : ℕ) : box κ a i = κ i + if i = a then 1 else 0 := by
  unfold box; by_cases h : i = a
  · subst h; simp
  · simp [h]

/-! ## The single-box cases: the rule of `localRule` -/

/-- Neither neighbour grew: `ν = κ + x e_0`. -/
theorem plRule_none (κ : ℕ → ℕ) (x : ℕ) (i : ℕ) :
    plRule κ κ κ x i = κ i + if i = 0 then x else 0 := by
  cases i <;> simp [plRule]

/-- One neighbour grew: `ν` is that neighbour. -/
theorem plRule_left (κ : ℕ → ℕ) (b i : ℕ) : plRule κ κ (box κ b) 0 i = box κ b i := by
  cases i with
  | zero => simp only [plRule, box_apply]; split_ifs <;> simp only [max_def] <;> split_ifs <;> omega
  | succ i => simp only [plRule, box_apply]; split_ifs <;> simp only [max_def] <;> split_ifs <;> omega

theorem plRule_right (κ : ℕ → ℕ) (a i : ℕ) : plRule κ (box κ a) κ 0 i = box κ a i := by
  cases i with
  | zero => simp only [plRule, box_apply]; split_ifs <;> simp only [max_def] <;> split_ifs <;> omega
  | succ i => simp only [plRule, box_apply]; split_ifs <;> simp only [max_def] <;> split_ifs <;> omega

/-- **Two different rows grew: both boxes are added**, `ν = κ + e_a + e_b`. -/
theorem plRule_two (κ : ℕ → ℕ) {a b : ℕ} (hab : a ≠ b) (i : ℕ) :
    plRule κ (box κ a) (box κ b) 0 i = box (box κ a) b i := by
  cases i with
  | zero => simp only [plRule, box_apply]; split_ifs <;> simp only [max_def] <;> split_ifs <;> omega
  | succ i => simp only [plRule, box_apply]; split_ifs <;> simp only [max_def] <;> split_ifs <;> omega

/-- **The same row grew on both sides: the overlap is passed to the next row**,
`ν = κ + e_a + e_{a+1}` (the bump). -/
theorem plRule_bump (κ : ℕ → ℕ) (a i : ℕ) :
    plRule κ (box κ a) (box κ a) 0 i = box (box κ a) (a + 1) i := by
  cases i with
  | zero => simp only [plRule, box_apply, max_self]; simp
  | succ i => simp only [plRule, box_apply, max_self, min_self]; split_ifs <;> omega

/-! ## Size -/

/-- **Size conservation, with the overlap still to pass**: for `κ ≤ μ, l` pointwise,
`Σ_{i ≤ N} ν_i + Σ_{i < N} κ_i + min(μ_N, l_N) = x + Σ_{i ≤ N} (μ_i + l_i)`. -/
theorem sum_plRule {κ μ l : ℕ → ℕ} (hμ : ∀ i, κ i ≤ μ i) (hl : ∀ i, κ i ≤ l i) (x N : ℕ) :
    ∑ i ∈ range (N + 1), plRule κ μ l x i + ∑ i ∈ range N, κ i + min (μ N) (l N) =
      x + ∑ i ∈ range (N + 1), (μ i + l i) := by
  induction N with
  | zero => simp only [zero_add, range_one, sum_singleton, range_zero, sum_empty, plRule]; omega
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ (fun i => κ i), sum_range_succ (fun i => μ i + l i)]
    have h1 : κ N ≤ min (μ N) (l N) := le_min (hμ N) (hl N)
    have h2 := min_add_max (μ (N + 1)) (l (N + 1))
    have h3 : plRule κ μ l x (N + 1) = max (μ (N + 1)) (l (N + 1)) + (min (μ N) (l N) - κ N) := rfl
    rw [h3]
    omega

/-- **`|ν| + |κ| = x + |μ| + |l|`** when `μ, l` vanish from row `N` on. -/
theorem sum_plRule_eq {κ μ l : ℕ → ℕ} (hμ : ∀ i, κ i ≤ μ i) (hl : ∀ i, κ i ≤ l i) (x N : ℕ)
    (hμN : μ N = 0) (hlN : l N = 0) :
    ∑ i ∈ range (N + 1), plRule κ μ l x i + ∑ i ∈ range N, κ i =
      x + ∑ i ∈ range (N + 1), (μ i + l i) := by
  have := sum_plRule hμ hl x N
  rw [hμN, hlN, min_self, add_zero] at this
  exact this

/-! ## On the Maya diagram -/

/-- The site of the particle of row `i`, `f_i − i − 1`. -/
def site (f : ℕ → ℕ) (i : ℕ) : ℤ := (f i : ℤ) - i - 1

/-- **The PL rule on the Maya line**: particle `0` takes the farther of its two positions and hops
`x` more; particle `i + 1` takes the farther of its two positions and hops on by the overlap
`min(μ_i, l_i) − κ_i` of the two hops of particle `i`, which is passed down to it. -/
theorem site_plRule_zero (κ μ l : ℕ → ℕ) (x : ℕ) :
    site (plRule κ μ l x) 0 = max (site μ 0) (site l 0) + x := by
  simp only [site, plRule]; push_cast; omega

theorem site_plRule_succ (κ μ l : ℕ → ℕ) (x i : ℕ) :
    site (plRule κ μ l x) (i + 1) =
      max (site μ (i + 1)) (site l (i + 1)) + ((min (μ i) (l i) - κ i : ℕ) : ℤ) := by
  simp only [site, plRule]; push_cast; omega

/-- `ν / κ` is a horizontal strip: `κ_i ≤ ν_i ≤ κ_{i−1}`. -/
def HStrip (κ ν : ℕ → ℕ) : Prop := (∀ i, κ i ≤ ν i) ∧ ∀ i, ν (i + 1) ≤ κ i

/-- **A horizontal strip is a set of non-overtaking hops**: every particle moves right, and
particle `i + 1` stays strictly left of the old site of particle `i`. -/
theorem hStrip_iff_site (κ ν : ℕ → ℕ) :
    HStrip κ ν ↔ (∀ i, site κ i ≤ site ν i) ∧ ∀ i, site ν (i + 1) < site κ i := by
  unfold HStrip site
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by have := h1 i; omega, fun i => by have := h2 i; push_cast; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by have := h1 i; omega, fun i => by have := h2 i; push_cast at this; omega⟩

/-! ## The bridge to `localRule` -/

theorem getD_addRow_eq_box {ρ : Shape} {a : ℕ} (ha : a ≤ ρ.length) :
    (fun j => (Shape.addRow ρ a).getD j 0) = box (fun j => ρ.getD j 0) a := by
  funext j; rw [getD_addRow ρ a j ha, box_apply]; split_ifs <;> simp_all

/-- **On single boxes the PL rule is Fomin's local rule** (`localRule`, #130): two different rows. -/
theorem localRule_two_eq_plRule {ρ : Shape} {a b : ℕ} (hab : a ≠ b) (ha : a ≤ ρ.length)
    (hb : b ≤ ρ.length) (x : Bool) :
    (fun j => (localRule ρ (Shape.addRow ρ a) (Shape.addRow ρ b) x).getD j 0) =
      plRule (fun j => ρ.getD j 0) (fun j => (Shape.addRow ρ a).getD j 0)
        (fun j => (Shape.addRow ρ b).getD j 0) 0 := by
  have hb' : b ≤ (Shape.addRow ρ a).length := by
    rw [length_addRow ρ a ha]; split_ifs <;> omega
  rw [localRule_two ρ hab ha hb, getD_addRow_eq_box hb', getD_addRow_eq_box ha,
    getD_addRow_eq_box hb]
  funext i; rw [plRule_two _ hab]

/-- The same row on both sides: the bump. -/
theorem localRule_bump_eq_plRule {ρ : Shape} {a : ℕ} (ha : a ≤ ρ.length) (x : Bool) :
    (fun j => (localRule ρ (Shape.addRow ρ a) (Shape.addRow ρ a) x).getD j 0) =
      plRule (fun j => ρ.getD j 0) (fun j => (Shape.addRow ρ a).getD j 0)
        (fun j => (Shape.addRow ρ a).getD j 0) 0 := by
  have ha' : a + 1 ≤ (Shape.addRow ρ a).length := by
    rw [length_addRow ρ a ha]; split_ifs <;> omega
  rw [localRule_bump ρ ha, getD_addRow_eq_box ha', getD_addRow_eq_box ha]
  funext i; rw [plRule_bump]

/-- One side grew. -/
theorem localRule_left_eq_plRule {ρ : Shape} {b : ℕ} (hb : b ≤ ρ.length) (x : Bool) :
    (fun j => (localRule ρ ρ (Shape.addRow ρ b) x).getD j 0) =
      plRule (fun j => ρ.getD j 0) (fun j => ρ.getD j 0) (fun j => (Shape.addRow ρ b).getD j 0) 0 := by
  rw [localRule_left ρ hb, getD_addRow_eq_box hb]
  funext i; rw [plRule_left]

/-- Neither side grew: the entry `x` of the square (`0` or `1`) goes into row `0`. -/
theorem localRule_none_eq_plRule (ρ : Shape) (x : Bool) :
    (fun j => (localRule ρ ρ ρ x).getD j 0) =
      plRule (fun j => ρ.getD j 0) (fun j => ρ.getD j 0) (fun j => ρ.getD j 0)
        (if x then 1 else 0) := by
  rw [localRule_none]
  funext i
  rw [plRule_none]
  cases x
  · simp
  · have := congrFun (getD_addRow_eq_box (ρ := ρ) (a := 0) (Nat.zero_le _)) i
    simp only [ite_true] at this ⊢
    rw [this, box_apply]

end RMT.Growth

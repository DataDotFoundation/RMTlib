import RMTlib.Growth.RSK
import RMTlib.Symmetric.FominMaya

/-!
# Fomin's local rule on the Maya diagram

`RMT.Growth.localRule` is the local rule of Fomin's growth diagrams (the two-variable recursion
that computes RSK, `RMT.RSK.Fomin.rsk_eq`). Read on the Maya diagram (`mayaL`: the particle of
row `j` sits at `l_j − j − 1`; `mayaL_addRow`: adding a box in row `i` is a hop of particle `i`
one site to the right), the rule is a rule for hops. With `ρ` the corner of the square and
`μ, ν` its two neighbours:

* `localRule_none_maya`: neither neighbour grew: particle `0` hops iff the square holds a `1`;
* `localRule_left_maya`: one neighbour grew: that particle hops;
* `localRule_two_maya`: the neighbours grew in rows `a ≠ b`: **particles `a` and `b` hop,
  independently** (hops of different particles commute);
* `localRule_bump_maya`: both grew in the same row `a`: **particle `a` hops and the hop passes
  to the next particle**, `a + 1` (Schensted's bump). It can always hop (`addable_bump`).

So the only interaction in RSK, read on fermions, is the passing of a hop from a particle to the
next one, and a wall is a condition on which hops are allowed (#129): the `N`-row wall forbids the
hop of particle `N`, the mirror wall keeps the particles on one parity class (#126).

The shape lemmas (`getD_addRow`, `diffRow_addRow`, `sup_addRow_addRow`, …) and the four cases on
shapes (`localRule_none`, `localRule_left`, `localRule_right`, `localRule_two`,
`localRule_bump`) are stated for the list shapes of `RMT.Growth`.
-/

namespace RMT.Growth

open Shape

/-! ## Shape lemmas -/

theorem getD_addRow : ∀ (l : Shape) (i j : ℕ), i ≤ l.length →
    (addRow l i).getD j 0 = if j = i then l.getD i 0 + 1 else l.getD j 0
  | [], i, j, h => by
    have : i = 0 := by simpa using h
    subst this; rcases j with _ | j <;> simp [addRow]
  | a :: xs, 0, j, _ => by rcases j with _ | j <;> simp [addRow]
  | a :: xs, i + 1, j, h => by
    rcases j with _ | j
    · simp [addRow]
    · simp only [addRow, List.getD_cons_succ]
      rw [getD_addRow xs i j (by simpa using h)]
      simp

theorem length_addRow : ∀ (l : Shape) (i : ℕ), i ≤ l.length →
    (addRow l i).length = if i = l.length then l.length + 1 else l.length
  | [], i, h => by have : i = 0 := by simpa using h
                   subst this; simp [addRow]
  | a :: xs, 0, _ => by simp [addRow]
  | a :: xs, i + 1, h => by
    simp only [addRow, List.length_cons]
    rw [length_addRow xs i (by simpa using h)]
    split_ifs <;> simp_all

/-- `diffRow` recovers the row where a box was added. -/
theorem diffRow_addRow : ∀ (l : Shape) (i : ℕ), i ≤ l.length → diffRow (addRow l i) l = i
  | [], i, h => by have : i = 0 := by simpa using h
                   subst this; simp [addRow, diffRow]
  | a :: xs, 0, _ => by simp [addRow, diffRow]
  | a :: xs, i + 1, h => by
    simp only [addRow, diffRow]
    rw [diffRow_addRow xs i (by simpa using h)]
    simp

theorem sup_self : ∀ l : Shape, Shape.sup l l = l
  | [] => rfl
  | a :: xs => by simp [Shape.sup, sup_self xs]

theorem sup_addRow_right : ∀ (l : Shape) (i : ℕ), Shape.sup l (addRow l i) = addRow l i
  | [], i => by simp [Shape.sup, addRow]
  | a :: xs, 0 => by simp [Shape.sup, addRow, sup_self]
  | a :: xs, i + 1 => by simp [Shape.sup, addRow, sup_addRow_right xs i]

theorem sup_addRow_left : ∀ (l : Shape) (i : ℕ), Shape.sup (addRow l i) l = addRow l i
  | [], i => by simp [Shape.sup, addRow]
  | a :: xs, 0 => by simp [Shape.sup, addRow, sup_self]
  | a :: xs, i + 1 => by simp [Shape.sup, addRow, sup_addRow_left xs i]

/-- **Boxes in two different rows**: the union of the two one-box extensions adds both boxes. -/
theorem sup_addRow_addRow : ∀ (l : Shape) (a b : ℕ), a ≠ b → a ≤ l.length → b ≤ l.length →
    Shape.sup (addRow l a) (addRow l b) = addRow (addRow l a) b
  | [], a, b, hab, ha, hb => by simp at ha hb; omega
  | c :: xs, 0, 0, hab, _, _ => absurd rfl hab
  | c :: xs, 0, b + 1, _, _, _ => by simp [Shape.sup, addRow, sup_addRow_right]
  | c :: xs, a + 1, 0, _, _, _ => by simp [Shape.sup, addRow, sup_addRow_left]
  | c :: xs, a + 1, b + 1, hab, ha, hb => by
    simp only [Shape.sup, addRow, max_self]
    rw [sup_addRow_addRow xs a b (by omega) (by simpa using ha) (by simpa using hb)]

theorem addRow_ne (l : Shape) {i : ℕ} (hi : i ≤ l.length) : addRow l i ≠ l := fun h => by
  have := congrArg (fun m : Shape => m.getD i 0) h
  rw [getD_addRow l i i hi, ite_eq_left rfl] at this; omega

/-! ## The four cases of the local rule -/

/-- Neither neighbour grew: add a box in row `0` iff the square holds a `1`. -/
theorem localRule_none (ρ : Shape) (x : Bool) :
    localRule ρ ρ ρ x = if x then addRow ρ 0 else ρ := by
  simp [localRule]

/-- Only one neighbour grew: the new shape is that neighbour. -/
theorem localRule_left (ρ : Shape) {b : ℕ} (hb : b ≤ ρ.length) (x : Bool) :
    localRule ρ ρ (addRow ρ b) x = addRow ρ b := by
  rw [localRule, ite_eq_left (Ne.symm (addRow_ne ρ hb)), sup_addRow_right]

theorem localRule_right (ρ : Shape) {a : ℕ} (ha : a ≤ ρ.length) (x : Bool) :
    localRule ρ (addRow ρ a) ρ x = addRow ρ a := by
  rw [localRule, ite_eq_left (addRow_ne ρ ha), sup_addRow_left]

/-- **Two different rows grew: both boxes are added.** -/
theorem localRule_two (ρ : Shape) {a b : ℕ} (hab : a ≠ b) (ha : a ≤ ρ.length) (hb : b ≤ ρ.length)
    (x : Bool) : localRule ρ (addRow ρ a) (addRow ρ b) x = addRow (addRow ρ a) b := by
  have hne : addRow ρ a ≠ addRow ρ b := fun h => hab (by
    rw [← diffRow_addRow ρ a ha, ← diffRow_addRow ρ b hb, h])
  rw [localRule, ite_eq_left hne, sup_addRow_addRow ρ a b hab ha hb]

/-- **The same row grew on both sides: the box is bumped to the next row.** -/
theorem localRule_bump (ρ : Shape) {a : ℕ} (ha : a ≤ ρ.length) (x : Bool) :
    localRule ρ (addRow ρ a) (addRow ρ a) x = addRow (addRow ρ a) (a + 1) := by
  rw [localRule, ite_eq_right (not_not.mpr rfl), ite_eq_right (addRow_ne ρ ha), diffRow_addRow ρ a ha]

/-! ## The Maya diagram of a list shape -/

/-- A list shape is a partition: its rows, padded by `0`, are weakly decreasing. -/
def IsPart (l : Shape) : Prop := Antitone fun j => l.getD j 0

/-- The site of the particle of row `j`: `l_j − j − 1`. -/
def pos (l : Shape) (j : ℕ) : ℤ := (l.getD j 0 : ℤ) - j - 1

/-- The Maya set of `l` with `N` particles (rows `0, …, N − 1`). -/
def mayaL (l : Shape) (N : ℕ) : Finset ℤ := (Finset.range N).image (pos l)

theorem pos_injective {l : Shape} (hl : IsPart l) : Function.Injective (pos l) := by
  intro i j h
  unfold pos at h
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := hl hij.le; simp only at this; omega
  · rfl
  · have := hl hij.le; simp only at this; omega

/-- A box can be added in row `i` (`i = 0`, or the row above is longer). -/
def Addable (l : Shape) (i : ℕ) : Prop := i ≤ l.length ∧ (i = 0 ∨ l.getD i 0 < l.getD (i - 1) 0)

theorem isPart_addRow {l : Shape} (hl : IsPart l) {i : ℕ} (hi : Addable l i) :
    IsPart (addRow l i) := by
  intro j k hjk
  simp only [getD_addRow l i _ hi.1]
  have h1 := hl hjk
  simp only at h1 ⊢
  split_ifs with h2 h3 h3
  · omega
  · subst h2
    have hjk' : j < k := lt_of_le_of_ne hjk h3
    rcases hi.2 with h | h
    · omega
    · have := hl (show j ≤ k - 1 by omega); simp only at this; omega
  · subst h3; omega
  · exact h1

open RMT.Symmetric.Corners in
/-- **Adding a box in row `i` is a hop of particle `i`.** -/
theorem mayaL_addRow {l : Shape} (hl : IsPart l) {i N : ℕ} (hi : i ≤ l.length) (hiN : i < N) :
    mayaL (addRow l i) N = hop (mayaL l N) (pos l i) (pos l i + 1) := by
  have hpos : ∀ j, pos (addRow l i) j = if j = i then pos l i + 1 else pos l j := fun j => by
    unfold pos; rw [getD_addRow l i j hi]; split_ifs with h
    · subst h; push_cast; ring
    · rfl
  ext y
  simp only [mayaL, hop, Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_erase,
    hpos]
  constructor
  · rintro ⟨j, hj, hy⟩
    split_ifs at hy with h
    · exact Or.inl hy.symm
    · exact Or.inr ⟨fun hx => h (pos_injective hl (hx ▸ hy)), j, hj, hy⟩
  · rintro (rfl | ⟨hx, j, hj, rfl⟩)
    · exact ⟨i, hiN, by simp⟩
    · refine ⟨j, hj, ?_⟩
      have hji : j ≠ i := fun h => hx (by rw [h])
      rw [ite_eq_right hji]

/-! ## Fomin's local rule as a hop rule -/

section Hops

open RMT.Symmetric.Corners

theorem pos_addRow_ne {l : Shape} {i j : ℕ} (hi : i ≤ l.length) (h : j ≠ i) :
    pos (addRow l i) j = pos l j := by
  unfold pos; rw [getD_addRow l i j hi, ite_eq_right h]

/-- **Two different rows grew: two different particles hop**, independently. -/
theorem localRule_two_maya {ρ : Shape} (hρ : IsPart ρ) {a b N : ℕ} (hab : a ≠ b)
    (ha : Addable ρ a) (hb : b ≤ ρ.length) (hN : ρ.length < N) (x : Bool) :
    mayaL (localRule ρ (addRow ρ a) (addRow ρ b) x) N =
      hop (hop (mayaL ρ N) (pos ρ a) (pos ρ a + 1)) (pos ρ b) (pos ρ b + 1) := by
  have hlen : b ≤ (addRow ρ a).length := by rw [length_addRow ρ a ha.1]; split_ifs <;> omega
  rw [localRule_two ρ hab ha.1 hb, mayaL_addRow (isPart_addRow hρ ha) hlen (by omega),
    mayaL_addRow hρ ha.1 (by have := ha.1; omega), pos_addRow_ne ha.1 (Ne.symm hab)]

/-- **The same row grew on both sides: the particle hops, and the hop passes to the next
particle down** (Schensted's bump: the box goes to row `a + 1`). -/
theorem localRule_bump_maya {ρ : Shape} (hρ : IsPart ρ) {a N : ℕ} (ha : Addable ρ a)
    (hN : ρ.length + 1 < N) (x : Bool) :
    mayaL (localRule ρ (addRow ρ a) (addRow ρ a) x) N =
      hop (hop (mayaL ρ N) (pos ρ a) (pos ρ a + 1)) (pos ρ (a + 1)) (pos ρ (a + 1) + 1) := by
  have hlen : a + 1 ≤ (addRow ρ a).length := by
    rw [length_addRow ρ a ha.1]; have := ha.1; split_ifs <;> omega
  rw [localRule_bump ρ ha.1, mayaL_addRow (isPart_addRow hρ ha) hlen (by have := ha.1; omega),
    mayaL_addRow hρ ha.1 (by have := ha.1; omega), pos_addRow_ne ha.1 (by omega)]

/-- **Only one side grew: that particle hops.** -/
theorem localRule_left_maya {ρ : Shape} (hρ : IsPart ρ) {b N : ℕ} (hb : b ≤ ρ.length)
    (hN : ρ.length < N) (x : Bool) :
    mayaL (localRule ρ ρ (addRow ρ b) x) N = hop (mayaL ρ N) (pos ρ b) (pos ρ b + 1) := by
  rw [localRule_left ρ hb, mayaL_addRow hρ hb (by omega)]

/-- **Neither side grew: the first particle hops iff the square holds a `1`.** -/
theorem localRule_none_maya {ρ : Shape} (hρ : IsPart ρ) {N : ℕ} (hN : 0 < N) (x : Bool) :
    mayaL (localRule ρ ρ ρ x) N =
      if x then hop (mayaL ρ N) (pos ρ 0) (pos ρ 0 + 1) else mayaL ρ N := by
  rw [localRule_none]; split_ifs
  · exact mayaL_addRow hρ (Nat.zero_le _) hN
  · rfl

/-- **The bumped particle can always hop**: after particle `a` hops, row `a + 1` is addable
(on the Maya line, the site right of particle `a + 1` is empty). -/
theorem addable_bump {ρ : Shape} (hρ : IsPart ρ) {a : ℕ} (ha : Addable ρ a) :
    Addable (addRow ρ a) (a + 1) := by
  refine ⟨by rw [length_addRow ρ a ha.1]; have := ha.1; split_ifs <;> omega, Or.inr ?_⟩
  rw [getD_addRow ρ a _ ha.1, getD_addRow ρ a _ ha.1, ite_eq_right (by omega),
    show a + 1 - 1 = a by omega, ite_eq_left rfl]
  have := hρ (show a ≤ a + 1 by omega); simp only at this; omega

end Hops

end RMT.Growth

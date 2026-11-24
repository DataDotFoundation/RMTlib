import RMTlib.RSK.GrowthGeneric

/-!
# Growth diagrams one row at a time, by structural recursion

`RMT.RSK.GrowthGeneric.grow` and `back` define a growth diagram by a well-founded recursion
on the grid, with three recursive calls per square. This file keeps the algorithm and the local
rule fixed and changes only the recursion: the grid is computed one row at a time, and every
definition is structural. The aim is to see which costs belong to the grid recursion.

* Forward. `nextRow F z σ i` turns row `i` (a list of `m + 1` shapes) into row `i + 1` by one
  sweep left to right (`scanRow`, structural on the list). `rows F z σ m i` iterates it,
  structural on `i`. `rowsRev` keeps all rows, and `edges` reads off the top row and the right
  column.
* Backward. `prevRow B i r` turns row `i + 1` into row `i` by one sweep right to left
  (`scanBack`, a right fold, structural on the list; `r = λ(i, m)` comes from the right edge).
  `backRows` iterates it from the top edge, structural on the number of steps. `backEntries`
  reads the entries of the squares off consecutive pairs of rows.
* Fomin's rule. `rskRows` and `unrskRows` are `RMT.RSK.Growth.rskGrowth` and `unrskGrowth`
  with the grid computed by rows. `unrskEdges` is the inverse proper: it uses only the two edges.

`RMT.Growth.row` (in `RMTlib.Growth.RSK`) is an earlier structural row-by-row growth diagram,
with the same outer recursion on `i` and an inner sweep like `scanRow`. It uses unpadded shapes
and its own local rule, and nothing there is proved about invertibility. Here the shapes are the
padded `Part`s of `RMT.RSK.Growth`, the rule is a parameter, and the rows are tied to `grow` and
`back` by proof. For Fomin's rule `rows` plays the role of `RMT.Growth.row`; the two are not
compared formally.

## The recursion scheme and what it costs

What changed against `RMT.RSK.Growth`:

* No definition needs a termination proof: all are structural recursions (on a list or a
  `Nat`). The one `termination_by` left is in the proof `back_eq`, which relates two existing
  well-founded definitions.
* The kernel evaluates them. Permutations of size 4, 5, 7 and 10 go through `rskRows` and
  back by `decide` below, each in well under a second. For `unrskGrowth`, `decide` fails already
  at size 4, because the kernel does not unfold the well-founded `grow` and `back`.
* Polynomial time. Each square is computed once: `(n+1)²` applications of the local rule each
  way, each `O(n)` on shapes of length `n + 1`. `grow` and `back` recompute shared
  subproblems, so their cost grows exponentially; compiled `#eval` of `unrskGrowth` on a
  permutation of size 6 did not finish within a minute.

What it cost:

* The correspondence theorems, which `Growth` does not need: `rows_eq` and `backRows_eq` say
  that the lists computed are `(List.range' 0 (m+1)).map (grow … i)` and the same for `back`.
  Each is a nested induction: an inner one along the row (`scanRow_eq`, `scanBack_eq`,
  `scanEntries_eq`), with the sweep stated for every suffix `List.range' (j+1) k`, inside an
  outer one on the row index. The work is index bookkeeping: `range'` splitting, list heads,
  `n - (k+1) = i`, and `getD` against `getElem?`.
* The backward sweep must run right to left, so it is a right fold whose step needs the head
  of the recursive result (`headD`), and the right-edge shape is threaded in as the base case.
  The entries are a third pass (`scanEntries`, `entryRows`) over pairs of consecutive rows.
* Invertibility is transferred, not reproved. `backRows_rows` and `backEntries_grow` rewrite
  with `backRows_eq` / `backEntries_eq` and apply `GrowthGeneric.back_grow` /
  `backEntry_grow`. A native row-by-row proof would be the same nested induction as
  `backRows_eq`, with the local inverse used at each step in place of the defining equation of
  `back`; since the correspondence is needed anyway, it would repeat work. The local theorem
  `bwd_fwd` and the invariants `square_ok` are still proved by the well-founded recursion of
  `Growth`: rows change how the grid is computed, not how its squares are checked.
* For Fomin's rule, the equalities with `rskGrowth` and `unrskGrowth` hold for every list, and
  `unrskRows_rskRows` follows from `unrskGrowth_rskGrowth`. The second needs `back_eq`:
  `RMT.RSK.Growth.back` is the generic `back` for `bwd` (one more well-founded induction), and
  `chainTab_congr`, `firstTrue_map` to match the readouts.

## Main results

* `rows_eq`, `rows_getElem?`: row `i` from `rows` is `[grow F z σ i 0, …, grow F z σ i m]`.
* `edges_top_getD`, `edges_right_getD`: `edges` returns the top row and the right column.
* `backRows_eq`, `backEntries_eq`: the backward rows are those of `back`, the entries those of
  `backEntry`.
* `backRows_rows`, `backEntries_grow`: if `B` undoes `F` on every square, the backward rows
  rebuild the forward rows and every entry from the two edges (transferred from
  `GrowthGeneric`).
* `rskRows_eq`, `unrskRows_eq`: `rskRows = rskGrowth` and `unrskRows = unrskGrowth`.
* `unrskRows_rskRows`: inverse RSK by rows recovers every permutation of `{0, …, n-1}`.

Mathlib-free.
-/

namespace RMT.RSK.GrowthRows

open RMT.RSK.GrowthGeneric (grow back backEntry grow_zero_left grow_zero_right grow_succ
  LocallyInvertible back_grow backEntry_grow back_congr)

universe u v

variable {S : Type u} {E : Type v}

/-! ## The forward grid, row by row -/

/-- One sweep along a row of squares, left to right. `scanRow F σ i j left a rest` returns the
shapes at `(i+1, j+1), …` of row `i+1`. Here `left` is the shape at `(i+1, j)`, `a` the shape at
`(i, j)` and `rest` the shapes at `(i, j+1), …` of row `i`. Structural on `rest`. -/
def scanRow (F : Nat → Nat → S → S → S → E → S) (σ : Nat → Nat → E) (i : Nat) :
    Nat → S → S → List S → List S
  | _, _, _, [] => []
  | j, left, a, b :: rest =>
    let c := F i j a left b (σ i j)
    c :: scanRow F σ i (j + 1) c b rest

/-- Row `i+1` of the grid from row `i`: the boundary shape `z`, then one sweep. -/
def nextRow (F : Nat → Nat → S → S → S → E → S) (z : S) (σ : Nat → Nat → E) (i : Nat) :
    List S → List S
  | [] => []
  | a :: rest => z :: scanRow F σ i 0 z a rest

/-- Row `i` of the forward grid, columns `0, …, m`, by structural recursion on `i`. -/
def rows (F : Nat → Nat → S → S → S → E → S) (z : S) (σ : Nat → Nat → E) (m : Nat) :
    Nat → List S
  | 0 => List.replicate (m + 1) z
  | i + 1 => nextRow F z σ i (rows F z σ m i)

/-- Rows `i, i-1, …, 0` of the forward grid, newest first. Each row is computed once. -/
def rowsRev (F : Nat → Nat → S → S → S → E → S) (z : S) (σ : Nat → Nat → E) (m : Nat) :
    Nat → List (List S)
  | 0 => [List.replicate (m + 1) z]
  | i + 1 =>
    let rs := rowsRev F z σ m i
    nextRow F z σ i (rs.headD []) :: rs

/-- The two outer edges of the `n × m` grid: the top row `λ(n, 0..m)` and the right column
`λ(0..n, m)`, from one pass over the rows. -/
def edges (F : Nat → Nat → S → S → S → E → S) (z : S) (σ : Nat → Nat → E) (n m : Nat) :
    List S × List S :=
  let rs := rowsRev F z σ m n
  (rs.headD [], rs.reverse.map fun r => r.getD m z)

section Forward

variable (F : Nat → Nat → S → S → S → E → S) (z : S) (σ : Nat → Nat → E)

theorem scanRow_eq (i : Nat) : ∀ k j,
    scanRow F σ i j (grow F z σ (i + 1) j) (grow F z σ i j)
        ((List.range' (j + 1) k).map (grow F z σ i))
      = (List.range' (j + 1) k).map (grow F z σ (i + 1))
  | 0, j => by simp [scanRow]
  | k + 1, j => by
    simp only [List.range'_succ, List.map_cons, scanRow, ← grow_succ]
    rw [scanRow_eq i k (j + 1)]

/-- **Correspondence.** Row `i` computed by `rows` is the list of `grow F z σ i j`, `j ≤ m`. -/
theorem rows_eq (m : Nat) : ∀ i, rows F z σ m i = (List.range' 0 (m + 1)).map (grow F z σ i)
  | 0 => by
    have h : grow F z σ 0 = fun _ => z := funext (grow_zero_left F z σ)
    rw [rows, h, List.map_const', List.length_range']
  | i + 1 => by
    have h := scanRow_eq F z σ i m 0
    rw [grow_zero_right, grow_zero_right] at h
    rw [rows, rows_eq m i, List.range'_succ, List.map_cons, List.map_cons, nextRow,
      grow_zero_right, grow_zero_right, h]

theorem length_rows (m i : Nat) : (rows F z σ m i).length = m + 1 := by
  simp [rows_eq]

/-- **Correspondence**, entrywise. -/
theorem rows_getElem? (m i j : Nat) (hj : j ≤ m) :
    (rows F z σ m i)[j]? = some (grow F z σ i j) := by
  rw [rows_eq, List.getElem?_map, List.getElem?_range']
  · simp
  · omega

theorem rows_getD (m i j : Nat) (hj : j ≤ m) (d : S) :
    (rows F z σ m i).getD j d = grow F z σ i j := by
  simp [List.getD_eq_getElem?_getD, rows_getElem? F z σ m i j hj]

theorem rowsRev_eq (m : Nat) : ∀ i,
    rowsRev F z σ m i = ((List.range (i + 1)).reverse).map (rows F z σ m)
  | 0 => by simp [rowsRev, rows]
  | i + 1 => by
    rw [rowsRev, rowsRev_eq m i, List.range_succ (n := i + 1)]
    simp [rows, List.range_succ]

theorem edges_top_getD (n m j : Nat) (hj : j ≤ m) :
    (edges F z σ n m).1.getD j z = grow F z σ n j := by
  simp only [edges, rowsRev_eq, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, List.map_cons, List.headD_cons]
  exact rows_getD F z σ m n j hj z

theorem edges_right_getD (n m i : Nat) (hi : i ≤ n) :
    (edges F z σ n m).2.getD i z = grow F z σ i m := by
  simp only [edges, rowsRev_eq, List.map_reverse, List.reverse_reverse, List.map_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some]
  exact rows_getD F z σ m i m (Nat.le_refl m) z

end Forward

/-! ## The backward grid, row by row from the top -/

/-- One sweep along a row of squares, right to left. `scanBack B i r j a rest` returns the
shapes at `(i, j), …, (i, m)` of row `i`. Here `a` is the shape at `(i+1, j)`, `rest` the
shapes at `(i+1, j+1), …, (i+1, m)` and `r` the shape at `(i, m)` (the right edge). The
recursive call comes first: the sweep is a right fold. Structural on `rest`. -/
def scanBack (B : Nat → Nat → S → S → S → S × E) (i : Nat) (r : S) :
    Nat → S → List S → List S
  | _, _, [] => [r]
  | j, a, b :: rest =>
    let t := scanBack B i r (j + 1) b rest
    (B i j a (t.headD r) b).1 :: t

/-- Row `i` of the backward grid from row `i+1` and the right-edge shape `r = λ(i, m)`. -/
def prevRow (B : Nat → Nat → S → S → S → S × E) (i : Nat) (r : S) : List S → List S
  | [] => []
  | a :: rest => scanBack B i r 0 a rest

/-- Rows `n-k, …, n` of the backward grid of an `n × m` rectangle, by structural recursion on
`k`. Row `n` is the top edge; each step prepends the row below. -/
def backRows (B : Nat → Nat → S → S → S → S × E) (top right : Nat → S) (n m : Nat) :
    Nat → List (List S)
  | 0 => [(List.range' 0 (m + 1)).map top]
  | k + 1 =>
    let rs := backRows B top right n m k
    prevRow B (n - (k + 1)) (right (n - (k + 1))) (rs.headD []) :: rs

/-- The entries of squares `(i, j), (i, j+1), …` from two consecutive rows. `a` is the shape at
`(i+1, j)`, `as` the shapes at `(i+1, j+1), …` and `cs` those at `(i, j+1), …`. -/
def scanEntries (B : Nat → Nat → S → S → S → S × E) (i : Nat) :
    Nat → S → List S → List S → List E
  | j, a, b :: as, c :: cs => (B i j a c b).2 :: scanEntries B i (j + 1) b as cs
  | _, _, _, _ => []

/-- The entries of row `i` of squares, from row `i+1` (`above`) and row `i` (`cur`). -/
def rowEntries (B : Nat → Nat → S → S → S → S × E) (i : Nat) (above cur : List S) : List E :=
  match above, cur with
  | a :: as, _ :: cs => scanEntries B i 0 a as cs
  | _, _ => []

/-- The entries of rows of squares `i, i+1, …` from the list of rows `cur, above, …`. -/
def entryRows (B : Nat → Nat → S → S → S → S × E) : Nat → List S → List (List S) → List (List E)
  | _, _, [] => []
  | i, cur, above :: rest => rowEntries B i above cur :: entryRows B (i + 1) above rest

/-- All entries of the `n × m` rectangle recovered from the top and right edges, as a list of
rows of squares `0, …, n-1`, each of length `m`. -/
def backEntries (B : Nat → Nat → S → S → S → S × E) (top right : Nat → S) (n m : Nat) :
    List (List E) :=
  match backRows B top right n m n with
  | cur :: rest => entryRows B 0 cur rest
  | [] => []

section Backward

variable (B : Nat → Nat → S → S → S → S × E) (top right : Nat → S) (n m : Nat)

theorem back_top (i j : Nat) (h : n ≤ i) : back B top right n m i j = top j := by
  rw [back]; simp [h]

theorem back_right (i j : Nat) (hi : i < n) (hj : m ≤ j) : back B top right n m i j = right i := by
  rw [back]; simp [show ¬ n ≤ i by omega, hj]

theorem back_step (i j : Nat) (hi : i < n) (hj : j < m) : back B top right n m i j
    = (B i j (back B top right n m (i + 1) j) (back B top right n m i (j + 1))
        (back B top right n m (i + 1) (j + 1))).1 := by
  rw [back]; simp [show ¬ n ≤ i by omega, show ¬ m ≤ j by omega]

theorem scanBack_eq (i : Nat) (hi : i < n) : ∀ k j, j + k = m →
    scanBack B i (right i) j (back B top right n m (i + 1) j)
        ((List.range' (j + 1) k).map (back B top right n m (i + 1)))
      = (List.range' j (k + 1)).map (back B top right n m i)
  | 0, j, h => by simp [scanBack, back_right B top right n m i j hi (by omega)]
  | k + 1, j, h => by
    simp only [List.range'_succ, List.map_cons, scanBack]
    have ih := scanBack_eq i hi k (j + 1) (by omega)
    simp only [List.range'_succ, List.map_cons] at ih
    rw [ih, List.headD_cons, ← back_step B top right n m i j hi (by omega)]

theorem prevRow_eq (i : Nat) (hi : i < n) :
    prevRow B i (right i) ((List.range' 0 (m + 1)).map (back B top right n m (i + 1)))
      = (List.range' 0 (m + 1)).map (back B top right n m i) := by
  have h := scanBack_eq B top right n m i hi m 0 (by omega)
  rw [List.range'_succ, List.map_cons, prevRow, h]
  rfl

/-- **Correspondence** for the backward grid: `backRows k` lists rows `i, …, n` of `back`,
for `i + k = n`. -/
theorem backRows_eq : ∀ k i, i + k = n → backRows B top right n m k
    = (List.range' i (k + 1)).map fun i => (List.range' 0 (m + 1)).map (back B top right n m i)
  | 0, i, h => by
    have hb : back B top right n m i = top := funext fun j => back_top B top right n m i j (by omega)
    rw [backRows, List.range'_succ (n := 0), List.range'_zero, List.map_cons, List.map_nil, hb]
  | k + 1, i, h => by
    rw [backRows, backRows_eq k (i + 1) (by omega), List.range'_succ (s := i),
      List.range'_succ (s := i + 1)]
    simp only [List.map_cons, List.headD_cons, show n - (k + 1) = i by omega]
    rw [prevRow_eq B top right n m i (by omega)]

theorem scanEntries_eq (i : Nat) : ∀ k j,
    scanEntries B i j (back B top right n m (i + 1) j)
        ((List.range' (j + 1) k).map (back B top right n m (i + 1)))
        ((List.range' (j + 1) k).map (back B top right n m i))
      = (List.range' j k).map (backEntry B top right n m i)
  | 0, j => by simp [scanEntries]
  | k + 1, j => by
    simp only [List.range'_succ, List.map_cons, scanEntries]
    rw [scanEntries_eq i k (j + 1)]
    rfl

theorem rowEntries_eq (i : Nat) :
    rowEntries B i ((List.range' 0 (m + 1)).map (back B top right n m (i + 1)))
        ((List.range' 0 (m + 1)).map (back B top right n m i))
      = (List.range' 0 m).map (backEntry B top right n m i) := by
  simp only [List.range'_succ, List.map_cons, rowEntries]
  exact scanEntries_eq B top right n m i m 0

theorem entryRows_eq : ∀ k i,
    entryRows B i ((List.range' 0 (m + 1)).map (back B top right n m i))
        ((List.range' (i + 1) k).map fun i =>
          (List.range' 0 (m + 1)).map (back B top right n m i))
      = (List.range' i k).map fun i => (List.range' 0 m).map (backEntry B top right n m i)
  | 0, i => by simp [entryRows]
  | k + 1, i => by
    simp only [List.range'_succ, List.map_cons, entryRows]
    have ih := entryRows_eq k (i + 1)
    have hr := rowEntries_eq B top right n m i
    simp only [List.range'_succ, List.map_cons] at ih hr
    rw [ih, hr]

/-- **Correspondence**: `backEntries` lists `backEntry B top right n m i j` for `i < n`,
`j < m`. -/
theorem backEntries_eq : backEntries B top right n m
    = (List.range' 0 n).map fun i => (List.range' 0 m).map (backEntry B top right n m i) := by
  unfold backEntries
  rw [backRows_eq B top right n m n 0 (by omega), List.range'_succ (n := n), List.map_cons]
  exact entryRows_eq B top right n m n 0

end Backward

/-! ## Invertibility, transferred from `GrowthGeneric` -/

section Inverse

variable (F : Nat → Nat → S → S → S → E → S) (B : Nat → Nat → S → S → S → S × E)
  (z : S) (σ : Nat → Nat → E)

/-- **The backward rows rebuild the forward rows** from the two outer edges. -/
theorem backRows_rows (n m : Nat) (h : LocallyInvertible F B z σ n m) :
    backRows B (fun j => grow F z σ n j) (fun i => grow F z σ i m) n m n
      = (List.range' 0 (n + 1)).map (rows F z σ m) := by
  rw [backRows_eq _ _ _ n m n 0 (by omega)]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range'_1] at hi
  rw [rows_eq]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range'_1] at hj
  exact back_grow F B z σ n m h i j (by omega) (by omega)

/-- **The backward rows recover every entry**, from edges that agree with the forward grid on
the rectangle (for example the lists computed by `edges`). -/
theorem backEntries_grow (n m : Nat) (h : LocallyInvertible F B z σ n m) (top right : Nat → S)
    (ht : ∀ j, j ≤ m → top j = grow F z σ n j) (hr : ∀ i, i ≤ n → right i = grow F z σ i m) :
    backEntries B top right n m = (List.range' 0 n).map fun i => (List.range' 0 m).map (σ i) := by
  rw [backEntries_eq]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range'_1] at hi
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range'_1] at hj
  have hb := back_congr B n m top right (fun j => grow F z σ n j) (fun i => grow F z σ i m) ht hr
  unfold backEntry
  rw [hb (i + 1) j (by omega) (by omega), hb i (j + 1) (by omega) (by omega),
    hb (i + 1) (j + 1) (by omega) (by omega)]
  exact backEntry_grow F B z σ n m h i j (by omega) (by omega)

end Inverse

/-! ## Fomin's rule: RSK of a permutation -/

open RMT.RSK.Growth (Part zeros fwd bwd perm chainTab rskGrowth unrskGrowth)

/-- `RMT.RSK.Growth.back` is the generic backward grid for Fomin's backward rule. -/
theorem back_eq (top right : Nat → Part) (n : Nat) : ∀ i j,
    RMT.RSK.Growth.back top right n i j = back (fun _ _ => bwd) top right n n i j
  | i, j => by
    rw [RMT.RSK.Growth.back.eq_def, GrowthGeneric.back.eq_def]
    by_cases h1 : n ≤ i
    · simp [h1]
    · by_cases h2 : n ≤ j
      · simp [h1, h2]
      · simp only [h1, h2, if_false]
        rw [back_eq top right n (i + 1) j, back_eq top right n i (j + 1),
          back_eq top right n (i + 1) (j + 1)]
termination_by i j => (n - i, n - j)

theorem backEntry_eq (top right : Nat → Part) (n i j : Nat) :
    RMT.RSK.Growth.backEntry top right n i j = backEntry (fun _ _ => bwd) top right n n i j := by
  unfold RMT.RSK.Growth.backEntry backEntry
  rw [back_eq, back_eq, back_eq]

/-- The index of the first `true` in a list of booleans, counting from `j`; `d` if none. -/
def firstTrue (d : Nat) : Nat → List Bool → Nat
  | _, [] => d
  | j, b :: bs => if b then j else firstTrue d (j + 1) bs

theorem firstTrue_map (p : Nat → Bool) : ∀ k s,
    firstTrue 0 s ((List.range' s k).map p) = ((List.range' s k).find? p).getD 0
  | 0, s => by simp [firstTrue]
  | k + 1, s => by
    simp only [List.range'_succ, List.map_cons, firstTrue, List.find?_cons]
    cases p s <;> simp [firstTrue_map p k (s + 1)]

theorem chainTab_congr (s s' : Nat → Part) (n : Nat) (h : ∀ k, k ≤ n → s k = s' k) :
    chainTab s n = chainTab s' n := by
  unfold chainTab
  suffices ∀ (l : List Nat) t, (∀ k ∈ l, k < n) →
      l.foldl (fun t k => RMT.RSK.Growth.addAt (RMT.RSK.Growth.firstDiff (s (k + 1)) (s k)) k t) t
        = l.foldl (fun t k =>
            RMT.RSK.Growth.addAt (RMT.RSK.Growth.firstDiff (s' (k + 1)) (s' k)) k t) t from
    this _ _ (fun k hk => List.mem_range.mp hk)
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons k l ih =>
    intro t hl
    have hk := hl k (by simp)
    simp only [List.foldl_cons]
    rw [h k (by omega), h (k + 1) (by omega)]
    exact ih _ (fun k' hk' => hl k' (by simp [hk']))

/-- The two outer edges of the growth diagram of a permutation, computed row by row. -/
def permEdges (π : List Nat) : List Part × List Part :=
  edges (fun _ _ => fwd) (zeros (π.length + 1)) (perm π) π.length π.length

/-- **RSK by growth diagram, row by row**: `(P, Q)` read off the two outer edges. -/
def rskRows (π : List Nat) : List (List Nat) × List (List Nat) :=
  let n := π.length
  let e := permEdges π
  (chainTab (fun j => e.1.getD j (zeros (n + 1))) n,
    chainTab (fun i => e.2.getD i (zeros (n + 1))) n)

/-- **Inverse RSK from the two outer edges**, row by row from the top: `top` is `λ(n, 0..n)`,
`right` is `λ(0..n, n)`. Row `i` of the output is the column of the `1` in row `i` of the
recovered matrix. -/
def unrskEdges (n : Nat) (top right : List Part) : List Nat :=
  (backEntries (fun _ _ => bwd) (fun j => top.getD j (zeros (n + 1)))
      (fun i => right.getD i (zeros (n + 1))) n n).map (firstTrue 0 0)

/-- Inverse RSK of the edges of `π`, the row-by-row counterpart of `unrskGrowth`. -/
def unrskRows (π : List Nat) : List Nat :=
  unrskEdges π.length (permEdges π).1 (permEdges π).2

theorem permEdges_top (π : List Nat) (j : Nat) (hj : j ≤ π.length) :
    (permEdges π).1.getD j (zeros (π.length + 1))
      = RMT.RSK.Growth.grow (perm π) (π.length + 1) π.length j := by
  rw [GrowthGeneric.Growth.grow_eq]
  exact edges_top_getD _ _ _ _ _ _ hj

theorem permEdges_right (π : List Nat) (i : Nat) (hi : i ≤ π.length) :
    (permEdges π).2.getD i (zeros (π.length + 1))
      = RMT.RSK.Growth.grow (perm π) (π.length + 1) i π.length := by
  rw [GrowthGeneric.Growth.grow_eq]
  exact edges_right_getD _ _ _ _ _ _ hi

/-- **Same output as `rskGrowth`**, on every list. -/
theorem rskRows_eq (π : List Nat) : rskRows π = rskGrowth π := by
  unfold rskRows rskGrowth
  simp only
  rw [chainTab_congr _ _ _ (fun j hj => permEdges_top π j hj),
    chainTab_congr _ _ _ (fun i hi => permEdges_right π i hi)]

/-- **Same output as `unrskGrowth`**, on every list. -/
theorem unrskRows_eq (π : List Nat) : unrskRows π = unrskGrowth π := by
  unfold unrskRows unrskEdges unrskGrowth
  simp only [backEntries_eq, List.map_map, List.range_eq_range']
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range'_1] at hi
  simp only [Function.comp, firstTrue_map]
  congr 1
  apply RMT.RSK.Growth.find?_congr
  intro j hj
  rw [List.mem_range'_1] at hj
  rw [backEntry_eq]
  unfold backEntry
  have hb := back_congr (fun _ _ => bwd) π.length π.length _ _ _ _
    (fun j hj => permEdges_top π j hj) (fun i hi => permEdges_right π i hi)
  rw [hb (i + 1) j (by omega) (by omega), hb i (j + 1) (by omega) (by omega),
    hb (i + 1) (j + 1) (by omega) (by omega)]

/-- **Inverse RSK, row by row, recovers every permutation** of `{0, …, n-1}`. Transferred from
`RMT.RSK.Growth.unrskGrowth_rskGrowth`. -/
theorem unrskRows_rskRows (π : List Nat) (hnd : π.Nodup) (hlt : ∀ x ∈ π, x < π.length) :
    unrskRows π = π := by
  rw [unrskRows_eq]
  exact RMT.RSK.Growth.unrskGrowth_rskGrowth π hnd hlt

/-! ## Kernel evaluation

The kernel reduces every definition above, so `decide` checks these. The same statements about
`rskGrowth` and `unrskGrowth` fail with `decide` (the instance does not reduce), and are only
`#guard`ed in `RMTlibExamples/RSK.lean`. -/

example : rskRows [2, 0, 3, 1] = ([[0, 1], [2, 3]], [[0, 2], [1, 3]]) := by decide
example : unrskRows [2, 0, 3, 1] = [2, 0, 3, 1] := by decide
example : rskRows [4, 2, 0, 3, 1] = ([[0, 1], [2, 3], [4]], [[0, 3], [1, 4], [2]]) := by decide
example : unrskRows [4, 2, 0, 3, 1] = [4, 2, 0, 3, 1] := by decide
example : unrskRows [3, 5, 0, 6, 2, 4, 1] = [3, 5, 0, 6, 2, 4, 1] := by decide
example : unrskRows [7, 3, 9, 0, 5, 1, 8, 2, 6, 4] = [7, 3, 9, 0, 5, 1, 8, 2, 6, 4] := by decide

end RMT.RSK.GrowthRows

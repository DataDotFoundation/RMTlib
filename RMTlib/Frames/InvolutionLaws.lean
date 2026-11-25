import Lean

/-!
# Involution laws by statement shape (`#involution_laws`)

Which theorems of a library are **laws of an involution** `ι`, i.e. say how a family of
statistics changes when its argument is replaced by `ι μ`, whether or not anyone recorded them?
For `ι = ω` (transposition of shapes) this is the ω-twin finder of `docs/omega-twin-finder.md`
(RMTlib#4). The command reads the elaborated statements, so it finds laws whatever they are called.

This file imports only `Lean` (no Mathlib, no RMTlib), so that it can move to MeaningLib as a rule
kind of its own. RMTlib's instance (`RMT.Frames.omegaSpec`) is in `RMTlib.Frames.Omega`.

## Shapes

For each theorem, after the `∀`-telescope, the conclusion is classified. `μ` is a bound variable,
and `μ′` an application `ι … μ` of one of the spec's involutions to it.

| shape | conclusion | twin | out |
|---|---|---|---|
| `id` | `F a μ′ = F b μ` | `a ↦ b` | `id` |
| `¬` | `P a μ′ ↔ ¬ P b μ` | `a ↦ b` | `Not` |
| `out g` | `F a μ′ = g (F b μ)`, `g` free of `μ` | `a ↦ b` | `g` |
| `out(μ)` | `F a μ′ = g μ (F b μ)` (e.g. `c μ * ·`) | `a ↦ b` | `g μ` |
| `invariant` | `F a μ′ = F a μ` | none | `id` |
| `preserved` | `P μ → P μ′` (a hypothesis is the conclusion at `μ`) | none | — |
| `operator` | no shape involution, an operator involution occurs | — | — |
| `other involution` | only an involution that is not ω occurs (e.g. `Matrix.transpose`) | — | — |
| `unknown` | a shape involution occurs in no shape above | — | — |

The two sides may be written either way round. Each row also names the **recording instances**:
definitions whose type is an application of the spec's recording structure and whose value names
the theorem directly. A law with no recording instance is on the to-do list.

Rules are syntactic, the output is deterministic, and nothing is judged true or false: the
command only reads what is proved.
-/

open Lean Meta Elab Command

namespace RMT.Frames.Involution

/-- What to look for. -/
structure Spec where
  /-- Name of the involution, for the report. -/
  name : String
  /-- Involutions of shapes; their last explicit argument is the shape (e.g.
  `YoungDiagram.transpose`). -/
  shapes : List Name
  /-- Involutions of a space of functions or operators (e.g. `ω` on `Λ`): a theorem mentioning one
  is an operator law. -/
  operators : List Name := []
  /-- Other involutions, reported but never as laws (e.g. `Matrix.transpose`). -/
  others : List Name := []
  /-- The structure whose instances record laws (e.g. `RMT.Symmetric.OmegaCovariant`). -/
  recorder : Option Name := none
  /-- Substrings of theorem names counted as name hits (lower case). -/
  nameHints : List String := []
  deriving Repr, Inhabited

/-- The kinds of row. -/
inductive Shape
  /-- `F a μ′ = F b μ`. -/
  | idOut
  /-- `P a μ′ ↔ ¬ P b μ`. -/
  | notOut
  /-- `F a μ′ = g (F b μ)`, `g` free of `μ`. -/
  | outG
  /-- `F a μ′ = g μ (F b μ)`. -/
  | outMu
  /-- `F a μ′ = F a μ`. -/
  | invariant
  /-- `P μ → P μ′`. -/
  | preserved
  /-- `ι (ι μ) = μ`: the involution itself. -/
  | involutive
  /-- An operator involution occurs, and no shape involution. -/
  | operator
  /-- Only an involution that is not the spec's occurs. -/
  | other
  /-- A shape involution occurs in no recognised shape. -/
  | unknown
  deriving BEq, Repr, Inhabited

/-- Short label of a shape. -/
def Shape.label : Shape → String
  | .idOut => "id" | .notOut => "¬" | .outG => "out g" | .outMu => "out(μ)"
  | .invariant => "invariant" | .preserved => "preserved" | .involutive => "involutive"
  | .operator => "operator"
  | .other => "other involution" | .unknown => "unknown"

/-- Is the shape a law of the shape involution? -/
def Shape.isLaw : Shape → Bool
  | .idOut | .notOut | .outG | .outMu | .invariant | .preserved => true
  | _ => false

/-- All shapes, in report order. -/
def Shape.all : List Shape :=
  [.idOut, .notOut, .outG, .outMu, .invariant, .preserved, .involutive, .operator, .other,
    .unknown]

/-- One row of the report. -/
structure Row where
  /-- The theorem. -/
  decl : Name
  /-- Its module. -/
  module : Name
  /-- Its shape. -/
  shape : Shape
  /-- The parameter map, as printed. -/
  twin : MessageData := .nil
  /-- The value correction, as printed. -/
  correction : MessageData := .nil
  /-- Recording instances that name the theorem. -/
  instances : Array Name := #[]
  /-- Whether the theorem's name contains one of the hints. -/
  nameHit : Bool := false

/-- Does `e` mention a constant from `cs`? -/
def mentionsAny (cs : List Name) (e : Expr) : Bool :=
  (e.find? fun s => match s with | .const n _ => cs.contains n | _ => false).isSome

/-- The first subterm `ι … μ` with `ι` one of `shapes` and `μ` a free variable. Only whole
application spines are matched: in `ι K (ι N λ)`, the partial application `ι K` is not a shape. -/
partial def findShapeApp? (shapes : List Name) (e : Expr) : Option (Expr × Expr) :=
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let here := match f with
      | .const n _ => shapes.contains n && args.back!.isFVar
      | _ => false
    if here then some (e, args.back!)
    else (args.findSome? (findShapeApp? shapes)).orElse fun _ =>
      if f.isConst then none else findShapeApp? shapes f
  | .lam _ t b _ | .forallE _ t b _ =>
    (findShapeApp? shapes t).orElse fun _ => findShapeApp? shapes b
  | .letE _ t v b _ =>
    ((findShapeApp? shapes t).orElse fun _ => findShapeApp? shapes v).orElse fun _ =>
      findShapeApp? shapes b
  | .mdata _ b | .proj _ _ b => findShapeApp? shapes b
  | _ => none

/-- Same family at the shape `μ`: the same head (a constant or a bound variable), the same number
of arguments, and `μ` itself among the arguments of both. -/
def sameFamily (μ x y : Expr) : Bool :=
  (x.getAppFn.isConst || x.getAppFn.isFVar) && x.getAppFn == y.getAppFn &&
    x.getAppNumArgs == y.getAppNumArgs && x.getAppArgs.contains μ && y.getAppArgs.contains μ

/-- The parameter map between two applications of the same family: the argument pairs that
differ, printed `a ↦ b`. -/
def twinOf (x y : Expr) : MessageData := Id.run do
  let pairs := (x.getAppArgs.zip y.getAppArgs).filter fun (a, b) => a != b
  if pairs.isEmpty then return m!"none"
  return MessageData.joinSep (pairs.toList.map fun (a, b) => m!"{a} ↦ {b}") m!", "

/-- Classify the two sides of an equation or equivalence. `lμ` is the side containing `μ′`, with
`μ′` replaced by `μ`; `r` is the other side. -/
def classifySides (shapes : List Name) (μ lμ r : Expr) (isIff : Bool) :
    Shape × MessageData × MessageData :=
  if r == μ && shapes.any (lμ.isAppOf ·) then (.involutive, m!"none", m!"id")
  else if lμ == r then (.invariant, m!"none", m!"id")
  else if sameFamily μ lμ r then (.idOut, twinOf lμ r, m!"id")
  else if isIff && r.isAppOfArity ``Not 1 && sameFamily μ lμ r.appArg! then
    (.notOut, twinOf lμ r.appArg!, m!"Not")
  else if r.isApp && sameFamily μ lμ r.appArg! then
    let g := r.appFn!
    if g.containsFVar μ.fvarId! then (.outMu, twinOf lμ r.appArg!, m!"{g}")
    else (.outG, twinOf lμ r.appArg!, m!"{g}")
  else (.unknown, .nil, m!"{r}")

/-- Classify one theorem statement (`none`: no involution of the spec occurs in it). -/
def classify (spec : Spec) (ty : Expr) : MetaM (Option (Shape × MessageData × MessageData)) := do
  let all := spec.shapes ++ spec.operators ++ spec.others
  unless mentionsAny all ty do return none
  forallTelescope ty fun xs concl => do
    let ctx (r : Shape × MessageData × MessageData) : MetaM (Shape × MessageData × MessageData) :=
      do return (r.1, ← addMessageContext r.2.1, ← addMessageContext r.2.2)
    let concl ← instantiateMVars concl
    let some (s, μ) := findShapeApp? spec.shapes concl
      | -- no shape involution in the conclusion
        if mentionsAny spec.shapes ty then return some (← ctx (.unknown, .nil, m!"{concl}"))
        if mentionsAny spec.operators ty then return some (.operator, .nil, .nil)
        return some (.other, .nil, .nil)
    let unprime (e : Expr) := e.replace fun t => if t == s then some μ else none
    let sides : Option (Expr × Expr × Bool) :=
      if let some (_, a, b) := concl.eq? then some (a, b, false)
      else if let some (a, b) := concl.iff? then some (a, b, true)
      else none
    match sides with
    | some (a, b, isIff) =>
      let (l, r) := if a.containsFVar μ.fvarId! && (a.find? (· == s)).isSome &&
          (b.find? (· == s)).isNone then (a, b) else (b, a)
      if (r.find? (· == s)).isSome then return some (← ctx (.unknown, .nil, m!"{concl}"))
      return some (← ctx (classifySides spec.shapes μ (unprime l) r isIff))
    | none =>
      -- `P μ → P μ′`: some hypothesis is the conclusion with `μ′` replaced by `μ`
      let atμ := unprime concl
      for x in xs do
        if (← instantiateMVars (← inferType x)) == atμ then
          return some (.preserved, m!"none", .nil)
      return some (← ctx (.unknown, .nil, m!"{concl}"))

/-- The constants used by the value `e` of the definition `n`, looking through the auxiliary
declarations `n.proof_k`, … that Lean makes for its proof fields. -/
partial def usedThroughAux (env : Environment) (n : Name) (e : Expr) : Array Name :=
  e.getUsedConstants.foldl (init := #[]) fun acc c =>
    if n.isPrefixOf c && c != n then
      match env.find? c with
      | some ci => match ci.value? (allowOpaque := true) with
        | some v => acc ++ usedThroughAux env c v
        | none => acc.push c
      | none => acc.push c
    else acc.push c

/-- Recording instances: definitions whose type ends in an application of `recorder`, mapped
from each theorem their value names directly. -/
def recordingInstances (env : Environment) (recorder : Name) : Std.HashMap Name (Array Name) :=
  env.constants.fold (init := {}) fun acc n ci =>
    match ci with
    | .defnInfo v =>
      if n.isInternalDetail then acc else
      let rec target : Expr → Expr
        | .forallE _ _ b _ => target b
        | e => e
      if (target v.type).getAppFn.constName? != some recorder || recorder.isPrefixOf n then acc
      else
      (usedThroughAux env n v.value).foldl (init := acc) fun acc c =>
        acc.insert c ((acc.getD c #[]).push n)
    | _ => acc

/-- The theorems whose names have `pfx` as a prefix (no internal details), sorted by name. -/
def theoremsUnder (env : Environment) (pfx : Name) : Array (Name × Expr) :=
  let all := env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo v => if pfx.isPrefixOf n && !n.isInternalDetail then acc.push (n, v.type) else acc
    | _ => acc
  all.qsort fun x y => Name.lt x.1 y.1

/-- Does the last component of `n` contain one of the hints? -/
def nameHit (hints : List String) (n : Name) : Bool :=
  let s := (n.componentsRev.headD .anonymous).toString.toLower
  hints.any fun h => (s.splitOn h).length > 1

/-- Rows of the report for the theorems under `pfx`. -/
def rows (spec : Spec) (pfx : Name) : MetaM (Array Row) := do
  let env ← getEnv
  let recs := match spec.recorder with
    | some r => recordingInstances env r
    | none => {}
  let mainMod ← getMainModule
  let mut res : Array Row := #[]
  for (n, ty) in theoremsUnder env pfx do
    if n.componentsRev.head? == some `congr_simp then continue
    if let some r := spec.recorder then
      if r.isPrefixOf n then continue
    let hit := nameHit spec.nameHints n
    let module := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!
      | none => mainMod
    match ← classify spec ty with
    | some (shape, twin, outM) =>
      let row : Row :=
        { decl := n, module := module, shape := shape, twin := twin, correction := outM,
          instances := recs.getD n #[], nameHit := hit }
      res := res.push row
    | none =>
      if hit then
        let row : Row :=
          { decl := n, module := module, shape := .unknown, nameHit := hit,
            correction := m!"(name hit, no involution in the statement)" }
        res := res.push row
  return res

/-- Evaluate a spec constant. -/
unsafe def evalSpecUnsafe (n : Name) : CoreM Spec := evalConstCheck Spec ``Spec n

/-- Evaluate a spec constant (implemented by `evalSpecUnsafe`). -/
@[implemented_by evalSpecUnsafe]
opaque evalSpec (n : Name) : CoreM Spec

/-- `#involution_laws spec in N`: the laws of the spec's involution among the theorems under `N`.
`#involution_laws spec in N summary` prints the counts only. -/
syntax (name := involutionLaws) "#involution_laws " ident " in " ident (&" summary")? : command

/-- Elaborator of `#involution_laws`. -/
@[command_elab involutionLaws]
def elabInvolutionLaws : CommandElab := fun stx => do
  let sName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let pfx := stx[3].getId
  let summaryOnly := !stx[4].isNone
  let spec ← liftCoreM <| evalSpec sName
  let rs ← liftTermElabM (rows spec pfx)
  let count (p : Row → Bool) := (rs.filter p).size
  let laws := rs.filter (·.shape.isLaw)
  let mut msg : MessageData := m!"involution {spec.name}, spec {sName}, on {pfx}: \
    {rs.size} rows, {laws.size} laws, {count (fun r => r.shape.isLaw && r.instances.isEmpty)} \
    not recorded"
  for sh in Shape.all do
    let k := count (·.shape == sh)
    if k > 0 then msg := msg ++ m!"\n  {sh.label}: {k}"
  msg := msg ++ m!"\nname hits: {count (·.nameHit)}; laws with a name hit: \
    {count (fun r => r.nameHit && r.shape.isLaw)}; laws without one: \
    {count (fun r => !r.nameHit && r.shape.isLaw)}"
  unless summaryOnly do
    for r in rs do
      let inst := if r.instances.isEmpty then m!"" else m!"  [recorded: {r.instances.toList}]"
      let hit := if r.nameHit then m!"" else m!"  [no name hit]"
      let detail :=
        if r.shape.isLaw then m!"\n    twin: {r.twin}\n    out: {r.correction}"
        else if r.shape == .unknown then m!"\n    {r.correction}" else .nil
      msg := msg ++ m!"\n{r.decl} ({r.module}): {r.shape.label}{inst}{hit}" ++ detail
  logInfo msg

end RMT.Frames.Involution

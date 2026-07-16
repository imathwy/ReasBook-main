import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

open scoped Rockafellar

variable {𝕜 : Type v} {E : Type u} {β : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.1 introduces an ordinary convex program: a constraint set `C`
  together with a convex objective on `C`, convex inequality functions on `C`, and affine
  equality functions on `C`. The source data is only the tuple of values on `C`.
- `core/canonical`: the owner predicates are `ConvexOn 𝕜 C F` and `affOn[𝕜](F, C)` on ambient
  functions. Their canonical ambient layer needs only the scalar/order data required by those
  owners (`Semiring 𝕜`, `PartialOrder 𝕜`, additive ambient spaces with scalar action). Chapter 1
  already fixes `affOn[𝕜](·, ·)` as the project's canonical affine-on-a-set owner.
- `bridge/view`: the source indexing `i = 1, …, r` and `i = r + 1, …, m` is represented by two
  index owners (inequality/equality blocks), with defaults `Fin r` and `Fin s` for textbook
  numbering. Restricted data on `C` is compared to the ambient owners through the canonical
  extension bridge `Function.extendByZero`, exactly as other restricted-data files in the project
  use namespaced subtype-extension owners (`Function.extendByTop`, `Function.toWithTopBotOn`).

Domain-style sampling used here:
- `ConvexOn` and `ConcaveOn` from mathlib's convex-function API;
- the conjunction projections from the project affine-on-set owner notation `affOn[𝕜](·, ·)` in
  `ConvexAnalysis_Rockafellar_1970/Chap01/Definition_4_3.lean`;
- `Function.extend_val_apply` / `Function.extend_val_apply'` from mathlib's subtype-extension API;
- the restricted-data owner bridge `Function.extendByTop` in
  `ConvexAnalysis_Rockafellar_1970/Chap04/Definition_17_2_2.lean`;
- the set-affine bridge pattern in
  `ConvexAnalysis_Rockafellar_1970/Chap01/Definition_4_3.lean` and
  `ConvexAnalysis_Rockafellar_1970/Chap01/Remark_4_5_0.lean`.

Primitive data vs derived API:
- primitive data: the constraint set together with the objective, inequality family, and equality
  family as functions on the subtype `C`;
- primitive owner properties: convexity of the objective and inequalities, and affinity of the
  equalities, recorded through `ConvexOn`/`affOn[𝕜](·, ·)` on the canonical ambient extension of the
  restricted data;
- derived API: the fact that the constraint set is convex, recovered from the owner's
  `ConvexOn` fields instead of stored primitively as duplicate data.

Layer target: `source-facing`. This item defines a genuine program object, so it stays a
structure; the later feasible set, perturbation function, and Kuhn-Tucker data should be derived
from this owner rather than stored primitively.
-/

/-- Extend a function on a subtype domain to the ambient type by `0` off the subtype. -/
def Function.extendByZero {C : Set E} [Zero β] (f : C → β) : E → β :=
  Function.extend Subtype.val f (fun _ ↦ 0)

/-- On the defining constraint set, `extendZero f` agrees with `f`. -/
@[simp] theorem Function.extendByZero_apply_of_mem
    {C : Set E} [Zero β] (f : C → β) {x : E} (hx : x ∈ C) :
    Function.extendByZero f x = f ⟨x, hx⟩ := by
  simpa [Function.extendByZero] using
    (Function.extend_val_apply (g := f) (j := fun _ : E ↦ (0 : β)) hx)

/-- Off the defining constraint set, `extendZero f` takes the value `0`. -/
@[simp] theorem Function.extendByZero_apply_of_notMem
    {C : Set E} [Zero β] (f : C → β) {x : E}
    (hx : x ∉ C) :
    Function.extendByZero f x = 0 := by
  simpa [Function.extendByZero] using
    (Function.extend_val_apply' (g := f) (j := fun _ : E ↦ (0 : β)) hx)

/-- On the subtype domain, `Function.extendByZero` agrees with the original function. -/
@[simp] theorem Function.extendByZero_apply
    {C : Set E} [Zero β] (f : C → β) (x : C) :
    Function.extendByZero f x = f x := by
  simp [Function.extendByZero]

/-- Restricting `Function.extendByZero` back to the subtype recovers the original function. -/
@[simp] theorem Function.extendByZero_comp_subtype_val
    {C : Set E} [Zero β] (f : C → β) :
    Function.extendByZero f ∘ (Subtype.val : C → E) = f := by
  funext x
  simp [Function.extendByZero]

/-- Backward-compatible short name for `Function.extendByZero`. -/
abbrev extendZero {C : Set E} [Zero β] (f : C → β) : E → β :=
  Function.extendByZero f

/-- On the defining constraint set, `extendZero f` agrees with `f`. -/
@[simp] theorem extendZero_apply {C : Set E} [Zero β] (f : C → β) (x : C) :
    extendZero f x = f x := by
  simp [extendZero]

/-- Off the defining constraint set, `extendZero f` takes the value `0`. -/
@[simp] theorem extendZero_apply_of_notMem {C : Set E} [Zero β] (f : C → β) {x : E}
    (hx : x ∉ C) :
    extendZero f x = 0 := by
  simpa [extendZero] using (Function.extendByZero_apply_of_notMem (f := f) hx)

variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

/-- Definition 6.28.1: an ordinary convex program consists of a constraint set together with a
`β`-valued objective, finitely many convex inequalities, and finitely many affine equalities, all
given only on that constraint set. The indexing owners are explicit type parameters
`inequalityIndex` and `equalityIndex`, required to be finite and cardinality-matched to `r` and
`s`. Defaults `Fin r` and `Fin s` retain the textbook block numbering surface when ordered
positions are desired. -/
structure OrdinaryConvexProgram (𝕜 : Type v) (E : Type u) (β : Type w)
    [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]
    [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
    (r s : ℕ)
    (inequalityIndex : Type := Fin r)
    (equalityIndex : Type := Fin s)
    [Fintype inequalityIndex] [Fintype equalityIndex]
    [Fact (Fintype.card inequalityIndex = r)]
    [Fact (Fintype.card equalityIndex = s)] where
  constraintSet : Set E
  objective : constraintSet → β
  objective_convexOn : ConvexOn 𝕜 constraintSet (Function.extendByZero objective)
  inequality : inequalityIndex → constraintSet → β
  inequality_convexOn (i : inequalityIndex) :
    ConvexOn 𝕜 constraintSet (Function.extendByZero (inequality i))
  equality : equalityIndex → constraintSet → β
  equality_affOn (i : equalityIndex) :
    affOn[𝕜](Function.extendByZero (equality i), constraintSet)

namespace OrdinaryConvexProgram

instance (n : ℕ) : Fact (Fintype.card (Fin n) = n) := ⟨Fintype.card_fin n⟩

variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

abbrev objectiveAmbient : E → β :=
  Function.extendByZero P.objective

abbrev inequalityAmbient (i : ι) : E → β :=
  Function.extendByZero (P.inequality i)

abbrev equalityAmbient (i : κ) : E → β :=
  Function.extendByZero (P.equality i)

/-- On the constraint set, `P.objectiveAmbient` agrees with `P.objective`. -/
@[simp] theorem objectiveAmbient_apply (x : P.constraintSet) :
    P.objectiveAmbient x = P.objective x := by
  simp [OrdinaryConvexProgram.objectiveAmbient]

/-- On the constraint set, `P.inequalityAmbient i` agrees with `P.inequality i`. -/
@[simp] theorem inequalityAmbient_apply (i : ι) (x : P.constraintSet) :
    P.inequalityAmbient i x = P.inequality i x := by
  simp [OrdinaryConvexProgram.inequalityAmbient]

/-- On the constraint set, `P.equalityAmbient i` agrees with `P.equality i`. -/
@[simp] theorem equalityAmbient_apply (i : κ) (x : P.constraintSet) :
    P.equalityAmbient i x = P.equality i x := by
  simp [OrdinaryConvexProgram.equalityAmbient]

/-- Each equality constraint in an ordinary convex program is convex on the constraint set. -/
theorem equality_convexOn (i : κ) :
    ConvexOn 𝕜 P.constraintSet (P.equalityAmbient i) :=
  (P.equality_affOn i).1

/-- Each equality constraint in an ordinary convex program is concave on the constraint set. -/
theorem equality_concaveOn (i : κ) :
    ConcaveOn 𝕜 P.constraintSet (P.equalityAmbient i) :=
  (P.equality_affOn i).2

/-- Bridge view: each equality constraint is convex on `P.constraintSet` as an ambient map. -/
theorem equality_convexOn_ambient (i : κ) :
    ConvexOn 𝕜 P.constraintSet (P.equalityAmbient i) :=
  P.equality_convexOn i

/-- Bridge view: each equality constraint is concave on `P.constraintSet` as an ambient map. -/
theorem equality_concaveOn_ambient (i : κ) :
    ConcaveOn 𝕜 P.constraintSet (P.equalityAmbient i) :=
  P.equality_concaveOn i

/-- The constraint set of an ordinary convex program is convex. -/
theorem constraintSet_convex :
    Convex 𝕜 P.constraintSet :=
  P.objective_convexOn.1

end OrdinaryConvexProgram

end

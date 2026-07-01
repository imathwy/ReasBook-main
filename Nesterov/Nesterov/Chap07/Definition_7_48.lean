import Nesterov.Chap06.Definition_6_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/- Definition 7.48 lies in the primal-dual bilinear saddle-model domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel` in `Chap06/Definition_6_6`, the chapter owner for bounded closed
  convex primal/dual sets equipped with a canonical saddle map;
- `StructuredObjectiveModel.saddleFunction` in `Chap06/Definition_6_6`, the owner-level saddle
  function `\hat f(x) + ⟪A x, u⟫ - \hat φ(u)`;
- `SimplexSaddlePointProblem.toStructuredObjectiveModel` in `Chap06/Definition_6_12`, the
  project pattern for keeping a source-facing bilinear saddle problem while exposing a stronger
  Chapter 6 owner bridge;
- `Seminorm.primalDualOperatorNorm_toDual_eq_sSup_pairing` in `Chap02/Definition_2_32`, the
  project pattern for keeping an `F`-valued linear map source-facing and deriving the canonical
  dual-valued coupling through `InnerProductSpace.toDual`.

Best owner abstraction:
- source-facing: `BilinearSaddlePointProblem E F`;
- core/canonical under stronger boundedness and finite-dimensional hypotheses:
  `StructuredObjectiveModel E F`;
- bridge/view: the dual-valued `couplingMap`, together with the stronger-assumption bridge
  `toStructuredObjectiveModel`.

Primitive data:
- the primal and dual feasible sets with their closedness and convexity;
- the source linear operator `A : E →ₗ[ℝ] F`;
- the linear terms `c ∈ E` and `b ∈ F`.

Derived API:
- the canonical dual-valued coupling `x ↦ ⟪A x, ·⟫`;
- the saddle function and its coercion;
- under stronger hypotheses, the Chapter 6 bridge `toStructuredObjectiveModel`.

Source/core/bridge triage:
- source-facing: `BilinearSaddlePointProblem` and its saddle function;
- core/canonical under stronger assumptions: `StructuredObjectiveModel`;
- bridge/view: `couplingMap`, `couplingMap_apply`, and `toStructuredObjectiveModel`.

Because Definition 7.48 imposes only closed/convex feasible sets and a raw linear map
`A : E →ₗ[ℝ] F`, it cannot be replaced directly by `StructuredObjectiveModel`, which also stores
boundedness and a continuous dual-valued coupling. The correct refinement therefore keeps the
source-facing owner, moves the bilinear term onto the canonical dual-valued coupling map, and
adds only a stronger-assumption bridge to the Chapter 6 owner.
-/

/-- Definition 7.48: [Bilinear saddle-point problem] a bilinear saddle-point problem consists of
closed convex feasible sets `Q_p ⊆ E` and `Q_d ⊆ F`, a linear operator `A : E → F`, and linear
terms given by vectors `c ∈ E` and `b ∈ F`; its canonical saddle function is
`(x, w) ↦ ⟪A x, w⟫ + ⟪c, x⟫ + ⟪b, w⟫` on `Q_p × Q_d`. -/
structure BilinearSaddlePointProblem (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  /-- The primal feasible set `Q_p ⊆ E`. -/
  primalSet : Set E
  /-- The primal feasible set is closed. -/
  primalSet_closed : IsClosed primalSet
  /-- The primal feasible set is convex. -/
  primalSet_convex : Convex ℝ primalSet
  /-- The dual feasible set `Q_d ⊆ F`. -/
  dualSet : Set F
  /-- The dual feasible set is closed. -/
  dualSet_closed : IsClosed dualSet
  /-- The dual feasible set is convex. -/
  dualSet_convex : Convex ℝ dualSet
  /-- The linear operator `A : E → F` defining the bilinear coupling term. -/
  linearMap : E →ₗ[ℝ] F
  /-- The primal linear term `c ∈ E`. -/
  primalLinearTerm : E
  /-- The dual linear term `b ∈ F`. -/
  dualLinearTerm : F

namespace BilinearSaddlePointProblem

/-- The canonical dual-valued coupling `x ↦ ⟪A x, ·⟫` attached to a bilinear saddle-point
problem. -/
abbrev couplingMap (problem : BilinearSaddlePointProblem E F) : E →ₗ[ℝ] StrongDual ℝ F :=
  (InnerProductSpace.toDualMap ℝ F).toLinearMap.comp problem.linearMap

/-- Evaluating `couplingMap` recovers the bilinear term `⟪A x, w⟫`. -/
@[simp] theorem couplingMap_apply
    (problem : BilinearSaddlePointProblem E F) (x : E) (w : F) :
    problem.couplingMap x w = inner ℝ (problem.linearMap x) w := by
  simp [couplingMap, InnerProductSpace.toDualMap_apply_apply]

/-- The canonical saddle function
`(x, w) ↦ ⟪A x, w⟫ + ⟪c, x⟫ + ⟪b, w⟫` on `Q_p × Q_d`. -/
def saddleFunction (problem : BilinearSaddlePointProblem E F) :
    problem.primalSet → problem.dualSet → ℝ :=
  fun x w ↦
    problem.couplingMap (x : E) w +
      inner ℝ problem.primalLinearTerm (x : E) +
      inner ℝ problem.dualLinearTerm (w : F)

/-- A bilinear saddle-point problem can be evaluated as its canonical saddle function on
`Q_p × Q_d`. -/
instance : CoeFun (BilinearSaddlePointProblem E F)
    (fun problem ↦ problem.primalSet → problem.dualSet → ℝ) where
  coe problem := problem.saddleFunction

/-- Evaluating a bilinear saddle-point problem as a function means evaluating its canonical saddle
function. -/
@[simp] theorem coe_apply
    (problem : BilinearSaddlePointProblem E F) (x : problem.primalSet) (w : problem.dualSet) :
    problem x w = problem.saddleFunction x w :=
  rfl

-- Proof sketch: unfold `saddleFunction`; the displayed equality is exactly the defining bilinear
-- affine expression on `Q_p × Q_d`.
/-- Evaluating the saddle function recovers the bilinear term `⟪A x, w⟫` together with the linear
contributions `⟪c, x⟫` and `⟪b, w⟫`. -/
@[simp] theorem saddleFunction_apply (problem : BilinearSaddlePointProblem E F)
    (x : problem.primalSet) (w : problem.dualSet) :
    problem.saddleFunction x w =
      inner ℝ (problem.linearMap (x : E)) (w : F) +
        inner ℝ problem.primalLinearTerm (x : E) +
        inner ℝ problem.dualLinearTerm (w : F) := by
  simp [saddleFunction]

section StructuredObjectiveBridge

variable [FiniteDimensional ℝ E]

/-- Under the stronger hypotheses needed by Chapter 6, a bilinear saddle-point problem becomes a
structured objective model with linear smooth and dual-penalty parts. -/
def toStructuredObjectiveModel
    (problem : BilinearSaddlePointProblem E F)
    (hprimal_bounded : Bornology.IsBounded problem.primalSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    StructuredObjectiveModel E F where
  primalSet := problem.primalSet
  primalSet_bounded := hprimal_bounded
  primalSet_closed := problem.primalSet_closed
  primalSet_convex := problem.primalSet_convex
  dualSet := problem.dualSet
  dualSet_bounded := hdual_bounded
  dualSet_closed := problem.dualSet_closed
  dualSet_convex := problem.dualSet_convex
  smoothPart := InnerProductSpace.toDualMap ℝ E problem.primalLinearTerm
  dualPenalty := -InnerProductSpace.toDualMap ℝ F problem.dualLinearTerm
  linearMap := problem.couplingMap.toContinuousLinearMap
  smoothPart_continuous := by
    sorry
  smoothPart_convex := by
    sorry
  dualPenalty_continuous := by
    sorry
  dualPenalty_convex := by
    sorry

/-- The Chapter 6 saddle function of `toStructuredObjectiveModel` is exactly the source-facing
bilinear saddle function of Definition 7.48. -/
  @[simp] theorem toStructuredObjectiveModel_saddleFunction_apply
      (problem : BilinearSaddlePointProblem E F)
      (hprimal_bounded : Bornology.IsBounded problem.primalSet)
      (hdual_bounded : Bornology.IsBounded problem.dualSet)
      (x : problem.primalSet) (w : problem.dualSet) :
      (problem.toStructuredObjectiveModel hprimal_bounded hdual_bounded).saddleFunction x w =
      problem.saddleFunction x w := by
  simp [toStructuredObjectiveModel, saddleFunction, StructuredObjectiveModel.saddleFunction,
    sub_eq_add_neg, add_left_comm, add_comm]

end StructuredObjectiveBridge

end BilinearSaddlePointProblem

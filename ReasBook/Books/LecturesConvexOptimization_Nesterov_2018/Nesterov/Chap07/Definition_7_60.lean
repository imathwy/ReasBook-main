import LecturesConvexOptimization_Nesterov_2018.Chap03.Theorem_3_1_25
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis WithTopConvexAnalysis

universe u v w

section MinimizerSelection

variable {P : Type u} {S : Type v}

/- This item belongs to the Chapter 7 saddle-representation / selected-subgradient domain.

Relevant owner declarations:
- `SaddlePointRepresentation` in `Definition_7_59`;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`;
- `mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient` in
  `Chap03/Theorem_3_1_25`.

The source-facing auxiliary data are:
- a minimizing branch `w : P → S` for the saddle slices `Ψ(x, ·)`;
- a chosen first-argument saddle subgradient evaluated along that branch.

The canonical owner remains `SaddlePointRepresentation`; the minimizer-selection predicate and the
selected subgradient field are thin source-facing layers over that owner. -/

namespace SaddlePointRepresentation

/-- A function `w : P → S` is a barrier-subproblem minimizer selection for a saddle-point
representation when each chosen point `w x` belongs to the canonical minimizing fiber of the
saddle slice `Ψ(x, ·)`. -/
def IsBarrierSubproblemMinimizerSelection
    (representation : SaddlePointRepresentation P S) (w : P → S) : Prop :=
  ∀ x : P, w x ∈ argmin[Set.univ] (representation.saddleFunction x)

namespace IsBarrierSubproblemMinimizerSelection

variable {representation : SaddlePointRepresentation P S} {w : P → S}

/-- Evaluating a barrier-subproblem minimizer selection at `x` yields a point of the canonical
argmin set of the saddle slice `Ψ(x, ·)`. -/
-- Proof sketch: unfold `IsBarrierSubproblemMinimizerSelection`.
theorem apply
    (hw : representation.IsBarrierSubproblemMinimizerSelection w) (x : P) :
    w x ∈ argmin[Set.univ] (representation.saddleFunction x) := sorry

/-- The selected point `w x` minimizes the saddle slice `Ψ(x, ·)` on the whole parameter space
`S`. -/
-- Proof sketch: rewrite argmin membership with `mem_constrainedArgmin_iff`.
theorem isMinOn
    (hw : representation.IsBarrierSubproblemMinimizerSelection w) (x : P) :
    IsMinOn (representation.saddleFunction x) Set.univ (w x) := sorry

/-- Along a minimizing branch, the represented objective value equals the saddle value at the
selected minimizer. -/
-- Proof sketch: compare the least-value witness `representation.objective_isLeast x` with the
-- least-value witness induced by `hw.isMinOn x`.
theorem objective_eq_saddleFunction
    (hw : representation.IsBarrierSubproblemMinimizerSelection w) (x : P) :
    representation x = representation.saddleFunction x (w x) := sorry

end IsBarrierSubproblemMinimizerSelection

end SaddlePointRepresentation

end MinimizerSelection

section SelectedSubgradient

variable {P : Type u} {S : Type v}

namespace SaddlePointRepresentation

/-- Definition 7.60: [Subgradient selection] if `w(x)` is a chosen minimizer of the saddle slice
`Ψ(x, ·)` and `∇₁Ψ` is a chosen subgradient with respect to the first argument, then the selected
subgradient field of the represented objective is `x ↦ ∇₁Ψ(x, w(x))`. -/
def barrierSubgradientSelection
    (firstSubgradient : P → S → P) (w : P → S) : P → P :=
  fun x ↦ firstSubgradient x (w x)

/-- Evaluating `barrierSubgradientSelection` at `x` returns the chosen first-argument saddle
subgradient at `(x, w(x))`. -/
-- Proof sketch: unfold `barrierSubgradientSelection`.
theorem barrierSubgradientSelection_apply
    (firstSubgradient : P → S → P) (w : P → S) (x : P) :
    barrierSubgradientSelection firstSubgradient w x = firstSubgradient x (w x) := sorry

variable [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- A selected barrier subgradient field is a pointwise subgradient of the represented objective
on the whole-space relative subdifferential `∂[Set.univ] representation(x)`. -/
def IsBarrierSubgradientSelection
    (representation : SaddlePointRepresentation P S) (g : P → P) : Prop :=
  ∀ x : P, g x ∈ ∂[Set.univ] representation(x)

namespace IsBarrierSubgradientSelection

variable {representation : SaddlePointRepresentation P S} {g : P → P}

/-- Evaluating a selected barrier subgradient field at `x` gives a subgradient of the represented
objective at `x`. -/
-- Proof sketch: unfold `IsBarrierSubgradientSelection`.
theorem apply
    (hg : representation.IsBarrierSubgradientSelection g) (x : P) :
    g x ∈ ∂[Set.univ] representation(x) := sorry

end IsBarrierSubgradientSelection

section Transfer

variable [NormedAddCommGroup S] [InnerProductSpace ℝ S]

/-- The canonical `EReal` partial-infimum projection attached to a saddle-point representation. -/
private def saddlePartialInfProjection
    (representation : SaddlePointRepresentation P S) : P → EReal :=
  partialInfProjection (Set.univ : Set (P × S))
    (withTopToEReal ∘ fun z : P × S ↦
      ((representation.saddleFunction z.1 z.2 : ℝ) : WithTop ℝ))

/-- The image of the `x`-fiber under a two-variable function is the range of its `x`-slice. -/
-- Proof sketch: unpack membership in the image and in the range and rewrite by the equation
-- `z.1 = x`.
private theorem image_saddleFiber_eq_range
    {α : Type w} (f : P → S → α) (x : P) :
    (fun z : P × S ↦ f z.1 z.2) '' {z : P × S | z.1 = x} = Set.range (f x) := sorry

/-- Every point `x` lies in the effective domain of the canonical partial-infimum projection
attached to a saddle-point representation. -/
-- Proof sketch: rewrite the partial-infimum projection as the infimum of the slice
-- `representation.saddleFunction x`, then use `representation.objective_isLeast x` to witness a
-- finite attained infimum.
private theorem saddlePartialInfProjection_mem_dom
    (representation : SaddlePointRepresentation P S) (x : P) :
    x ∈ dom (saddlePartialInfProjection representation) := sorry

/-- The finite real part of the canonical partial-infimum projection agrees with the represented
objective. -/
-- Proof sketch: identify both sides with the infimum of the slice
-- `representation.saddleFunction x`, using `representation.objective_eq x` on one side and
-- `extendedRealRealPart_partialInfProjection_eq_sInf` on the other.
private theorem objective_eq_saddlePartialInfProjection
    (representation : SaddlePointRepresentation P S) :
    representation = extendedRealRealPart (saddlePartialInfProjection representation) := sorry

/-- If a minimizing branch `w(x)` is paired with a chosen product-space saddle subgradient at
`(x, w(x))` satisfying the Chapter 3 subgradient and variational-inequality hypotheses, then the
selected field `x ↦ ∇₁Ψ(x, w(x))` is a genuine subgradient selection of the represented objective.
-/
-- Proof sketch: apply
-- `mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient` to the
-- canonical partial-infimum projection of `representation`, then rewrite the resulting objective
-- with `objective_eq_saddlePartialInfProjection`.
theorem barrierSubgradientSelection_isBarrierSubgradientSelection
    {representation : SaddlePointRepresentation P S}
    {w : P → S}
    (hw : representation.IsBarrierSubproblemMinimizerSelection w)
    (saddleSubgradient : P → S → P × S)
    (hsub :
      ∀ x : P,
        WithLp.toLp 2 (saddleSubgradient x (w x)) ∈
          subdifferential
            (fun z : WithLp 2 (P × S) ↦
              ((representation.saddleFunction z.1.1 z.1.2 : ℝ) : WithTop ℝ))
            (WithLp.toLp 2 (x, w x)))
    (hvar :
      ∀ x : P, ∀ y : S,
        inner ℝ (saddleSubgradient x (w x)).2 (y - w x) ≥ 0) :
    representation.IsBarrierSubgradientSelection
      (barrierSubgradientSelection (fun x s ↦ (saddleSubgradient x s).1) w) := sorry

end Transfer

end SaddlePointRepresentation

end SelectedSubgradient

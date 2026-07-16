import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Example 5.1.2 lies in the Chapter 5 self-concordance / quadratic-objective domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the Chapter 5 source-facing
  owner for diagonal third derivatives;
* `IsSelfConcordantOnWith` from `Chap05/Definition_5_1_1`, the chapter owner predicate;
* `quadraticObjective` from `Chap01/Definition_1_9_1`, the Euclidean matrix-model quadratic owner;
* `nesterovQuadraticObjective` from `Chap02/Proposition_2_6`, the specialized operator quadratic
  owner without an affine term.

Source/core/bridge triage:
* source-facing: the affine-quadratic objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫`;
* core/canonical: `hessian`, `thirdDirectionalDerivative`, and `IsSelfConcordantOnWith`;
* bridge/view: the Euclidean matrix model `quadraticObjective` and the Chapter 2 specialization
  `nesterovQuadraticObjective`.

Primitive data:
* the scalar offset `α`;
* the linear coefficient `a`;
* the bounded operator `A : E →L[ℝ] E`.

Derived API:
* the gradient identity `∇f(x) = a + A x`;
* the constant-Hessian identity `hessian f x = A`;
* the vanishing third directional derivative;
* the self-concordance conclusion with constant `0`.

No upstream owner packages this exact affine operator-valued quadratic objective at the intrinsic
Hilbert-space level, so this file remains the source-facing owner. The supporting API is refined to
the canonical Chapter 1/5 differential owners rather than the raw `fderiv ℝ (∇ ·)` surface. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic-affine objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` on `E`. -/
def quadraticAffineObjective (α : ℝ) (a : E) (A : E →L[ℝ] E) : E → ℝ :=
  fun x ↦ α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A x) x

/-- Evaluating the quadratic-affine objective gives its defining formula. -/
@[simp]
theorem quadraticAffineObjective_apply (α : ℝ) (a : E) (A : E →L[ℝ] E) (x : E) :
    quadraticAffineObjective α a A x =
      α + inner ℝ a x + (1 / 2 : ℝ) * inner ℝ (A x) x :=
  rfl

/-- The zero-quadratic specialization of `quadraticAffineObjective` is the affine objective
`x ↦ α + ⟪a, x⟫`. -/
@[simp]
theorem quadraticAffineObjective_zero_operator (α : ℝ) (a : E) :
    quadraticAffineObjective α a (0 : E →L[ℝ] E) = fun x ↦ α + inner ℝ a x := by
  funext x
  simp [quadraticAffineObjective]

/-- The third directional derivative of a quadratic-affine objective vanishes identically. -/
-- Proof sketch: the Hessian is constant, so differentiating it once more gives zero.
theorem quadraticAffineObjective_thirdDirectionalDerivative_eq_zero
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (x u : E) :
    thirdDirectionalDerivative (quadraticAffineObjective α a A) x u = 0 := sorry

variable [CompleteSpace E]

/-- The gradient of the quadratic-affine objective is `x ↦ a + A x` when `A` is self-adjoint. -/
-- Proof sketch: differentiate the affine term and the quadratic form; self-adjointness identifies
-- the symmetrized Hessian contribution with `A`.
theorem quadraticAffineObjective_gradient_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) :
    ∇ (quadraticAffineObjective α a A) = fun x ↦ a + A x := sorry

/-- The Hessian of the quadratic-affine objective is the constant operator `A` when `A` is
self-adjoint. -/
-- Proof sketch: differentiate `quadraticAffineObjective_gradient_eq`; the affine term vanishes and
-- the derivative of `x ↦ A x` is the constant operator `A`.
theorem quadraticAffineObjective_hessian_eq
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (x : E) :
    hessian (quadraticAffineObjective α a A) x = A := sorry

/-- Example 5.1.2: if `A` is positive, then the quadratic-affine objective
`f(x) = α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` on all of `E` is self-concordant with self-concordance
constant `M_f = 0`. -/
-- Proof sketch: `A.IsPositive` gives the Hessian positive-semidefinite condition, the quadratic
-- objective is `C^3` on all of `E`, and
-- `quadraticAffineObjective_thirdDirectionalDerivative_eq_zero` makes the cubic bound with
-- constant `0` immediate.
theorem quadraticAffineObjective_isSelfConcordantOnWith_zero
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (hA : A.IsPositive) :
    IsSelfConcordantOnWith (Set.univ : Set E) 0 (quadraticAffineObjective α a A) := sorry

end

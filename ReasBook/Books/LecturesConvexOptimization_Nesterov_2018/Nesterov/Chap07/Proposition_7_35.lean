import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap02.Definition_2_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap02.Lemma_2_18
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v w

/- Proposition 7.35 lies in the chapter's affine-residual / strict-positivity domain.

Sampled owner-style declarations:
- `Seminorm.IsNorm` in `Chap02/Definition_2_5`, the project owner for a separated seminorm;
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the project owner for
  pointwise maxima over a nonempty finite index type;
- `StrictlyPositiveOn` in `Chap07/Definition_7_81`, the source-facing positivity predicate;
- `StrictlyPositiveOn.inequality_comp_affineMap_image_adjoint` in `Chap07/Lemma_7_16`, the
  intrinsic affine-pullback bridge on linear maps;
- `StrictlyPositiveOn.nonnegative_linear_combination` in `Chap07/Lemma_7_18`, the finite-sum
  closure pattern used by Proposition 7.35.

Best owner abstraction:
- source-facing: Proposition 7.35's strict-positivity assertions for
  `x ↦ p (A x - b)`, `x ↦ ∑ i, p (Aᵢ x - bᵢ)`, and
  `x ↦ maxᵢ p (Aᵢ x - bᵢ)`;
- core/canonical: `Seminorm.IsNorm`, `maxTypeObjective`, and `StrictlyPositiveOn`;
- bridge/view: the Euclidean matrix specialization obtained by taking
  `E := EuclideanSpace ℝ (Fin n)`, `F := EuclideanSpace ℝ (Fin m)`, and
  `Aᵢ := (Mᵢ).toEuclideanLin`.

Primitive data:
- a seminorm `p : Seminorm ℝ F`;
- linear maps `A : E →ₗ[ℝ] F` and `A : ι → E →ₗ[ℝ] F`;
- translations `b : F` and `b : ι → F`;
- a finite family index type `ι` for the aggregate cases.

Derived API:
- the direct objective expressions `fun x ↦ p (A x - b)`,
  `fun x ↦ ∑ i, p (A i x - b i)`, and
  `maxTypeObjective (fun i x ↦ p (A i x - b i))`;
- the strict-positivity theorems on `Set.univ`.

This refinement moves the public API from the over-concrete display model
`EuclideanSpace ℝ (Fin n)` with matrix families indexed by `Fin m` to the intrinsic owner layer of
real vector spaces, linear maps, and a separate finite index type. It also deletes proposition-local
wrapper definitions whose only role was to rename those direct objective expressions. The textbook
matrix formulas are now recovered by specialization rather than by a second concrete owner.
-/

section StrictPositivity

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {ι : Type w} [Fintype ι]

/-- If `p` is a norm, then the affine residual objective `x ↦ p (A x - b)` is strictly positive
on the whole space. -/
-- Proof sketch: identify `p` with the real-valued support function of its dual unit ball, apply
-- the support-function strict-positivity theorem on `F`, and then pull back along the affine map
-- `x ↦ A x - b` using the intrinsic affine-pullback lemma from `Lemma_7_16`.
theorem affineResidualSeminorm_strictlyPositiveOn_univ
    (p : Seminorm ℝ F) [p.IsNorm]
    (A : E →ₗ[ℝ] F) (b : F) :
    StrictlyPositiveOn Set.univ (fun x ↦ p (A x - b)) := sorry

-- Proof sketch: each summand `x ↦ p (Aᵢ x - bᵢ)` is strictly positive on `E` by
-- `affineResidualSeminorm_strictlyPositiveOn_univ`; then iterate
-- `StrictlyPositiveOn.nonnegative_linear_combination` with coefficients `1` to combine the family
-- into its finite sum.
/-- Proposition 7.35 (1): the aggregate objective
`f₁(x) = ∑ᵢ p (Aᵢ x - bᵢ)` is strictly positive on the whole space in the sense of
Definition 7.81. -/
theorem affineResidualSeminormSum_strictlyPositiveOn
    (p : Seminorm ℝ F) [p.IsNorm]
    (A : ι → E →ₗ[ℝ] F) (b : ι → F) :
    StrictlyPositiveOn Set.univ (fun x ↦ ∑ i : ι, p (A i x - b i)) := sorry

variable [Nonempty ι]

-- Proof sketch: each branch `x ↦ p (Aᵢ x - bᵢ)` is strictly positive on `E` by
-- `affineResidualSeminorm_strictlyPositiveOn_univ`; then induct on the nonempty finite family and
-- use the two-branch max closure theorem at each step.
/-- Proposition 7.35 (2): the aggregate objective
`f₂(x) = maxᵢ p (Aᵢ x - bᵢ)` is strictly positive on the whole space in the sense of
Definition 7.81. -/
theorem affineResidualSeminormMax_strictlyPositiveOn
    (p : Seminorm ℝ F) [p.IsNorm]
    (A : ι → E →ₗ[ℝ] F) (b : ι → F) :
    StrictlyPositiveOn Set.univ (maxTypeObjective fun i x ↦ p (A i x - b i)) := sorry

end StrictPositivity

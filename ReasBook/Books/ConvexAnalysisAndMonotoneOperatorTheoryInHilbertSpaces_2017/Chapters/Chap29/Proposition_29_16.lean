import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import BauschkeLean.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

universe u v w

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type w}

/-
Source/core/bridge triage:
- `source-facing`: Proposition 29.16 describes the metric projection onto the diagonal of constant
  coordinate families in a finite weighted-product Hilbert geometry.
- `core/canonical`: the repository owner for metric projection is `projectionPoint`/`P[C, hC]`.
- `bridge/view`: the coordinate identification `e : E ≃ₗ[ℝ] (I → H)` supplies the diagonal set and
  its distinguished constant points inside `E`, while the weighted inner-product formula remains
  source-facing data because the repository has no separate weighted-product Hilbert owner yet.
-/

-- Semantic recall: `lean_leansearch` only surfaced the generic orthogonal-projection owners. The
-- repository does not yet expose a dedicated weighted finite-product Hilbert owner, so this item
-- keeps the source geometry explicit via a coordinate identification `e` and the weighted
-- inner-product formula on `E`.

/-- The constant family with value `p`, viewed in the coordinate model `E ≃ₗ[ℝ] (I → H)`. -/
def weightedProductDiagonalPoint (e : E ≃ₗ[ℝ] (I → H)) (p : H) : E :=
  e.symm (fun _ : I ↦ p)

/-- Evaluating `weightedProductDiagonalPoint e p` in coordinates gives the constant family `p`. -/
@[simp] theorem weightedProductDiagonalPoint_apply
    (e : E ≃ₗ[ℝ] (I → H)) (p : H) :
    e (weightedProductDiagonalPoint e p) = fun _ : I ↦ p := by
  -- Unfold the diagonal point and cancel the linear equivalence with its inverse.
  simp [weightedProductDiagonalPoint]

/-- The diagonal subset in a coordinate model `E ≃ₗ[ℝ] (I → H)` consists of the constant
families. -/
def weightedProductDiagonal (e : E ≃ₗ[ℝ] (I → H)) : Set E :=
  Set.range (weightedProductDiagonalPoint e)

/-- Every constant coordinate family belongs to the weighted-product diagonal. -/
@[simp] theorem weightedProductDiagonalPoint_mem
    (e : E ≃ₗ[ℝ] (I → H)) (p : H) :
    weightedProductDiagonalPoint e p ∈ weightedProductDiagonal e := by
  exact ⟨p, rfl⟩

/-- A point of the weighted-product diagonal is exactly a point whose chosen coordinates are
constant. -/
@[simp] theorem mem_weightedProductDiagonal_iff
    (e : E ≃ₗ[ℝ] (I → H)) (x : E) :
    x ∈ weightedProductDiagonal e ↔ ∃ p : H, e x = fun _ : I ↦ p := by
  constructor
  · intro hx
    rcases hx with ⟨p, rfl⟩
    -- Diagonal points have constant coordinates by definition.
    exact ⟨p, weightedProductDiagonalPoint_apply e p⟩
  · rintro ⟨p, hp⟩
    -- A point with constant coordinates is the diagonal point determined by that value.
    refine ⟨p, ?_⟩
    apply e.injective
    simpa [weightedProductDiagonalPoint_apply] using hp.symm

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type w} [Fintype I] [CompleteSpace E]

/-- Helper for Proposition 29.16: the residual from `x` to the weighted diagonal point is
orthogonal to every diagonal direction. -/
private lemma weightedDiagonalResidualInner_eq_zero
    (e : E ≃ₗ[ℝ] (I → H)) (ω : I → ℝ) (hω_sum : ∑ i, ω i = 1)
    (hinner : ∀ x y : E, ⟪x, y⟫_ℝ = ∑ i, ω i * ⟪e x i, e y i⟫_ℝ)
    (x : E) (z : H) :
    ⟪x - weightedProductDiagonalPoint e (∑ i, ω i • e x i),
      weightedProductDiagonalPoint e z -
        weightedProductDiagonalPoint e (∑ i, ω i • e x i)⟫_ℝ = 0 := by
  let p : H := ∑ i, ω i • e x i
  have hsum_zero : ∑ i, ω i • (e x i - p) = 0 := by
    -- The weighted residual coordinates sum to zero because `p` is the weighted barycenter.
    calc
      ∑ i, ω i • (e x i - p)
          = (∑ i, ω i • e x i) - ∑ i, ω i • p := by
              simp [smul_sub, Finset.sum_sub_distrib]
      _ = p - (∑ i, ω i) • p := by
            rw [Finset.sum_smul]
      _ = p - p := by simp [hω_sum]
      _ = 0 := by simp
  -- Rewrite the weighted inner product in coordinates and collapse the weighted residual sum.
  rw [hinner]
  calc
    ∑ i, ω i *
        ⟪e (x - weightedProductDiagonalPoint e p) i,
          e (weightedProductDiagonalPoint e z - weightedProductDiagonalPoint e p) i⟫_ℝ
        = ∑ i, ω i * ⟪e x i - p, z - p⟫_ℝ := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [p]
    _ = ∑ i, ⟪ω i • (e x i - p), z - p⟫_ℝ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [real_inner_smul_left]
    _ = ⟪∑ i, ω i • (e x i - p), z - p⟫_ℝ := by
          rw [sum_inner]
    _ = 0 := by
          rw [hsum_zero]
          simp

/-- Helper for Proposition 29.16: the squared distance to a diagonal competitor splits into the
squared distance to the weighted diagonal point plus the squared diagonal gap. -/
private lemma weightedDiagonalDistanceSqDecomposition
    (e : E ≃ₗ[ℝ] (I → H)) (ω : I → ℝ) (hω_sum : ∑ i, ω i = 1)
    (hinner : ∀ x y : E, ⟪x, y⟫_ℝ = ∑ i, ω i * ⟪e x i, e y i⟫_ℝ)
    (x q : E) (hq : q ∈ weightedProductDiagonal e) :
    dist x q ^ 2 =
      dist x (weightedProductDiagonalPoint e (∑ i, ω i • e x i)) ^ 2 +
        ‖q - weightedProductDiagonalPoint e (∑ i, ω i • e x i)‖ ^ 2 := by
  rcases (mem_weightedProductDiagonal_iff e q).mp hq with ⟨z, hz⟩
  let p : H := ∑ i, ω i • e x i
  have hq_eq : q = weightedProductDiagonalPoint e z := by
    apply e.injective
    simpa [weightedProductDiagonalPoint_apply] using hz
  have horth :
      ⟪x - weightedProductDiagonalPoint e p,
        q - weightedProductDiagonalPoint e p⟫_ℝ = 0 := by
    -- The competitor is a diagonal point, so the residual is orthogonal to its diagonal offset.
    rw [hq_eq]
    simpa [p] using weightedDiagonalResidualInner_eq_zero e ω hω_sum hinner x z
  have hsplit :
      x - q =
        (x - weightedProductDiagonalPoint e p) - (q - weightedProductDiagonalPoint e p) := by
    abel_nf
  -- Expand the squared norm of the difference and kill the cross terms by orthogonality.
  rw [dist_eq_norm, dist_eq_norm, hsplit]
  calc
    ‖(x - weightedProductDiagonalPoint e p) - (q - weightedProductDiagonalPoint e p)‖ ^ 2
        = ⟪(x - weightedProductDiagonalPoint e p) - (q - weightedProductDiagonalPoint e p),
            (x - weightedProductDiagonalPoint e p) - (q - weightedProductDiagonalPoint e p)⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq]
    _ = ⟪x - weightedProductDiagonalPoint e p, x - weightedProductDiagonalPoint e p⟫_ℝ
          - ⟪x - weightedProductDiagonalPoint e p, q - weightedProductDiagonalPoint e p⟫_ℝ
          - ⟪q - weightedProductDiagonalPoint e p, x - weightedProductDiagonalPoint e p⟫_ℝ
          + ⟪q - weightedProductDiagonalPoint e p, q - weightedProductDiagonalPoint e p⟫_ℝ := by
            rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right,
              inner_sub_right]
            ring
    _ = ⟪x - weightedProductDiagonalPoint e p, x - weightedProductDiagonalPoint e p⟫_ℝ
          + ⟪q - weightedProductDiagonalPoint e p, q - weightedProductDiagonalPoint e p⟫_ℝ := by
            simp [horth, real_inner_comm]
    _ = ‖x - weightedProductDiagonalPoint e p‖ ^ 2
          + ‖q - weightedProductDiagonalPoint e p‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- Helper for Proposition 29.16: the diagonal point given by the weighted coordinate sum is a
best approximation of `x` from the weighted diagonal. -/
private lemma constantWeightedCoordinateSum_isBestApproximation
    (e : E ≃ₗ[ℝ] (I → H)) (ω : I → ℝ) (hω_sum : ∑ i, ω i = 1)
    (hinner : ∀ x y : E, ⟪x, y⟫_ℝ = ∑ i, ω i * ⟪e x i, e y i⟫_ℝ)
    (x : E) :
    IsBestApproximation x (weightedProductDiagonal e)
      (weightedProductDiagonalPoint e (∑ i, ω i • e x i)) := by
  let p : H := ∑ i, ω i • e x i
  have hp_mem : weightedProductDiagonalPoint e p ∈ weightedProductDiagonal e := by
    exact weightedProductDiagonalPoint_mem e p
  refine ⟨hp_mem, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hp_mem)⟩
  rw [Metric.le_infDist ⟨weightedProductDiagonalPoint e p, hp_mem⟩]
  intro q hq
  have hdecomp :
      dist x q ^ 2 = dist x (weightedProductDiagonalPoint e p) ^ 2 +
        ‖q - weightedProductDiagonalPoint e p‖ ^ 2 := by
    simpa [p] using weightedDiagonalDistanceSqDecomposition e ω hω_sum hinner x q hq
  have hsq :
      dist x (weightedProductDiagonalPoint e p) ^ 2 ≤ dist x q ^ 2 := by
    nlinarith [sq_nonneg ‖q - weightedProductDiagonalPoint e p‖, hdecomp]
  -- Compare nonnegative square roots to recover the distance inequality.
  exact (sq_le_sq₀ dist_nonneg dist_nonneg).1 hsq

/-- Under the weighted inner-product geometry from Proposition 29.16, the diagonal of constant
coordinate families is a Chebyshev set in `E`. -/
theorem weightedProductDiagonal_isChebyshev
    (e : E ≃ₗ[ℝ] (I → H)) (ω : I → ℝ) (hω_sum : ∑ i, ω i = 1)
    (hinner : ∀ x y : E, ⟪x, y⟫_ℝ = ∑ i, ω i * ⟪e x i, e y i⟫_ℝ) :
    IsChebyshev (weightedProductDiagonal e) := by
  intro x
  let p : H := ∑ i, ω i • e x i
  let pD : E := weightedProductDiagonalPoint e p
  have hp_best : IsBestApproximation x (weightedProductDiagonal e) pD := by
    -- The weighted diagonal point is the explicit best approximation candidate.
    simpa [p, pD] using constantWeightedCoordinateSum_isBestApproximation e ω hω_sum hinner x
  refine ⟨pD, hp_best, ?_⟩
  intro q hq_best
  have hdecomp :
      dist x q ^ 2 = dist x pD ^ 2 + ‖q - pD‖ ^ 2 := by
    simpa [p, pD] using
      weightedDiagonalDistanceSqDecomposition e ω hω_sum hinner x q hq_best.1
  have hsq_eq : dist x q ^ 2 = dist x pD ^ 2 := by
    have hdist_eq : dist x q = dist x pD := by
      rw [hq_best.2, hp_best.2]
    exact congrArg (fun t : ℝ ↦ t ^ 2) hdist_eq
  have hgap_nonpos : ‖q - pD‖ ^ 2 ≤ 0 := by
    nlinarith [hdecomp, hsq_eq]
  have hgap_sq : ‖q - pD‖ ^ 2 = 0 := by
    exact le_antisymm hgap_nonpos (sq_nonneg ‖q - pD‖)
  have hgap : ‖q - pD‖ = 0 := sq_eq_zero_iff.mp hgap_sq
  exact sub_eq_zero.mp (norm_eq_zero.mp hgap)

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type w} [Fintype I]

/-- The weighted barycenter of the coordinates of `x : E` in the model `E ≃ₗ[ℝ] (I → H)`. -/
def weightedCoordinateBarycenter (e : E ≃ₗ[ℝ] (I → H)) (ω : I → ℝ) (x : E) : H :=
  ∑ i, ω i • e x i

/-- Evaluating `weightedCoordinateBarycenter` gives the corresponding finite weighted coordinate
sum. -/
theorem weightedCoordinateBarycenter_eq_sum
    (e : E ≃ₗ[ℝ] (I → H)) (ω : I → ℝ) (x : E) :
    weightedCoordinateBarycenter e ω x = ∑ i, ω i • e x i := by
  -- This is just the defining formula of the weighted coordinate barycenter.
  rfl

/-- Proposition 29.16: let `I` be a nonempty finite index type, let `ω : I → ℝ` satisfy
`ω i ∈ [0, 1]` for every `i` and `∑ i, ω i = 1`, and let `E` be a real Hilbert space identified
with the Cartesian product `(I → H)` through a linear equivalence `e` whose inner product is
`⟪x, y⟫ = ∑ i, ω i * ⟪(e x) i, (e y) i⟫`. Then the metric projection of `x` onto the diagonal set
of constant families is the constant family with value `∑ i, ω i • (e x) i`.

The source's interval hypothesis is stronger than the projection identity itself: once the weighted
inner-product formula is fixed, the public statement only needs the normalization `∑ i, ω i = 1`.
-/
theorem projectionPoint_weightedProductDiagonal_eq_constant_weightedCoordinateBarycenter
    [CompleteSpace E] (e : E ≃ₗ[ℝ] (I → H)) (ω : I → ℝ)
    (hω_sum : ∑ i, ω i = 1)
    (hinner : ∀ x y : E, ⟪x, y⟫_ℝ = ∑ i, ω i * ⟪e x i, e y i⟫_ℝ) (x : E) :
    P[weightedProductDiagonal e, weightedProductDiagonal_isChebyshev e ω hω_sum hinner] x =
      weightedProductDiagonalPoint e (weightedCoordinateBarycenter e ω x) := by
  -- Route correction: use the explicit best-approximation witness, then rewrite the raw weighted
  -- sum to the public barycenter notation.
  symm
  refine eq_projectionPoint_of_isBestApproximation
    (weightedProductDiagonal e)
    (weightedProductDiagonal_isChebyshev e ω hω_sum hinner) ?_
  simpa [weightedCoordinateBarycenter_eq_sum] using
    constantWeightedCoordinateSum_isBestApproximation e ω hω_sum hinner x

end

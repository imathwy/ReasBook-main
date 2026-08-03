import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap17.Proposition_17_48
import BauschkeLean.Chap20.Example_20_34
import BauschkeLean.Chap20.Proposition_20_40
import BauschkeLean.Chap20.Proposition_20_22

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open Filter
open SetValuedOperator
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

noncomputable section

namespace HilbertBasis

local notation "L2" => ℓ²(ℕ, ℝ)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use `0 ≤ β n ≤ 1` to bound `‖β n * x n‖^2` by `‖x n‖^2`, then apply the
-- summability characterization of `Memℓp` for `p = 2`.
/-- The diagonal coordinate multiplier is square-summable on `ℓ²`. -/
private theorem diagonalForward_mem_lp (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : L2) :
    Memℓp (fun n ↦ (β n : ℝ) * x n) 2 := by
  -- TODO: re-express this as `memℓp_gen` for `p = 2` using the termwise estimate
  -- `‖β n * x n‖² ≤ ‖x n‖²`.
  sorry

/-- The diagonal coordinate multiplier on `ℓ²`. -/
private def diagonalForward (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : L2) : L2 :=
  ⟨fun n ↦ (β n : ℝ) * x n, diagonalForward_mem_lp β hβ_le_one x⟩

/-- The diagonal coordinate multiplier preserves addition. -/
private theorem diagonalForward_map_add (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x y : L2) :
    diagonalForward β hβ_le_one (x + y) =
      diagonalForward β hβ_le_one x + diagonalForward β hβ_le_one y := by
  -- Compare the two `ℓ²` vectors coordinatewise; the diagonal multiplier is pointwise additive.
  ext n
  change (β n : ℝ) * (x n + y n) = ((fun n ↦ (β n : ℝ) * x n) + fun n ↦ (β n : ℝ) * y n) n
  simp [mul_add]

/-- The diagonal coordinate multiplier preserves scalar multiplication. -/
private theorem diagonalForward_map_smul (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (a : ℝ) (x : L2) :
    diagonalForward β hβ_le_one (a • x) = a • diagonalForward β hβ_le_one x := by
  -- Compare the two `ℓ²` vectors coordinatewise; scalar multiplication commutes with the weights.
  ext n
  simp [diagonalForward, Pi.smul_apply, mul_assoc, mul_left_comm]

/-- The diagonal coordinate multiplier as a linear map on `ℓ²`. -/
private def diagonalForwardLinearMap (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) : L2 →ₗ[ℝ] L2 where
  toFun := diagonalForward β hβ_le_one
  map_add' := diagonalForward_map_add β hβ_le_one
  map_smul' := diagonalForward_map_smul β hβ_le_one

/-- The diagonal coordinate multiplier has operator norm at most `1`. -/
private theorem norm_diagonalForward_le (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : L2) :
    ‖diagonalForward β hβ_le_one x‖ ≤ 1 * ‖x‖ := by
  -- TODO: compare the squared `ℓ²` norms coordinatewise and then take square roots.
  sorry

/-- The diagonal coordinate multiplier as a continuous linear map on `ℓ²`. -/
private def diagonalForwardContinuousLinearMap (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) : L2 →L[ℝ] L2 :=
  (diagonalForwardLinearMap β hβ_le_one).mkContinuous 1
    (norm_diagonalForward_le β hβ_le_one)

section Forward

variable (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
variable (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1)

/-- Example 20.41. The diagonal operator `B`, written as a bounded linear operator in
Hilbert-basis coordinates. -/
def diagonalForwardOperator : H →L[ℝ] H :=
  let e : H ≃L[ℝ] L2 := b.repr.toContinuousLinearEquiv
  e.symm.toContinuousLinearMap.comp
    ((diagonalForwardContinuousLinearMap β hβ_le_one).comp e.toContinuousLinearMap)

/-- Helper for Example 20.41: the forward diagonal operator acts on `b.repr` by
coordinatewise multiplication with the weights `β`. -/
@[simp] theorem repr_diagonalForwardOperator_apply
    (x : H) (n : ℕ) :
    b.repr (diagonalForwardOperator b β hβ_le_one x) n =
      (β n : ℝ) * b.repr x n := by
  -- Unfold the transported operator and evaluate the diagonal multiplier in `ℓ²` coordinates.
  simp [diagonalForwardOperator, diagonalForwardContinuousLinearMap, diagonalForwardLinearMap,
    diagonalForward, ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply]

-- Proof sketch: in Hilbert-basis coordinates, `b n` is the `n`th unit vector, so the diagonal
-- multiplier scales that coordinate by `β n` and leaves all others zero.
/-- The weighted diagonal operator sends the basis vector `b n` to `β n • b n`. -/
theorem diagonalForwardOperator_apply_basis (n : ℕ) :
    diagonalForwardOperator b β hβ_le_one (b n) = (β n : ℝ) • b n := by
  -- Compare the two vectors in Hilbert-basis coordinates and isolate the unique nonzero slot.
  apply b.repr.injective
  ext m
  by_cases hm : m = n
  · subst hm
    rw [repr_diagonalForwardOperator_apply]
    simp [HilbertBasis.repr_apply_apply]
  · rw [repr_diagonalForwardOperator_apply]
    have horth : ⟪b m, b n⟫_ℝ = 0 := b.orthonormal.inner_eq_zero hm
    simp [HilbertBasis.repr_apply_apply, horth]

-- Proof sketch: transport `diagonalForwardOperator` to the diagonal multiplier on `ℓ²`, whose
-- matrix in the standard basis has real diagonal entries `β n`; such a diagonal operator equals
-- its adjoint, and conjugation by the Hilbert-basis equivalence preserves self-adjointness.
/-- The diagonal operator `B` is self-adjoint. -/
theorem diagonalForwardOperator_isSelfAdjoint [CompleteSpace H] :
    IsSelfAdjoint (diagonalForwardOperator b β hβ_le_one) := by
  -- Expand both inner products in Hilbert-basis coordinates and commute the real diagonal weights.
  refine LinearMap.IsSymmetric.isSelfAdjoint ?_
  intro x y
  calc
    ⟪diagonalForwardOperator b β hβ_le_one x, y⟫_ℝ
        = ∑' n, (b.repr (diagonalForwardOperator b β hβ_le_one x) n) * (b.repr y n) := by
            simpa [HilbertBasis.repr_apply_apply, real_inner_comm] using
              (b.tsum_inner_mul_inner (diagonalForwardOperator b β hβ_le_one x) y).symm
    _ = ∑' n, ((β n : ℝ) * b.repr x n) * (b.repr y n) := by
          refine tsum_congr fun n ↦ ?_
          rw [repr_diagonalForwardOperator_apply]
    _ = ∑' n, (b.repr x n) * ((β n : ℝ) * b.repr y n) := by
          refine tsum_congr fun n ↦ ?_
          ring
    _ = ∑' n, (b.repr x n) * (b.repr (diagonalForwardOperator b β hβ_le_one y) n) := by
          refine tsum_congr fun n ↦ ?_
          rw [repr_diagonalForwardOperator_apply]
    _ = ⟪x, diagonalForwardOperator b β hβ_le_one y⟫_ℝ := by
          simpa [HilbertBasis.repr_apply_apply, real_inner_comm] using
            b.tsum_inner_mul_inner x (diagonalForwardOperator b β hβ_le_one y)

-- Proof sketch: in Hilbert-basis coordinates, `diagonalForwardOperator` is multiplication by the
-- nonnegative diagonal sequence `β`; hence `⟪B x, x⟫ = ∑ β n * ‖x n‖^2 ≥ 0`.
/-- The diagonal operator `B` is monotone. -/
theorem diagonalForwardOperator_isMonotone :
    (diagonalForwardOperator b β hβ_le_one).toSetValuedOperator.IsMonotone := by
  -- TODO: prove the quadratic-form formula
  -- `⟪B x, x⟫ = ∑' n, (β n : ℝ) * ‖b.repr x n‖^2` and conclude by positivity.
  sorry

-- Proof sketch: Example 20.34 applies to bounded linear operators. Once `B` is identified as a
-- monotone bounded linear map, its associated singleton-valued set-valued operator is maximally
-- monotone.
/-- The diagonal operator `B` is maximally monotone as a singleton-valued set-valued operator. -/
theorem diagonalForwardOperator_isMaximallyMonotone :
    Maximal IsMonotone
      (diagonalForwardOperator b β hβ_le_one).toSetValuedOperator := by
  -- Route correction: once monotonicity is available, Example 20.34 upgrades the bounded linear
  -- map directly to maximal monotonicity.
  have hmonoLinear :
      (diagonalForwardOperator b β hβ_le_one).toLinearMap.IsMonotone :=
    (LinearMap.toSetValuedOperator_isMonotone_iff
      (diagonalForwardOperator b β hβ_le_one).toLinearMap).1
      (diagonalForwardOperator_isMonotone b β hβ_le_one)
  exact
    ContinuousLinearMap.toSetValuedOperator_isMaximallyMonotone_of_isMonotone
      (diagonalForwardOperator b β hβ_le_one) hmonoLinear

end Forward

section Inverse

variable (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)

/-- The inverse diagonal coordinate condition holds at `0`. -/
private theorem diagonalInverseDomain_zero_mem :
    Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr (0 : H) n) 2 := by
  -- The Hilbert-basis coordinates of `0` vanish, so the inverse-weighted sequence is zero.
  convert (zero_memℓp : Memℓp (0 : ℕ → ℝ) 2) using 1
  ext n
  rw [map_zero, lp.coeFn_zero, Pi.zero_apply, mul_zero]

/-- The inverse diagonal coordinate condition is closed under addition. -/
private theorem diagonalInverseDomain_add_mem {x y : H}
    (hx : Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr x n) 2)
    (hy : Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr y n) 2) :
    Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr (x + y) n) 2 := by
  -- Rewrite the weighted coordinates of `x + y` as the pointwise sum and use `Memℓp.add`.
  have hsum :
      Memℓp (fun n ↦ (β n : ℝ)⁻¹ * (b.repr x n + b.repr y n)) 2 := by
    simpa [mul_add] using hx.add hy
  simpa [map_add] using hsum

/-- The inverse diagonal coordinate condition is closed under scalar multiplication. -/
private theorem diagonalInverseDomain_smul_mem (a : ℝ) {x : H}
    (hx : Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr x n) 2) :
    Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr (a • x) n) 2 := by
  -- Pull the scalar outside the weighted coordinates and reuse closure of `Memℓp` under scaling.
  simpa [map_smul, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hx.const_mul a

/-- The dense proper linear subspace that forms the domain of the inverse diagonal operator. -/
def diagonalInverseDomain : Submodule ℝ H where
  carrier := {x | Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr x n) 2}
  zero_mem' := diagonalInverseDomain_zero_mem b β
  add_mem' := fun {_} {_} hx hy ↦ diagonalInverseDomain_add_mem b β hx hy
  smul_mem' := fun a {_} hx ↦ diagonalInverseDomain_smul_mem b β a hx

/-- Membership in the inverse diagonal domain means square summability of the inverse-weighted
coordinate sequence. -/
@[simp] theorem mem_diagonalInverseDomain (x : H) :
    x ∈ diagonalInverseDomain b β ↔ Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr x n) 2 :=
    Iff.rfl

/-- The inverse-weighted coordinate sequence attached to a domain element. -/
private def diagonalInverseCoordinates (x : diagonalInverseDomain b β) : L2 :=
  ⟨fun n ↦ (β n : ℝ)⁻¹ * b.repr x.1 n, x.2⟩

/-- Helper for Example 20.41: inverse-weighted coordinates are additive on the inverse domain. -/
private theorem diagonalInverseCoordinates_add
    (x y : diagonalInverseDomain b β) :
    diagonalInverseCoordinates b β (x + y) =
      diagonalInverseCoordinates b β x + diagonalInverseCoordinates b β y := by
  -- Compare the two `ℓ²` vectors coordinatewise after expanding `repr (x + y)`.
  ext n
  change (β n : ℝ)⁻¹ * b.repr ((x : H) + (y : H)) n =
      (β n : ℝ)⁻¹ * b.repr (x : H) n + (β n : ℝ)⁻¹ * b.repr (y : H) n
  rw [map_add, lp.coeFn_add, Pi.add_apply, mul_add]

/-- The inverse diagonal coordinate map preserves addition. -/
private theorem diagonalInverseLinearMap_map_add
    (x y : diagonalInverseDomain b β) :
    b.repr.symm (diagonalInverseCoordinates b β (x + y)) =
      b.repr.symm (diagonalInverseCoordinates b β x) +
        b.repr.symm (diagonalInverseCoordinates b β y) := by
  -- First normalize the inverse-weighted coordinates, then use linearity of `repr.symm`.
  rw [diagonalInverseCoordinates_add]
  exact map_add _ _ _

/-- The inverse diagonal coordinate map preserves scalar multiplication. -/
private theorem diagonalInverseLinearMap_map_smul
    (a : ℝ) (x : diagonalInverseDomain b β) :
    b.repr.symm (diagonalInverseCoordinates b β (a • x)) =
      a • b.repr.symm (diagonalInverseCoordinates b β x) := by
  -- Apply `repr` and compare the resulting `ℓ²` coordinates termwise.
  apply b.repr.injective
  ext n
  simp [diagonalInverseCoordinates, map_smul, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- The linear map `A` on its dense proper domain. -/
def diagonalInverseLinearMap : diagonalInverseDomain b β →ₗ[ℝ] H where
  toFun := fun x ↦ b.repr.symm (diagonalInverseCoordinates b β x)
  map_add' := diagonalInverseLinearMap_map_add b β
  map_smul' := diagonalInverseLinearMap_map_smul b β

/-- The source-facing inverse operator `A = B⁻¹`. -/
def diagonalInverseOperator (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) : SetValuedOperator H H :=
  ((diagonalForwardOperator b β hβ_le_one).toSetValuedOperator)⁻¹

/-- Helper for Example 20.41: the inverse diagonal map acts on `b.repr` by
coordinatewise multiplication with the inverse weights `β⁻¹`. -/
@[simp] theorem repr_diagonalInverseLinearMap_apply
    (x : diagonalInverseDomain b β) (n : ℕ) :
    b.repr (diagonalInverseLinearMap b β x) n =
      (β n : ℝ)⁻¹ * b.repr (x : H) n := by
  -- Unfold the inverse coordinate model and read off the `n`th coordinate after applying `repr`.
  simp [diagonalInverseLinearMap, diagonalInverseCoordinates]

/-- Helper for Example 20.41: every image point `B x` satisfies the inverse weighted
coordinate condition defining `dom A`. -/
private theorem diagonalForwardOperator_mem_inverseDomain
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : H) :
    diagonalForwardOperator b β hβ_le_one x ∈ diagonalInverseDomain b β := by
  -- Rewrite the inverse-weighted coordinates of `B x` back to the original `ℓ²` coordinates.
  rw [mem_diagonalInverseDomain]
  have hcoords :
      (fun n ↦ (β n : ℝ)⁻¹ * b.repr (diagonalForwardOperator b β hβ_le_one x) n) = b.repr x := by
    funext n
    rw [repr_diagonalForwardOperator_apply]
    have hβn0_nnreal : (β n : NNReal) ≠ 0 := Units.ne_zero (β n)
    have hβn0 : (β n : ℝ) ≠ 0 := by
      exact_mod_cast hβn0_nnreal
    rw [← mul_assoc, inv_mul_cancel₀ hβn0, one_mul]
  have hxrepr : Memℓp (fun n ↦ (b.repr x : L2) n) 2 := (b.repr x).2
  simpa [hcoords] using hxrepr

-- Proof sketch: in Hilbert-basis coordinates, `B` maps `x` to the sequence `β n * x n`, so its
-- range consists exactly of those vectors whose inverse-weighted coordinates remain square
-- summable. That is precisely the defining condition for `diagonalInverseDomain`.
/-- Every value of the diagonal operator `B` lies in the domain of its inverse `A`. -/
theorem diagonalForwardOperator_mem_diagonalInverseDomain
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : H) :
    diagonalForwardOperator b β hβ_le_one x ∈ diagonalInverseDomain b β := by
  -- Use the direct coordinate computation instead of routing through the range theorem.
  exact diagonalForwardOperator_mem_inverseDomain b β hβ_le_one x

-- Proof sketch: in coordinates, `A` multiplies by `β n⁻¹` on the range of `B`, so applying `A`
-- after `B` cancels the diagonal weights coordinatewise.
/-- On the range of `B`, the inverse diagonal operator `A` satisfies `A (B x) = x`. -/
theorem diagonalInverseLinearMap_apply_diagonalForwardOperator
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : H) :
    diagonalInverseLinearMap b β
      ⟨diagonalForwardOperator b β hβ_le_one x,
        diagonalForwardOperator_mem_diagonalInverseDomain b β hβ_le_one x⟩ = x := by
  -- Compare the two vectors in Hilbert-basis coordinates and cancel `β n` pointwise.
  apply b.repr.injective
  ext n
  rw [repr_diagonalInverseLinearMap_apply, repr_diagonalForwardOperator_apply]
  have hβn0_nnreal : (β n : NNReal) ≠ 0 := Units.ne_zero (β n)
  have hβn0 : (β n : ℝ) ≠ 0 := by
    exact_mod_cast hβn0_nnreal
  rw [← mul_assoc, inv_mul_cancel₀ hβn0, one_mul]

-- Proof sketch: if `x` already lies in `diagonalInverseDomain`, then its coordinates are
-- inverse-weighted square summable. Applying `A` multiplies by `β n⁻¹`, and applying `B` then
-- multiplies by `β n`, so the two maps cancel on the domain.
/-- On its natural domain, the inverse diagonal operator `A` satisfies `B (A x) = x`. -/
theorem diagonalForwardOperator_apply_diagonalInverseLinearMap
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : diagonalInverseDomain b β) :
    diagonalForwardOperator b β hβ_le_one (diagonalInverseLinearMap b β x) = x := by
  -- Compare the two vectors in Hilbert-basis coordinates and cancel `β n` pointwise.
  apply b.repr.injective
  ext n
  rw [repr_diagonalForwardOperator_apply, repr_diagonalInverseLinearMap_apply]
  have hβn0_nnreal : (β n : NNReal) ≠ 0 := Units.ne_zero (β n)
  have hβn0 : (β n : ℝ) ≠ 0 := by
    exact_mod_cast hβn0_nnreal
  rw [← mul_assoc, mul_inv_cancel₀ hβn0, one_mul]

-- Proof sketch: in Hilbert-basis coordinates, `B` maps `x` to the sequence `β n * x n`, so its
-- range consists exactly of those vectors whose inverse-weighted coordinates remain square
-- summable. That is precisely the defining condition for `diagonalInverseDomain`.
/-- The coordinate domain of the inverse diagonal operator is exactly the range of `B`. -/
theorem diagonalInverseDomain_eq_range_diagonalForwardOperator
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    diagonalInverseDomain b β = (diagonalForwardOperator b β hβ_le_one).toLinearMap.range := by
  -- Use the two cancellation identities to identify the inverse domain with the range of `B`.
  ext x
  constructor
  · intro hx
    refine ⟨diagonalInverseLinearMap b β ⟨x, hx⟩, ?_⟩
    simpa using diagonalForwardOperator_apply_diagonalInverseLinearMap b β hβ_le_one ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    exact diagonalForwardOperator_mem_inverseDomain b β hβ_le_one y

-- Proof sketch: the previous range and inverse laws identify the singleton-valued operator
-- induced by `A` with the graph-inverse of the singleton-valued operator induced by `B`.
/-- The source-facing inverse operator agrees with the coordinate presentation on its natural
domain. -/
theorem diagonalInverseOperator_eq_ofFunction
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    diagonalInverseOperator b β hβ_le_one =
      ofFunction (diagonalInverseDomain b β : Set H) (diagonalInverseLinearMap b β) := by
  -- Compare the two set-valued operators pointwise by translating inverse-graph membership.
  ext x y
  constructor
  · intro hy
    rw [diagonalInverseOperator, SetValuedOperator.mem_inverse_iff] at hy
    have hy' : x = diagonalForwardOperator b β hβ_le_one y := by
      simpa [ContinuousLinearMap.toSetValuedOperator] using hy
    have hx : x ∈ diagonalInverseDomain b β := by
      simpa [hy'] using diagonalForwardOperator_mem_inverseDomain b β hβ_le_one y
    refine ⟨hx, ?_⟩
    have hsub :
        (⟨x, hx⟩ : diagonalInverseDomain b β) =
          ⟨diagonalForwardOperator b β hβ_le_one y,
            diagonalForwardOperator_mem_inverseDomain b β hβ_le_one y⟩ := by
      exact Subtype.ext hy'
    simpa [hsub] using
      (diagonalInverseLinearMap_apply_diagonalForwardOperator b β hβ_le_one y).symm
  · rintro ⟨hx, rfl⟩
    rw [diagonalInverseOperator, SetValuedOperator.mem_inverse_iff]
    simpa [ContinuousLinearMap.toSetValuedOperator] using
      (diagonalForwardOperator_apply_diagonalInverseLinearMap b β hβ_le_one ⟨x, hx⟩).symm

/-- The inverse operator `A = B⁻¹` satisfies `dom A = ran B`. -/
theorem diagonalInverseOperator_dom_eq_range_diagonalForwardOperator
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    (diagonalInverseOperator b β hβ_le_one).dom =
      (diagonalForwardOperator b β hβ_le_one).toLinearMap.range := by
  -- This is the canonical `dom_inverse = range` owner specialized to the forward diagonal map.
  rw [diagonalInverseOperator, SetValuedOperator.dom_inverse,
    ContinuousLinearMap.toSetValuedOperator_range]

/-- The inverse diagonal operator is at most single-valued. -/
theorem diagonalInverseOperator_isAtMostSingleValued
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    IsAtMostSingleValued (diagonalInverseOperator b β hβ_le_one) := by
  -- Identify `A` with the singleton-valued operator attached to the inverse linear map.
  rw [diagonalInverseOperator_eq_ofFunction b β hβ_le_one]
  exact SetValuedOperator.isAtMostSingleValued_ofFunction
    (diagonalInverseDomain b β : Set H) (diagonalInverseLinearMap b β)

-- Proof sketch: the previous bridge theorem identifies the inverse diagonal operator with `B⁻¹`;
-- Proposition 20.22 then transports maximal monotonicity from the maximally monotone operator
-- induced by `B`.
/-- The inverse diagonal operator is maximally monotone under the weighted Hilbert-basis
hypotheses. -/
theorem diagonalInverseOperator_isMaximallyMonotone (b : HilbertBasis ℕ ℝ H)
    (β : ℕ → NNRealˣ) (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    Maximal IsMonotone (diagonalInverseOperator b β hβ_le_one) := by
  -- Proposition 20.22 transports maximal monotonicity across graph inversion.
  simpa [diagonalInverseOperator] using
    (SetValuedOperator.Maximal.inverse
      (diagonalForwardOperator_isMaximallyMonotone b β hβ_le_one))

section

variable [CompleteSpace H]

-- Proof sketch: in Hilbert-basis coordinates, `b n` is the `n`th unit vector, so the
-- inverse-weighted sequence is supported only at `n`.
/-- Helper for Example 20.41: every basis vector belongs to the inverse diagonal domain. -/
theorem basis_mem_diagonalInverseDomain (n : ℕ) :
    b n ∈ diagonalInverseDomain b β := by
  -- Rewrite the inverse-weighted coordinates of `b n` as the single supported sequence.
  rw [mem_diagonalInverseDomain]
  have hsingle :
      (fun m ↦ (β m : ℝ)⁻¹ * b.repr (b n) m) =
        fun m ↦ (lp.single (E := fun _ : ℕ ↦ ℝ) 2 n ((β n : ℝ)⁻¹) : L2) m := by
    funext m
    by_cases hm : m = n
    · subst hm
      simp [HilbertBasis.repr_self]
    · simp [HilbertBasis.repr_self, hm]
  simpa [hsingle] using
    (show Memℓp
        (fun m ↦ (lp.single (E := fun _ : ℕ ↦ ℝ) 2 n ((β n : ℝ)⁻¹) : L2) m) 2 from
      (lp.single (E := fun _ : ℕ ↦ ℝ) 2 n ((β n : ℝ)⁻¹)).2)

-- Proof sketch: once `b n` is known to lie in the domain, applying the inverse diagonal map
-- multiplies the unique nonzero basis coordinate by `(β n)⁻¹`.
/-- Helper for Example 20.41: the inverse diagonal map sends `b n` to `(β n)⁻¹ • b n`. -/
theorem diagonalInverseLinearMap_apply_basis (n : ℕ) :
    diagonalInverseLinearMap b β ⟨b n, basis_mem_diagonalInverseDomain b β n⟩ =
      (β n : ℝ)⁻¹ • b n := by
  -- Compare both sides in Hilbert-basis coordinates, where only the `n`th coordinate survives.
  apply b.repr.injective
  ext m
  rw [repr_diagonalInverseLinearMap_apply, map_smul, HilbertBasis.repr_self]
  by_cases hm : m = n
  · subst hm
    simp
  · simp [lp.single_apply, hm]

-- Proof sketch: for `β n > 0`, the inverse-weighted coordinates of `β n • b n` are zero except
-- at the `n`th slot, where the value is `1`; this is the standard basis vector of `ℓ²`.
/-- Each weighted basis vector `β n • b n` belongs to the inverse diagonal domain. -/
theorem smul_basis_mem_diagonalInverseDomain (n : ℕ) :
    (β n : ℝ) • b n ∈ diagonalInverseDomain b β := by
  -- The inverse diagonal domain is a submodule, so it is closed under scalar multiplication.
  exact (diagonalInverseDomain b β).smul_mem (β n : ℝ)
    (basis_mem_diagonalInverseDomain b β n)

-- Proof sketch: the vectors `β n • b n` all lie in the domain and span the same linear span as
-- the basis vectors `b n`, since each `β n` is nonzero. The closed span of the Hilbert basis is
-- all of `H`, so the domain is dense.
/-- The inverse diagonal domain is dense when all weights are strictly positive. -/
theorem diagonalInverseDomain_dense :
    Dense (diagonalInverseDomain b β : Set H) := by
  -- Once the basis vectors lie in the domain, the dense span of the Hilbert basis sits inside it.
  have hspan :
      Submodule.span ℝ (Set.range b) ≤ diagonalInverseDomain b β := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact basis_mem_diagonalInverseDomain b β n
  have hdenseSpan : Dense ((Submodule.span ℝ (Set.range b) : Set H)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    simpa using b.dense_span
  exact Dense.mono (show ((Submodule.span ℝ (Set.range b) : Submodule ℝ H) : Set H) ⊆
      diagonalInverseDomain b β from hspan) hdenseSpan

-- Proof sketch: if the inverse diagonal domain were all of `H`, then every basis vector would lie
-- in it, so `‖(β n)⁻¹ • b n‖ = β n⁻¹` would stay bounded. This contradicts `β n → 0`, which forces
-- `β n⁻¹ → +∞` along the basis vectors.
/-- The inverse diagonal domain is proper when the positive weights decrease to `0`. -/
theorem diagonalInverseDomain_ne_univ
    (hβ_tendsto : Tendsto (fun n ↦ (β n : ℝ)) atTop (𝓝 0)) :
    (diagonalInverseDomain b β : Set H) ≠ Set.univ := sorry

-- Proof sketch: a dense linear subspace with nonempty interior is all of `H`; since the domain is
-- dense and proper, its interior must be empty.
/-- A dense proper linear subspace of the Hilbert space has empty interior, applied to the inverse
diagonal domain. -/
theorem diagonalInverseDomain_interior_eq_empty
    (hdense : Dense (diagonalInverseDomain b β : Set H))
    (hproper : (diagonalInverseDomain b β : Set H) ≠ Set.univ) :
    interior (diagonalInverseDomain b β : Set H) = ∅ := by
  -- A submodule with nonempty interior is the whole space, contradicting properness.
  by_contra hinterior
  have hnonempty : (interior (diagonalInverseDomain b β : Set H)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hinterior
  have htop : diagonalInverseDomain b β = ⊤ :=
    Submodule.eq_top_of_nonempty_interior' _ hnonempty
  have hfull : (diagonalInverseDomain b β : Set H) = Set.univ := by
    simpa using congrArg (fun S : Submodule ℝ H ↦ (S : Set H)) htop
  exact hproper hfull

-- Proof sketch: in Hilbert-basis coordinates, both inner products expand as the same series
-- `∑ (β n : ℝ)⁻¹ * x n * y n`, so the inverse diagonal map is symmetric on its domain.
/-- In Hilbert-basis coordinates, the inverse diagonal map is symmetric on its natural domain. -/
theorem diagonalInverseLinearMap_isSymmetric
    (x y : diagonalInverseDomain b β) :
    ⟪(x : H), diagonalInverseLinearMap b β y⟫_ℝ =
      ⟪diagonalInverseLinearMap b β x, (y : H)⟫_ℝ := by
  -- TODO: finish the coordinate proof by expanding both inner products with
  -- `HilbertBasis.tsum_inner_mul_inner` and rewriting with
  -- `repr_diagonalInverseLinearMap_apply`.
  sorry

-- Proof sketch: in coordinates, `diagonalInverseLinearMap` multiplies by the positive sequence
-- `(β n : ℝ)⁻¹`, so the pointwise monotonicity inequality is a sum of nonnegative terms.
/-- The inverse diagonal map is monotone on its natural domain. -/
theorem diagonalInverseLinearMap_isMonotone :
    (ofFunction (diagonalInverseDomain b β : Set H)
      (diagonalInverseLinearMap b β)).IsMonotone := by
  -- TODO: reduce the monotonicity pairing to `z := x - y` and evaluate
  -- `⟪z, A z⟫` coordinatewise using `repr_diagonalInverseLinearMap_apply`.
  sorry

-- Proof sketch: Proposition 20.40 (2) applies directly to the primitive data
-- `diagonalInverseDomain b β` and `diagonalInverseLinearMap b β`; the only input is that the
-- inverse diagonal map is symmetric and monotone, which uses positivity of `(β n : ℝ)⁻¹` but not
-- the forward-operator bound `β n ≤ 1`.
/-- Helper for Example 20.41: affine real functions, viewed in `EReal`, belong to `Γ(ℝ)`. -/
private theorem realAffineMemGamma (c : ℝ) :
    (fun t : ℝ ↦ ((t - c : ℝ) : EReal)) ∈ gamma ℝ := by
  -- The scalar affine model is exactly Jensen linearity plus continuity.
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    change (((a * x + (1 - a) * y - c : ℝ) : ℝ) : EReal) ≤
      (a : EReal) * ((x - c : ℝ) : EReal) + (1 - a : EReal) * ((y - c : ℝ) : EReal)
    exact le_of_eq <| by
      have hreal : a * x + (1 - a) * y - c = a * (x - c) + (1 - a) * (y - c) := by
        ring
      exact_mod_cast hreal
  · simpa [Function.comp] using
      (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)).lowerSemicontinuous

/-- Helper for Example 20.41: each affine branch of the inverse supremal potential belongs to
`Γ(H)`. -/
private theorem diagonalInversePotentialBranch_memGamma
    (y : diagonalInverseDomain b β) :
    (fun x : H ↦
      (((⟪x, diagonalInverseLinearMap b β y⟫_ℝ -
          (1 / 2 : ℝ) * ⟪(y : H), diagonalInverseLinearMap b β y⟫_ℝ : ℝ) : EReal))) ∈ gamma H := by
  -- Compose the scalar affine model with the continuous linear functional `x ↦ ⟪x, A y⟫`.
  have hcomp :=
    mem_gamma_comp_continuousLinearMap
      (fun t : ℝ ↦
        ((t - ((1 / 2 : ℝ) * ⟪(y : H), diagonalInverseLinearMap b β y⟫_ℝ) : ℝ) : EReal))
      (innerSL ℝ (diagonalInverseLinearMap b β y))
      (realAffineMemGamma
        ((1 / 2 : ℝ) * ⟪(y : H), diagonalInverseLinearMap b β y⟫_ℝ))
  simpa [Function.comp, innerSL_apply_apply, real_inner_comm] using hcomp

/-- The canonical potential attached to the inverse diagonal operator belongs to `Γ₀(H)`. -/
theorem diagonalInversePotential_mem_gammaZero :
    supremalPotential
        (diagonalInverseDomain b β) (diagonalInverseLinearMap b β) ∈ Γ₀(H) := by
  -- TODO: the clean proof either rebuilds the affine-branch API locally, because the file cannot
  -- access the private owners from `Proposition_20_40`, or adds the missing public bridge.
  sorry

-- Proof sketch: apply Proposition 20.40 (3) to the subspace `diagonalInverseDomain b β` and the
-- symmetric linear map `diagonalInverseLinearMap b β`; the needed maximal monotonicity of `A`
-- comes from `diagonalInverseOperator_isMaximallyMonotone`, which identifies its graph with the
-- subdifferential of the associated supremal potential.
/-- The subdifferential of the canonical potential is exactly the inverse diagonal operator. -/
theorem subdifferential_diagonalInversePotential_eq
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1)
    :
    ∂ (supremalPotential
      (diagonalInverseDomain b β) (diagonalInverseLinearMap b β)) =
        diagonalInverseOperator b β hβ_le_one := by
  -- First use Proposition 20.40 in the canonical `ofFunction` form, then rewrite back to `A`.
  have hmax :
      Maximal IsMonotone
        (ofFunction (diagonalInverseDomain b β : Set H) (diagonalInverseLinearMap b β)) := by
    simpa [diagonalInverseOperator_eq_ofFunction b β hβ_le_one] using
      (diagonalInverseOperator_isMaximallyMonotone b β hβ_le_one)
  rw [diagonalInverseOperator_eq_ofFunction b β hβ_le_one]
  exact SetValuedOperator.subdifferential_supremalPotential_eq
    (D := diagonalInverseDomain b β) (T := diagonalInverseLinearMap b β)
    (diagonalInverseLinearMap_isSymmetric b β)
    hmax

/-- For the inverse diagonal operator, the canonical potential is finite exactly
on the inverse-domain subspace. -/
theorem effectiveDomain_diagonalInversePotential_eq :
    effectiveDomain
        (supremalPotential
          (diagonalInverseDomain b β) (diagonalInverseLinearMap b β)) =
      (diagonalInverseDomain b β : Set H) := sorry

-- Proof sketch: for a linear subspace `D`, the translated set `D - {x}` is again `D` at every
-- point `x ∈ D`, so `x ∈ core D` would force `cone D = univ`. For a proper submodule this is
-- impossible, because `cone D = D`.
/-- The inverse diagonal domain has empty algebraic core as soon as it is a proper subspace. -/
theorem diagonalInverseDomain_core_eq_empty
    (hproper : (diagonalInverseDomain b β : Set H) ≠ Set.univ) :
    Set.core (diagonalInverseDomain b β : Set H) = ∅ := by
  -- Route correction: use the defining cone criterion for `core` and the fact that a translated
  -- submodule is itself.
  ext x
  constructor
  · intro hx
    rcases Set.mem_core_iff.mp hx with ⟨hxD, hcone⟩
    have htranslate :
        ((diagonalInverseDomain b β : Set H) - ({x} : Set H)) =
          (diagonalInverseDomain b β : Set H) := by
      ext y
      constructor
      · rintro ⟨z, hz, w, hw, hzw⟩
        rw [Set.mem_singleton_iff] at hw
        subst w
        have hy : z - x ∈ diagonalInverseDomain b β :=
          (diagonalInverseDomain b β).sub_mem hz hxD
        simpa [hzw] using hy
      · intro hy
        refine Set.mem_sub.2 ?_
        refine ⟨y + x, (diagonalInverseDomain b β).add_mem hy hxD, x, by simp, ?_⟩
        abel
    have hfull : (diagonalInverseDomain b β : Set H) = Set.univ := by
      rw [htranslate, cone_eq_self_of_submodule] at hcone
      exact hcone
    exact (hproper hfull).elim
  · intro hx
    exact False.elim (Set.notMem_empty x hx)

-- Proof sketch: if the source `]-∞,+∞]`-valued potential were Gâteaux differentiable at some `x`,
-- then the canonical Chapter 17 owner theorem would place `x` in
-- `core (effectiveDomain f)`. For this diagonal inverse example, the effective domain is exactly
-- `diagonalInverseDomain b β`, while the empty-interior hypothesis forces that submodule to be
-- proper, hence to have empty algebraic core. This contradiction rules out Gâteaux
-- differentiability at every point.
/-- The canonical potential of the inverse diagonal map is nowhere Gâteaux differentiable
in the source Chapter 17 `]-∞,+∞]`-valued sense once the inverse diagonal domain has empty
interior. -/
theorem diagonalInversePotential_nowhere_gateauxDifferentiable
    (hinterior : interior (diagonalInverseDomain b β : Set H) = ∅)
    (x : H) :
    ¬ GateauxDifferentiableAt
      (supremalPotential
        (diagonalInverseDomain b β) (diagonalInverseLinearMap b β)) x := by
  intro hdiff
  -- The `Γ₀` package supplies convexity of the canonical potential on its effective domain.
  have hgamma :
      supremalPotential
          (diagonalInverseDomain b β) (diagonalInverseLinearMap b β) ∈ Γ₀(H) :=
    diagonalInversePotential_mem_gammaZero b β
  have hconv :
      ConvexOn
        (supremalPotential
          (diagonalInverseDomain b β) (diagonalInverseLinearMap b β))
        (effectiveDomain
          (supremalPotential
            (diagonalInverseDomain b β) (diagonalInverseLinearMap b β))) :=
    (mem_gammaZero_iff.mp hgamma).2
  -- Proposition 17.48 places every Gâteaux differentiability point in the algebraic core.
  have hxcore :
      x ∈ Set.core
        (effectiveDomain
          (supremalPotential
            (diagonalInverseDomain b β) (diagonalInverseLinearMap b β))) :=
    ERealFunction.mem_core_effectiveDomain_of_convexOn_of_gateauxDifferentiableAt
      (supremalPotential
        (diagonalInverseDomain b β) (diagonalInverseLinearMap b β))
      hconv hdiff
  have hproper : (diagonalInverseDomain b β : Set H) ≠ Set.univ := by
    intro hfull
    have hunit : interior (diagonalInverseDomain b β : Set H) = Set.univ := by
      simpa [hfull] using (show interior (Set.univ : Set H) = Set.univ by simp)
    rw [hinterior] at hunit
    exact Set.empty_ne_univ hunit
  have hcoreEmpty :
      Set.core (diagonalInverseDomain b β : Set H) = ∅ :=
    diagonalInverseDomain_core_eq_empty b β hproper
  rw [effectiveDomain_diagonalInversePotential_eq b β, hcoreEmpty] at hxcore
  simpa using hxcore

end

end Inverse

end HilbertBasis

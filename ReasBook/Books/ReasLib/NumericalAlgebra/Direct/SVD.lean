import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import ReasLib.NumericalAlgebra.Basics.Orthogonality

/-!
# Singular Value Decomposition for Linear Map

## Main Results

This file contains the following results of the singular value decomposition theorem
* `singular_value_decomposition` : The singular value decomposition theorem for linear map
-/

namespace LinearMap

variable {𝕜 V W : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

open InnerProductSpace ContinuousLinearMap Module LinearMap Submodule NNReal RCLike Matrix

/-- Define Operator Norm for LinearMap between FiniteDimensional Space
-/
@[simp]
noncomputable def opNorm [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) : ℝ := ‖toContinuousLinearMap T‖


/--
For any linear map T between finite-dimensional inner product spaces, there exists a constant C
such that:
1. The norm difference of outputs is bounded by their distance (Lipschitz continuity)
2. The operator is bounded by C times the input difference
This implies the norm map v ↦ ‖T v‖ is continuous.
-/
lemma norm_sub_le_of_linear_map [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) :
    ∃ C ≥ 0, ∀ v₁ v₂ : V, |‖T v₁‖ - ‖T v₂‖| ≤ ‖T v₁ - T v₂‖ ∧ ‖T v₁ - T v₂‖ ≤ C * ‖v₁ - v₂‖ := by
  have first_ineq : ∀ v₁ v₂ : V, |‖T v₁‖ - ‖T v₂‖| ≤ ‖T v₁ - T v₂‖ := by
    intro v₁ v₂
    exact abs_norm_sub_norm_le (T v₁) (T v₂)
  let C := ‖toContinuousLinearMap T‖
  have second_ineq : ∀ v₁ v₂ : V, ‖T v₁ - T v₂‖ ≤ C * ‖v₁ - v₂‖ := by
    intro v₁ v₂
    calc
      ‖T v₁ - T v₂‖ = ‖(toContinuousLinearMap T) (v₁ - v₂)‖ := by
        simp [toContinuousLinearMap, map_sub]
      _ ≤ ‖toContinuousLinearMap T‖ * ‖v₁ - v₂‖ := by
        exact T.toContinuousLinearMap.le_opNorm (v₁ - v₂)
  refine ⟨‖toContinuousLinearMap T‖ , by positivity, ?_⟩
  intro v₁ v₂
  exact ⟨first_ineq v₁ v₂, second_ineq v₁ v₂⟩


/--
For any linear map T between finite-dimensional inner product spaces, there exists a unit vector u
at which T attains its maximum operator norm on the unit sphere. This is proved via:
1. Compactness of the unit sphere in finite dimensions
2. Extreme value theorem for continuous norm mapping
-/
lemma exists_max_norm_apply [Nontrivial V] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) :
    ∃ u : V, ‖u‖ = 1 ∧ ∀ v : V, ‖v‖ = 1 → ‖T v‖ ≤ ‖T u‖ := by
  let S : Set V := Metric.sphere 0 1
  have h_compact : IsCompact S := by
    have : ProperSpace V := FiniteDimensional.proper_rclike 𝕜 V
    exact isCompact_sphere 0 1
  have h_nonempty : S.Nonempty := by
    obtain ⟨a, ha⟩ := @NormedSpace.sphere_nonempty_rclike 𝕜 _ V _ _ _ 1 zero_le_one
    use a
  let f : V → ℝ := fun v => ‖T v‖
  have h_cont : Continuous f:= by
    apply Continuous.comp continuous_norm (T.toContinuousLinearMap.cont)
  obtain ⟨u, hu_mem, hu_max⟩ := h_compact.exists_isMaxOn h_nonempty h_cont.continuousOn
  refine ⟨u, ?_, ?_⟩
  case _ => rwa [mem_sphere_zero_iff_norm] at hu_mem
  case _ => intro v hv; exact hu_max (mem_sphere_zero_iff_norm.mpr hv)


/--
This is an alternative formulation of `exists_max_norm_apply`, stating that the operator norm of T
is attained at some unit vector u. The proof follows from:
1. Compactness of the unit sphere in finite dimensions
2. Extreme value theorem for continuous norm mapping
-/
lemma exists_max_norm_apply' [Nontrivial V] [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W) :
    ∃ u : V, ‖u‖ = 1 ∧ T.opNorm = ‖T u‖ := by
  rcases exists_max_norm_apply T with ⟨u, hu, hT⟩
  have hnorm : ∀ v: V, ‖T v‖ = ‖toContinuousLinearMap T v‖ := by intro v; rfl
  use u
  constructor
  · exact hu
  · apply le_antisymm
    · simp [LinearMap.opNorm]
      apply opNorm_le_bound
      · apply norm_nonneg
      intro x
      by_cases hx : ‖x‖ = 0
      · exact le_trans (le_opNorm _ _) (by simp [hx])
      · rw [← div_le_iff₀ (norm_pos_iff.mpr _), ← hnorm]
        · have : ‖T x‖ / ‖x‖ = ‖T ((1/‖x‖: 𝕜) • x)‖ := by
            simp [map_smul, norm_smul]
            field_simp
          rw [this]
          apply hT ((1 / ‖x‖: 𝕜) • x)
          simp
          apply norm_smul_inv_norm
          apply ne_zero_of_norm_ne_zero hx
        apply ne_zero_of_norm_ne_zero hx
    · rw [LinearMap.opNorm, ← mul_one ‖toContinuousLinearMap T‖, ← hu, hnorm]
      apply le_opNorm


/-- If a linear map `T` attains its operator norm at a unit vector `e`,
then `T` maps vectors orthogonal to `e` to vectors orthogonal to `T e`. -/
lemma orthogonal_after_operator_norm [FiniteDimensional 𝕜 V] {T : V →ₗ[𝕜] W} {e : V}
    (he : ‖e‖ = 1) (hT : T.opNorm = ‖T e‖) {u : V} (hu : ⟪e, u⟫_𝕜 = 0) :
    ⟪T e, T u⟫_𝕜 = 0 := by
  set σ := T.opNorm with hσ
  by_cases hσ_zero : σ = 0
  · simp [(LinearEquiv.map_eq_zero_iff toContinuousLinearMap).mp (norm_eq_zero.mp hσ_zero)]
  by_cases hu_zero : ‖u‖ = 0
  · simp [norm_eq_zero.mp hu_zero]
  push_neg at hσ_zero
  push_neg at hu_zero
  have h_ineq : ∀ (a : 𝕜), ‖T (e + a • u)‖^2 ≤ σ^2  * (1 + ‖a‖^2 * ‖u‖^2) := by
    intro a
    calc
      ‖T (e + a • u)‖^2 ≤ σ^2 * ‖e + a • u‖^2 := by
        rw [← mul_pow, sq_le_sq, abs_mul, hσ]
        simp only [LinearMap.opNorm, abs_eq_self.mpr (norm_nonneg _)]
        apply le_opNorm (toContinuousLinearMap T) _
      _= σ^2 * (‖e‖^2 + ‖a • u‖^2) := by simp [@norm_add_sq 𝕜 _ _ _ _ e, inner_smul_right, hu]
      _= σ^2 * (1 + ‖a‖^2 * ‖u‖^2) := by simp [he, norm_smul, ← mul_pow]
  have h_norm_expansion : ∀ (a : 𝕜), ‖T (e + a • u)‖^2 ≥ σ^2 + 2 * re (a * ⟪T e, T u⟫_𝕜) := by
    intro a
    calc
      ‖T (e + a • u)‖^2 = ‖T e‖^2 + 2 * re (a * ⟪T e, T u⟫_𝕜) + ‖a‖^2 * ‖T u‖^2 := by
        rw [map_add, @norm_add_sq 𝕜 _ _ _ _ (T e) (T (a • u))]
        rw [map_smul, norm_smul, inner_smul_right, mul_pow]
      _≥ σ^2 + 2 * re (a * ⟪T e, T u⟫_𝕜) := by simp [hT, ← mul_pow, sq_nonneg]
  have h_combined_ineq : ∀ (a : 𝕜), 2 * re (a * ⟪T e, T u⟫_𝕜) ≤ σ^2 * ‖a‖^2 * ‖u‖^2 := by
    intro a
    rw [← add_le_add_iff_left (σ^2), mul_assoc]
    apply le_trans (h_norm_expansion a)
    simp only [mul_add, mul_one] at h_ineq
    exact h_ineq a
  by_contra h
  push_neg at h
  set ε := 1 / (σ^2 * ‖u‖^2) with hε
  have hε_pos : 0 < ε := by
    simp only [ε]
    apply div_pos zero_lt_one (mul_pos (sq_pos_iff.mpr hσ_zero) (sq_pos_iff.mpr hu_zero))
  set a := (⟪T u, T e⟫_𝕜) * ε with ha
  have h_combined_ineq_a : 2 * re (a * ⟪T e, T u⟫_𝕜) ≤ σ^2 * ‖a‖^2 * ‖u‖^2 := by
    apply h_combined_ineq a
  have : 2 * ‖⟪T e, T u⟫_𝕜‖^2 * ε ≤ 1 * ‖⟪T e, T u⟫_𝕜‖^2 * ε := by
    calc
      2 * ‖⟪T e, T u⟫_𝕜‖^2 * ε = 2 * re (a * ⟪T e, T u⟫_𝕜) := by
        rw [ha, mul_assoc, hε, mul_comm ⟪T u, T e⟫_𝕜, mul_assoc, re_ofReal_mul]
        rw [inner_mul_symm_re_eq_norm, norm_mul, norm_inner_symm]
        linarith
      _ ≤ σ^2 * ‖a‖^2 * ‖u‖^2 := by apply h_combined_ineq_a
      _ = 1 * ‖⟪T e, T u⟫_𝕜‖^2  * ε := by
        rw [ha, norm_mul, mul_pow, ← mul_assoc, norm_inner_symm, norm_ofReal, hε]
        simp
        field_simp
  rw [mul_assoc, ← le_div_iff₀ (mul_pos (pow_pos (norm_pos_iff.mpr h) 2) hε_pos), one_mul] at this
  rw [div_self (mul_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr h)) (ne_of_gt hε_pos))] at this
  linarith


/-- The rank of a linear operator `T` with a norm-attaining direction `e₁` decomposes as the sum of
the rank of its restriction to `𝕜 e₁` and its restriction to the orthogonal complement. -/
theorem finrank_range_decomp_of_norm_attains [FiniteDimensional 𝕜 V]
    {T : V →ₗ[𝕜] W} {e₁ : V} (he₁ : ‖e₁‖ = 1)
    (hT_e₁_nonzero : T e₁ ≠ 0) (hT_e₁_norm : T.opNorm = ‖T e₁‖) :
    finrank 𝕜 (range T) = 1 + finrank 𝕜 (range (T.domRestrict (span 𝕜 {e₁})ᗮ)) := by
  let V₂ := (span 𝕜 {e₁})ᗮ
  let T₂ := T.domRestrict V₂
  have : range T = (𝕜 ∙ (T e₁)) ⊔ range T₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨v, rfl⟩ := mem_range.mp hx
      let a := ⟪e₁, v⟫_𝕜
      let v₂ := v - a • e₁
      have hv₂ : v₂ ∈ V₂ := by
        rw [mem_orthogonal']
        intro u hu
        rw [mem_span_singleton] at hu
        obtain ⟨c, rfl⟩ := hu
        simp [v₂, inner_sub_left, inner_smul_right]
        right
        simp [inner_smul_left, a]
        rw [he₁]
        norm_num
      simp at T₂
      refine mem_sup.mpr ⟨a • T e₁, ?_, T₂ ⟨v₂, hv₂⟩, by simp, ?_⟩
      · exact mem_span_singleton.mpr ⟨a,rfl⟩
      · unfold v₂ T₂
        simp [domRestrict_apply]
    · refine sup_le (by simp) (range_domRestrict_le_range T V₂)
  have : 1 + finrank 𝕜 (range T₂) = finrank 𝕜 (range T) := by
    have h_disjoint : finrank 𝕜 ↥(span 𝕜 {T e₁} ⊓ range T₂) = 0 := by
      have : span 𝕜 {T e₁} ⊓ range T₂ = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        rcases hx with ⟨hx_span, hx_range⟩
        simp [mem_span_singleton] at hx_span
        obtain ⟨a, hx_span⟩ := hx_span
        obtain ⟨⟨v, hv⟩, hx_range⟩ := hx_range
        have h_ortho : ⟪v, e₁⟫_𝕜 = 0 := by
          rw [mem_orthogonal'] at hv
          exact hv e₁ (mem_span_singleton_self _)
        have h_zero : a = 0 := by
          have : ⟪T e₁, T v⟫_𝕜 = 0 := by
            convert orthogonal_after_operator_norm he₁ hT_e₁_norm (inner_eq_zero_symm.mp h_ortho)
          rw [inner_eq_zero_symm] at this
          have h_Tv_eq_x : T v = x := by rw [← hx_range, domRestrict_apply]
          rw [h_Tv_eq_x, ← hx_span] at this
          simp [inner_smul_left] at this
          exact Or.resolve_right this hT_e₁_nonzero
        rw [← hx_span, h_zero, zero_smul]
      rw [this, finrank_bot]
    rw [this, ← add_zero (finrank 𝕜 ↥(span 𝕜 {T e₁} ⊔ range T₂)), ← h_disjoint,
        finrank_sup_add_finrank_inf_eq (span 𝕜 {T e₁}) (range T₂),
        finrank_span_singleton hT_e₁_nonzero]
  exact _root_.id (Eq.symm this)


/-- Construct an orthonormal family by prepending a unit vector to an orthonormal family
 in its orthogonal complement.
* `e₁` is a unit vector
* `v'` is an orthonormal family in `e₁`'s orthogonal complement
* The cons operation `[e₁, v'...]` produces an orthonormal family -/
lemma orthonormal_cons_orthogonal {e₁ : V} (he₁ : ‖e₁‖ = 1) {U : Submodule 𝕜 V}
    (hU : U = (span 𝕜 {e₁})ᗮ) {n : ℕ} {v' : Fin n → U}
    (hv_ortho' : Orthonormal 𝕜 (fun i => (v' i : V))) :
    Orthonormal 𝕜 (Fin.cons e₁ (fun i => (v' i : V))) := by
  refine ⟨?unit,?orth⟩
  case unit =>
    intro i
    cases i using Fin.cases with
    | zero => simp [he₁]
    | succ i' => exact hv_ortho'.1 i'
  case orth =>
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        exact (hij rfl).elim
      | succ j' => simp[← hU, mem_orthogonal_singleton_iff_inner_right.mp _]
    | succ i' =>
      cases j using Fin.cases with
      | zero => simp [← hU, mem_orthogonal_singleton_iff_inner_left.mp _]
      | succ j' => simp; simp at hij; apply hv_ortho'.2 hij


/-- Construct an orthonormal family for right singular vectors by:
* Scaling the operator's norm-attaining direction to create the first vector
* Using an existing orthonormal family for the complement
* Ensuring orthogonality via the `orthogonal_after_operator_norm` property -/
lemma orthonormal_cons_singular_vectors {n : ℕ} [FiniteDimensional 𝕜 V]
    {T : V →ₗ[𝕜] W} {e₁ : V} (he₁ : ‖e₁‖ = 1) (hT : T.opNorm = ‖T e₁‖) (hT_e₁_nonzero : T e₁ ≠ 0)
    {σ' : Fin n → ℝ≥0} (hσ_pos' : ∀ (i : Fin n), σ' i > 0)
    {v' : Fin n → (span 𝕜 {e₁})ᗮ} {w' : Fin n → W} (hw_ortho' : Orthonormal 𝕜 w')
    (hTv' : ∀ (i : Fin n), (T.domRestrict (span 𝕜 {e₁})ᗮ) (v' i) = ((σ' i : ℝ) : 𝕜) • (w' i)) :
    Orthonormal 𝕜 (Fin.cons ((‖T e₁‖⁻¹ : 𝕜) • T e₁) w') := by
  let V₂ := (span 𝕜 {e₁})ᗮ
  let T₂ := T.domRestrict V₂
  have hT_eq : ∀ (v' : Fin n → V₂) (j: Fin n), T (v' j) = T₂ (v' j) := by intro v' j; rfl
  have horth : ∀ i, ⟪w' i, T e₁⟫_𝕜 = 0 := by
    intro i
    have hw'i : w' i = ((σ' i : ℝ)⁻¹ : 𝕜) • T (v' i) := by
      rw [hT_eq v' i, hTv' i, smul_comm, smul_inv_smul₀]
      simp [pos_iff_ne_zero.mp (hσ_pos' i)]
    rw [hw'i, inner_smul_left]
    have h_orth : ⟪T (v' i), T e₁⟫_𝕜 = 0 := by
      simp [inner_eq_zero_symm]
      apply orthogonal_after_operator_norm he₁ hT ?_
      simp [mem_orthogonal_singleton_iff_inner_right.mp _]
    rw [h_orth, mul_zero]
  refine ⟨?unit,?orth⟩
  case unit =>
    intro i
    cases i using Fin.cases with
    | zero =>
      simp [norm_smul, hT_e₁_nonzero]
    | succ i' =>
      simp [hw_ortho'.1 i']
  case orth =>
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        exact (hij rfl).elim
      | succ j' =>
        simp [inner_smul_left]
        rw [inner_eq_zero_symm]
        exact Or.inr (horth j')
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        simp [inner_smul_right]
        exact Or.inr (horth i')
      | succ j' => simp at hij; apply hw_ortho'.2; simp [hij]


/-- Verifies kernel inclusion for SVD construction:
Orthogonality to the left singular vectors implies membership in the kernel. -/
lemma hT_kernel_condition {T : V →ₗ[𝕜] W} {e₁ : V}
    {T₂ : (span 𝕜 {e₁})ᗮ →ₗ[𝕜] W} (hT₂ : T₂ = T.domRestrict (span 𝕜 {e₁})ᗮ)
    {n : ℕ} {v' : Fin n → (span 𝕜 {e₁})ᗮ}
    (hker' : (span 𝕜 (Set.range v'))ᗮ ≤ LinearMap.ker T₂) :
    (span 𝕜 (Set.range (Fin.cons e₁ fun i ↦ ↑(v' i))))ᗮ ≤ ker T := by
  let V₂ := (span 𝕜 {e₁})ᗮ
  intro x hx
  have hx_e₁ : ⟪x, e₁⟫_𝕜 = 0 := by
    apply inner_eq_zero_symm.mp (hx e₁ _)
    exact subset_span (Set.mem_range.mpr ⟨0, rfl⟩)
  have hx_v' : ∀ i, ⟪x, v' i⟫_𝕜 = 0 := by
    intro i
    have := hx (v' i) (subset_span (Set.mem_range.mpr ⟨i.succ, rfl⟩))
    exact inner_eq_zero_symm.mp this
  have hx_V₂ : x ∈ V₂ := by
    rw [mem_orthogonal_singleton_iff_inner_left]
    exact hx_e₁
  let x' : V₂ := ⟨x, hx_V₂⟩
  have hx'_v' : x' ∈ (span 𝕜 (Set.range v')).orthogonal := by
    rw [mem_orthogonal]
    intro y hy
    simp [mem_span_range_iff_exists_fun] at hy
    rcases hy with ⟨c,hy⟩
    rw [← hy, sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    simp [inner_smul_left]
    exact Or.inr (inner_eq_zero_symm.mp (hx_v' i))
  have hT₂x_zero : T₂ x' = 0 := hker' hx'_v'
  change T x = 0
  simpa [hT₂, domRestrict_apply] using hT₂x_zero

/-- Partial Singular Value Decomposition (PSVD) for linear operators between
finite-dimensional inner product spaces.
Given linear operator T : V → W and a natural `r, the PSVD includes
1. Decreasing singular values σ₁ ≥ ⋯ ≥ σᵣ > 0
2. Left orthonormal singular vectors {vᵢ} ⊆ V
3. Right orthonormal singular vectors {wᵢ} ⊆ W
such that:
  T(vᵢ) = σᵢ • wᵢ

We called it partial because r could be less than the rank of T, i.e.
a PSVD does not necessarily have all singular values.
-/
structure PartialSingularValueDecomposition (T : V →ₗ[𝕜] W) (r : ℕ) where
  σ : Fin r → ℝ≥0 -- singular values
  σ_pos : ∀ i : Fin r, σ i > 0
  σ_antitone : Antitone σ
  v : Fin r  → V
  w : Fin r → W
  v_orthonormal : Orthonormal 𝕜 v := by infer_instance
  w_orthonormal : Orthonormal 𝕜 w := by infer_instance

  map : ∀ i, T (v i) = ((σ i : ℝ) : 𝕜) • (w i)


namespace PartialSingularValueDecomposition
scoped notation "PSVD" => PartialSingularValueDecomposition

attribute [simp] v_orthonormal
attribute [simp] w_orthonormal

variable {T : V →ₗ[𝕜] W} {r : ℕ} (hT : PSVD T r)

@[simp] lemma σ_ne_zero (i : Fin r) : (hT.σ i) ≠ 0 :=
  ne_zero_of_lt (hT.σ_pos i)

@[simp] lemma v_ne_zero (i : Fin r) : hT.v i ≠ 0 :=
  Orthonormal.ne_zero hT.v_orthonormal i

@[simp] lemma w_ne_zero (i : Fin r) : hT.w i ≠ 0 :=
  Orthonormal.ne_zero hT.w_orthonormal i

@[simp] lemma T_v_ne_zero (i : Fin r) : T (hT.v i) ≠ 0 := by
  simp [map]

@[simp] lemma v_linearIndependent : LinearIndependent 𝕜 hT.v :=
  hT.v_orthonormal.linearIndependent

@[simp] lemma w_linearIndependent : LinearIndependent 𝕜 hT.w :=
  hT.w_orthonormal.linearIndependent

variable [FiniteDimensional 𝕜 V]


end PartialSingularValueDecomposition

open PartialSingularValueDecomposition
/--
A Singular Value Decomposition (SVD) is a partial singular value decomposition with
`orthogonal_span_range_v_le_ker : (span 𝕜 (Set.range v))ᗮ ≤ ker T`
-/
structure SingularValueDecomposition (T : V →ₗ[𝕜] W) (r : ℕ)
  extends PSVD T r where
  orthogonal_span_range_v_le_ker : (span 𝕜 (Set.range v))ᗮ ≤ ker T


-- /-- Singular Value Decomposition (SVD) for linear operators between
-- finite-dimensional inner product spaces.
-- Given linear operator T : V → W with rank r, there exist:
-- 1. Decreasing singular values σ₁ ≥ ⋯ ≥ σᵣ > 0
-- 2. Left orthonormal singular vectors {vᵢ} ⊆ V
-- 3. Right orthonormal singular vectors {wᵢ} ⊆ W
-- such that:
--   T(vᵢ) = σᵢ • wᵢ
-- and
--   (span{vᵢ})ᗮ ⊆ ker T

-- The decomposition satisfies:
--   ‖T‖ = σ₁  and  T = ∑ σᵢ wᵢ ⊗ vᵢ
-- where ⊗ denotes the outer product. -/


namespace SingularValueDecomposition

scoped notation "SVD" => SingularValueDecomposition

variable {T : V →ₗ[𝕜] W} {r : ℕ} (hT : SVD T r) [FiniteDimensional 𝕜 V]

/--
The left singular vectors span the orthogonal complement of the kernel of the linear map.
-/
@[simp] theorem span_range_v_eq_orthogonal_ker :
  span 𝕜 (Set.range (hT.v)) = (ker T)ᗮ := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    simp [mem_orthogonal]
    intro u Tu_eq_0
    -- goal : `_, T u = 0 ⊢ ⟪u, T.rightSingularVectors i⟫_𝕜 = 0`
    have := exists_orthogonal_decompose (span 𝕜 (Set.range (hT.v))) u
    obtain ⟨u₁, hu₁, u₂, hu₂, hu_eq⟩ := this
    have : u₂ ∈ (ker T) := hT.orthogonal_span_range_v_le_ker hu₂
    simp at this
    simp [hu_eq, this] at Tu_eq_0
    -- Now we should get a contradiction from `Tu_eq_0 : T u₁ = 0`
    -- The plan is to write `u₁` as a lincomb of left vectors, and use `T_map` to change
    -- it into a lincomb of right vectors, and to prove all coefs are zero from orthonormality
    have inj : LinearIndependent 𝕜 hT.w :=
      Orthonormal.linearIndependent hT.w_orthonormal
    simp [LinearIndependent, Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.sum] at hu₁ inj
    obtain ⟨coef, hu₁⟩ := hu₁
    by_cases u₁_eq_0 : u₁ = 0
    · simp [u₁_eq_0, hu_eq]
      apply (mem_orthogonal' (span 𝕜 (Set.range hT.v)) u₂).mp
      · exact hu₂
      · apply mem_span_of_mem; simp
    simp [← hu₁] at Tu_eq_0
    /- rw `Tu_eq_0` with `T_map`-/
    have : ∀ x, coef x • T (hT.v x) = (coef x * (hT.σ x : ℝ)) • (hT.w x) :=by
      intro x; simp [← smul_smul]; congr; exact hT.map x
    simp [this] at Tu_eq_0
    let f : Fin r →₀ 𝕜 := {
      support := coef.support
      toFun := fun x => (coef x • (hT.σ x : ℝ))
      mem_support_toFun a := by simp [coef.mem_support_toFun]; rfl
      }
    have : (fun x => (coef x * ((hT.σ x : ℝ) : 𝕜)) • hT.w x) = fun x => f x • (hT.w x) := by rfl
    simp [this, ← hu₁] at Tu_eq_0 u₁_eq_0
    -- now `Tu_eq_0 : ∑ x ∈ coef.support, f x • T.leftSingularVectors x = 0`
    have : f = 0 := by apply inj; simp; exact Tu_eq_0
    suffices coef = 0 from by simp[this] at u₁_eq_0
    ext x
    have : f x = 0 := by simp [this]
    simp [f] at this
    exact this
  · rw [orthogonal_le_iff_orthogonal_le]
    exact hT.orthogonal_span_range_v_le_ker

/--
The right singular vectors span the range of the linear map.
-/
@[simp] theorem span_range_w_eq_range :
  span 𝕜 (Set.range hT.w) = (range T) := by
  apply Submodule.span_eq_of_le
  · intro w'
    simp
    intro i hi
    use ((hT.σ i : ℝ) : 𝕜)⁻¹ • hT.v i
    have : T (hT.v i) = ((hT.σ i : ℝ):𝕜) • hT.w i := hT.map i
    simp [← hi, this]
  · intro w h
    simp at h
    obtain ⟨x, hx⟩ := h
    rw [← hx, mem_span_range_iff_exists_fun]
    have := exists_orthogonal_decompose (ker T) x
    obtain ⟨x₁, hx₁, x₂, hx₂, xeq⟩ := this
    simp at hx₁
    simp [xeq, hx₁]
    rw [← hT.span_range_v_eq_orthogonal_ker,
      mem_span_range_iff_exists_fun] at hx₂
    obtain ⟨c, hc⟩ := hx₂
    use fun i => c i * (hT.σ i : ℝ)
    simp [← hc, hT.map, ← smul_smul]


/--
For linear map `T` with a SVD, its left vectors are an orthonormal basis of the orthogonal
complement of the kernel of `T`
-/
lemma exists_orthonormalBasis_orthogonal_ker :
  ∃ b : OrthonormalBasis (Fin r) 𝕜 (ker T)ᗮ, ∀ i, b i = hT.v i := by
  rw [← span_range_v_eq_orthogonal_ker]
  exact Orthonormal.exists_orthonormalBasis_span_range hT.v_orthonormal

/--
For linear map `T` with a SVD, its right vectors are an orthonormal basis of the orthogonal
complement of the range of `T`
-/
lemma exists_orthonormalBasis_range :
  ∃ b : OrthonormalBasis (Fin r) 𝕜 (range T), ∀ i, b i = hT.w i := by
  rw [← span_range_w_eq_range]
  exact Orthonormal.exists_orthonormalBasis_span_range hT.w_orthonormal


/--
If linear map `T : V →ₗ[𝕜] W` has an SVD, then the star projection (orthogonal projection as an
endomorphism) onto its range equals to `∑ i, ⟪w(i), · ⟫ • w(i)`
-/
theorem starProjection_range_eq_sum_inner (v : W) :
  (range T).starProjection v =
    ∑ i : Fin r, (⟪hT.w i, v ⟫_𝕜) • hT.w i := by
  obtain ⟨b₂, hb₂⟩ := hT.exists_orthonormalBasis_range
  have := OrthonormalBasis.orthogonalProjection_eq_sum
    (U := range T)
    (b := b₂) v
  simp [starProjection_apply, this, hb₂]

/--
If linear map `T : V →ₗ[𝕜] W` has an SVD, then the star projection (orthogonal projection as an
endomorphism) onto the orthogonal complement of its kernel equals to `∑ i, ⟪v(i), · ⟫ • v(i)`.
-/
theorem starProjection_orthogonal_ker_eq_sum_inner (v : V) :
  (ker T)ᗮ.starProjection v =
    ∑ i : Fin r, (⟪hT.v i, v⟫_𝕜) • hT.v i := by
  obtain ⟨b₁, hb₁⟩ := hT.exists_orthonormalBasis_orthogonal_ker
  have := OrthonormalBasis.orthogonalProjection_eq_sum
    (U := (ker T)ᗮ)
    (b := b₁) v
  simp [starProjection_apply, this, hb₁]

@[simp]
theorem r_eq_finrank_range_T (hT : SVD T r) : r = finrank 𝕜 (range T) := by
  rw [← hT.span_range_w_eq_range]
  simp [finrank_span_eq_card (b:=hT.w) hT.w_orthonormal.linearIndependent]


end SingularValueDecomposition

open SingularValueDecomposition
/--
Any linear map with a finite rank whose domain is finite dimensional has a SVD.
-/
theorem singular_value_decomposition [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] W)
    {r : ℕ} (hr : r = finrank 𝕜 (range T)) :
  Nonempty (SVD T r) := by
  induction r generalizing T V with
  | zero =>
    have h_range_zero : T = 0 := by rw [← range_eq_bot, ← finrank_eq_zero, hr]
    refine ⟨⟨Fin.elim0, fun x => Fin.elim0 x, Subsingleton.antitone Fin.elim0, Fin.elim0,
      Fin.elim0, by simp, by simp, by simp⟩, by simp [ker_eq_top.mpr h_range_zero]⟩
  | succ r ih =>
    by_cases hV : ¬ Nontrivial V
    · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      have : finrank 𝕜 (range T) = 0 := by simp [range_eq_bot.mpr (Subsingleton.eq_zero T)]
      have := hr.trans this
      exact False.elim (by simp at this)
    simp at hV
    obtain ⟨e₁, he₁_unit, hT_e₁_max⟩ := exists_max_norm_apply' T
    have hT_e₁_nonzero : T e₁ ≠ 0 := by
      by_contra hT_e₁_zero
      simp [hT_e₁_zero] at hT_e₁_max
      have : finrank 𝕜 (range T) = 0 := by simp [range_eq_bot.mpr hT_e₁_max]
      have := hr.trans this
      exact False.elim (by simp at this)
    let σ₁ : ℝ≥0 := ⟨‖T e₁‖, norm_nonneg _⟩
    let w₁ : W := ((σ₁:ℝ) ⁻¹ : 𝕜) • T e₁
    let V₂ := (span 𝕜 {e₁})ᗮ
    let T₂ := T.domRestrict V₂
    have hT_eq : ∀ (v' : Fin r → V₂) (j: Fin r), T (v' j) = T₂ (v' j) := by intro v' j; rfl
    have hrank_T₂ : finrank 𝕜 (range T₂) = r := by
      rw [← add_right_cancel_iff, hr]
      rw [finrank_range_decomp_of_norm_attains he₁_unit hT_e₁_nonzero hT_e₁_max, add_comm]

    -- Applying the inductive hypothesis
    obtain ⟨⟨σ', hσ_pos', hσ_anti', v', w', hv_ortho', hw_ortho', hTv'⟩, hker'⟩ :=
      ih T₂ hrank_T₂.symm
    -- Constructing a complete decomposition
    refine ⟨⟨Fin.cons σ₁ σ', ?_, ?_, Fin.cons e₁ (fun i => (v' i : V)),
            Fin.cons w₁ w', ?_, ?_, ?_⟩, ?_⟩

    · --Singular values ​​are positive
      intro i
      cases i using Fin.cases with
      | zero =>
        simp [σ₁]
        apply norm_pos_iff.mpr hT_e₁_nonzero
      | succ i =>
        simp [hσ_pos' i]
    · -- Singular values ​​are monotonically decreasing
      intro i j h
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simp
        | succ j =>
          simp [σ₁]
          have : σ' j ≤ ‖T e₁‖ := by
            have hnorm : ‖T (v' j)‖ = σ' j * ‖w' j‖ := by simp [hT_eq, hTv' j, norm_smul]
            simp [hw_ortho'.1 j] at hnorm
            rw [← hnorm, ← hT_e₁_max]
            have : ∀ v: V, ‖T v‖ = ‖toContinuousLinearMap T v‖ := by intro v; rfl
            rw [LinearMap.opNorm, ← mul_one ‖toContinuousLinearMap T‖, ← hv_ortho'.1 j, this]
            apply le_opNorm
          exact coe_le_coe.mpr this
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          have : 0 < i.succ := by simp
          contradiction
        | succ j =>
          simp [hσ_anti' (Fin.succ_le_succ_iff.mp h)]
    · -- Left singular vectors are orthogonal
      exact orthonormal_cons_orthogonal he₁_unit rfl hv_ortho'
    · -- Right singular vectors are orthogonal
      exact orthonormal_cons_singular_vectors he₁_unit hT_e₁_max hT_e₁_nonzero hσ_pos' hw_ortho'
        hTv'
    · -- The equation for operator T
      intro i
      cases i using Fin.cases with
      | zero =>
        have hn : ‖T e₁‖ ≠ 0 := norm_ne_zero_iff.mpr hT_e₁_nonzero
        have hn' : ((‖T e₁‖ : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast hn
        simp [w₁, σ₁, smul_smul]
        change T e₁ = (((‖T e₁‖ : ℝ) : 𝕜) * ((‖T e₁‖ : ℝ) : 𝕜)⁻¹) • T e₁
        rw [mul_inv_cancel₀ hn', one_smul]
      | succ i' => simp [hT_eq, hTv' i']
    · -- Kernel condition
      apply hT_kernel_condition (by simp [T₂, V₂]) hker'



/-- For any orthonormal basis `v` and vector `u`, the sum of squared magnitudes of inner products
equals the squared norm of `u`. -/
lemma sum_inner_sq_eq_norm_sq {n : ℕ} (v : OrthonormalBasis (Fin n) 𝕜 V) (u : V) :
    (‖u‖ ^ 2: 𝕜) = (∑ i, ‖⟪v i, u⟫_𝕜‖^2: 𝕜) := by
  -- Express u in terms of the orthonormal basis
  have hu_expand : u = ∑ i, ⟪v i, u⟫_𝕜 • v i := by
    rw [OrthonormalBasis.sum_repr']
  have : ⟪∑ i, ⟪v i ,u⟫_𝕜 • v i, ∑ i, ⟪v i ,u⟫_𝕜 • v i⟫_𝕜 =
      (‖∑ i, ⟪v i ,u⟫_𝕜 • v i‖ ^ 2 : 𝕜) := by simp [inner_self_eq_norm_sq_to_K]
  have hv_orth: Orthonormal 𝕜 v := by exact OrthonormalBasis.orthonormal v
  calc (‖u‖ ^ 2: 𝕜) = (‖∑ i, ⟪v i ,u⟫_𝕜 • v i‖ ^ 2: 𝕜) := by nth_rw 1 [hu_expand]
  _ = ⟪∑ i, ⟪v i ,u⟫_𝕜 • v i, ∑ i, ⟪v i ,u⟫_𝕜 • v i⟫_𝕜 := by rw [this]
  _ = ∑ i, (starRingEnd 𝕜) ⟪v i, u⟫_𝕜 * ⟪v i, u⟫_𝕜 := by
    rw [Orthonormal.inner_sum]
    apply hv_orth
  _ = ∑ i, (‖⟪v i, u⟫_𝕜‖^2: 𝕜) := by
    have : ∀ i, (starRingEnd 𝕜) ⟪v i, u⟫_𝕜 * ⟪v i, u⟫_𝕜 = ↑‖⟪v i, u⟫_𝕜‖ ^ 2 := by
      intro i
      exact RCLike.conj_mul ⟪v i, u⟫_𝕜
    congr
    ext i
    exact this i
  _ = ((∑ i, ‖⟪v i, u⟫_𝕜‖^2):𝕜) := by
    simp


theorem real_smul_one_inj {a b : ℝ} (h : a • (1 : 𝕜) = b • (1 : 𝕜)) : a = b := by
  simp only [Algebra.smul_def] at h
  rw [mul_one, mul_one] at h
  exact RCLike.ofReal_inj.mp h


/-! ### Auxiliary Lemma: rewrite `‖T u‖²` as a sum of squared singular values -/

/-- Decompose `u` into `span (range v)` and its orthogonal complement,
use the kernel condition to kill the orthogonal component under `T`,
then rewrite `‖T u‖²` as `∑ σ i^2 ‖⟪v i, u⟫‖²`. -/
lemma norm_T_sq_expand
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] [InnerProductSpace 𝕜 V]
  {r : ℕ} {T : V →ₗ[𝕜] W}
  {σ : Fin r → ℝ≥0} {v : Fin r → V} {w : Fin r → W}
  (hv : Orthonormal 𝕜 v) (hw : Orthonormal 𝕜 w)
  (hTv : ∀ i, T (v i) = ((σ i : ℝ) : 𝕜) • w i)
  (hker : (span 𝕜 (Set.range v)).orthogonal ≤ LinearMap.ker T)
  (u : V) :
  (‖T u‖ ^ 2 : 𝕜) = ∑ i, ((σ i : ℝ)^2 : 𝕜) * (‖⟪v i, u⟫_𝕜‖ ^ 2 : 𝕜) := by
  let n := finrank 𝕜 V
  let ι : Type := Fin n
  let s : Set ι := {i : ι | i.val < r}
  sorry


/-! ### Main Result 1: `‖T‖ = σ₀` -/

lemma opNorm_eq_first_singular_value
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
  (hV : Nontrivial V) {T : V →ₗ[𝕜] W}
  {r : ℕ} (hr : r = finrank 𝕜 (range T)) (hr_pos : r > 0)
  (hT : SVD T r) : T.opNorm = (hT.σ ⟨0, hr_pos⟩ : ℝ) := by
  classical
  obtain ⟨⟨σ, hσ_pos, hσ_anti, v, w, hv_ortho, hw_ortho, hTv⟩, hker⟩ := hT
  -- Square both sides and compare
  have hT_norm : T.opNorm ^ 2 = ((σ ⟨0, hr_pos⟩ : ℝ) ^ 2) := by
    apply le_antisymm_iff.mpr
    constructor
    · -- `‖T‖² ≤ σ₀²`
      obtain ⟨u, hu, hTu⟩ := exists_max_norm_apply' T
      -- By the expansion lemma above: ‖T u‖² = ∑ σ i² ‖⟪v i, u⟫‖²
      have hu' :
          (‖T u‖ ^ 2 : 𝕜)
            = ∑ i, ((σ i : ℝ)^2 : 𝕜) * (‖⟪v i, u⟫_𝕜‖ ^ 2 : 𝕜) :=
        norm_T_sq_expand hv_ortho hw_ortho hTv hker u
      -- Compare real parts (RHS is nonnegative; treat `𝕜`-values as reals)
      have hu'' :
          (‖T u‖ ^ 2 : ℝ)
            = ∑ i, ((σ i : ℝ)^2) * (‖⟪v i, u⟫_𝕜‖ ^ 2) := by
        sorry
      -- By monotonicity: σ i ≤ σ 0, hence σ i² ≤ σ 0²
      have hbound : ∀ i, (σ i : ℝ)^2 ≤ (σ ⟨0, hr_pos⟩ : ℝ)^2 := by
        intro i
        have : (σ ⟨0, hr_pos⟩ : ℝ) ≥ σ i := by
          -- `Antitone σ` gives `σ 0 ≥ σ i`
          apply hσ_anti
          apply @Fin.zero_le r (by simp [neZero_iff, ← pos_iff_ne_zero, hr_pos])
        exact sq_le_sq.mpr (by apply abs_le_abs this; sorry)
      -- Coefficients are nonnegative
      have hnonneg : ∀ i, 0 ≤ (‖⟪v i, u⟫_𝕜‖ ^ 2) := by
        intro i; exact sq_nonneg _
      -- Apply the algebraic inequality
      have :
          ∑ i, ((σ i : ℝ)^2) * (‖⟪v i, u⟫_𝕜‖ ^ 2)
            ≤ (σ ⟨0, hr_pos⟩ : ℝ)^2 * ∑ i, (‖⟪v i, u⟫_𝕜‖ ^ 2) := by
        sorry
      -- The RHS sum is `‖u‖²`, and `u` is a unit vector
      have hsum : (∑ i, (‖⟪v i, u⟫_𝕜‖ ^ 2) : ℝ) = (‖u‖ ^ 2 : ℝ) := by
        -- Use the Parseval identity proved above in this file
        sorry
      -- Therefore: ‖T u‖² ≤ σ₀² ‖u‖² = σ₀²
      have : (‖T u‖ ^ 2 : ℝ) ≤ (σ ⟨0, hr_pos⟩ : ℝ)^2 := by
        sorry
      -- Finally, choose `u` to realize the operator norm
      have : (T.opNorm ^ 2 : ℝ) ≤ (σ ⟨0, hr_pos⟩ : ℝ)^2 := by
        -- `hTu : ‖T u‖ = ‖T‖` and `hu : ‖u‖ = 1`
        sorry
      exact_mod_cast this
    · -- `σ₀² ≤ ‖T‖²`: take `u = v 0`
      have hv0 : ‖v ⟨0, hr_pos⟩‖ = 1 := by simpa using (hv_ortho.1 ⟨0, hr_pos⟩)
      -- `‖T (v 0)‖ = σ₀`
      have hT0 : ‖T (v ⟨0, hr_pos⟩)‖ = (σ ⟨0, hr_pos⟩ : ℝ) := by
        sorry
      -- Use the operator norm definition
      have : (σ ⟨0, hr_pos⟩ : ℝ) ≤ T.opNorm := by
        sorry
      -- Square both sides
      sorry
  -- Operator norm and singular values are nonnegative, so equality of squares implies equality
  refine (sq_eq_sq₀ (by apply opNorm_nonneg)
    (by exact_mod_cast (le_of_lt (hσ_pos ⟨0, hr_pos⟩)))).mp ?_
  exact hT_norm

/-! ### Main Result 2: uniqueness of singular values (proof skeleton only) -/

/-- Uniqueness of the first singular value: two SVDs give the same `σ 0`. -/
lemma first_singular_value_unique
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
  (hV : Nontrivial V) {T : V →ₗ[𝕜] W}
  {r : ℕ} (hr : r = finrank 𝕜 (range T)) (hr_pos : r > 0)
  (hT hT' : SVD T r) : hT.σ ⟨0, hr_pos⟩ = hT'.σ ⟨0, hr_pos⟩ := by
  have h1 := opNorm_eq_first_singular_value hV hr hr_pos hT
  have h2 := opNorm_eq_first_singular_value hV hr hr_pos hT'
  refine NNReal.eq ?_
  rw [← h1, h2]

/-- Recursive skeleton for "removing the first singular pair" (used by the main theorem):
if we synchronize the first singular value and vector (allowing a phase),
then the induced reduced operators on the remaining rank have the same singular value sequence.
Details are omitted; we provide an interface for the main proof. -/
lemma singular_values_unique_tail
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
  {r : ℕ} {T : V →ₗ[𝕜] W}
  (hT hT' : SVD T (r + 1)) (hhead : hT.σ 0 = hT'.σ 0) :
  (fun i : Fin r => hT.σ i.succ) = (fun i : Fin r => hT'.σ i.succ) := by
  admit

/-- **Uniqueness of singular values** (proof skeleton):
two SVDs (same rank r) yield the same singular value function. -/
theorem singular_values_unique
  [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
  (hV : Nontrivial V) {T : V →ₗ[𝕜] W}
  {r : ℕ} (hr : r = finrank 𝕜 (range T))
  (hT hT' : SVD T r) :
  hT.σ = hT'.σ := by
  obtain ⟨⟨σ ,hσ_pos, hσ_anti,v , w, hv_ortho, hw_ortho, hTv⟩, hker⟩ := hT
  obtain ⟨⟨σ' ,hσ'_pos, hσ'_anti,v' , w', hv'_ortho, hw'_ortho, hTv'⟩, hker'⟩ := hT'

  classical
  -- Induction on rank
  cases r with
  | zero =>
      -- Rank 0: no singular values, functions equal (empty function)
      ext i; exact Fin.elim0 i
  | succ r' =>
    have hr_pos : r'.succ > 0 := Nat.succ_pos _
    -- First compare the leading singular value
    have hhead :
        σ ⟨0, hr_pos⟩ = σ' ⟨0, hr_pos⟩ :=
      first_singular_value_unique hV hr hr_pos
      ⟨⟨σ ,hσ_pos, hσ_anti,v , w, hv_ortho, hw_ortho, hTv⟩, hker⟩
      ⟨⟨σ' ,hσ'_pos, hσ'_anti,v' , w', hv'_ortho, hw'_ortho, hTv'⟩, hker'⟩
    -- Then match the tail (r' values)
    have htail :
        (fun i : Fin r' => σ i.succ)
          = (fun i : Fin r' => σ' i.succ) :=
      singular_values_unique_tail
        ⟨⟨σ ,hσ_pos, hσ_anti,v , w, hv_ortho, hw_ortho, hTv⟩, hker⟩
        ⟨⟨σ' ,hσ'_pos, hσ'_anti,v' , w', hv'_ortho, hw'_ortho, hTv'⟩, hker'⟩
         (by simpa using hhead)
    -- Combine "head + tail"
    -- Use `Fin.cases` to split `Fin (r'.succ)` into 0 and succ i cases
    funext i
    cases i using Fin.cases with
    | zero =>
      -- Head
      simpa using hhead
    | succ j =>
      -- Tail
      simpa using congrArg (fun f => f j) htail

end LinearMap

namespace Matrix

open InnerProductSpace ContinuousLinearMap Module LinearMap Submodule NNReal RCLike Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n : ℕ}


structure SingularValueDecomposition' (A : Matrix (Fin m) (Fin n) 𝕜) (r : ℕ) where
  σ : Fin r → ℝ≥0
  U : Matrix (Fin m) (Fin m) 𝕜
  V : Matrix (Fin n) (Fin n) 𝕜
  S : Matrix (Fin m) (Fin n) 𝕜
  σ_pos : ∀ i : Fin r, 0 < σ i
  σ_antitone : Antitone σ
  U_unitary : U ∈ unitaryGroup (Fin m) 𝕜
  V_unitary : V ∈ unitaryGroup (Fin n) 𝕜
  S_eq_ite : ∀ i j, S i j = if H: i.1 = j.1 ∧ (i : ℕ) < r then ((σ ⟨i.1, H.2⟩ : ℝ): 𝕜) else 0
  eq_mul_mul : A = U * S * Vᴴ


namespace SingularValueDecomposition'
scoped notation "SVD'" => SingularValueDecomposition'
end SingularValueDecomposition'

open LinearMap SingularValueDecomposition Matrix SingularValueDecomposition'

theorem singular_value_decomposition (A : Matrix (Fin m) (Fin n) 𝕜)
  (hr : r = finrank 𝕜 (range (Matrix.toLin' A))) :
  Nonempty (SVD' A r) := by sorry


noncomputable def singularValue
  (A : Matrix (Fin m) (Fin n) 𝕜) (i : Fin (min m n)) : ℝ≥0 :=
  let r := finrank 𝕜 (range (Matrix.toLin' A))
  if h : i.1 < r then
    (singular_value_decomposition A rfl).some.σ ⟨i.1, h⟩
  else 0

/-- The largest singular value of a nonempty matrix. -/
noncomputable def largestSingularValue (A : Matrix (Fin m) (Fin n) 𝕜) : ℝ≥0 :=
  if hmn : 0 < m ∧ 0 < n then
    singularValue A ⟨0, Nat.lt_min.mpr hmn⟩
  else 0

/-- The smallest singular value of a nonempty matrix. -/
noncomputable def smallestSingularValue (A : Matrix (Fin m) (Fin n) 𝕜) : ℝ≥0 :=
  let r := Nat.min m n
  if hr : 0 < r then
    singularValue A ⟨r - 1, Nat.pred_lt (ne_of_gt hr)⟩
  else 0

end Matrix

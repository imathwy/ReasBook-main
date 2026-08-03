import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap25.Proposition_25_43

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise SetValuedOperator

noncomputable section

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

local notation "δ0" => (ι[{(0 : K)}] : K → Set.Ioi (⊥ : EReal))

omit [CompleteSpace K] in
/-- Helper for the current corollary: negating a set negates its conic hull. -/
private theorem cone_neg_eq_neg_cone {C : Set K} :
    cone (-C) = -cone C := by
  have hmap :
      (((ConvexCone.hull ℝ C).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) = -cone C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_neg]
      simpa [Set.cone_def] using hy
    · intro hx
      rw [Set.mem_neg] at hx
      exact ⟨-x, by simpa [Set.cone_def] using hx, by simp⟩
  have hmap' :
      (((ConvexCone.hull ℝ (-C)).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) = -cone (-C) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Set.mem_neg]
      simpa [Set.cone_def] using hy
    · intro hx
      rw [Set.mem_neg] at hx
      exact ⟨-x, by simpa [Set.cone_def] using hx, by simp⟩
  have hsubset :
      (-C) ⊆ (((ConvexCone.hull ℝ C).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) := by
    intro x hx
    rw [Set.mem_neg] at hx
    exact ⟨-x, by simpa [Set.cone_def] using (ConvexCone.subset_hull hx), by simp⟩
  have hsubset' :
      C ⊆ (((ConvexCone.hull ℝ (-C)).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) := by
    intro x hx
    exact ⟨-x, by simpa using (ConvexCone.subset_hull (by simpa)), by simp⟩
  have hneg :
      cone (-C) ⊆ -cone C := by
    have hneg_map :
        cone (-C) ⊆ (((ConvexCone.hull ℝ C).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) := by
      exact ConvexCone.hull_min hsubset
    exact hneg_map.trans (by simp [hmap])
  have hneg' :
      cone C ⊆ -cone (-C) := by
    have hneg_map :
        cone C ⊆ (((ConvexCone.hull ℝ (-C)).map (-LinearMap.id : K →ₗ[ℝ] K)) : Set K) := by
      exact ConvexCone.hull_min hsubset'
    exact hneg_map.trans (by simp [hmap'])
  refine Set.Subset.antisymm hneg ?_
  intro x hx
  rw [Set.mem_neg] at hx
  have hx' : -x ∈ cone C := hx
  have hx'' : -x ∈ -cone (-C) := hneg' hx'
  rw [Set.mem_neg] at hx''
  simpa using hx''

omit [CompleteSpace H] in
private theorem zero_mem_sri_neg_of_zero_mem_sri
    {C : Set H} (hC_convex : Convex ℝ C) (hzero : (0 : H) ∈ sri C) :
    (0 : H) ∈ sri (-C) := by
  rcases Set.mem_strongRelativeInterior_iff.mp hzero with ⟨hzero_mem, hcone_eq⟩
  have hneg_nonempty : (-C : Set H).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [Set.mem_neg] using hzero_mem
  refine
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      hneg_nonempty hC_convex.neg).2 ?_
  calc
    cone (-C) = -cone C := cone_neg_eq_neg_cone
    _ = -(((Submodule.span ℝ C).topologicalClosure : Submodule ℝ H) : Set H) := by
      simpa using congrArg Neg.neg hcone_eq
    _ = (((Submodule.span ℝ C).topologicalClosure : Submodule ℝ H) : Set H) := by
      ext x
      constructor
      · intro hx
        simpa using ((Submodule.span ℝ C).topologicalClosure.neg_mem hx)
      · intro hx
        exact ((Submodule.span ℝ C).topologicalClosure.neg_mem hx)
    _ = (((Submodule.span ℝ (-C)).topologicalClosure : Submodule ℝ H) : Set H) := by
      simp [Submodule.span_neg]

omit [CompleteSpace H] in
private theorem zero_mem_sri_sub_rev_of_zero_mem_sri_sub
    {A B : Set H} (hA_convex : Convex ℝ A) (hB_convex : Convex ℝ B)
    (hzero : (0 : H) ∈ sri (A - B)) :
    (0 : H) ∈ sri (B - A) := by
  have hneg : (0 : H) ∈ sri (-(A - B)) :=
    zero_mem_sri_neg_of_zero_mem_sri (hA_convex.sub hB_convex) hzero
  have hset : -(A - B) = B - A := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_neg.mp hx with hx
      rcases Set.mem_sub.mp hx with ⟨a, ha, b, hb, hab⟩
      refine Set.mem_sub.mpr ⟨b, hb, a, ha, ?_⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hab
    · intro hx
      refine Set.mem_neg.mpr ?_
      rcases Set.mem_sub.mp hx with ⟨b, hb, a, ha, hba⟩
      refine Set.mem_sub.mpr ⟨a, ha, b, hb, ?_⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hba
  simpa [hset] using hneg

omit [CompleteSpace K] in
private theorem singletonIndicatorZero_mem_gammaZero :
    δ0 ∈ Γ₀(K) := by
  exact
    indicator_mem_gammaZero_of_nonempty_isClosed_convex
      (by simp) isClosed_singleton (convex_singleton (0 : K))

omit [CompleteSpace K] in
private theorem effectiveDomain_gammaZeroConjugate_singletonIndicatorZero :
    effectiveDomain (δ0∗[singletonIndicatorZero_mem_gammaZero]) = Set.univ := by
  ext u
  rw [mem_effectiveDomain_iff, gammaZeroConjugate_apply]
  have hconj : (((ι[{(0 : K)}] : K → Set.Ioi (⊥ : EReal)).asEReal)∗) = fun _ : K ↦ (0 : EReal) := by
    simpa [ERealFunction.indicator] using
      (conjugate_indicator_submodule_eq_indicator_orthogonal (⊥ : Submodule ℝ K))
  rw [hconj]
  simp

private theorem hsri_conjugateDomains_singletonIndicator
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (L : H →L[ℝ] K)
    (hsri : (0 : H) ∈ sri (Set.range L.adjoint - effectiveDomain (f∗[hf]))) :
    (0 : H) ∈ sri (effectiveDomain (f∗[hf]) -
      L.adjoint '' effectiveDomain (δ0∗[singletonIndicatorZero_mem_gammaZero])) := by
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hrange_convex : Convex ℝ (Set.range L.adjoint) := by
    let M : Submodule ℝ H := L.adjoint.range
    simpa [M] using M.convex
  have hdom_convex : Convex ℝ (effectiveDomain (f∗[hf])) := hfConj.2.convex_effectiveDomain
  have hsri' : (0 : H) ∈ sri (effectiveDomain (f∗[hf]) - Set.range L.adjoint) :=
    zero_mem_sri_sub_rev_of_zero_mem_sri_sub hrange_convex hdom_convex hsri
  simpa [effectiveDomain_gammaZeroConjugate_singletonIndicatorZero] using hsri'

omit [InnerProductSpace ℝ K] [CompleteSpace K] in
private theorem infimalConvolution_singletonIndicator_zero_eq
    (φ : K → EReal) (hφ_bot : ∀ x, φ x ≠ ⊥) :
    φ □ δ0 = φ := by
  ext x
  rw [infimalConvolution_apply]
  refine le_antisymm ?_ ?_
  · simpa [indicator_apply] using
      (iInf_le (fun y : K ↦ φ y + (δ0 (x - y) : EReal)) x)
  · refine le_iInf ?_
    intro y
    by_cases hxy : y = x
    · subst hxy
      simp [indicator_apply]
    · have hxy0 : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
      calc
        φ x ≤ ⊤ := le_top
        _ = φ y + (δ0 (x - y) : EReal) := by
          rw [show (δ0 (x - y) : EReal) = ⊤ by simp [indicator_apply, hxy0]]
          exact (EReal.add_top_of_ne_bot (hφ_bot y)).symm

omit [CompleteSpace K] in
/-- Helper for the current corollary: the singleton indicator at the origin has a subgradient at `u`
exactly when `u = 0`. -/
private theorem mem_subdifferential_singletonIndicatorZero_iff
    {u v : K} :
    v ∈ (∂ δ0) u ↔ u = 0 := by
  rw [mem_subdifferential_iff]
  constructor
  · intro hu
    by_contra hu0
    have htop_le_zero : (⊤ : EReal) ≤ 0 := by
      have hineq := hu 0
      have hu_top : (δ0 u : EReal) = ⊤ := by
        simp [indicator_apply, hu0]
      have hzero_zero : (δ0 0 : EReal) = 0 := by
        simp [indicator_apply]
      have hleft :
          (⟪(0 : K) - u, v⟫_ℝ : EReal) + (δ0 u : EReal) = ⊤ := by
        rw [hu_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      calc
        (⊤ : EReal) = (⟪(0 : K) - u, v⟫_ℝ : EReal) + (δ0 u : EReal) := hleft.symm
        _ ≤ (δ0 0 : EReal) := hineq
        _ = 0 := hzero_zero
    simp at htop_le_zero
  · intro hu0
    subst hu0
    intro y
    by_cases hy : y = 0
    · subst hy
      simp
    · have hy_top : (δ0 y : EReal) = ⊤ := by
        simp [indicator_apply, hy]
      have hzero_zero : (δ0 0 : EReal) = 0 := by
        simp [indicator_apply]
      calc
        (⟪y - (0 : K), v⟫_ℝ : EReal) + (δ0 0 : EReal) = (⟪y - (0 : K), v⟫_ℝ : EReal) := by
          rw [hzero_zero, add_zero]
        _ ≤ ⊤ := le_top
        _ = (δ0 y : EReal) := hy_top.symm

omit [CompleteSpace K] in
private theorem parallelSum_subdifferential_singletonIndicator_zero_eq
    (A : SetValuedOperator K K) :
    ((A □ ∂ δ0) : SetValuedOperator K K) = A := by
  ext x u
  rw [SetValuedOperator.mem_parallelSum_iff]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rw [SetValuedOperator.mem_inverse_iff] at hy hz
    have hz0 : z = 0 :=
      mem_subdifferential_singletonIndicatorZero_iff.1 hz
    subst z
    simpa [SetValuedOperator.mem_inverse_iff] using hy
  · intro hu
    refine ⟨x, ?_, 0, ?_, by simp⟩
    · simpa [SetValuedOperator.mem_inverse_iff] using hu
    · rw [SetValuedOperator.mem_inverse_iff]
      exact
        mem_subdifferential_singletonIndicatorZero_iff.2 rfl

/- Source/core/bridge triage:
- `source-facing`: this corollary specializes Proposition 25.43 to the pure infimal
  postcomposition `L ▷ f`.
- `core/canonical`: the function owner is Chapter 12 `infimalPostcomposition`, and the operator
  owner is Chapter 25 `parallelComposition`.
- `bridge/view`: this file keeps the source-facing regularity and subdifferential formulas in the
  repository's existing `IsProper ∧ gamma` and `∂ ... = ...` surfaces.
-/

/-! The present corollary is formalized below as the two source clauses `(1)` and `(2)`, so each
conclusion remains a separate theorem. -/

section ParallelComposition

variable {f : H → Set.Ioi (⊥ : EReal)}

/-- Helper for the current corollary: Proposition 25.43 specialized to `δ0`
gives the regularity of `(L ▷ f) □ δ0`. -/
private theorem regularity_infimalConvolution_singletonIndicator
    (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K)
    (hsri :
      (0 : H) ∈ sri (Set.range L.adjoint - effectiveDomain (f∗[hf])))
    :
    IsProper ((L ▷ f) □ δ0) ∧
      ((L ▷ f) □ δ0) ∈ gamma K := by
  exact (
  isProper_and_mem_gamma_infimalPostcomposition_infimalConvolution_of_zero_mem_sri_conjugateDomains
      hf singletonIndicatorZero_mem_gammaZero L
      (hsri_conjugateDomains_singletonIndicator hf L hsri))

/-- Regularity clause of the present corollary: if `f ∈ Γ₀(H)` and
`0 ∈ sri (ran L^* - dom f^*)`, then `L ▷ f` is proper, convex, and lower semicontinuous.
In the project's raw `EReal` owner, this is recorded as `IsProper (L ▷ f)` together with
`(L ▷ f) ∈ gamma K`. -/
theorem isProper_and_mem_gamma_infimalPostcomposition_of_regular
    (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K)
    (hsri :
      (0 : H) ∈ sri (Set.range L.adjoint - effectiveDomain (f∗[hf])))
    :
    IsProper (L ▷ f) ∧
      (L ▷ f) ∈ gamma K := by
  have hmain :
      IsProper ((L ▷ f) □ δ0) ∧
        ((L ▷ f) □ δ0) ∈ gamma K :=
    regularity_infimalConvolution_singletonIndicator hf L hsri
  have hbot : ∀ x, (L ▷ f) x ≠ ⊥ := by
    intro x hx
    have hle : (((L ▷ f) □ δ0) x) ≤ (L ▷ f) x := by
      simpa [infimalConvolution_apply, indicator_apply] using
        (iInf_le (fun y : K ↦ (L ▷ f) y + (δ0 (x - y) : EReal)) x)
    have hconv_bot : (((L ▷ f) □ δ0) x) = ⊥ := by
      exact le_bot_iff.mp <| by simpa [hx] using hle
    exact hmain.1.1 x hconv_bot
  have hcollapse : (L ▷ f) □ δ0 = (L ▷ f) :=
    infimalConvolution_singletonIndicator_zero_eq (L ▷ f) hbot
  constructor
  · rw [← hcollapse]
    exact hmain.1
  · rw [← hcollapse]
    exact hmain.2

/-- Helper for the current corollary: Proposition 25.43 specialized to `δ0`
identifies the subdifferential of `((L ▷ f) □ δ0)`. -/
private theorem subdifferential_infimalConvolution_singletonIndicator_eq_parallelSum
    (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K)
    (hsri :
      (0 : H) ∈ sri (Set.range L.adjoint - effectiveDomain (f∗[hf])))
    :
    ∂ (((L ▷ f) □ δ0)) = (L ▷ ∂ f) □ ∂ δ0 := by
  exact
    subdifferential_infimalPostcomposition_infimalConvolution_eq_parallelSum_of_zero_mem_sri_conjugateDomains
      hf singletonIndicatorZero_mem_gammaZero L
      (hsri_conjugateDomains_singletonIndicator hf L hsri)

/-- Subdifferential clause of the present corollary: if `f ∈ Γ₀(H)` and
`0 ∈ sri (ran L^* - dom f^*)`, then `∂ (L ▷ f) = L ▷ ∂ f`. -/
theorem
    subdifferential_infimalPostcomposition_eq_parallelComposition_of_regular
    (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K)
    (hsri :
      (0 : H) ∈ sri (Set.range L.adjoint - effectiveDomain (f∗[hf])))
    :
    ∂ (L ▷ f) = ((L ▷ ∂ f) : SetValuedOperator K K) := by
  have hproper : IsProper (L ▷ f) :=
    (isProper_and_mem_gamma_infimalPostcomposition_of_regular hf L hsri).1
  have hcollapse : (L ▷ f) □ δ0 = (L ▷ f) :=
    infimalConvolution_singletonIndicator_zero_eq (L ▷ f) hproper.1
  calc
    ∂ (L ▷ f) = ∂ (((L ▷ f) □ δ0)) := by rw [hcollapse]
    _ = (L ▷ ∂ f) □ ∂ δ0 :=
      subdifferential_infimalConvolution_singletonIndicator_eq_parallelSum hf L hsri
    _ = ((L ▷ ∂ f) : SetValuedOperator K K) := by
      exact
        parallelSum_subdifferential_singletonIndicator_zero_eq
          ((L ▷ ∂ f) : SetValuedOperator K K)

/-- Corollary 25.44: if `f ∈ Γ₀(H)` and
`0 ∈ sri (ran L^* - dom f^*)`, then
`L ▷ f` is proper, convex, and lower semicontinuous, and
`∂ (L ▷ f) = L ▷ ∂ f`. On this file's raw `EReal` surface, the regularity clause is recorded
as `IsProper (L ▷ f) ∧ (L ▷ f) ∈ gamma K`. -/
theorem infimalPostcomposition_mem_gammaZero_and_subdifferential_eq_parallelComposition_of_regular
    (hf : f ∈ Γ₀(H))
    (L : H →L[ℝ] K)
    (hsri :
      (0 : H) ∈ sri (Set.range L.adjoint - effectiveDomain (f∗[hf])))
    :
    (IsProper (L ▷ f) ∧
      (L ▷ f) ∈ gamma K) ∧
      ∂ (L ▷ f) = ((L ▷ ∂ f) : SetValuedOperator K K) := by
  constructor
  · exact isProper_and_mem_gamma_infimalPostcomposition_of_regular hf L hsri
  · exact subdifferential_infimalPostcomposition_eq_parallelComposition_of_regular hf L hsri

end ParallelComposition

end ERealFunction

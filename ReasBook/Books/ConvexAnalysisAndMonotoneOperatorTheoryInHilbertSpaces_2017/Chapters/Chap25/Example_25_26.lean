import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap01.Text_1_0_12
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Remark_16_28
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap25.Definition_25_10
import BauschkeLean.Chap25.Example_25_13

open scoped EuclideanSpace InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

noncomputable section

namespace SetValuedOperator

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/- Source/core/bridge triage:
- `source-facing`: Example 25.26 specializes the Remark 16.28 counterexample to the common
  operator `A = B = ∂ f*` and records the three Chapter 25 claims attached to that operator.
- `core/canonical`: the reusable owners are `oneSubSqrtAbsMaxCounterexample`,
  `oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]`,
  `SetValuedOperator.IsThreeStarMonotone`, `Maximal IsMonotone`, and `.range`.
- `bridge/view`: `remark1628ConjugateSubdifferential` names the Example 25.26 operator built from
  the canonical Remark 16.28 counterexample. -/

attribute [local instance] Classical.propDecidable

/-- The common operator `A = B = ∂ f*` attached to the Remark 16.28 counterexample
`f = oneSubSqrtAbsMaxCounterexample`. -/
abbrev remark1628ConjugateSubdifferential : SetValuedOperator ℝ² ℝ² :=
  ∂ (oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero])

private theorem maximal_isMonotone_smul
    {A : SetValuedOperator ℝ² ℝ²} (hA : Maximal IsMonotone A) {γ : ℝ} (hγ : 0 < γ) :
    Maximal IsMonotone (γ • A) := by
  rw [maximal_iff_mem_iff]
  intro x u
  rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ hγ.ne']
  constructor
  · intro hxu y v hv
    rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ hγ.ne'] at hv
    have hrel := (Maximal.mem_iff hA x (γ⁻¹ • u)).1 hxu hv
    rw [← smul_sub, real_inner_smul_right] at hrel
    nlinarith [inv_pos.mpr hγ]
  · intro hrel
    refine (Maximal.mem_iff hA x (γ⁻¹ • u)).2 ?_
    intro y w hw
    have hw' : γ • w ∈ (γ • A) y := by
      simpa [Pi.smul_apply] using Set.smul_mem_smul_set hw
    have hrel' := hrel hw'
    have hrewrite :
        inner ℝ (x - y) (u - γ • w) = γ * inner ℝ (x - y) (γ⁻¹ • u - w) := by
      calc
        inner ℝ (x - y) (u - γ • w)
            = inner ℝ (x - y) (γ • ((γ⁻¹ : ℝ) • u - w)) := by
                congr 2
                calc
                  u - γ • w = γ • ((γ⁻¹ : ℝ) • u) - γ • w := by
                    rw [smul_inv_smul₀ hγ.ne' u]
                  _ = γ • ((γ⁻¹ : ℝ) • u - w) := by
                    rw [smul_sub]
        _ = γ * inner ℝ (x - y) ((γ⁻¹ : ℝ) • u - w) := by
              rw [real_inner_smul_right]
    rw [hrewrite] at hrel'
    nlinarith

private theorem remark1628ConjugateSubdifferential_eq_inverse_subdifferential :
    remark1628ConjugateSubdifferential = (∂ oneSubSqrtAbsMaxCounterexample)⁻¹ := by
  simpa [remark1628ConjugateSubdifferential] using
    (inverse_subdifferential_eq_subdifferential_gammaZeroConjugate
      oneSubSqrtAbsMaxCounterexample oneSubSqrtAbsMaxCounterexample_mem_gammaZero).symm

private theorem remark1628ConjugateSubdifferential_add_self_eq_two_smul :
    remark1628ConjugateSubdifferential + remark1628ConjugateSubdifferential =
      (2 : ℝ) • remark1628ConjugateSubdifferential := by
  ext x u
  constructor
  · intro hu
    rcases Set.mem_add.mp hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    have hconv : Convex ℝ (remark1628ConjugateSubdifferential x) := by
      simpa [remark1628ConjugateSubdifferential] using
        convex_subdifferential
          (oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]) x
    have hmid :
        (1 / 2 : ℝ) • u₁ + (1 - 1 / 2 : ℝ) • u₂ ∈ remark1628ConjugateSubdifferential x :=
      hconv hu₁ hu₂ (by norm_num) (by norm_num) (by norm_num)
    refine Set.mem_smul_set.mpr ?_
    refine ⟨(1 / 2 : ℝ) • u₁ + (1 - 1 / 2 : ℝ) • u₂, hmid, ?_⟩
    calc
      (2 : ℝ) • ((1 / 2 : ℝ) • u₁ + (1 - 1 / 2 : ℝ) • u₂)
          = ((2 : ℝ) * (1 / 2 : ℝ)) • u₁ + ((2 : ℝ) * (1 - 1 / 2 : ℝ)) • u₂ := by
              simp [smul_add, smul_smul]
      _ = (1 : ℝ) • u₁ + (1 : ℝ) • u₂ := by norm_num
      _ = u₁ + u₂ := by simp
  · intro hu
    rcases Set.mem_smul_set.mp hu with ⟨v, hv, rfl⟩
    exact Set.mem_add.mpr ⟨v, hv, v, hv, by simp [two_smul]⟩

private theorem range_smul (γ : ℝ) (A : SetValuedOperator ℝ² ℝ²) :
    (γ • A).range = γ • A.range := by
  ext u
  constructor
  · intro hu
    rcases (SetValuedOperator.mem_range_iff (γ • A) u).1 hu with ⟨x, hx⟩
    rcases Set.mem_smul_set.mp hx with ⟨v, hv, rfl⟩
    exact Set.mem_smul_set.mpr ⟨v, (SetValuedOperator.mem_range_iff A v).2 ⟨x, hv⟩, rfl⟩
  · intro hu
    rcases Set.mem_smul_set.mp hu with ⟨v, hv, rfl⟩
    rcases (SetValuedOperator.mem_range_iff A v).1 hv with ⟨x, hx⟩
    exact (SetValuedOperator.mem_range_iff (γ • A) ((γ : ℝ) • v)).2
      ⟨x, by simpa [Pi.smul_apply] using Set.smul_mem_smul_set hx⟩

private theorem zero_not_mem_remark1628ConjugateSubdifferential_range :
    (0 : ℝ²) ∉ remark1628ConjugateSubdifferential.range := by
  rw [remark1628ConjugateSubdifferential_eq_inverse_subdifferential,
    SetValuedOperator.range_inverse,
    subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq]
  simp

private theorem left_boundary_mem_remark1628ConjugateSubdifferential_range :
    (!₂[(0 : ℝ), (-1 : ℝ)] : ℝ²) ∈ remark1628ConjugateSubdifferential.range := by
  rw [remark1628ConjugateSubdifferential_eq_inverse_subdifferential,
    SetValuedOperator.range_inverse,
    subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq]
  simp

private theorem right_boundary_mem_remark1628ConjugateSubdifferential_range :
    (!₂[(0 : ℝ), (1 : ℝ)] : ℝ²) ∈ remark1628ConjugateSubdifferential.range := by
  rw [remark1628ConjugateSubdifferential_eq_inverse_subdifferential,
    SetValuedOperator.range_inverse,
    subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq]
  simp

/-- Example 25.26 (1): for the Remark 16.28 counterexample `f` on `ℝ²`, if
`A = B = ∂ f*`, then the common operator `A` is `3*` monotone, hence both `A` and `B` are
`3*` monotone. -/
theorem remark1628ConjugateSubdifferential_isThreeStarMonotone :
    remark1628ConjugateSubdifferential.IsThreeStarMonotone := by
  have hproper :
      IsProper
        ((oneSubSqrtAbsMaxCounterexample∗[oneSubSqrtAbsMaxCounterexample_mem_gammaZero]).asEReal) :=
    isProper_of_mem_gammaZero
      (gammaZeroConjugate_mem_gammaZero oneSubSqrtAbsMaxCounterexample_mem_gammaZero)
  simpa [remark1628ConjugateSubdifferential] using
    subdifferential_isThreeStarMonotone hproper

/-- The common operator `A = ∂ f*` in Example 25.26 is maximally monotone by Moreau's theorem,
since `f* ∈ Γ₀(ℝ²)`. -/
theorem remark1628ConjugateSubdifferential_isMaximallyMonotone :
    Maximal IsMonotone remark1628ConjugateSubdifferential := by
  simpa [remark1628ConjugateSubdifferential] using
    subdifferential_isMaximallyMonotone_of_mem_gammaZero
      (gammaZeroConjugate_mem_gammaZero oneSubSqrtAbsMaxCounterexample_mem_gammaZero)

/-- Example 25.26 (2): for the Remark 16.28 counterexample `f` on `ℝ²`, if
`A = B = ∂ f*`, then `A + B` is maximally monotone. Since `A = B`, this is
`Maximal IsMonotone (A + A)`. -/
theorem remark1628ConjugateSubdifferential_add_self_isMaximallyMonotone :
    Maximal IsMonotone
      (remark1628ConjugateSubdifferential + remark1628ConjugateSubdifferential) := by
  simpa [remark1628ConjugateSubdifferential_add_self_eq_two_smul] using
    maximal_isMonotone_smul
      remark1628ConjugateSubdifferential_isMaximallyMonotone
      (show 0 < (2 : ℝ) by norm_num)

/-- Example 25.26 (3): for the Remark 16.28 counterexample `f` on `ℝ²`, if
`A = B = ∂ f*`, then `ran (A + B) ≠ ran A + ran B`. This is the source counterexample showing that
the closure or interior operation in Theorem 25.24 cannot be omitted. -/
theorem remark1628ConjugateSubdifferential_add_self_range_ne_range_sum :
    (remark1628ConjugateSubdifferential + remark1628ConjugateSubdifferential).range ≠
      remark1628ConjugateSubdifferential.range + remark1628ConjugateSubdifferential.range := by
  intro hEq
  have hzero_sum :
      (0 : ℝ²) ∈
        remark1628ConjugateSubdifferential.range + remark1628ConjugateSubdifferential.range := by
    refine Set.mem_add.mpr ?_
    exact ⟨!₂[(0 : ℝ), (-1 : ℝ)], left_boundary_mem_remark1628ConjugateSubdifferential_range,
      !₂[(0 : ℝ), (1 : ℝ)], right_boundary_mem_remark1628ConjugateSubdifferential_range, by
        ext i
        fin_cases i <;> simp⟩
  have hzero_add :
      (0 : ℝ²) ∈
        (remark1628ConjugateSubdifferential + remark1628ConjugateSubdifferential).range := by
    rw [hEq]
    exact hzero_sum
  have hzero_not :
      (0 : ℝ²) ∉
        (remark1628ConjugateSubdifferential + remark1628ConjugateSubdifferential).range := by
    intro hzero
    rw [remark1628ConjugateSubdifferential_add_self_eq_two_smul, range_smul,
      Set.mem_smul_set_iff_inv_smul_mem₀ (show (2 : ℝ) ≠ 0 by norm_num)] at hzero
    exact zero_not_mem_remark1628ConjugateSubdifferential_range (by simpa using hzero)
  exact hzero_not hzero_add

end SetValuedOperator

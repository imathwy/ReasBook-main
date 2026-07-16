import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section04.«0031_Exercise_16»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0027_Remark_II_1_extra_17»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0001_Definition_III_4_extra_1»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0006_Proposition_4_1»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0008_Definition_III_4_extra_6»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0009_Theorem_III_4_extra_7»
import DifferentialForms_Cartan_1970.cartan.III.section10.«0010_Remark_III_4_extra_8»
import DifferentialForms_Cartan_1970.cartan.III.section10.frozen_0011_Theorem_III_4_extra_9.PuncturedBallNormalForm

open Metric Set
open scoped Topology unitInterval

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: analyticity on a neighborhood
of `D` restricts to the `DiffContOnCl` package on `U` once `closure U ⊆ D`. -/
lemma diffContOnCl_of_analyticOnNhd_of_closure_subset
    {D U : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D)
    (hclosure : closure U ⊆ D) :
    DiffContOnCl ℂ f U := by
  -- Restrict analyticity to `closure U`, then package the result in the boundary-value form used
  -- by the maximum-modulus theorem.
  exact (hf.differentiableOn.mono hclosure).diffContOnCl

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: if one analytic branch is
uniformly bounded by the same constant on arbitrarily small centered circles, then that branch is
eventually bounded on the punctured neighborhood filter at `0`. -/
lemma eventuallyBounded_of_shrinkingCircleBounds
    {h : ℂ → ℂ} {ε M : ℝ}
    (hε : 0 < ε)
    (hh_analytic : AnalyticOnNhd ℂ h (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hcircle :
      ∀ δ > 0, ∃ ρ, 0 < ρ ∧ ρ < min δ ε ∧ ∀ z, ‖z‖ = ρ → ‖h z‖ ≤ M) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖h z‖ ≤ B := by
  obtain ⟨R, hR_pos, hR_small, hR_bound⟩ := hcircle (ε / 2) (half_pos hε)
  have hR_lt_ε : R < ε := lt_of_lt_of_le hR_small (min_le_right _ _)
  refine ⟨M, ?_⟩
  have hball : ball (0 : ℂ) R \ ({0} : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
    -- Use the chosen outer radius as the punctured-neighborhood basis element.
    rw [show ball (0 : ℂ) R \ ({0} : Set ℂ) = ball (0 : ℂ) R ∩ ({(0 : ℂ)}ᶜ) by
      ext z
      simp [Set.diff_eq]]
    exact Metric.mem_nhdsWithin_iff.mpr ⟨R, hR_pos, subset_rfl⟩
  refine Filter.mem_of_superset hball ?_
  intro z hz
  have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz.2
  obtain ⟨ρ, hρ_pos, hρ_small, hρ_bound⟩ := hcircle ‖z‖ hz_norm_pos
  have hz_norm_lt_ε : ‖z‖ < ε := by
    have hz_norm_lt_R : ‖z‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz.1
    exact lt_trans hz_norm_lt_R hR_lt_ε
  have hρ_lt_z : ρ < ‖z‖ := by
    have hmin_eq : min ‖z‖ ε = ‖z‖ := min_eq_left (le_of_lt hz_norm_lt_ε)
    simpa [hmin_eq] using hρ_small
  let A : Set ℂ := ball (0 : ℂ) R \ closedBall (0 : ℂ) ρ
  have hA_open : IsOpen A := by
    dsimp [A, Set.diff_eq]
    exact isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl
  have hA_bounded : Bornology.IsBounded A :=
    isBounded_ball.subset fun _ hw ↦ hw.1
  have hA_subset_closedBall : A ⊆ closedBall (0 : ℂ) R := by
    intro w hw
    have hw_lt : ‖w‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw.1
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hw_lt
  have hA_subset_outsideBall : A ⊆ (ball (0 : ℂ) ρ)ᶜ := by
    intro w hw hw_ball
    have hw_closed : w ∈ closedBall (0 : ℂ) ρ := by
      have hw_lt : ‖w‖ < ρ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw_ball
      simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hw_lt
    exact hw.2 hw_closed
  have hclosure_subset :
      closure A ⊆ ball (0 : ℂ) ε \ ({0} : Set ℂ) := by
    intro w hw
    have hw_closedBall : w ∈ closedBall (0 : ℂ) R :=
      closure_minimal hA_subset_closedBall Metric.isClosed_closedBall hw
    have hw_not_ball : w ∈ (ball (0 : ℂ) ρ)ᶜ :=
      closure_minimal hA_subset_outsideBall
        (show IsClosed ((ball (0 : ℂ) ρ)ᶜ) from isOpen_ball.isClosed_compl) hw
    constructor
    · -- The closure annulus still lies inside the original punctured-ball radius `ε`.
      exact lt_of_le_of_lt hw_closedBall hR_lt_ε
    · -- Staying outside `ball (0, ρ)` keeps the closure away from the puncture.
      intro hw0
      have hw_mem_ball : w ∈ ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm, hw0]
        simpa using hρ_pos
      exact hw_not_ball hw_mem_ball
  have hdiff : DiffContOnCl ℂ h A :=
    diffContOnCl_of_analyticOnNhd_of_closure_subset hh_analytic hclosure_subset
  have hz_closure : z ∈ closure A := by
    have hzA : z ∈ A := by
      constructor
      · exact hz.1
      · intro hz_closed
        have hz_le : ‖z‖ ≤ ρ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz_closed
        exact not_le_of_gt hρ_lt_z hz_le
    exact subset_closure hzA
  have hboundary :
      ∀ w ∈ frontier A, ‖h w‖ ≤ M := by
    intro w hw
    rw [frontier, mem_diff] at hw
    have hw_closedBall : w ∈ closedBall (0 : ℂ) R :=
      closure_minimal hA_subset_closedBall Metric.isClosed_closedBall hw.1
    have hw_not_ball : w ∈ (ball (0 : ℂ) ρ)ᶜ :=
      closure_minimal hA_subset_outsideBall
        (show IsClosed ((ball (0 : ℂ) ρ)ᶜ) from isOpen_ball.isClosed_compl) hw.1
    have hw_not_mem : w ∉ A := by
      simpa [hA_open.interior_eq] using hw.2
    have hw_ge_ρ : ρ ≤ ‖w‖ := by
      by_contra hw_lt
      exact hw_not_ball (by simpa [Metric.mem_ball, dist_eq_norm] using hw_lt)
    by_cases hw_ρ : ‖w‖ = ρ
    · -- Points on the inner boundary use the chosen shrinking-circle estimate.
      exact hρ_bound w hw_ρ
    · by_cases hw_R : ‖w‖ = R
      · -- Points on the outer boundary use the fixed outer-circle estimate.
        exact hR_bound w hw_R
      · have hw_le_R : ‖w‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hw_closedBall
        have hw_lt_R : ‖w‖ < R := lt_of_le_of_ne hw_le_R hw_R
        have hwA : w ∈ A := by
          constructor
          · simpa [Metric.mem_ball, dist_eq_norm] using hw_lt_R
          · intro hw_closed
            have hw_le_ρ : ‖w‖ ≤ ρ := by
              simpa [Metric.mem_closedBall, dist_eq_norm] using hw_closed
            exact not_le_of_gt (lt_of_le_of_ne hw_ge_ρ (Ne.symm hw_ρ)) hw_le_ρ
        exact False.elim (hw_not_mem hwA)
  -- Apply the maximum-modulus theorem on the annulus between the inner shrinking circle and the
  -- fixed outer circle.
  show ‖h z‖ ≤ M
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hA_bounded hdiff hboundary hz_closure

/-- Helper for Cartan section10 frozen_0011_Theorem_III_4_extra_9: once every small scale admits
some centered circle on which one reciprocal branch is uniformly bounded, one branch is eventually
bounded on the punctured-neighborhood filter. -/
lemma eventualReciprocalBranch_of_smallCircles
    {g : ℂ → ℂ} {ε K : ℝ}
    (hε : 0 < ε)
    (hgInv :
      AnalyticOnNhd ℂ (fun z ↦ (g z)⁻¹) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (honeSubInv :
      AnalyticOnNhd ℂ (fun z ↦ ((1 - g z)⁻¹)) (ball (0 : ℂ) ε \ ({0} : Set ℂ)))
    (hcircle :
      ∀ δ > 0, ∃ ρ, 0 < ρ ∧ ρ < min δ ε ∧
        ((∀ z, ‖z‖ = ρ → ‖(g z)⁻¹‖ ≤ K) ∨
          ∀ z, ‖z‖ = ρ → ‖((1 - g z)⁻¹)‖ ≤ K)) :
    (∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖(g z)⁻¹‖ ≤ B) ∨
      ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖((1 - g z)⁻¹)‖ ≤ B := by
  classical
  by_cases hleft :
      ∀ δ > 0, ∃ ρ, 0 < ρ ∧ ρ < min δ ε ∧
        ∀ z, ‖z‖ = ρ → ‖(g z)⁻¹‖ ≤ K
  · -- If arbitrarily small circles always carry the `g⁻¹` bound, apply the existing
    -- shrinking-circle maximum-modulus package directly to that branch.
    exact Or.inl <|
      eventuallyBounded_of_shrinkingCircleBounds
        (h := fun z ↦ (g z)⁻¹) hε hgInv hleft
  · push Not at hleft
    rcases hleft with ⟨δ₀, hδ₀pos, hδ₀fail⟩
    have hright :
        ∀ δ > 0, ∃ ρ, 0 < ρ ∧ ρ < min δ ε ∧
          ∀ z, ‖z‖ = ρ → ‖((1 - g z)⁻¹)‖ ≤ K := by
      intro δ hδ
      let δ' : ℝ := min δ δ₀
      have hδ' : 0 < δ' := by
        dsimp [δ']
        exact lt_min hδ hδ₀pos
      rcases hcircle δ' hδ' with ⟨ρ, hρpos, hρsmall, hρbranch⟩
      refine ⟨ρ, hρpos, ?_, ?_⟩
      · -- The circle chosen below `min δ' ε` is automatically below `min δ ε`.
        exact lt_of_lt_of_le hρsmall (min_le_min_right ε (min_le_left δ δ₀))
      · rcases hρbranch with hρleft | hρright
        · -- Below the exceptional scale `δ₀`, the left branch is forbidden by construction.
          exfalso
          obtain ⟨z, hz_norm, hz_large⟩ := hδ₀fail ρ hρpos
            (lt_of_lt_of_le hρsmall (min_le_min_right ε (min_le_right δ δ₀)))
          exact not_lt_of_ge (hρleft z hz_norm) hz_large
        · exact hρright
    -- The remaining circles therefore all land in the `(1 - g)⁻¹` branch.
    exact Or.inr <|
      eventuallyBounded_of_shrinkingCircleBounds
        (h := fun z ↦ ((1 - g z)⁻¹)) hε honeSubInv hright


import Mathlib
import DifferentialForms_Cartan_1970.VI.section24.«0002_Corollary_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Set Metric

/-- Corollary 2. Two simply connected open sets `D₁` and `D₂` of the complex plane are always
homeomorphic. -/
theorem simply_connected_open_sets_homeomorphic {D₁ D₂ : Set ℂ} (hD₁_open : IsOpen D₁)
    (hD₂_open : IsOpen D₂) (hD₁_simplyConnected : IsSimplyConnected D₁)
    (hD₂_simplyConnected : IsSimplyConnected D₂) : Nonempty (D₁ ≃ₜ D₂) := by
  let eUnit : (univ : Set ℂ) ≃ₜ ball (0 : ℂ) 1 :=
    (Homeomorph.Set.univ ℂ).trans (Homeomorph.unitBall : ℂ ≃ₜ ball (0 : ℂ) 1)
  have hUnitBall_simplyConnected : IsSimplyConnected (ball (0 : ℂ) 1) := by
    change SimplyConnectedSpace (ball (0 : ℂ) 1)
    let _ : ContractibleSpace (ball (0 : ℂ) 1) :=
      ((Homeomorph.unitBall : ℂ ≃ₜ ball (0 : ℂ) 1)).contractibleSpace_iff.mp inferInstance
    infer_instance
  have hUnitBall_proper : ball (0 : ℂ) 1 ≠ univ := by
    intro hUnitBall
    have : (2 : ℂ) ∈ ball (0 : ℂ) 1 := by simp [hUnitBall]
    norm_num [mem_ball_zero_iff] at this
  by_cases hD₁_univ : D₁ = univ
  · by_cases hD₂_univ : D₂ = univ
    · exact hD₁_univ ▸ hD₂_univ ▸ ⟨Homeomorph.refl _⟩
    · rcases
        simply_connected_open_sets_biholomorphic hD₂_open isOpen_ball hD₂_simplyConnected
          hUnitBall_simplyConnected hD₂_univ hUnitBall_proper with
        ⟨e⟩
      refine hD₁_univ ▸ ⟨?_⟩
      exact eUnit.trans e.toHomeomorph.symm
  · by_cases hD₂_univ : D₂ = univ
    · rcases
        simply_connected_open_sets_biholomorphic hD₁_open isOpen_ball hD₁_simplyConnected
          hUnitBall_simplyConnected hD₁_univ hUnitBall_proper with
        ⟨e⟩
      refine hD₂_univ ▸ ⟨?_⟩
      exact e.toHomeomorph.trans eUnit.symm
    · rcases
        simply_connected_open_sets_biholomorphic hD₁_open hD₂_open hD₁_simplyConnected
          hD₂_simplyConnected hD₁_univ hD₂_univ with
        ⟨e⟩
      exact ⟨e.toHomeomorph⟩

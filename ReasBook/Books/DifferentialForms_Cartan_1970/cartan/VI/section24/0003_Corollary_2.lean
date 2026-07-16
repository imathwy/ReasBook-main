import Mathlib
import DifferentialForms_Cartan_1970.cartan.VI.section24.«0002_Corollary_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Set Metric

/-- Corollary 2. Two simply connected open sets `D₁` and `D₂` of the complex plane are always
homeomorphic. -/
theorem simply_connected_open_sets_homeomorphic {D₁ D₂ : Set ℂ} (hD₁_open : IsOpen D₁)
    (hD₂_open : IsOpen D₂) (hD₁_simplyConnected : IsSimplyConnected D₁)
    (hD₂_simplyConnected : IsSimplyConnected D₂) : Nonempty (D₁ ≃ₜ D₂) := by
  -- Compare the whole plane with the standard proper simply connected model, the unit disc.
  let eUnit : (univ : Set ℂ) ≃ₜ ball (0 : ℂ) 1 :=
    (Homeomorph.Set.univ ℂ).trans (Homeomorph.unitBall : ℂ ≃ₜ ball (0 : ℂ) 1)
  -- Follow the textbook split: either a domain is all of `ℂ`, or both are proper.
  by_cases hD₁_univ : D₁ = univ
  · by_cases hD₂_univ : D₂ = univ
    -- If both domains are the whole plane, the identity homeomorphism closes the goal.
    · exact hD₁_univ ▸ hD₂_univ ▸ ⟨Homeomorph.refl _⟩
    -- If `D₁ = ℂ` and `D₂` is proper, compare `D₂` with the unit disc and compose with `eUnit`.
    · rcases
        simply_connected_open_sets_biholomorphic hD₂_open isOpen_ball hD₂_simplyConnected
          unitDisc_isSimplyConnected hD₂_univ unitDisc_ne_univ with
        ⟨e⟩
      refine hD₁_univ ▸ ⟨?_⟩
      exact eUnit.trans e.toHomeomorph.symm
  · by_cases hD₂_univ : D₂ = univ
    -- If `D₂ = ℂ` and `D₁` is proper, use the symmetric composition through the unit disc.
    · rcases
        simply_connected_open_sets_biholomorphic hD₁_open isOpen_ball hD₁_simplyConnected
          unitDisc_isSimplyConnected hD₁_univ unitDisc_ne_univ with
        ⟨e⟩
      refine hD₂_univ ▸ ⟨?_⟩
      exact e.toHomeomorph.trans eUnit.symm
    -- If both domains are proper, Corollary 1 already gives a biholomorphism and hence a
    -- homeomorphism.
    · rcases
        simply_connected_open_sets_biholomorphic hD₁_open hD₂_open hD₁_simplyConnected
          hD₂_simplyConnected hD₁_univ hD₂_univ with
        ⟨e⟩
      exact ⟨e.toHomeomorph⟩

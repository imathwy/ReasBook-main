import Mathlib
import DifferentialForms_Cartan_1970.VI.section22.«0006_Definition_VI_1_extra_4»
import DifferentialForms_Cartan_1970.VI.section24.«0001_Theorem_VI_3_extra_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set

-- Domain sampling note:
-- * source-facing layer: the corollary asserts existence of a biholomorphic correspondence
--   between two planar domains;
-- * core/canonical owner in this chapter: `HolomorphicIsomorph`;
-- * bridge/view layer used immediately downstream: `HolomorphicIsomorph.toHomeomorph`;
-- * discarded bridge/view layer: the local predecessor structure `BiholomorphicOn`, which only
--   recopied the owner data already bundled by `OpenPartialHomeomorph` plus holomorphicity.

namespace HolomorphicIsomorph

variable {D D' : Set ℂ}

/-- Helper for Corollary 1: the inverse of a holomorphic isomorphism is again a holomorphic
isomorphism. -/
def symm (e : HolomorphicIsomorph D D') : HolomorphicIsomorph D' D :=
  ⟨(e : OpenPartialHomeomorph ℂ ℂ).symm,
    { source_eq := e.target_eq
      target_eq := e.source_eq
      analyticOn_toFun := e.analyticOn_invFun
      analyticOn_symm := e.analyticOn_toFun }⟩

end HolomorphicIsomorph

/-- Helper for Corollary 1: if two domains are both holomorphically isomorphic to the same target,
then they are holomorphically isomorphic to each other. -/
theorem nonempty_holomorphic_isomorph_of_common_target {D₁ D₂ Δ : Set ℂ}
    (h₁ : Nonempty (HolomorphicIsomorph D₁ Δ)) (h₂ : Nonempty (HolomorphicIsomorph D₂ Δ)) :
    Nonempty (HolomorphicIsomorph D₁ D₂) := by
  rcases h₁ with ⟨e₁⟩
  rcases h₂ with ⟨e₂⟩
  -- Compose through the common model `Δ`, reversing the second isomorphism.
  exact ⟨e₁.trans e₂.symm⟩

/-- Corollary 1. Two simply-connected open sets `D₁` and `D₂` of the complex plane are
biholomorphic whenever both are proper open subsets of `ℂ`. -/
theorem simply_connected_open_sets_biholomorphic {D₁ D₂ : Set ℂ} (hD₁_open : IsOpen D₁)
    (hD₂_open : IsOpen D₂) (hD₁_simplyConnected : IsSimplyConnected D₁)
    (hD₂_simplyConnected : IsSimplyConnected D₂) (hD₁_proper : D₁ ≠ univ)
    (hD₂_proper : D₂ ≠ univ) : Nonempty (HolomorphicIsomorph D₁ D₂) := by
  -- Model each proper simply connected domain on the common unit disc.
  have h₁ :
      Nonempty (HolomorphicIsomorph D₁ (Metric.ball (0 : ℂ) 1)) :=
    simply_connected_open_set_biholomorphic_to_open_unit_disc
      hD₁_open hD₁_simplyConnected hD₁_proper
  have h₂ :
      Nonempty (HolomorphicIsomorph D₂ (Metric.ball (0 : ℂ) 1)) :=
    simply_connected_open_set_biholomorphic_to_open_unit_disc
      hD₂_open hD₂_simplyConnected hD₂_proper
  -- Then compose one model with the inverse of the other.
  exact nonempty_holomorphic_isomorph_of_common_target h₁ h₂

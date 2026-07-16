import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap11.Remark_11_11_1_3.TensorCharacterRingRestriction
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1

-- Stable restriction-family infrastructure extracted from Remark 11-11.1-3.

noncomputable section

namespace Representation

section CharacterizationOfCharacters

open scoped Pointwise Representation TensorProduct

variable {G : Type} [Group G] [Finite G]

/-- The restriction algebra hom from `R(G)` to the finite product of the local rings `R(H)`. -/
def characterRingRestriction (X : Finset (Subgroup G)) : R(G) →ₐ[ℤ] (Π H : X, R(H.1)) :=
  Pi.algHom ℤ (fun H : X ↦ R(H.1)) fun H ↦ H.1 ↾R[ℂ]

/-- Helper for Remark 11-11.1-3: evaluating the restriction family at `H` recovers the ordinary
restriction of the global character to `H`. -/
@[simp] theorem characterRingRestriction_apply
    (X : Finset (Subgroup G)) (χ : R(G)) (H : X) (h : H.1) :
    ((characterRingRestriction X χ H : R(H.1)) : H.1 → ℂ) h = (χ : G → ℂ) h := by
  simp [characterRingRestriction]

end CharacterizationOfCharacters

end Representation

import LinearRepresentations_Serre_1977.Serre.Chap10.Lemma_10_10_2_3

noncomputable section

namespace Representation

section

variable {G : Type} [Group G] [Finite G]
variable {A : Type} [CommRing A] [Algebra A ℂ] [IsIntegralClosure A ℤ ℂ]
variable {p : ℕ} [Fact p.Prime]

/-- Helper for Theorem 10-10.2-1: the theorem-local descent bridge is the Chapter `10.2.3`
intersection theorem specialized for this rescue file. -/
theorem pElementaryInducedCharacterScalarExtension_inter_characterRing_eq_image_local :
    ((pElementaryInducedCharacterScalarExtension A p G : Set (G → ℂ)) ∩
        (R(G) : Set (G → ℂ))) =
      ((LinearMap.range (pElementaryInducedCharacterToFunction p G)) : Set (G → ℂ)) := by
  simpa using
    pElementaryInducedCharacterScalarExtension_inter_characterRing_eq_image
      (A := A) (G := G) (p := p)

end

end Representation

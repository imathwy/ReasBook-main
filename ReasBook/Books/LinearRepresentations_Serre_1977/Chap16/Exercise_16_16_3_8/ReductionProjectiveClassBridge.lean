import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4

noncomputable section

universe u

open scoped Representation

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Exercise 16-16.3-8: on an actual projective generator, the reduction equivalence
agrees with the generator formula for reduction modulo the maximal ideal. -/
theorem projectiveGrothendieckReductionEquiv_projectiveClass_eq_residueFieldReduction_public
    (P : FiniteProjectiveGroupAlgebraModule A G) :
    projectiveGrothendieckReductionEquiv (A := A) (G := G) [P]ₚ₀ =
      [P.residueFieldReduction]ₚ₀ := by
  -- Route correction: the source proof only needs the generator formula, so we change from the
  -- opaque equivalence surface to the canonical reduction homomorphism owner.
  change
    projectiveGrothendieckReductionHom (A := A) (G := G) [P]ₚ₀ =
      [P.residueFieldReduction]ₚ₀
  -- On generator classes, Corollary `14-14.4-3` already gives the required reduction formula.
  simpa using
    (projectiveGrothendieckReductionHom_projectiveClass_eq (A := A) (G := G) P)

end

end Representation

import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.DiagonalQuotient

noncomputable section

universe u

namespace Representation

section RegularIntegerDiagonalQuotient

variable {p : ℕ}
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

/-- The additive quotient by the regular integer diagonal lattice is the product of the
coordinatewise cyclic groups with moduli given by the centralizer `p`-parts. -/
noncomputable def regularIntegerDiagonalQuotient_addEquiv_pi_centralizerPPart :
    ((PRegularConjClass G p → ℤ) ⧸
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) ≃+
      ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1) :=
  regularIntegerQuotient_addEquiv_pi_centralizerPPart (p := p) (G := G)

end RegularIntegerDiagonalQuotient

end Representation

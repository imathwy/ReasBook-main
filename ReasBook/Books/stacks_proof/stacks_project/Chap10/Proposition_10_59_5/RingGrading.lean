import stacks_proof.stacks_project.Chap10.Proposition_10_59_5.OwnerPackaging

universe u

open scoped Ideal

noncomputable section

namespace Ideal

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

-- Register the quotient-Rees structure declarations from the owner-package module for downstream
-- helper files that depend on fast ambient typeclass search.
attribute [instance] idealAssociatedGradedRing_commRing
attribute [instance] idealAssociatedGradedRing_addCommMonoid
attribute [instance] idealAssociatedGradedRing_monoid
attribute [instance] idealAssociatedGradedRing_module
attribute [instance] idealAssociatedGradedRing_algebra
-- Register the owner-package graded monoid for the downstream graded-algebra instance.
attribute [instance] idealAssociatedGradedRingGrade_gradedMonoid

/-- Helper for Proposition 10.59.5: the quotient-Rees decomposition equips the associated graded
ring with its internal grading. -/
instance idealAssociatedGradedRing_gradedAlgebra :
    GradedAlgebra (idealAssociatedGradedRingGrade (R := R) I) :=
  GradedAlgebra.ofAlgHom (idealAssociatedGradedRingGrade (R := R) I)
    (idealAssociatedGradedRing_decomposeAlgHom (R := R) I)
    (idealAssociatedGradedRing_decomposeAlgHom_right_inv (R := R) I)
    (idealAssociatedGradedRing_decomposeAlgHom_left_inv (R := R) I)

/-- Helper for Proposition 10.59.5: the quotient-Rees model of `gr_I(R)` is naturally an algebra
over `R / I`. -/
noncomputable instance idealAssociatedGradedRing_algebraQuotient :
    Algebra (R ⧸ I) (idealAssociatedGradedRing I) :=
  Ideal.Quotient.algebraQuotientMapQuotient

end Ideal

end

import Mathlib

universe u

noncomputable section

open Polynomial

section

variable {R : Type u} [CommRing R]

/-- The quotient-Rees model of the associated graded ring `⊕_{n ≥ 0} I^n / I^(n + 1)` of an
ideal `I`. -/
abbrev idealAssociatedGradedRing (I : Ideal R) : Type u :=
  (reesAlgebra I) ⧸ Ideal.map (algebraMap R (reesAlgebra I)) I

instance idealAssociatedGradedRing.commRing (I : Ideal R) :
    CommRing (idealAssociatedGradedRing I) := by
  dsimp [idealAssociatedGradedRing]
  infer_instance

instance idealAssociatedGradedRing.algebra (I : Ideal R) :
    Algebra R (idealAssociatedGradedRing I) := by
  dsimp [idealAssociatedGradedRing]
  infer_instance

/-- The quotient-Rees model of `gr_I(R)` is naturally an algebra over `R / I`. -/
instance idealAssociatedGradedRing.algebraQuotient (I : Ideal R) :
    Algebra (R ⧸ I) (idealAssociatedGradedRing I) :=
  Ideal.Quotient.algebraQuotientMapQuotient

/-- The degree-one monomial attached to an element of `I` lies in the Rees algebra of `I`. -/
theorem idealAssociatedGradedDegreeOne_mem {I : Ideal R} (x : I) :
    monomial 1 (x : R) ∈ reesAlgebra I := by
  refine (reesAlgebra.monomial_mem (I := I) (i := 1) (r := (x : R))).2 ?_
  simpa [pow_one] using x.2

/-- The degree-one class in the associated graded ring determined by an element of `I`. -/
def idealAssociatedGradedDegreeOne {I : Ideal R} (x : I) :
    idealAssociatedGradedRing I :=
  Ideal.Quotient.mk _ ⟨monomial 1 (x : R), idealAssociatedGradedDegreeOne_mem x⟩

end

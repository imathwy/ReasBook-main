import StacksProject_2024.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial
open HomogeneousLocalization

section

variable {R : Type u} [CommRing R] [IsDomain R]

omit [IsDomain R] in
private theorem reesAlgebraDegreeOne_ne_zero (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    reesAlgebraDegreeOne I a ≠ 0 := by
  intro h
  exact ha <| (monomial_eq_zero_iff (a : R) 1).mp <| by
    simpa [reesAlgebraDegreeOne] using congrArg Subtype.val h

/-- An affine blowup chart of a domain along a nonzero chart parameter is a domain. -/
instance (I : Ideal R) (a : I) [Fact ((a : R) ≠ 0)] :
    IsDomain (affineBlowupChart I a) := by
  let x : Submonoid (reesAlgebra I) := Submonoid.powers (reesAlgebraDegreeOne I a)
  let A := HomogeneousLocalization (reesAlgebraGrade I) x
  change IsDomain A
  have hdeg : reesAlgebraDegreeOne I a ≠ 0 := reesAlgebraDegreeOne_ne_zero I a Fact.out
  haveI : IsDomain (Localization.Away (reesAlgebraDegreeOne I a)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away (reesAlgebraDegreeOne I a))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hdeg)
  haveI : IsDomain (Localization x) := by
    simpa [x, Away] using
      (inferInstance : IsDomain (Localization.Away (reesAlgebraDegreeOne I a)))
  exact Function.Injective.isDomain (algebraMap A (Localization x))
    (val_injective x)

/-- Lemma 10.70.10: if `R` is a domain, `I ⊂ R` is an ideal, and `a ∈ I` is nonzero, then the
affine blowup chart `(Bl_I(R))_(a^(1)) = R[I/a]` is a domain. -/
theorem affineBlowupChart_isDomain (I : Ideal R) (a : I) (ha : (a : R) ≠ 0) :
    IsDomain (affineBlowupChart I a) := by
  haveI : Fact ((a : R) ≠ 0) := ⟨ha⟩
  infer_instance

end

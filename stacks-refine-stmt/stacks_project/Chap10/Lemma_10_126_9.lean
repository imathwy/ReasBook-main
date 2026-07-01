import Mathlib
import stacks_project.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']

-- Proof sketch: choose finitely many generators of the finite type `R`-algebra `S'`; surjectivity
-- modulo `I S'` lifts each generator to an element of the image up to an error term in `I S'`.
-- Those error coefficients lie in a finitely generated `ℤ`-subalgebra of `R`, where Lemma
-- `10.32.5` upgrades local nilpotence to nilpotence. The resulting polynomial change of variables
-- is then an automorphism, forcing the generators themselves to lie in the image.
/-- Lemma 10.126.9: let `I` be a locally nilpotent ideal of `R`. If `f : S →ₐ[R] S'` becomes
surjective after quotienting `S'` by `I S'`, and `S'` is of finite type over `R`, then `f` is
surjective. -/
theorem surjective_of_surjective_quotient_of_finiteType_of_locallyNilpotent
    {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] S')
    (hquot :
      Function.Surjective ((Ideal.Quotient.mkₐ R (I.map (algebraMap R S'))).comp f))
    [Algebra.FiniteType R S'] :
    Function.Surjective f := sorry

end

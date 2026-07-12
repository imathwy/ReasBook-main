import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Over

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: choose lifts in `S` of a finite set of algebra generators of
-- `S ⧸ I.map (algebraMap R S)` over `R ⧸ I`, let `A ⊆ S` be the `R`-subalgebra they generate, and
-- apply Nakayama's lemma to the `R`-module cokernel of `A → S` using that `I` is nilpotent.
/-- Lemma 10.126.8: if `I` is a nilpotent ideal of `R` and the quotient algebra
`S ⧸ I.map (algebraMap R S)` is of finite type over `R ⧸ I`, then `S` is of finite type over
`R`. -/
theorem finiteType_of_quotient_finiteType_of_isNilpotent (I : Ideal R) (hI : IsNilpotent I)
    [Algebra.FiniteType (R ⧸ I) (S ⧸ I.map (algebraMap R S))] : Algebra.FiniteType R S := sorry

end

import Mathlib
import Serre.Chap10.Definition_10_10_1_2
import Serre.Chap12.CharacterRingOverFieldScalarExtension
import Serre.Chap12.Theorem_12_12_4_1
import Serre.Chap12.GaloisPowerClasses

noncomputable section

open Representation
open PrimeSpectrum
open scoped Representation

universe u v w

namespace Representation

open IsCyclotomicExtension.Rat

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)
variable [Algebra A K] [IsFractionRing A K]
variable {p : ℕ} [Fact p.Prime]

local notation "ΓK" => Γ[K](G)

/- Route correction: this is source Lemma 16 in §12.7. If the `p`-regular components
of two elements are `Γ_K`-conjugate, then every function in `A ⊗ R_K(G)` has congruent values
modulo each prime of `A` above `(p)`. Downstream Lemma 18 only needs the ideal-membership
form below; quotient formulations should be derived from this theorem locally. -/

theorem character_value_sub_mem_primeIdealOverPrime_of_pRegularComponents_galoisPowerConjugate
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) {x y : G}
    (hxy :
      pRegularGaloisPowerClassMk ΓK p
          ⟨pRegularComponent p x, isPRegular_pRegularComponent (p := p) x⟩ =
        pRegularGaloisPowerClassMk ΓK p
          ⟨pRegularComponent p y, isPRegular_pRegularComponent (p := p) y⟩)
    (Q : PrimeSpectrum A) (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal) :
    ∃ q : Q.asIdeal, algebraMap A K q.1 = f x - f y := by
  -- Serre, §12.7, Lemma 16: reduce to the `p'`-component and apply the same congruence
  -- argument as Lemma 7, using Corollary 12.4.2 for `Γ_K`-class constancy. Since owner values live
  -- in the fraction field `K`, membership in a prime ideal of `A` is stated by an `A`-lift in that
  -- ideal whose image is the corresponding difference.
  sorry

end

end Representation

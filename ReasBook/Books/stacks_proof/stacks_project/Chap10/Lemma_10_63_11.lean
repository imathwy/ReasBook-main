import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_63_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/- Domain triage: this item is in commutative algebra of associated primes under restriction of
scalars.
* `source-facing`: the textbook statement is about the source-facing set
  `associatedPrimesOfModule`.
* `core/canonical`: the owner abstraction in mathlib is `associatedPrimes R M`.
* `bridge/view`: the primitive contraction statement already lives upstream as
  `Ideal.isAssociatedToModule_comap` on the predicate `Ideal.IsAssociatedToModule`.
The present file should therefore stay a thin set-level bridge, with no parallel owner wrapper.
-/

/-- Lemma 10.63.11: contracting associated primes of an `S`-module `M` along `Spec(S) → Spec(R)`
lands in the associated primes of `M` viewed as an `R`-module. -/
@[stacks 05BW]
theorem associatedPrimesOfModule_image_comap_subset :
    Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M ⊆ associatedPrimesOfModule R M :=
  by
    rintro _ ⟨P, hP, rfl⟩
    exact Ideal.isAssociatedToModule_comap R M hP

end

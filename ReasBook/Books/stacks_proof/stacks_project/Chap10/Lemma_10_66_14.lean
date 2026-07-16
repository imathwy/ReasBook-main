import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_66_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
variable [IsScalarTower R (R ⧸ I) M]

/- Domain triage:
* primary domain: weakly associated primes under restriction of scalars in commutative algebra;
* `core/canonical` owner: the set-valued declaration `weaklyAssociatedPrimes R M`;
* `bridge/view`: the quotient-map specialization `R → R ⧸ I`.

This item adds no new primitive data: it is exactly the quotient specialization of the owner
theorem `weaklyAssociatedPrimes.restrictScalars_eq_image_comap_of_finite`, so the file should
reuse that theorem directly rather than keeping a parallel local shell. -/

/- Lemma 10.66.14: via the canonical map `Spec (R ⧸ I) → Spec R`, the weakly associated primes of
the `R ⧸ I`-module `M` are exactly the weakly associated primes of `M` viewed as an `R`-module. -/
#check
  (by
    simpa [Ideal.Quotient.algebraMap_eq] using
      (weaklyAssociatedPrimes.restrictScalars_eq_image_comap_of_finite :
        Ideal.comap (algebraMap R (R ⧸ I)) '' weaklyAssociatedPrimes (R ⧸ I) M =
          weaklyAssociatedPrimes R M))

end

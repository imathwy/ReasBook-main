import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_153_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_153_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [StrictHenselianLocalRing R] [StrictHenselianLocalRing S]
variable (φ : R →+* S) [IsLocalHom φ]
variable {n : ℕ}

/-
Domain-style sampling:
* primary domain: points of étale algebras over strictly henselian local rings;
* sampled owner declarations of the same kind:
  `StrictHenselianLocalRing`,
  `henselian_local_ring_tfae`,
  `etale_retraction_unique_property`,
  `Algebra.Etale.iff_exists_algEquiv_prod`;
* best owner abstraction:
  for `A := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)`, the core owner is the étale
  `R`-algebra `A`; the two polynomial zero loci are only the source-facing presentations of the
  `R`- and `S`-points of that owner algebra;
* primitive data vs. derived API:
  the primitive data are the equations `P i` and the owner hypothesis `[Algebra.Etale R A]`;
  the solution sets are derived from algebra maps out of `A` by the quotient universal property of
  `MvPolynomial.aeval`, not additional primitive structure.

Source/core/bridge triage:
* `source-facing`: the coordinate zero-locus bijection theorem below;
* `core/canonical`: `StrictHenselianLocalRing`, the henselian clause
  `etale_retraction_unique_property`, and the field-level classification
  `Algebra.Etale.iff_exists_algEquiv_prod`;
* `bridge/view`: identifying a common zero of `P` with an `R`-algebra map from the presented
  quotient, and similarly after applying `φ` to coefficients.
-/

-- Proof sketch: for an étale `R`-algebra `A`, the map on point sets `A(R) → A(S)` induced by the
-- local homomorphism `φ : R →+* S` is bijective over strictly henselian local rings. One proves
-- this by applying Lemma `10.153.3`, through the canonical owner clause
-- `etale_retraction_unique_property`, to pass from `A`-points over `R` and `S` to points over the
-- residue fields of `R` and `S`; then `Algebra.Etale.iff_exists_algEquiv_prod` identifies the
-- residue-field base change of `A` with a finite product of copies of the corresponding separably
-- closed residue field.
/-- Owner-level point statement for Lemma 10.153.12: if `φ : R →+* S` is a local homomorphism
between strictly henselian local rings and `A` is an étale `R`-algebra, then composition with `φ`
induces a bijection `A(R) ≃ A(S)`, formalized as a bijection on `R`-algebra maps
`A →ₐ[R] R` and `A →ₐ[R] S`. -/
theorem strictlyHenselian_localHom_bijective_pointMap_of_etale
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    letI : Algebra R S := φ.toAlgebra
    Function.Bijective (fun f : A →ₐ[R] R ↦ (Algebra.ofId R S).comp f) := sorry

-- The coordinate zero-locus statement is the source-facing bridge obtained by identifying common
-- zeros of `P` with `R`- and `S`-points of the étale quotient
-- `R[x_1, ..., x_n] / (P_1, ..., P_n)` via `MvPolynomial.aeval` and `Ideal.Quotient.liftₐ`.
/-- Lemma 10.153.12: for a local homomorphism `φ : R →+* S` between strictly henselian local
rings, if `R[x_1, ..., x_n] / (P_1, ..., P_n)` is étale over `R`, then applying `φ`
coordinatewise gives a bijection between the common zero locus of the `P_i` in `R^n` and the
common zero locus of the coefficientwise images `P_i^φ` in `S^n`. -/
theorem strictlyHenselian_localHom_bijOn_zeroLocus_of_etale_mvPolynomial_quotient
    (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))] :
    Set.BijOn
      (fun r ↦ φ ∘ r)
      {r : Fin n → R | ∀ i, MvPolynomial.eval r (P i) = 0}
      {s : Fin n → S | ∀ i, MvPolynomial.eval s (MvPolynomial.map φ (P i)) = 0} := sorry

end

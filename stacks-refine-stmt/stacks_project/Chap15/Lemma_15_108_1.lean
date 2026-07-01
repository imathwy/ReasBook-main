import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.Flat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum

/- Domain triage:
* primary domain: commutative algebra on fibers of `Spec B → Spec A`;
* sampled owner abstractions: `Algebra.Etale`, `Algebra.Unramified`,
  `Algebra.QuasiFinite`, `Algebra.IsIntegral`, the quasi-finite fiber theorem
  `Algebra.QuasiFinite.eq_of_le_of_under_eq`, `Ideal.primesOver`, and the Chapter 10 bridge
  `ringHom_injective_tfae_of_image_contains_dense_set`;
* source-facing layer: the theorem `ideal_comap_ne_bot_of_cases`, whose hypothesis is the direct
  seven-way disjunction from Stacks Lemma `15.108.1`, expressed on the owner predicates for
  intermediate algebras together with the fiberwise specialization condition on
  `p.asIdeal.primesOver B` and the proposition-valued unique generic-fiber condition
  `Nonempty ((⊥ : Ideal A).primesOver B) ∧ Subsingleton ((⊥ : Ideal A).primesOver B)`;
* core/canonical layer: the owner predicates `Algebra.Etale`, `Algebra.Unramified`,
  `Algebra.QuasiFinite`, `Algebra.IsIntegral`, and the owner fiber sets `p.asIdeal.primesOver B`.

Primitive data vs. derived API:
* primitive data in the localization clauses: an intermediate `A`-algebra `C`, a localization
  `C → B`, and one of the canonical owner predicates on `C`;
* derived API: the fiberwise antisymmetry consequence of quasi-finiteness and the generic-point
  image criterion over `Spec A`.
-/

variable {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
variable [Algebra A B]

-- Proof sketch: reduce cases (1) through (6) to the unique-generic-fiber case as in the Stacks
-- proof. In that case a nonzero element of `J` becomes a unit over the generic fiber and hence in
-- some localization `B_f`, producing a nonzero element of `A ∩ J`.
/-- Lemma 15.108.1: under any of the seven stated hypotheses on the domain map `A → B`, every
nonzero ideal of `B` has nonzero contraction to `A`. -/
theorem ideal_comap_ne_bot_of_cases
    (hAB :
      (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
          (_ : IsScalarTower A C B) (M : Submonoid C), Algebra.Etale A C ∧ IsLocalization M B) ∨
        (Module.Flat A B ∧
          ((∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.Unramified A C ∧ IsLocalization M B) ∨
            (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.QuasiFinite A C ∧ IsLocalization M B) ∨
            (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.IsIntegral A C ∧ IsLocalization M B) ∨
            ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q')) ∨
        (Nonempty ((⊥ : Ideal A).primesOver B) ∧
          ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q') ∨
      Nonempty ((⊥ : Ideal A).primesOver B) ∧ Subsingleton ((⊥ : Ideal A).primesOver B))
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := sorry

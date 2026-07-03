import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import StacksProject_2024.Chap15.IdempotentLifting
import StacksProject_2024.Chap15.Lemma_15_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial
open Polynomial

universe u

section

variable {A : Type u} [CommRing A]

namespace Ideal

/-
Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, expressed through the canonical owner
  `HenselianRing A I`, étale quotient sections, and quotient-induced maps on idempotents;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasFiniteAlgebraIdempotentLifting`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `RingHom.idempotentMap`,
  `Algebra.FormallyEtale.iff_comp_bijective`;
- best owner abstraction: the main owner remains `HenselianRing A I`; among the auxiliary clauses,
  the idempotent conditions are already canonically owned upstream in Chapter 15, while the
  étale-section and Gabber polynomial conditions are genuinely source-facing here and should be
  phrased through canonical comparison maps rather than parallel wrapper data;
- primitive data: the ideal `I`, the owner predicate `HenselianRing A I`, the canonical quotient
  composition map `τ ↦ (Ideal.Quotient.mkₐ A I).comp τ`, and the quotient polynomial identity
  defining Gabber's test polynomials;
- derived API: the TFAE packaging and the uniqueness of a root in `1 + I`.

Source/core/bridge triage:
- `source-facing`: `HasEtaleLiftProperty`, `IsGabberHenselPolynomial`,
  `SatisfiesGabberRootCriterion`, and the chapter TFAE theorem;
- `core/canonical`: `HenselianRing A I`, the Chapter 15 idempotent-lifting owners, and the
  canonical map `RingHom.idempotentMap`;
- `bridge/view`: the unique-root consequence extracted from Gabber's criterion.
-/

/-- The étale lifting formulation of the henselian pair condition modulo `I`. -/
def HasEtaleLiftProperty (I : Ideal A) : Prop :=
  ∀ ⦃A' : Type u⦄ [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
    Function.Surjective fun τ : A' →ₐ[A] A ↦ (Ideal.Quotient.mkₐ A I).comp τ

/-- A Gabber test polynomial for the henselian criterion modulo `I`. -/
def IsGabberHenselPolynomial (I : Ideal A) (f : A[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ f.Monic ∧
    f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1)

/-- Gabber's Jacobson-plus-root criterion for the pair `(A, I)`. -/
def SatisfiesGabberRootCriterion (I : Ideal A) : Prop :=
  I ≤ Ring.jacobson A ∧
    ∀ ⦃f : A[X]⦄, I.IsGabberHenselPolynomial f → ∃ i : I, f.IsRoot (1 + ↑i)

end Ideal

-- Proof sketch: use the Stacks chain of implications `(2) → (4) → (3) → (1) → (5) → (2)`.
-- The Jacobson-radical condition enters via the henselian definition and the idempotent
-- injectivity lemma, finite and integral cases are related by integrality of finite algebras, and
-- Gabber's polynomial criterion supplies the final lifting step for étale sections.
/-- Lemma 15.11.6: for a commutative ring `A` and an ideal `I`, the following are equivalent: the
pair `(A, I)` is henselian; every section modulo `I` of an étale `A`-algebra lifts to `A`; for
all finite `A`-algebras the reduction map induces a bijection on idempotents; for all integral
`A`-algebras the reduction map induces a bijection on idempotents; and Gabber's Jacobson-plus-root
criterion holds for `I`. -/
theorem henselianRing_tfae_etaleLift_idempotents_gabberCriterion (I : Ideal A) :
    List.TFAE
      [ HenselianRing A I
      , I.HasEtaleLiftProperty
      , I.HasFiniteAlgebraIdempotentLifting
      , I.HasIntegralAlgebraIdempotentLifting
      , I.SatisfiesGabberRootCriterion
      ] := sorry

namespace Ideal

-- Proof sketch: this is the `(5) → (1)` implication in Lemma `15.11.6`.
/-- Gabber's Jacobson-plus-root criterion implies that `(A, I)` is henselian. -/
theorem henselianRing_of_satisfiesGabberRootCriterion (I : Ideal A)
    (hI : I.SatisfiesGabberRootCriterion) :
    HenselianRing A I := sorry

-- Proof sketch: this is the `(1) → (3)` implication in Lemma `15.11.6`, specialized to the
-- identity `A`-algebra.
/-- If `(A, I)` is henselian, then reduction modulo `I` induces a bijection on idempotents of
`A`. -/
theorem quotientMk_bijective_idempotentMap_of_henselianRing (I : Ideal A) [HenselianRing A I] :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := sorry

end Ideal

-- Proof sketch: for a Gabber test polynomial, the derivative at any root in `1 + I` is a unit
-- modulo `I`; comparing two such roots modulo the square of their difference shows that the
-- difference is annihilated by a unit, hence the roots coincide.
/-- Under Gabber's criterion, a henselian test polynomial has a unique root in `1 + I`. -/
theorem existsUnique_gabber_root_of_satisfiesGabberRootCriterion (I : Ideal A)
    (hI : I.SatisfiesGabberRootCriterion) {f : A[X]} (hf : I.IsGabberHenselPolynomial f) :
    ∃! i : I, f.IsRoot (1 + ↑i) := sorry

end

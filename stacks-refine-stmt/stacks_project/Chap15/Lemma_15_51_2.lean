import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Definition_10_112_5
import stacks_project.Chap15.Lemma_15_51_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (P : FieldAlgebraProperty)
variable {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]

/- Domain sampling pass:
* primary domain: commutative algebra of fiber algebras, prime localizations, and local criteria
  for residue-field algebra properties on Noetherian fibers;
* sampled owner declarations:
  - `FieldAlgebraProperty`, the Chapter 15 owner for properties of residue-field algebras;
  - `FieldAlgebraProperty.HasPropertyB`, the canonical owner for axiom `(B)`;
  - `Ideal.Fiber`, the canonical owner for the fiber algebra `κ(𝔭) ⊗[R] Λ`;
  - `fiberLocalRingAt R Λ q` from `Definition_10_112_5`, the canonical owner for the local ring of
    the fiber at `q`;
  - `fiberLocalRingAtResidueFieldAlgebra`, the Chapter 10 owner-level bridge making
    `fiberLocalRingAt R Λ q` a `κ(q ∩ R)`-algebra;
  - `PrimeSpectrum.preimageHomeomorphFiber`, the canonical identification between primes of a fiber
    algebra and primes of `Λ` lying over a fixed base prime;
  - `isRegularRingMap_local_tfae` from `Lemma_15_41_2_Regular_is_a_local_property`, the same
    source-facing local-to-global TFAE pattern in the nearby chapter development.

Source/core/bridge triage:
* `source-facing`: `fiberProperty_tfae`, the textbook local criterion on fiber
  algebras and their localization at maximal source/target pairs;
* `core/canonical`: `FieldAlgebraProperty.HasPropertyB`, `Ideal.Fiber`, `fiberLocalRingAt`, and
  the owner-level bridge `fiberLocalRingAtResidueFieldAlgebra`;
* `bridge/view`: the identification between primes of the fiber algebra and primes of `Λ` lying
  over a fixed base prime.

Primitive data are the field-algebra property `P k A` together with the Chapter 15 owner axiom
`FieldAlgebraProperty.HasPropertyB`. The theorem below applies that owner directly to the fiber
algebras and their localizations. Following the chapter owner pattern from
`Lemma_15_41_2_Regular_is_a_local_property`, the source-facing theorem is phrased directly on the
three clauses rather than through one-off public wrapper names. In the maximal-ideal clause, the
source tests the single local fiber of `R_(m' ∩ R) → Λ_(m')` at each `m' : MaximalSpectrum Λ`;
the auxiliary source-localization choice is already absorbed by the canonical owner
`fiberLocalRingAt`.
-/

end

namespace Algebra

section

variable {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing Λ]
variable (P : FieldAlgebraProperty) [P.HasPropertyB]

-- Proof sketch: for each `p : Spec(R)`, the prime spectrum of the fiber algebra
-- `p.asIdeal.Fiber Λ = κ(p) ⊗[R] Λ` is identified with the primes of `Λ` lying over `p` by
-- `PrimeSpectrum.preimageHomeomorphFiber`. Under that identification, clause `(2)` says exactly
-- that every localization of the fiber algebra at a prime has `P`. Clause `(3)` is the same
-- local test specialized to the maximal-local fiber `R_(m' ∩ R) → Λ_(m')`. Apply property `(B)`
-- to each Noetherian fiber algebra; Noetherianity comes from the Noetherian target ring `Λ`, and
-- the maximal-local clause is the corresponding specialization of the prime-local one.
/-- Lemma 15.51.2: let `R → Λ` be a ring map with `Λ` Noetherian, and let `P` be a
field-algebra property satisfying `(B)`. Then the following are equivalent: every fiber algebra
`κ(p) ⊗[R] Λ` has `P` over `κ(p)`; for every prime `q` of `Λ`, the local fiber ring at `q`,
equivalently the fiber of `R_(q ∩ R) → Λ_q`, has `P` over `κ(q ∩ R)`; and it suffices to test
that local condition only for maximal ideals `m'` of `Λ`, using the maximal-local fiber of
`R_(m' ∩ R) → Λ_(m')`. -/
theorem fiberProperty_tfae :
    ([ ∀ p : PrimeSpectrum R, P p.asIdeal.ResidueField (p.asIdeal.Fiber Λ)
      , ∀ q : PrimeSpectrum Λ, P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q)
      , ∀ m' : MaximalSpectrum Λ,
          let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
          P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q)
      ] : List Prop).TFAE :=
  by
  sorry

end

end Algebra

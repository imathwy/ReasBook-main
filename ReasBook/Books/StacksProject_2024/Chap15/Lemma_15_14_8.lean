import StacksProject_2024.Chap15.Definition_15_11_1
import StacksProject_2024.Chap15.Definition_15_14_1
import StacksProject_2024.Chap15.Lemma_15_11_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] [IsAbsolutelyIntegrallyClosed A]

namespace Ideal

/- Domain-style sampling:
- primary domain: henselian pairs over absolutely integrally closed rings, with the canonical
  owner `HenselianRing A I` and quotient idempotent lifting as derived API;
- sampled owner-level declarations:
  `HenselianRing`,
  `Ideal.HasFiniteAlgebraIdempotentLifting`,
  `Ideal.le_ring_jacobson_of_henselianRing`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`,
  `quotientMk_injective_on_idempotents_of_le_jacobson`;
- best owner abstraction: this lemma is `source-facing`, but its proof should be organized around
  the existing henselian owner `HenselianRing A I` and the chapter-level idempotent-lifting owner
  `I.HasFiniteAlgebraIdempotentLifting`, not around a parallel local criterion;
- primitive data: the ideal `I`, the owner predicate `HenselianRing A I`, and the Jacobson plus
  quotient-idempotent surjectivity conditions from the source statement;
- derived API: injectivity of the quotient idempotent map from the Jacobson condition, the
  finite-algebra idempotent-lifting owner obtained from the chapter TFAE, and the resulting
  henselian conclusion.

Source/core/bridge triage:
- `source-facing`: the present equivalence specialized to absolutely integrally closed rings;
- `core/canonical`: `HenselianRing A I` and `I.HasFiniteAlgebraIdempotentLifting`;
- `bridge/view`: the internal Gabber-root-criterion step from Lemma `15.11.6` and the
  quotient-idempotent map `(Ideal.Quotient.mk I).idempotentMap`.
-/

-- Proof sketch: the forward implication should not rebuild idempotent lifting locally; instead,
-- specialize the finite-algebra idempotent clause of Lemma `15.11.6` to `B = A`. For the
-- converse, the source-specific step is first to turn surjectivity on quotient idempotents over
-- an absolutely integrally closed ring into Gabber's root criterion, and then immediately package
-- that step through the canonical owner `I.HasFiniteAlgebraIdempotentLifting`.

private theorem satisfiesGabberRootCriterion_of_le_jacobson_and_surjective_on_idempotents
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (hsurj : Function.Surjective (Ideal.Quotient.mk I).idempotentMap) :
    I.SatisfiesGabberRootCriterion := by
  refine ⟨hI, ?_⟩
  intro f hf
  -- Use absolute integral closedness to split `f`, then extract from the lifted idempotent data a
  -- root in `1 + I`; this is exactly the source-facing step not already packaged by the chapter
  -- TFAE owner.
  sorry

/-- Over an absolutely integrally closed ring, the source hypotheses in Lemma `15.14.8` imply the
henselian owner by way of Gabber's criterion. -/
private theorem henselianRing_of_le_jacobson_and_surjective_on_idempotents
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (hsurj : Function.Surjective (Ideal.Quotient.mk I).idempotentMap) :
    HenselianRing A I := by
  have hGabber : I.SatisfiesGabberRootCriterion :=
    satisfiesGabberRootCriterion_of_le_jacobson_and_surjective_on_idempotents I hI hsurj
  exact I.henselianRing_of_satisfiesGabberRootCriterion hGabber

/-- Lemma 15.14.8: for an absolutely integrally closed ring `A` and an ideal `I`, the pair
`(A, I)` is henselian if and only if `I` is contained in the Jacobson radical of `A` and the
quotient map `A → A ⧸ I` induces a surjection on idempotents. -/
theorem henselianRing_iff_le_jacobson_and_surjective_on_idempotents (I : Ideal A) :
    HenselianRing A I ↔
      I ≤ Ring.jacobson A ∧
        Function.Surjective (Ideal.Quotient.mk I).idempotentMap := by
  constructor
  · intro hH
    haveI := hH
    refine ⟨I.le_ring_jacobson_of_henselianRing, ?_⟩
    exact I.quotientMk_bijective_idempotentMap_of_henselianRing.surjective
  · rintro ⟨hI, hsurj⟩
    exact henselianRing_of_le_jacobson_and_surjective_on_idempotents I hI hsurj

end Ideal

end

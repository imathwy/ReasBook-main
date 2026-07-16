import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_157_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain-style sampling:
* primary domain: Serre conditions and reducedness for Noetherian commutative rings;
* sampled owner/bridge declarations:
  `SerreConditionR`,
  `SerreConditionS`,
  `Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`,
  `embeddedPrimes_eq_empty_iff`;
* best owner abstraction: the ring-theoretic owner classes `SerreConditionR R 0` and
  `SerreConditionS R 1` from Definition 10.157.1;
* primitive data vs derived API: the Serre conditions are primitive owners here, while the
  embedded-prime and associated-prime criteria are bridge/view API already provided upstream.

Source/core/bridge triage:
* `source-facing`: reducedness versus the textbook Serre conditions `(R_0)` and `(S_1)`;
* `core/canonical`: the owner classes `SerreConditionR R 0` and `SerreConditionS R 1`;
* `bridge/view`: the source-facing localized and associated-prime criteria already live upstream,
  so this file keeps only the reducedness implications and does not repackage the `(S_1)` clause
  as a new ring-specific wrapper.
-/

-- Proof sketch: localize at a height-zero prime ideal. Reducedness localizes, and a reduced local
-- ring of Krull dimension `0` is a field, hence a regular local ring.
/-- A reduced Noetherian ring satisfies Serre's condition `(R_0)`. -/
instance [IsReduced R] : SerreConditionR R 0 := sorry

-- Proof sketch: localize at a prime ideal of positive height. The localization remains reduced and
-- local. Use the upstream `(S_1)` bridge from `embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`,
-- specialized to the self-module, together with the reduced-ring control of associated primes from
-- Chapter 10 instead of introducing a separate ring-specific no-embedded-primes owner here.
/-- A reduced Noetherian ring satisfies Serre's condition `(S_1)`. -/
instance [IsReduced R] : SerreConditionS R 1 := sorry

-- Proof sketch: the forward implication is given by the two preceding reducedness instances. For
-- the converse, use `(R_0)` to see that localizations at minimal primes are fields, and use the
-- canonical `(S_1)` owner together with its upstream associated-prime bridge to rule out
-- nilpotents in every localization.
/-- Lemma 10.157.3: for a Noetherian ring `R`, reducedness is equivalent to Serre's conditions
`(R_0)` and `(S_1)`. -/
lemma isReduced_iff_serreConditionR_zero_and_serreConditionS_one :
    IsReduced R ↔ SerreConditionR R 0 ∧ SerreConditionS R 1 := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, inferInstance⟩
  · intro h
    sorry

end

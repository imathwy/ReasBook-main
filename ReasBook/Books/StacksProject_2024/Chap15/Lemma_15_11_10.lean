import Mathlib
import StacksProject_2024.Chap15.Lemma_15_11_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] (I I' : Ideal A)
variable [HenselianRing A I] [HenselianRing A I']

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, compared through the quotient pair
  criterion for a subideal `I ≤ J`;
- sampled owner declarations:
  `HenselianRing`,
  `ideal_map_henselianRing_of_isIntegral`,
  `henselianRing_iff_henselianRing_and_quotient_henselianRing`,
  `Ideal.map_sup`;
- best owner abstraction: the public conclusion is again the canonical owner
  `HenselianRing A (I + I')`; the quotient-pair comparison from Lemma `15.11.9` and the quotient
  transport from Lemma `15.11.8` are derived bridge API, not new local owners;
- primitive data: the ideals `I`, `I'`, the two henselian owner instances on `A`, and the
  canonical quotient map `Ideal.Quotient.mk I : A →+* A ⧸ I`;
- derived API: the quotient henselian structure on `A ⧸ I` coming from `I'`, and the ideal-map
  identity `map (Ideal.Quotient.mk I) (I + I') = map (Ideal.Quotient.mk I) I'`.

Source/core/bridge triage:
- `source-facing`: the henselianity of the sum pair `(A, I + I')`;
- `core/canonical`: `HenselianRing`;
- `bridge/view`: Lemma `15.11.9` for the quotient criterion and Lemma `15.11.8` for passing
  henselianity to quotient rings.
-/

-- Proof sketch: apply Lemma `15.11.9` with `I ≤ I + I'`. The quotient ideal
-- `(I + I') / I` is canonically `I' / I` because `I / I = 0`, and Lemma `15.11.8` supplies the
-- henselian structure on that quotient pair from `(A, I')`. The forward implication of
-- Lemma `15.11.9` then yields henselianity of `(A, I + I')`.
/-- Lemma 15.11.10: if `(A, I)` and `(A, I')` are henselian pairs, then the
pair `(A, I + I')` is henselian. -/
instance ideal_add_henselianRing : HenselianRing A (I + I') := by
  refine
    (henselianRing_iff_henselianRing_and_quotient_henselianRing I (I + I') le_sup_left).2 ?_
  refine ⟨inferInstance, ?_⟩
  simpa [Ideal.map_sup] using
    (show HenselianRing (A ⧸ I) (Ideal.map (algebraMap A (A ⧸ I)) I') from
      ideal_map_henselianRing_of_isIntegral I')

end

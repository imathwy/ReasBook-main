import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {J : Type v} {A : J → Type u} [∀ j, CommRing (A j)]
variable (I : ∀ j, Ideal (A j))

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra and their behavior under finite products;
- sampled owner declarations:
  `HenselianRing`,
  `HenselianRing.jac`,
  `HenselianRing.is_henselian`,
  `inverseSystem_limit_henselianRing`;
- best owner abstraction: the canonical owner remains `HenselianRing`; this file should not
  introduce a product-specific wrapper for henselian pairs, only the product/component bridge for
  that owner;
- primitive data: the ideal family `I` and the owner instances `HenselianRing (A j) (I j)` or
  `HenselianRing ((j : J) → A j) (Ideal.pi I)`;
- derived API: the componentwise instance extracted from the product pair, the product instance
  assembled from the component pairs, and the source-facing textbook `iff`.

Source/core/bridge triage:
- `source-facing`: the textbook equivalence `henselianRing_pi_iff`;
- `core/canonical`: the owner `HenselianRing`;
- `bridge/view`: the two instance declarations transporting `HenselianRing` between the product
  pair and its components.
-/

/-- If the product pair is henselian, then each component pair is henselian. -/
instance henselianRing_of_pi_henselianRing (j : J)
    [HenselianRing (∀ j, A j) (Ideal.pi I)] : HenselianRing (A j) (I j) := sorry

/-- If each component pair is henselian, then the product pair is henselian. -/
instance pi_henselianRing [∀ j, HenselianRing (A j) (I j)] :
    HenselianRing (∀ j, A j) (Ideal.pi I) := sorry

-- Proof sketch: for the forward implication, apply henselianity along each projection
-- `Π j, A j → A i`, which sends `Ideal.pi I` to `I i`. For the reverse implication, use that the
-- Jacobson-radical condition and the Hensel lifting property are both checked componentwise in a
-- product ring.
/-- Lemma 15.11.11: the product pair `((j : J) → A j, Ideal.pi I)` is henselian if and only if
each component pair `(A j, I j)` is henselian. -/
theorem henselianRing_pi_iff :
    HenselianRing (∀ j, A j) (Ideal.pi I) ↔ ∀ j, HenselianRing (A j) (I j) := by
  constructor
  · intro h j
    let _ : HenselianRing (∀ j, A j) (Ideal.pi I) := h
    infer_instance
  · intro h
    let _ : ∀ j, HenselianRing (A j) (I j) := h
    infer_instance

end

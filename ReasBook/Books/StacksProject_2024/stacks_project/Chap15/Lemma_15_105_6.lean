import Mathlib
import StacksProject_2024.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {ι : Type u} (K : ι → Type v) [∀ i, Field (K i)]

/- Domain-style sampling:
- primary domain: commutative algebra of absolutely flat rings and coordinatewise product rings;
- sampled owner declarations:
  `IsAbsolutelyFlatRing`,
  the field instance for `IsAbsolutelyFlatRing`,
  the coordinatewise product instance for `IsAbsolutelyFlatRing`,
  `Pi.commRing`;
- best owner abstraction: `IsAbsolutelyFlatRing` on each factor is the primitive data, while
  absolute flatness of the product ring is the owner-derived coordinatewise instance now living
  upstream in `Definition_15_105_1`. The source-facing product-of-fields item should therefore be
  a direct specialization of that owner rather than a second local instance.
-
- Source/core/bridge triage:
- `source-facing`: the product-of-fields specialization below;
- `core/canonical`: the upstream coordinatewise instance
  `[∀ i, IsAbsolutelyFlatRing (K i)] → IsAbsolutelyFlatRing ((i : ι) → K i)`;
- `bridge/view`: the factorwise field instances from `Definition_15_105_1`.
-/

/-- Helper for Lemma 15.105.6: the product ring inherits absolute flatness by combining the
factorwise field instance with the upstream coordinatewise product instance. -/
lemma pi_isAbsolutelyFlatRing_of_field : IsAbsolutelyFlatRing ((i : ι) → K i) := by
  -- Instance search first turns each field factor into an absolutely flat ring.
  -- The imported coordinatewise product instance then closes the product-ring goal.
  infer_instance

/-- Lemma 15.105.6: a product of fields is an absolutely flat ring, by specializing the canonical
coordinatewise product instance for absolutely flat rings to the field case. -/
theorem isAbsolutelyFlatRing_pi : IsAbsolutelyFlatRing ((i : ι) → K i) := by
  -- Reuse the helper that packages the factorwise field instances into the product instance.
  exact pi_isAbsolutelyFlatRing_of_field (K := K)

end

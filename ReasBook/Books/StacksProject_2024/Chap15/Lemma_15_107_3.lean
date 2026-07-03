import Mathlib
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap15.Definition_15_107_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A Ah : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-
Domain-style sampling:
- primary domain: local commutative algebra of unibranch local rings, henselizations, and minimal
  prime ideals;
- sampled owner declarations of the same kind:
  `IsUnibranch`,
  `IsHenselizationOf`,
  `henselizationMap_faithfullyFlat`,
  `unibranchNormalizationTensorHenselization_bijOn_minimalPrimes`;
- best owner abstraction: `IsUnibranch` is the core owner, while the chosen henselization `Ah` and
  its minimal-prime set form the bridge/view used to restate the source criterion;
- primitive data: the local ring `A` and the chosen henselization `Ah`;
- derived API: the unique-minimal-prime characterization on `Ah`.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `IsUnibranch`, `IsHenselizationOf`, `minimalPrimes`;
- `bridge/view`: the chosen henselization `Ah`.
-/

-- Proof sketch: for `(2) → (1)`, contract the unique minimal prime of `Ah` along the faithfully
-- flat henselization map to get the unique minimal prime of `A`, then use the reduced henselized
-- quotient to force the normalization of `Ared` to be local. For `(1) → (2)`, use the local
-- normalization of `Ared`, the comparison with its base change to `Ah` from Lemma `15.107.2`, and
-- the filtered-colimit description of henselization to show that every two minimal primes of `Ah`
-- coincide.
/-- Lemma 15.107.3: for a local ring `A` and a chosen henselization `Ah` of `A`, the ring `A` is
unibranch if and only if `Ah` has a unique minimal prime ideal. -/
theorem isUnibranch_iff_existsUnique_minimalPrime_henselization :
    IsUnibranch A ↔ ∃! p : Ideal Ah, p ∈ minimalPrimes Ah := sorry

end

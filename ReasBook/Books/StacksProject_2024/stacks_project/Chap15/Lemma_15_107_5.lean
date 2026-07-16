import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_107_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_107_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A Ash : Type u)
variable [CommRing A] [IsLocalRing A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-
Domain-style sampling:
- primary domain: local commutative algebra of geometrically unibranch local rings, strict
  henselizations, and minimal prime ideals;
- sampled owner declarations of the same kind:
  `IsGeometricallyUnibranch`,
  `IsStrictHenselizationOf`,
  `isUnibranch_iff_existsUnique_minimalPrime_henselization`,
  `unibranchNormalizationTensorStrictHenselization_bijOn_minimalPrimes`;
- best owner abstraction: `IsGeometricallyUnibranch` is the core owner, while the chosen strict
  henselization `Ash` and its minimal-prime set are the bridge/view used to restate the source
  criterion;
- primitive data: the local ring `A` and the chosen strict henselization `Ash`;
- derived API: the unique-minimal-prime characterization on `Ash`.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `IsGeometricallyUnibranch`, `IsUnibranch`, `minimalPrimes`,
  `IsStrictHenselizationOf`;
- `bridge/view`: the chosen strict henselization `Ash` together with the comparison of minimal
  primes from Lemma `15.107.4`.
-/

-- Proof sketch: combine the henselization criterion from Lemma `15.107.3` with the strict
-- henselization comparison results from Lemma `15.107.4`. The unibranch part is already owned by
-- the henselization theorem, while the geometric refinement is detected by the strict
-- henselization fibers and their minimal primes.
/-- Lemma 15.107.5: for a local ring `A` and a chosen strict henselization `Ash` of `A`, the ring
`A` is geometrically unibranch if and only if `Ash` has a unique minimal prime ideal. -/
theorem isGeometricallyUnibranch_iff_existsUnique_minimalPrime_strictHenselization :
    IsGeometricallyUnibranch A ↔ ∃! p : Ideal Ash, p ∈ minimalPrimes Ash := sorry

end

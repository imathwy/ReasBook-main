import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.49.2:
- primary domain: perfect complexes and perfect derived `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `CochainComplex.IsPerfect`,
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.isPerfect_iff_exists_perfect_representative`
  from `Definition_20_49_1`;
- best owner abstraction: the bridge owner
  `DerivedCategory.isPerfect_iff_exists_perfect_representative`, whose two directions are exactly
  the two parts of the source lemma;
- primitive data: the intrinsic predicates `CochainComplex.IsPerfect` and
  `DerivedCategory.IsPerfect`;
- derived API: the representative bridge theorem relating these owners.

Source/core/bridge triage:
- `source-facing`: the two source implications between perfect derived objects and perfect
  representative complexes;
- `core/canonical`: `CochainComplex.IsPerfect` and `DerivedCategory.IsPerfect`;
- `bridge/view`: `DerivedCategory.isPerfect_iff_exists_perfect_representative`.

This item adds no new owner-level mathematics beyond that existing bridge, so the faithful
refinement is a direct recall rather than parallel local theorem names for each implication. -/

namespace DerivedCategory

variable {X : RingedSpace.{u}}

/- Lemma 20.49.2: a derived `𝒪_X`-module is perfect if and only if it admits a perfect
representative complex. This is exactly the canonical bridge already introduced in Definition
20.49.1, so the main entry here should recall that owner theorem directly rather than restating its
two directions under new names. -/
recall isPerfect_iff_exists_perfect_representative

end DerivedCategory

end AlgebraicGeometry.RingedSpace

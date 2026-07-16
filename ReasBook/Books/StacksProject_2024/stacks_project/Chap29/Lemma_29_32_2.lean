import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap29.Definition_29_32_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 29.32.2:
- primary domain: scheme-level relative differentials via the scheme morphism `f.toShHom`;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.Ω[_]`,
  `AlgebraicGeometry.RingedSpace.d[_]`,
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`;
- best owner abstraction: the existing owner theorem
  `TopCat.Sheaf.relativeDifferentials_representsDerivations`, reused through the Chapter 29
  scheme-level notation `Ω[f.toShHom]` and `d[f.toShHom]`;
- this file is recall-only reuse of that owner theorem, not a second scheme-local alias.

Source/core/bridge triage:
- `source-facing`: the scheme-level notation `Ω[f.toShHom]` and `d[f.toShHom]`;
- `core/canonical`: `TopCat.Sheaf.relativeDifferentials_representsDerivations`;
- `bridge/view`: specialization along `f.toShHom`, already supplied by the existing notation and
  owner theorem. -/

/- Lemma 29.32.2: the universal property of `Ω[f.toShHom]` is already owned by
`TopCat.Sheaf.relativeDifferentials_representsDerivations`; Chapter 29 reuses that owner through
the established scheme-level notation `Ω[f.toShHom]` and `d[f.toShHom]`. -/
recall TopCat.Sheaf.relativeDifferentials_representsDerivations

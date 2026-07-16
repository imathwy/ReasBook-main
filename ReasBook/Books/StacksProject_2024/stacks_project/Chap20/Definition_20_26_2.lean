import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 20.26.2:
- primary domain: K-flat cochain complexes of sheaves of modules on a ringed space;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`;
- best owner abstraction: the Chapter 15 owner is the predicate `CochainComplex.IsKFlat K` on the
  cochain complex itself; ringed-space K-flatness is the specialization of that owner to
  `X.Modules`, not a second
  local predicate;
- primitive vs derived: the primitive data is only the complex `K`, while the preservation of
  acyclic complexes under totalized tensoring is exactly the companion theorem
  `CochainComplex.isKFlat_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook K-flatness notion for complexes of `𝒪_X`-modules;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: no extra bridge is needed, because the ringed-space notion is exactly this owner
  specialized to `X.Modules`. -/

/- Definition 20.26.2: a complex `K` of `𝒪_X`-modules on a ringed space `X` is K-flat if for
every acyclic complex `F`, the totalized tensor product `HomologicalComplex.tensorObj F K` is
acyclic. This is the canonical owner `CochainComplex.IsKFlat` specialized to `X.Modules`. -/
recall CochainComplex.IsKFlat

/- Totalized tensoring with `K` preserves acyclic complexes exactly when `K` is K-flat; the
canonical companion theorem is `CochainComplex.isKFlat_iff`. -/
recall CochainComplex.isKFlat_iff

end AlgebraicGeometry.RingedSpace

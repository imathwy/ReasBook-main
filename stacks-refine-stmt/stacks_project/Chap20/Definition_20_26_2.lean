import Mathlib.Tactic.Recall
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 20.26.2:
- primary domain: K-flat cochain complexes of sheaves of modules on a ringed space;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`;
- best owner abstraction: the Chapter 15 owner is the predicate `CochainComplex.IsKFlat K` on the
  cochain complex itself;
  ringed-space K-flatness is the specialization of that owner to `(RingedSpace.Modules X)`, not a second
  local predicate;
- primitive vs derived: the primitive data is only the complex `K`, while the preservation of
  acyclic complexes under totalized tensoring is exactly the companion theorem
  `CochainComplex.isKFlat_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook K-flatness notion for complexes of `\mathcal O_X`-modules;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: no extra bridge is needed, because the ringed-space notion is exactly this owner
  specialized to `(RingedSpace.Modules X)`. -/

/- Definition 20.26.2: a complex `\mathcal K^\bullet` of `\mathcal O_X`-modules on a ringed
space `(X, \mathcal O_X)` is K-flat if for every acyclic complex `\mathcal F^\bullet`, the
totalized tensor product `\mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X}
\mathcal K^\bullet)` is acyclic. This is the canonical owner
`CochainComplex.IsKFlat` specialized to `(RingedSpace.Modules X)`. -/
recall CochainComplex.IsKFlat

/- Totalized tensoring with `K` preserves acyclic complexes exactly when `K` is K-flat; the
canonical companion theorem is `CochainComplex.isKFlat_iff`. -/
recall CochainComplex.isKFlat_iff

section

variable (X : AlgebraicGeometry.RingedSpace)
variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable (K : CochainComplex (RingedSpace.Modules X) ℤ)

/- Source-facing specialization: for a ringed space `(X, \mathcal O_X)`, Definition 20.26.2 uses
exactly the Chapter 15 owner predicate and its canonical iff-formulation on `(RingedSpace.Modules X)`. -/
#check K.IsKFlat
#check CochainComplex.isKFlat_iff K

end

end AlgebraicGeometry.RingedSpace

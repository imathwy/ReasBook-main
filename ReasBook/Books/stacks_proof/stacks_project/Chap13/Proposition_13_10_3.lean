import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import stacks_proof.stacks_project.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: triangulated structures on homotopy categories of cochain complexes;
- sampled owner declarations:
  `K(𝒜)`;
  `Pretriangulated (K(𝒜))`;
  `IsTriangulated (K(𝒜))`;
- best owner abstraction: the canonical owner `IsTriangulated (K(𝒜))`;
- primitive data: an additive category with zero object and binary biproducts;
- derived API: the triangulated structure on the homotopy category of cochain complexes.

Source/core/bridge triage:
- `source-facing`: Proposition 13.10.3, asserting that the homotopy category `K(\mathcal A)` is
  triangulated;
- `core/canonical`: the existing triangulated owner instance on `K(𝒜)`;
- `bridge/view`: the textbook notation `K(\mathcal A)` from `Definition_13_8_1` for
  `HomotopyCategory 𝒜 (up ℤ)`.

This proposition is therefore a pure canonical recall item. The file should use the existing owner
instance directly, with no local wrapper or duplicate declaration.
-/

/- Proposition 13.10.3: for an additive category `\mathcal A`, the homotopy category
`K(\mathcal A)` of cochain complexes, equipped with its standard translation functors and
distinguished triangles, carries the canonical triangulated structure. This is exactly the
existing owner instance `IsTriangulated (K(𝒜))`. -/
#check (inferInstance : IsTriangulated (K(𝒜)))

end CategoryTheory

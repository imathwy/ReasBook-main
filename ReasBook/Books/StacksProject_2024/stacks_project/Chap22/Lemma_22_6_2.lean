import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CochainComplex

universe v u

-- Semantic search tool unavailable in this runner; the owner choice was verified locally against
-- the existing Chapter 13 mapping-cone homotopy API.

/- Domain-style sampling for Lemma 22.6.2:
- primary domain: homotopy-commutative squares of differential graded module morphisms and the
  induced morphisms between their cone triangles in the homotopy category;
- inspected owner declarations:
  `CochainComplex.mappingCone.mapOfHomotopy`,
  `CochainComplex.mappingCone.trianglehMapOfHomotopy`;
- best owner abstraction: the canonical homotopy-category triangle morphism
  `CochainComplex.mappingCone.trianglehMapOfHomotopy`;
- primitive data: a homotopy witnessing that the square commutes up to homotopy;
- derived API: the cone morphism `c : C(f₁) ⟶ C(f₂)` is the third component of that canonical
  triangle morphism.
-/

/- Source/core/bridge triage:
- `source-facing`: a homotopy-commutative square of morphisms of differential graded modules;
- `core/canonical`: the induced morphism of standard mapping-cone triangles in the homotopy
  category, namely `CochainComplex.mappingCone.trianglehMapOfHomotopy`;
- `bridge/view`: the underlying cone map `CochainComplex.mappingCone.mapOfHomotopy`, which is the
  source map `c : C(f₁) ⟶ C(f₂)` before passing to the homotopy category.
-/

/-
Lemma 22.6.2: for a homotopy-commutative square of morphisms of differential graded modules
over a differential graded algebra `(A, d)`, the induced morphism of cone triangles in
`K(Mod_(A, d))` is exactly the canonical mathlib construction
`CochainComplex.mappingCone.trianglehMapOfHomotopy` on the underlying cochain complexes. The
underlying third component is the desired map `c : C(f₁) ⟶ C(f₂)`. -/
recall CochainComplex.mappingCone.trianglehMapOfHomotopy

/- Companion recall: the underlying third-component source map between mapping cones is the
canonical `CochainComplex.mappingCone.mapOfHomotopy`. -/
recall CochainComplex.mappingCone.mapOfHomotopy

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]
variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ}
variable {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
variable (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

/- Source-facing type specialization: a homotopy-commutative square induces a morphism between
the standard mapping-cone triangles, and the companion recall above identifies its underlying cone
map. -/
#check (mappingCone.trianglehMapOfHomotopy H :
  mappingCone.triangleh φ₁ ⟶ mappingCone.triangleh φ₂)

end

import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex

universe v u

/- Domain-style sampling for Lemma 13.9.2:
- primary domain: mapping-cone triangles in the cochain homotopy category and the functoriality
  of the cone construction under homotopy-commutative squares;
- inspected owner declarations:
  `CochainComplex.mappingCone.mapOfHomotopy`,
  `CochainComplex.mappingCone.triangleMapOfHomotopy_comm₃`,
  `CochainComplex.mappingCone.trianglehMapOfHomotopy`,
  `CochainComplex.mappingCone.map`;
- source/core/bridge triage:
  `source-facing`: a square of cochain-complex morphisms commuting up to homotopy;
  `core/canonical`: the induced triangle morphism
    `CochainComplex.mappingCone.trianglehMapOfHomotopy`;
  `bridge/view`: the underlying cone map `CochainComplex.mappingCone.mapOfHomotopy` and the
    component commutativity lemmas feeding the triangle-level owner;
- primitive data: only a homotopy `H : Homotopy (φ₁ ≫ b) (a ≫ φ₂)`;
- derived API: the induced map on mapping cones and the resulting morphism between the standard
  mapping-cone triangles in the homotopy category;
- best owner abstraction: `CochainComplex.mappingCone.trianglehMapOfHomotopy`, whose interface
  already matches the source statement exactly, so no chapter-local wrapper theorem should remain.
-/

/- Lemma 13.9.2: for a square of cochain complexes that commutes up to homotopy, the induced
morphism between the standard mapping-cone triangles in the homotopy category `K(𝒜)` is exactly
the canonical mathlib construction `CochainComplex.mappingCone.trianglehMapOfHomotopy`. -/
recall CochainComplex.mappingCone.trianglehMapOfHomotopy

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜] [Preadditive 𝒜]
  [HasBinaryBiproducts 𝒜]
variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ}
variable {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
variable (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

/- Source-facing type specialization: a homotopy-commutative square of cochain maps induces a
morphism between the standard mapping-cone triangles in `K(𝒜)`. -/
#check (mappingCone.trianglehMapOfHomotopy H :
  mappingCone.triangleh φ₁ ⟶ mappingCone.triangleh φ₂)

end

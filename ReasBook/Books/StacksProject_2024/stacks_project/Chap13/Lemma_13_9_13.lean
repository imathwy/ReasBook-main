import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Pretriangulated
open CochainComplex HomotopyCategory

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Limits.HasZeroObject 𝒜] [Preadditive 𝒜]
  [Limits.HasBinaryBiproducts 𝒜]
variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ}
variable {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}

/- Domain-style sampling for Lemma 13.9.13:
- primary domain: distinguished mapping-cone triangles in the homotopy category and the
  pretriangulated two-out-of-three isomorphism theorem for triangle morphisms;
- sampled owner declarations:
  `CochainComplex.mappingCone.triangleh`,
  `HomotopyCategory.mappingCone_triangleh_distinguished`,
  `CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂`,
  `CochainComplex.mappingCone.trianglehMapOfHomotopy`;
- best owner abstraction:
  `source-facing`: a morphism between the two standard mapping-cone triangles attached to `f₁`
    and `f₂` in `K(𝒜)`;
  `core/canonical`: the owner theorem `Pretriangulated.isIso₃_of_isIso₁₂` on distinguished
    triangles;
  `bridge/view`: the canonical fact that each standard mapping-cone triangle is distinguished,
    namely `HomotopyCategory.mappingCone_triangleh_distinguished`.

Primitive data are only the triangle morphism `φ` and the isomorphism assumptions on `φ.hom₁` and
`φ.hom₂`. The conclusion that `φ.hom₃` is an isomorphism is derived API from the canonical owner
theorem, so this file should keep only the thin source-facing specialization and not a parallel
triangle-level wrapper.
-/

-- Proof sketch: the standard mapping-cone triangles of `f₁` and `f₂` are distinguished in
-- `K(𝒜)` by `HomotopyCategory.mappingCone_triangleh_distinguished`. Apply the triangulated
-- two-out-of-three theorem `Pretriangulated.isIso₃_of_isIso₁₂` to the given morphism of
-- triangles.
/-- Lemma 13.9.13: for a morphism of the standard mapping-cone triangles in the homotopy category
`K(\mathcal A)`, if the first two components are isomorphisms, then the third component is also
an isomorphism. This is the canonical `K(\mathcal A)` formulation of the statement that if the
maps on `K_1^\bullet` and `L_1^\bullet` are homotopy equivalences, then so is the induced map on
cones. -/
theorem mappingCone_triangleh_isIso₃_of_isIso₁₂
    (φ : mappingCone.triangleh f₁ ⟶ mappingCone.triangleh f₂)
    [IsIso φ.hom₁] [IsIso φ.hom₂] :
    IsIso φ.hom₃ := by
  simpa using
    (isIso₃_of_isIso₁₂ φ
      (mappingCone_triangleh_distinguished f₁)
      (mappingCone_triangleh_distinguished f₂)
      inferInstance inferInstance : IsIso φ.hom₃)

end

end CategoryTheory

import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

local notation "Q" => HomotopyCategory.quotient 𝒜 (up ℤ)

-- Semantic recall hit: `CochainComplex.mappingCone.triangleh` and
-- `HomotopyCategory.mappingCone_triangleh_distinguished` are the canonical owners used locally for
-- mapping-cone triangles in the homotopy category.

/- Source/core/bridge triage for 22.27.13.1:
- `source-facing`: the dotted map from the cone term to the third vertex of a distinguished
  triangle with the same first morphism, making the displayed diagram commute in the homotopy
  category;
- `core/canonical`: the standard triangle `CochainComplex.mappingCone.triangleh α` in the
  homotopy category and the fixed-first-morphism uniqueness owner
  `exists_distinguished_triangle_unique_up_to_iso`;
- `bridge/view`: the triangle isomorphism from the mapping-cone triangle to the given
  distinguished triangle, and its third-component comparison isomorphism.
-/

/-- 22.27.13.1: if `x ⟶ y ⟶ z ⟶ x⟦(1 : ℤ)⟧` is a distinguished triangle in
`HomotopyCategory 𝒜 (up ℤ)` whose first morphism is represented by `α : x ⟶ y`, then the cone
term of the standard mapping-cone triangle of `α` admits an isomorphism to `z` making the two
displayed comparison squares commute. -/
@[stacks 09QV]
theorem exists_iso_from_mappingCone_of_distinguishedTriangle
    {x y z : CochainComplex 𝒜 ℤ} (α : x ⟶ y)
    {β : (Q).obj y ⟶ (Q).obj z} {δ : (Q).obj z ⟶ (Q).obj x⟦(1 : ℤ)⟧}
    (hT : Triangle.mk ((Q).map α) β δ ∈ distTriang (HomotopyCategory 𝒜 (up ℤ))) :
    ∃ e : (mappingCone.triangleh α).obj₃ ≅ (Q).obj z,
      CommSq (mappingCone.triangleh α).mor₂ (𝟙 ((Q).obj y)) e.hom β ∧
        CommSq e.hom (mappingCone.triangleh α).mor₃ δ (𝟙 ((Q).obj x⟦(1 : ℤ)⟧)) := by
  obtain ⟨eT, he₁, he₂⟩ :=
    exists_distinguished_triangle_unique_up_to_iso
      (HomotopyCategory.mappingCone_triangleh_distinguished α) hT
  refine ⟨Triangle.π₃.mapIso eT, ?_, ?_⟩
  · refine CommSq.mk ?_
    simpa [he₂] using eT.hom.comm₂
  · have hcomm₃ := eT.hom.comm₃
    refine CommSq.mk ?_
    simpa [he₁] using hcomm₃.symm

/-- Companion owner form of 22.27.13.1: the given distinguished triangle is isomorphic to the
standard mapping-cone triangle of `α`, through the identity on the first two vertices. -/
theorem exists_mappingCone_triangle_iso_of_distinguishedTriangle
    {x y z : CochainComplex 𝒜 ℤ} (α : x ⟶ y)
    {β : (Q).obj y ⟶ (Q).obj z} {δ : (Q).obj z ⟶ (Q).obj x⟦(1 : ℤ)⟧}
    (hT : Triangle.mk ((Q).map α) β δ ∈ distTriang (HomotopyCategory 𝒜 (up ℤ))) :
    ∃ e : mappingCone.triangleh α ≅ Triangle.mk ((Q).map α) β δ,
      e.hom.hom₁ = 𝟙 ((Q).obj x) ∧ e.hom.hom₂ = 𝟙 ((Q).obj y) :=
  exists_distinguished_triangle_unique_up_to_iso
    (HomotopyCategory.mappingCone_triangleh_distinguished α) hT

end CochainComplex

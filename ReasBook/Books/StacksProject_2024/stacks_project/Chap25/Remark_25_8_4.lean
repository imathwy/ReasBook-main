import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

namespace CategoryTheory

open CategoryTheory.Limits
open Opposite
open scoped Simplicial

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

-- Semantic search note: `lean_leansearch` recalled the canonical `MorphismProperty`
-- base-change/composition classes and generic hypercover owners.  This remark is the
-- source-specific `P`-hypercovering special case, encoded as a simplicial object in the slice
-- category `C/X` so that the coskeleta are the relative coskeleta used in the source.

/-- Remark 25.8.4 (1): for a morphism property `P` on a category with fibre products, a
`P`-hypercovering of `X` is a simplicial object in the slice category `C/X` whose structural
map `U₀ ⟶ X`, degree-`1` relative matching map `U₁ ⟶ U₀ ×_X U₀`, and higher relative matching
maps `U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}` for `n ≥ 1` all lie in `P`. -/
@[stacks 0DER]
structure Hypercovering (P : MorphismProperty C) {X : C} [HasPullbacks C]
    (U : SimplicialObject (Over X)) : Prop where
  /-- The degree-`0` augmentation map `U₀ ⟶ X` lies in `P`. -/
  zero_mem : P ((U.obj (Opposite.op ⦋0⦌)).hom)
  /-- The degree-`1` relative matching map, canonically the map `U₁ ⟶ U₀ ×_X U₀`, lies in `P`. -/
  one_mem
      [∀ F : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ Over X,
        (SimplexCategory.Truncated.inclusion 0).op.HasRightKanExtension F] :
    P ((((SimplicialObject.coskAdj 0).unit.app U).app (Opposite.op ⦋1⦌)).left)
  /-- For `n ≥ 1`, the map `U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}` lies in `P`. -/
  higher_mem (n : ℕ) (_ : 1 ≤ n)
      [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ Over X,
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    P ((((SimplicialObject.coskAdj n).unit.app U).app (Opposite.op ⦋n + 1⦌)).left)

namespace Hypercovering

/-- A `P`-hypercovering is proposition-valued, so its witnesses are proof-irrelevant. -/
instance instSubsingleton (P : MorphismProperty C) {X : C} [HasPullbacks C]
    (U : SimplicialObject (Over X)) : Subsingleton (Hypercovering P U) :=
  inferInstance

/-- The source-facing defining conditions of a `P`-hypercovering: the degree-`0`
augmentation map, the degree-`1` relative matching map, and every higher relative matching map
lie in `P`. -/
theorem zero_one_higher_mem_spec
    (P : MorphismProperty C) {X : C} [HasPullbacks C]
    (U : SimplicialObject (Over X)) (hU : Hypercovering P U) (n : ℕ) (hn : 1 ≤ n)
      [∀ F : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ Over X,
        (SimplexCategory.Truncated.inclusion 0).op.HasRightKanExtension F]
      [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ Over X,
        (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    P ((U.obj (Opposite.op ⦋0⦌)).hom) ∧
      P ((((SimplicialObject.coskAdj 0).unit.app U).app (Opposite.op ⦋1⦌)).left) ∧
        P ((((SimplicialObject.coskAdj n).unit.app U).app (Opposite.op ⦋n + 1⦌)).left) := sorry

/-- Remark 25.8.4 (2): if `P` is stable under base change and composition and contains all
isomorphisms, then every structural morphism `U_n ⟶ X` of a `P`-hypercovering lies in `P`. -/
@[stacks 0DER]
theorem augmentation_mem
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (hP_iso : ∀ {Y Z : C} (f : Y ⟶ Z), IsIso f → P f)
    {X : C} [HasPullbacks C]
    (U : SimplicialObject (Over X)) (hU : Hypercovering P U) (n : ℕ) :
    P ((U.obj (Opposite.op ⦋n⦌)).hom) := sorry

/-- Remark 25.8.4 (3): if `P` is stable under base change and composition and contains all
isomorphisms, then every face map `d_i^{n+1} : U_{n+1} ⟶ U_n` of a `P`-hypercovering lies in
`P`. -/
@[stacks 0DER]
theorem faceMap_mem
    (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    (hP_iso : ∀ {Y Z : C} (f : Y ⟶ Z), IsIso f → P f)
    {X : C} [HasPullbacks C]
    (U : SimplicialObject (Over X)) (hU : Hypercovering P U)
    (n : ℕ) (i : Fin (n + 2)) :
    P ((U.δ i).left) := sorry

end Hypercovering

/-- The degree-`0` augmentation condition of a `P`-hypercovering. -/
@[stacks 0DER]
theorem Hypercovering.zero_mem.spec
    (P : MorphismProperty C) {X : C} [HasPullbacks C]
    (U : SimplicialObject (Over X)) (hU : Hypercovering P U) :
    P ((U.obj (Opposite.op ⦋0⦌)).hom) := sorry

end MorphismProperty

end CategoryTheory

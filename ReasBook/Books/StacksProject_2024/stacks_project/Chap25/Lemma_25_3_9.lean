import Mathlib
import StacksProject_2024.Chap07.Lemma_7_12_4
import StacksProject_2024.Chap25.Lemma_25_2_3
import StacksProject_2024.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over
open scoped CategoryTheory.SemiRepresentableFamily
open scoped Simplicial

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C] [HasWeakSheafify J (Type (max w v))]
variable {X : C}

-- Semantic search note: `lean_leansearch` surfaced the generic sheafification-local-surjectivity
-- API (`Presheaf.isLocallySurjective_presheafToSheaf_map_iff`), and the statement layer here keeps
-- the local Chapter 25 `Hypercovering`/fixed-target augmentation owner instead of rebuilding a
-- parallel presheaf package.

/-- The degree-`0` augmentation `F(K)_0 ⟶ h_X` attached to a hypercovering of `X`. -/
abbrev hypercoveringZeroMap (K : @Hypercovering C _ J X) :
    SemiRepresentableFamily.toPresheaf.obj
        ((SemiRepresentableFamily.Over.forget).obj
          (K.toSimplicialObject.obj (op ⦋0⦌))) ⟶
      uliftYoneda.{w}.obj X :=
  augmentation (K.toSimplicialObject.obj (op ⦋0⦌))

/-- Unfolding `hypercoveringZeroMap` gives the canonical fixed-target augmentation in degree `0`.
-/
theorem hypercoveringZeroMap_def (K : @Hypercovering C _ J X) :
    hypercoveringZeroMap K =
      augmentation (K.toSimplicialObject.obj (op ⦋0⦌)) := sorry

/-- The two degree-`1` face maps of `F(K)` agree after composing with the augmentation to `h_X`. -/
theorem hypercoveringOneMap_condition (K : @Hypercovering C _ J X) :
    SemiRepresentableFamily.toPresheaf.map
        ((SemiRepresentableFamily.Over.forget).map (K.toSimplicialObject.δ 0)) ≫
        hypercoveringZeroMap K =
      SemiRepresentableFamily.toPresheaf.map
        ((SemiRepresentableFamily.Over.forget).map (K.toSimplicialObject.δ 1)) ≫
        hypercoveringZeroMap K := sorry

/-- The degree-`1` matching map `(d^1_0, d^1_1) : F(K)_1 ⟶ F(K)_0 ×_{h_X} F(K)_0`. -/
noncomputable def hypercoveringOneMap (K : @Hypercovering C _ J X) :
    SemiRepresentableFamily.toPresheaf.obj
        ((SemiRepresentableFamily.Over.forget).obj
          (K.toSimplicialObject.obj (op ⦋1⦌))) ⟶
      (pullback
        (hypercoveringZeroMap K)
        (hypercoveringZeroMap K) : Cᵒᵖ ⥤ Type (max w v)) :=
  (pullback.lift
    (SemiRepresentableFamily.toPresheaf.map
      ((SemiRepresentableFamily.Over.forget).map (K.toSimplicialObject.δ 0)))
    (SemiRepresentableFamily.toPresheaf.map
      ((SemiRepresentableFamily.Over.forget).map (K.toSimplicialObject.δ 1)))
    (hypercoveringOneMap_condition K) :
      SemiRepresentableFamily.toPresheaf.obj
          ((SemiRepresentableFamily.Over.forget).obj
            (K.toSimplicialObject.obj (op ⦋1⦌))) ⟶
        (pullback
          (hypercoveringZeroMap K)
          (hypercoveringZeroMap K) : Cᵒᵖ ⥤ Type (max w v)))

/-- The higher comparison map obtained by applying `F` to the canonical matching map in
`SR(C, X)`. -/
abbrev hypercoveringHigherMap
    (K : @Hypercovering C _ J X) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    SemiRepresentableFamily.toPresheaf.obj
        ((SemiRepresentableFamily.Over.forget).obj
          (K.toSimplicialObject.obj (op ⦋n + 1⦌))) ⟶
      SemiRepresentableFamily.toPresheaf.obj
        ((SemiRepresentableFamily.Over.forget).obj
          (((SimplicialObject.cosk n).obj K.toSimplicialObject).obj
            (op ⦋n + 1⦌))) :=
  SemiRepresentableFamily.toPresheaf.map
    ((SemiRepresentableFamily.Over.forget).map (matchingMap K.toSimplicialObject n))

/-- Unfolding `hypercoveringHigherMap` gives `F` applied to the canonical matching map in degree
`n + 1`. -/
theorem hypercoveringHigherMap_def
    (K : @Hypercovering C _ J X) (n : ℕ)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    hypercoveringHigherMap K n =
      SemiRepresentableFamily.toPresheaf.map
        ((SemiRepresentableFamily.Over.forget).map (matchingMap K.toSimplicialObject n)) := sorry

/-- Lemma 25.3.9 (1): for a hypercovering `K` of `X`, the degree-`0` augmentation
`F(K)_0 ⟶ h_X` becomes locally surjective after sheafification. -/
@[stacks 01G9]
theorem hypercoveringZeroMap_isLocallySurjective
    (K : @Hypercovering C _ J X) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map (hypercoveringZeroMap K)) := sorry

/-- Lemma 25.3.9 (2): for a hypercovering `K` of `X`, the degree-`1` matching morphism
`(d^1_0, d^1_1) : F(K)_1 ⟶ F(K)_0 ×_{h_X} F(K)_0` becomes locally surjective after
sheafification. -/
@[stacks 01G9]
theorem hypercoveringOneMap_isLocallySurjective
    (K : @Hypercovering C _ J X) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map (hypercoveringOneMap K)) := sorry

/-- Lemma 25.3.9 (3): for a hypercovering `K` of `X` and `n ≥ 1`, the degree-`n + 1` comparison
map becomes locally surjective after sheafification. The target is written as the degree-`n + 1`
term of `F(cosk_n sk_n K)`, which is the Chapter 25 canonical form of the source's
`(\operatorname{cosk}_n \operatorname{sk}_n F(K))_{n + 1}` for `n ≥ 1`. -/
@[stacks 01G9]
theorem hypercoveringHigherMap_isLocallySurjective
    (K : @Hypercovering C _ J X) (n : ℕ) (_ : 1 ≤ n)
    [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ SR(C, X),
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F] :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max w v))).map (hypercoveringHigherMap K n)) := sorry

end CategoryTheory

import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import StacksProject_2024.Chap18.Definition_18_5_1
import StacksProject_2024.Chap25.Definition_25_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped CategoryTheory.SemiRepresentableFamily
open scoped FreeAbelianSheaf

noncomputable section

universe w v u

namespace CategoryTheory

/- Source/core/bridge triage for Lemma 25.6.2:
- `source-facing`: the degree-`0` equalizer fork attached to a hypercovering of a presheaf;
- `core/canonical`: morphisms from the sheafification of the free abelian presheaf on `𝒢` into
  the coefficient sheaf `𝒜`;
- `bridge/view`: the presheaf-level functor `h0OverPresheafFunctor`, obtained by sheafifying the
  free abelian presheaf first and then applying the canonical represented-Hom owner. -/

-- Semantic search note: `lean_leansearch` surfaced equalizer/fork APIs; the owner choice follows
-- the Chapter 18 free-abelian sheafification owner together with the Chapter 25
-- hypercovering-of-a-presheaf API.

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasEqualizers C] [HasPullbacks C]
variable [HasWeakSheafify J (Type (max w v))]
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable {𝒢 : Cᵒᵖ ⥤ Type (max w v)}

/-- The contravariant additive `H^0(-, 𝒜)` functor on set-valued presheaves, obtained by
sheafifying the free abelian presheaf and then taking morphisms into `𝒜`. Pointwise this is the
Hom group of morphisms from the sheafification of `𝒢 ⋙ AddCommGrpCat.free` to `𝒜`. -/
abbrev h0OverPresheafFunctor
    (𝒜 : Sheaf J AddCommGrpCat.{max w v}) :
    (Cᵒᵖ ⥤ Type (max w v))ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  ((((Functor.whiskeringRight Cᵒᵖ (Type (max w v))
      AddCommGrpCat.{max w v}).obj AddCommGrpCat.free) ⋙
    presheafToSheaf J AddCommGrpCat.{max w v}).op) ⋙
      preadditiveYoneda.obj 𝒜

/-- Evaluating `H^0(-, 𝒜)` on a presheaf `𝒢` gives morphisms from the sheafification of the free
abelian presheaf on `𝒢`, namely the free abelian sheaf `(ℤ_ 𝒢)^#[J]`, to `𝒜`. -/
@[simp] theorem h0OverPresheafFunctor_obj
    (𝒜 : Sheaf J AddCommGrpCat.{max w v})
    (𝒢 : Cᵒᵖ ⥤ Type (max w v)) :
    (h0OverPresheafFunctor (J := J) 𝒜).obj (op 𝒢) =
      ((((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{max w v})) ⟶ 𝒜) :=
  rfl

namespace HypercoveringOf

/-- The degree-`0` comparison morphism on `H^0(-, 𝒜)` induced by the augmentation of a
hypercovering of `𝒢`. -/
abbrev h0AugmentationMap
    (K : HypercoveringOf J 𝒢)
    (𝒜 : Sheaf J AddCommGrpCat.{max w v}) :
    (h0OverPresheafFunctor 𝒜).obj (op 𝒢) ⟶
      (h0OverPresheafFunctor 𝒜).obj
        (op (hypercoveringTerm K.simplicial 0)) :=
  (h0OverPresheafFunctor 𝒜).map
    K.zeroMap.op

/-- The two degree-`1` face maps on `H^0(K₀, 𝒜)`, indexed by the face `i : Fin 2`. -/
abbrev h0FaceMap
    (K : HypercoveringOf J 𝒢)
    (𝒜 : Sheaf J AddCommGrpCat.{max w v})
    (i : Fin 2) :
    (h0OverPresheafFunctor 𝒜).obj
        (op (hypercoveringTerm K.simplicial 0)) ⟶
      (h0OverPresheafFunctor 𝒜).obj
        (op (hypercoveringTerm K.simplicial 1)) :=
  (h0OverPresheafFunctor 𝒜).map
    (SemiRepresentableFamily.toPresheaf.map (K.simplicial.δ i)).op

/-- The augmentation of a hypercovering of `𝒢` satisfies the degree-`0` equalizer relation after
passing to the additive `H^0(-, 𝒜)` owner. -/
theorem h0AugmentationMap_condition
    (K : HypercoveringOf J 𝒢)
    (𝒜 : Sheaf J AddCommGrpCat.{max w v}) :
    K.h0AugmentationMap 𝒜 ≫ K.h0FaceMap 𝒜 0 =
      K.h0AugmentationMap 𝒜 ≫ K.h0FaceMap 𝒜 1 := by
  simpa [h0AugmentationMap, h0FaceMap] using
    congrArg
      ((h0OverPresheafFunctor 𝒜).map)
      (K.oneMap_condition.op)

/-- The canonical fork computing degree-`0` hypercover sections of `𝒜` on a hypercovering of
`𝒢`. -/
def h0Fork
    (K : HypercoveringOf J 𝒢)
    (𝒜 : Sheaf J AddCommGrpCat.{max w v}) :
    Fork (K.h0FaceMap 𝒜 0) (K.h0FaceMap 𝒜 1) :=
  Fork.ofι
    (K.h0AugmentationMap 𝒜)
    (K.h0AugmentationMap_condition 𝒜)

@[simp] theorem h0Fork_ι
    (K : HypercoveringOf J 𝒢)
    (𝒜 : Sheaf J AddCommGrpCat.{max w v}) :
    (K.h0Fork 𝒜).ι = K.h0AugmentationMap 𝒜 :=
  rfl

theorem h0Fork_condition
    (K : HypercoveringOf J 𝒢)
    (𝒜 : Sheaf J AddCommGrpCat.{max w v}) :
    (K.h0Fork 𝒜).ι ≫ K.h0FaceMap 𝒜 0 =
      (K.h0Fork 𝒜).ι ≫ K.h0FaceMap 𝒜 1 := by
  simpa using (K.h0Fork 𝒜).condition

/-- Lemma 25.6.2: if `K` is a hypercovering of a presheaf `𝒢` and `𝒜` is a sheaf of abelian
groups, then `\check H^0(K, 𝒜) = H^0(𝒢, 𝒜)`. In Lean this is formalized by requiring the canonical
fork from `H^0(𝒢, 𝒜)` to the equalizer of the two degree-`1` face maps on `H^0(K_0, 𝒜)` to be a
limit fork. -/
@[stacks 09VV]
theorem h0Fork_isLimit
    (K : HypercoveringOf J 𝒢)
    (𝒜 : Sheaf J AddCommGrpCat.{max w v}) :
    IsLimit (K.h0Fork 𝒜) := sorry

/-- Companion reformulation of Lemma 25.6.2: the degree-`0` augmentation map on `H^0(-, 𝒜)`
itself exhibits `H^0(𝒢, 𝒜)` as the equalizer of the two degree-`1` face maps on `H^0(K_0, 𝒜)`.
-/
theorem h0AugmentationMap_isLimit
    (K : HypercoveringOf J 𝒢)
    (𝒜 : Sheaf J AddCommGrpCat.{max w v}) :
    IsLimit (Fork.ofι (K.h0AugmentationMap 𝒜) (K.h0AugmentationMap_condition 𝒜)) := by
  simpa [h0Fork] using K.h0Fork_isLimit 𝒜

end HypercoveringOf

end CategoryTheory

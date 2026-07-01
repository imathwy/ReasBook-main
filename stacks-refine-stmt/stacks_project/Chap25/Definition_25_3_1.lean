import Mathlib
import stacks_project.Chap25.Definition_25_2_2

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace Limits
namespace FormalCoproduct

/- Domain-style sampling for Definition 25.3.1:
- primary domain: formal coproducts in the slice `C / U` and the canonical comparison from the
  coproduct of the corresponding representables to the representable presheaf of `U`;
- sampled owner declarations:
  `FormalCoproduct`,
  `FormalCoproduct.toPresheaf`,
  `CategoryTheory.uliftYoneda`,
  `CategoryTheory.Limits.Sigma.desc`;
- best owner abstraction: the family side is the canonical coproduct-of-representables presheaf
  `FormalCoproduct.toPresheaf`, applied after forgetting from `FormalCoproduct (Over U)` to
  `FormalCoproduct C`;
- primitive data: only the fixed-target family `K : FormalCoproduct (Over U)`;
- derived API: the canonical forgetful functor `forgetOver`, the induced natural transformation
  `augmentation`, and its component formulas.

Source/core/bridge triage:
- `source-facing`: the canonical augmentation
  `toPresheaf.obj ((forgetOver U).obj K) ⟶ uliftYoneda.obj U`;
- `core/canonical`: `FormalCoproduct.toPresheaf`, `uliftYoneda`;
- `bridge/view`: `forgetOver` and the augmentation component formulas.
-/

/-- Forgetting the structure maps to `U` sends a formal coproduct in `C / U` to its underlying
formal coproduct in `C`. -/
def forgetOver (U : C) : FormalCoproduct.{w} (CategoryTheory.Over U) ⥤ FormalCoproduct.{w} C where
  obj K := ⟨K.I, fun i ↦ (K.obj i).left⟩
  map φ := ⟨φ.f, fun i ↦ (φ.φ i).left⟩

/-- Definition 25.3.1: a family of arrows with fixed target `U` induces a canonical map from the
associated coproduct of representable presheaves to the representable presheaf `h_U`. -/
noncomputable def augmentation {U : C} (K : FormalCoproduct.{w} (CategoryTheory.Over U)) :
    (CategoryTheory.Limits.FormalCoproduct.toPresheaf (C := C)).obj ((forgetOver U).obj K) ⟶
      uliftYoneda.obj U := by
  let F : K.I → Cᵒᵖ ⥤ Type (max w v) := fun i ↦ uliftYoneda.{w}.obj (K.obj i).left
  change ∐ F ⟶ uliftYoneda.{w}.obj U
  exact Limits.Sigma.desc fun i : K.I ↦ uliftYoneda.{w}.map (K.obj i).hom

@[simp] theorem augmentation_ι_app {U : C} (K : FormalCoproduct.{w} (CategoryTheory.Over U))
    (X : Cᵒᵖ) (i : K.I) (g : X.unop ⟶ (K.obj i).left) :
    (augmentation K).app X
        (((Sigma.ι (fun i : K.I ↦ uliftYoneda.{w}.obj (K.obj i).left) i).app X)
          (ULift.up g)) =
      ULift.up (g ≫ (K.obj i).hom) := by
  simpa [augmentation] using congrFun
    ((NatTrans.congr_app
      (Sigma.ι_desc (fun i : K.I ↦ uliftYoneda.{w}.map (K.obj i).hom) i) X))
    (ULift.up g)

@[simp] theorem augmentation_app {U : C} (K : FormalCoproduct.{w} (CategoryTheory.Over U))
    (X : Cᵒᵖ)
    (s : ((CategoryTheory.Limits.FormalCoproduct.toPresheaf (C := C)).obj ((forgetOver U).obj K)).obj X) :
    (augmentation K).app X s =
      ULift.up
        ((((forgetOver U).obj K).toPresheafObjEquiv X s).2 ≫
          (K.obj (((forgetOver U).obj K).toPresheafObjEquiv X s).1).hom) := by
  cases h : ((forgetOver U).obj K).toPresheafObjEquiv X s with
  | mk i g =>
      have hs : (((forgetOver U).obj K).toPresheafObjEquiv X).symm ⟨i, g⟩ = s :=
        (((forgetOver U).obj K).toPresheafObjEquiv X).symm_apply_eq.2 h.symm
      rw [← hs, ((forgetOver U).obj K).toPresheafObjEquiv_symm_sigma]
      simpa using augmentation_ι_app K X i g

end FormalCoproduct
end Limits

namespace SemiRepresentableFamily
namespace Over

open CategoryTheory.Limits

private abbrev toFormalCoproduct {U : C} (K : SR(C, U)) :
    FormalCoproduct.{w} (CategoryTheory.Over U) :=
  ⟨K.index, K.obj⟩

/-- Bridge/view companion: the chapter-level fixed-target family presentation of the canonical
augmentation from Definition 25.3.1. -/
noncomputable abbrev augmentation {U : C} (K : SR(C, U)) :
    SemiRepresentableFamily.toPresheaf.obj ((forget).obj K) ⟶ uliftYoneda.obj U :=
  FormalCoproduct.augmentation (toFormalCoproduct K)

@[simp] theorem augmentation_ι_app {U : C} (K : SR(C, U))
    (X : Cᵒᵖ) (i : K.index) (g : X.unop ⟶ ((forget).obj K).obj i) :
    (augmentation K).app X
        (((Sigma.ι (fun i : K.index ↦ uliftYoneda.{w}.obj (((forget).obj K).obj i)) i).app X)
          (ULift.up g)) =
      ULift.up (g ≫ (K.obj i).hom) := by
  simpa using FormalCoproduct.augmentation_ι_app (K := toFormalCoproduct K) X i g

@[simp] theorem augmentation_app {U : C} (K : SR(C, U))
    (X : Cᵒᵖ) (s : (SemiRepresentableFamily.toPresheaf.obj ((forget).obj K)).obj X) :
    (augmentation K).app X s =
      ULift.up
        ((((forget).obj K).toPresheafObjEquiv X s).2 ≫
          (K.obj (((forget).obj K).toPresheafObjEquiv X s).1).hom) := by
  cases h : ((forget).obj K).toPresheafObjEquiv X s with
  | mk i g =>
      have hs : (((forget).obj K).toPresheafObjEquiv X).symm ⟨i, g⟩ = s :=
        (((forget).obj K).toPresheafObjEquiv X).symm_apply_eq.2 h.symm
      rw [← hs, ((forget).obj K).toPresheafObjEquiv_symm_sigma]
      simpa using augmentation_ι_app K X i g

end Over
end SemiRepresentableFamily

end CategoryTheory

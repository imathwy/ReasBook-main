import StacksProject_2024.Chap25.Definition_25_2_1
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace Limits
namespace FormalCoproduct

/- Domain-style sampling for Definition 25.2.2:
- primary domain: semi-representable families and the associated coproducts of representable
  presheaves;
- sampled owner declarations:
  `CategoryTheory.SemiRepresentableFamily`,
  `CategoryTheory.Limits.FormalCoproduct`,
  `CategoryTheory.Limits.FormalCoproduct.eval`,
  `sigmaObjIso`,
  `Types.coproductIso`;
- best owner abstraction: the chapter owner is `SemiRepresentableFamily.toPresheaf`; the
  formal-coproduct side supplies the core implementation obtained from `FormalCoproduct.eval`
  applied to `CategoryTheory.uliftYoneda`;
- primitive data on the core side: only the indexed family `K : FormalCoproduct C`;
- derived API on the core side: the bridge functor `FormalCoproduct.toPresheaf` and the pointwise
  sigma-model equivalence `toPresheafObjEquiv`.

Source/core/bridge triage:
- `source-facing`: `SemiRepresentableFamily.toPresheaf`;
- `core/canonical`: `FormalCoproduct.eval` on `uliftYoneda`;
- `bridge/view`: `FormalCoproduct.toPresheaf` and the pointwise sigma-model equivalence on formal
  coproducts.
-/

/-- Core/canonical bridge: evaluating `uliftYoneda` on a formal coproduct produces the coproduct
of the corresponding representable presheaves. -/
noncomputable def toPresheaf :
    FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ Type (max w v)) :=
  (FormalCoproduct.eval C (Cᵒᵖ ⥤ Type (max w v))).obj (uliftYoneda.{w})

private noncomputable def toPresheafObjIsoULift (K : FormalCoproduct.{w} C) (X : Cᵒᵖ) :
    (toPresheaf.obj K).obj X ≅ Σ i : K.I, ULift.{w} (X.unop ⟶ K.obj i) :=
  (sigmaObjIso (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) X) ≪≫
    Types.coproductIso (fun i : K.I ↦ ULift.{w} (X.unop ⟶ K.obj i))

/-- The coproduct summand of `toPresheaf.obj K` determined by an index `i` and a section
`g : X.unop ⟶ K.obj i`. -/
noncomputable def toPresheafObjMk (K : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    (toPresheaf.obj K).obj X :=
  ((Sigma.ι (fun j : K.I ↦ uliftYoneda.obj (K.obj j)) i).app X) (ULift.up g)

/-- Core sigma-model equivalence for the formal-coproduct bridge `toPresheaf`. -/
noncomputable def toPresheafObjEquiv (K : FormalCoproduct.{w} C) (X : Cᵒᵖ) :
    (toPresheaf.obj K).obj X ≃ Σ i : K.I, X.unop ⟶ K.obj i :=
  (toPresheafObjIsoULift K X).toEquiv.trans (Equiv.sigmaCongrRight fun _ ↦ Equiv.ulift)

@[simp] theorem toPresheafObjEquiv_ι (K : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    K.toPresheafObjEquiv X (K.toPresheafObjMk X i g) = ⟨i, g⟩ := by
  have hULift :
      (toPresheafObjIsoULift K X).hom (K.toPresheafObjMk X i g) = ⟨i, ULift.up g⟩ := by
    have hcomp :
        ((Sigma.ι (fun j : K.I ↦ uliftYoneda.obj (K.obj j)) i).app X) ≫
            (toPresheafObjIsoULift K X).hom =
          (fun x : ULift.{w} (X.unop ⟶ K.obj i) ↦
            (⟨i, x⟩ : Σ j : K.I, ULift.{w} (X.unop ⟶ K.obj j))) := by
      let mid :
          ULift.{w} (X.unop ⟶ K.obj i) ⟶ Σ j : K.I, ULift.{w} (X.unop ⟶ K.obj j) :=
        Sigma.ι (fun j : K.I ↦ ULift.{w} (X.unop ⟶ K.obj j)) i ≫
          (Types.coproductIso fun j : K.I ↦ ULift.{w} (X.unop ⟶ K.obj j)).hom
      have hcomp₁ :
          ((Sigma.ι (fun j : K.I ↦ uliftYoneda.obj (K.obj j)) i).app X) ≫
              (toPresheafObjIsoULift K X).hom =
            mid := by
        have hsigma :
            ((Sigma.ι (fun j : K.I ↦ uliftYoneda.obj (K.obj j)) i).app X) ≫
                (sigmaObjIso (fun j : K.I ↦ uliftYoneda.obj (K.obj j)) X).hom =
              Sigma.ι (fun j : K.I ↦ ULift.{w} (X.unop ⟶ K.obj j)) i := by
          simpa using
            ι_comp_sigmaObjIso_hom
              (fun j : K.I ↦ uliftYoneda.obj (K.obj j)) X i
        simpa [toPresheafObjIsoULift, Category.assoc] using
          congrArg
            (fun k ↦ k ≫
              (Types.coproductIso fun j : K.I ↦ ULift.{w} (X.unop ⟶ K.obj j)).hom)
            hsigma
      have hcomp₂ :
          mid =
            (fun x : ULift.{w} (X.unop ⟶ K.obj i) ↦
              (⟨i, x⟩ : Σ j : K.I, ULift.{w} (X.unop ⟶ K.obj j))) := by
        simpa using
          Types.coproductIso_ι_comp_hom
            (fun j : K.I ↦ ULift.{w} (X.unop ⟶ K.obj j)) i
      exact hcomp₁.trans hcomp₂
    simpa [toPresheafObjMk] using congrFun hcomp (ULift.up g)
  simpa [toPresheafObjEquiv] using
    congrArg (Equiv.sigmaCongrRight fun _ ↦ Equiv.ulift) hULift

@[simp] theorem toPresheafObjEquiv_symm_sigma (K : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    (K.toPresheafObjEquiv X).symm ⟨i, g⟩ = K.toPresheafObjMk X i g := by
  apply (K.toPresheafObjEquiv X).injective
  simp

@[simp] theorem toPresheaf_map_objMk {K L : FormalCoproduct.{w} C} (φ : K ⟶ L) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    ((toPresheaf.map φ).app X) (K.toPresheafObjMk X i g) =
      L.toPresheafObjMk X (φ.f i) (g ≫ φ.φ i) := by
  change
      ((((FormalCoproduct.eval C (Cᵒᵖ ⥤ Type (max w v))).obj (uliftYoneda.{w, v, u})).map φ).app
          X)
        (((Sigma.ι (fun j : K.I ↦ uliftYoneda.{w, v, u}.obj (K.obj j)) i).app X) (ULift.up g)) =
      L.toPresheafObjMk X (φ.f i) (g ≫ φ.φ i)
  rw [FormalCoproduct.eval_obj_map]
  have h :
      Sigma.ι (fun j : K.I ↦ uliftYoneda.{w, v, u}.obj (K.obj j)) i ≫
          Sigma.desc (fun j ↦ uliftYoneda.{w, v, u}.map (φ.φ j) ≫
            Sigma.ι (uliftYoneda.{w, v, u}.obj ∘ L.obj) (φ.f j)) =
        uliftYoneda.{w, v, u}.map (φ.φ i) ≫
          Sigma.ι (uliftYoneda.{w, v, u}.obj ∘ L.obj) (φ.f i) := by
    simpa using
      (Sigma.ι_desc
        (fun j ↦ uliftYoneda.{w, v, u}.map (φ.φ j) ≫
          Sigma.ι (uliftYoneda.{w, v, u}.obj ∘ L.obj) (φ.f j))
        i)
  have happ := congr_app h X
  simpa [toPresheafObjMk] using congrFun happ (ULift.up g)

end FormalCoproduct
end Limits

namespace SemiRepresentableFamily

open CategoryTheory.Limits

/-- Definition 25.2.2: a semi-representable family in `SR(C)` determines the coproduct of the
representable presheaves represented by its members. -/
@[stacks 01G1]
noncomputable abbrev toPresheaf :
    SR(C) ⥤ (Cᵒᵖ ⥤ Type (max w v)) :=
  toFormalCoproduct ⋙ FormalCoproduct.toPresheaf

/-- The coproduct summand of `(toPresheaf.obj K).obj X` determined by an index `i` and a section
`g : X.unop ⟶ K.obj i`. -/
noncomputable abbrev toPresheafObjMk (K : SR(C)) (X : Cᵒᵖ)
    (i : K.index) (g : X.unop ⟶ K.obj i) :
    (toPresheaf.obj K).obj X :=
  (toFormalCoproduct.obj K).toPresheafObjMk X i g

/-- Companion sigma-model: the sections of `toPresheaf K` at `X` are equivalent to pairs
consisting of an index `i` of the family and a morphism `X.unop ⟶ K.obj i`. -/
noncomputable abbrev toPresheafObjEquiv (K : SR(C)) (X : Cᵒᵖ) :
    (toPresheaf.obj K).obj X ≃ Σ i : K.index, X.unop ⟶ K.obj i :=
  (toFormalCoproduct.obj K).toPresheafObjEquiv X

@[simp] theorem toPresheafObjEquiv_ι (K : SR(C)) (X : Cᵒᵖ)
    (i : K.index) (g : X.unop ⟶ K.obj i) :
    K.toPresheafObjEquiv X (K.toPresheafObjMk X i g) = ⟨i, g⟩ := by
  simpa [SemiRepresentableFamily.toPresheaf, SemiRepresentableFamily.toPresheafObjEquiv,
    SemiRepresentableFamily.toPresheafObjMk, SemiRepresentableFamily.toFormalCoproduct] using
    FormalCoproduct.toPresheafObjEquiv_ι (toFormalCoproduct.obj K) X i g

@[simp] theorem toPresheafObjEquiv_symm_sigma (K : SR(C)) (X : Cᵒᵖ) (i : K.index)
    (g : X.unop ⟶ K.obj i) :
    (K.toPresheafObjEquiv X).symm ⟨i, g⟩ = K.toPresheafObjMk X i g := by
  simpa [SemiRepresentableFamily.toPresheaf, SemiRepresentableFamily.toPresheafObjEquiv,
    SemiRepresentableFamily.toPresheafObjMk, SemiRepresentableFamily.toFormalCoproduct] using
    FormalCoproduct.toPresheafObjEquiv_symm_sigma (toFormalCoproduct.obj K) X i g

@[simp] theorem toPresheaf_map_objMk {K L : SR(C)} (φ : K ⟶ L) (X : Cᵒᵖ) (i : K.index)
    (g : X.unop ⟶ K.obj i) :
    ((toPresheaf.map φ).app X) (K.toPresheafObjMk X i g) =
      L.toPresheafObjMk X (φ.f i) (g ≫ φ.φ i) := by
  simpa [SemiRepresentableFamily.toPresheaf, SemiRepresentableFamily.toPresheafObjMk,
    SemiRepresentableFamily.toFormalCoproduct] using
    FormalCoproduct.toPresheaf_map_objMk (toFormalCoproduct.map φ) X i g

end SemiRepresentableFamily

end CategoryTheory

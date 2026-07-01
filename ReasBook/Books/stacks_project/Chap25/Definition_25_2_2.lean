import Mathlib
import stacks_project.Chap25.Definition_25_2_1

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
noncomputable abbrev toPresheaf :
    FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ Type (max w v)) :=
  (FormalCoproduct.eval C (Cᵒᵖ ⥤ Type (max w v))).obj (uliftYoneda.{w})

/-- Core pointwise sigma-model for the formal-coproduct bridge `toPresheaf`. -/
noncomputable def toPresheafObjIsoULift (K : FormalCoproduct.{w} C) (X : Cᵒᵖ) :
    (toPresheaf.obj K).obj X ≅ Σ i : K.I, ULift.{w} (X.unop ⟶ K.obj i) :=
  (sigmaObjIso (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) X) ≪≫
    Types.coproductIso (fun i : K.I ↦ ULift.{w} (X.unop ⟶ K.obj i))

/-- Core sigma-model equivalence for the formal-coproduct bridge `toPresheaf`. -/
noncomputable def toPresheafObjEquiv (K : FormalCoproduct.{w} C) (X : Cᵒᵖ) :
    (toPresheaf.obj K).obj X ≃ Σ i : K.I, X.unop ⟶ K.obj i :=
  (toPresheafObjIsoULift K X).toEquiv.trans (Equiv.sigmaCongrRight fun _ ↦ Equiv.ulift)

@[simp] theorem toPresheafObjEquiv_ι (K : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    toPresheafObjEquiv K X (((Sigma.ι (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) i).app X)
      (ULift.up g)) = ⟨i, g⟩ := by
  change (Equiv.sigmaCongrRight (fun _ ↦ Equiv.ulift))
      ((Types.coproductIso (fun i : K.I ↦ ULift.{w} (X.unop ⟶ K.obj i))).hom
        (((sigmaObjIso (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) X).hom)
          (((Sigma.ι (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) i).app X) (ULift.up g)))) = _
  rw [show ((sigmaObjIso (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) X).hom)
      (((Sigma.ι (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) i).app X) (ULift.up g)) =
        Sigma.ι (fun i : K.I ↦ ULift.{w} (X.unop ⟶ K.obj i)) i (ULift.up g) by
      simpa using congrFun
        (ι_comp_sigmaObjIso_hom (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) X i) (ULift.up g)]
  rw [show (Types.coproductIso (fun i : K.I ↦ ULift.{w} (X.unop ⟶ K.obj i))).hom
      (Sigma.ι (fun i : K.I ↦ ULift.{w} (X.unop ⟶ K.obj i)) i (ULift.up g)) =
        ⟨i, ULift.up g⟩ by
      exact congrFun
        (Types.coproductIso_ι_comp_hom (fun i : K.I ↦ ULift.{w} (X.unop ⟶ K.obj i)) i)
        (ULift.up g)]
  rfl

@[simp] theorem toPresheafObjEquiv_symm_sigma (K : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : K.I) (g : X.unop ⟶ K.obj i) :
    (toPresheafObjEquiv K X).symm ⟨i, g⟩ =
      (((Sigma.ι (fun i : K.I ↦ uliftYoneda.obj (K.obj i)) i).app X) (ULift.up g)) := by
  exact (toPresheafObjEquiv K X).symm_apply_eq.2 (toPresheafObjEquiv_ι K X i g).symm

end FormalCoproduct
end Limits

namespace SemiRepresentableFamily

open CategoryTheory.Limits

private abbrev toFormalCoproduct :
    SR(C) ⥤ FormalCoproduct.{w} C where
  obj K := ⟨K.index, K.obj⟩
  map φ := ⟨φ.α, φ.f⟩

/-- Definition 25.2.2: a semi-representable family in `SR(C)` determines the coproduct of the
representable presheaves represented by its members. -/
noncomputable abbrev toPresheaf :
    SR(C) ⥤ (Cᵒᵖ ⥤ Type (max w v)) :=
  toFormalCoproduct ⋙ FormalCoproduct.toPresheaf.{w, v, u}

/-- Pointwise, `toPresheaf K` is the sigma-type of sections into the components of `K`, still
remembering the `ULift` coming from `uliftYoneda`. -/
noncomputable abbrev toPresheafObjIsoULift (K : SR(C)) (X : Cᵒᵖ) :=
  (toFormalCoproduct.obj K).toPresheafObjIsoULift X

/-- Companion sigma-model: the sections of `toPresheaf K` at `X` are equivalent to pairs
consisting of an index `i` of the family and a morphism `X.unop ⟶ K.obj i`. -/
noncomputable abbrev toPresheafObjEquiv (K : SR(C)) (X : Cᵒᵖ) :=
  (toFormalCoproduct.obj K).toPresheafObjEquiv X

@[simp] theorem toPresheafObjEquiv_ι (K : SR(C)) (X : Cᵒᵖ)
    (i : K.index) (g : X.unop ⟶ K.obj i) :
    toPresheafObjEquiv K X (((Sigma.ι (fun i : K.index ↦ uliftYoneda.obj (K.obj i)) i).app X)
      (ULift.up g)) = ⟨i, g⟩ := by
  simpa using (toFormalCoproduct.obj K).toPresheafObjEquiv_ι X i g

@[simp] theorem toPresheafObjEquiv_symm_sigma (K : SR(C)) (X : Cᵒᵖ) (i : K.index)
    (g : X.unop ⟶ K.obj i) :
    (toPresheafObjEquiv K X).symm ⟨i, g⟩ =
      (((Sigma.ι (fun i : K.index ↦ uliftYoneda.obj (K.obj i)) i).app X) (ULift.up g)) := by
  simpa using (toFormalCoproduct.obj K).toPresheafObjEquiv_symm_sigma X i g

end SemiRepresentableFamily

end CategoryTheory

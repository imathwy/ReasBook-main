import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_25_2_1 (from Chap25) -/
universe w v u v' u'

namespace CategoryTheory

/- Domain-style sampling for Definition 25.2.1:
- primary domain: arbitrary type-indexed families of objects in a category and their
  componentwise morphisms;
- sampled declarations:
  `CategoryTheory.Over`,
  `CategoryTheory.Over.map`,
  `CategoryTheory.Over.forget`,
  `CategoryTheory.Sigma.desc`;
- best owner abstraction: `SemiRepresentableFamily C` itself. The sigma-category owner is too
  small because morphisms there do not allow retargeting indices along an arbitrary function, while
  the slice-category owners only supply fixed-target bridge/view API;
- primitive data: an indexing type together with its object family `index → C`;
- derived API: the category structure, componentwise functorial action `map`, the fixed-target
  bridge/view `Over X` with its indexed-arrow constructor `ofArrows`, and the forgetful functor
  `Over.forget : SR(C, X) ⥤ SR(C)`.

Source/core/bridge triage:
- `source-facing`: `SemiRepresentableFamily C`;
- `core/canonical`: the componentwise functorial owner `SemiRepresentableFamily.map`;
- `bridge/view`: `SemiRepresentableFamily.Over X`, `SemiRepresentableFamily.Over.ofArrows`, and
  the fixed-target forgetful functor induced by `CategoryTheory.Over.forget`.
-/

/-- Definition 25.2.1: `SR(C)` is the category whose objects are families of objects of `C`
indexed by an arbitrary type. -/
structure SemiRepresentableFamily (C : Type u) [Category.{v} C] where
  /-- The indexing type of the family. -/
  index : Type w
  /-- The object of `C` attached to each index. -/
  obj : index → C

namespace SemiRepresentableFamily

scoped notation "SR(" C ")" => _root_.CategoryTheory.SemiRepresentableFamily C

end SemiRepresentableFamily

open scoped CategoryTheory.SemiRepresentableFamily

namespace SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- A morphism of semi-representable families is a map on indices together with a component
morphism in `C` for each source index. -/
structure Hom (U V : SemiRepresentableFamily C) where
  /-- The induced map on the indexing types. -/
  α : U.index → V.index
  /-- The component morphism attached to each source index. -/
  f : ∀ i : U.index, U.obj i ⟶ V.obj (α i)

namespace Hom

def id (U : SemiRepresentableFamily C) : U.Hom U where
  α := fun i ↦ i
  f := fun i ↦ 𝟙 (U.obj i)

def comp {U V W : SemiRepresentableFamily C} (φ : U.Hom V) (ψ : V.Hom W) : U.Hom W where
  α := ψ.α ∘ φ.α
  f := fun i ↦ φ.f i ≫ ψ.f (φ.α i)

@[ext] theorem ext {U V : SemiRepresentableFamily C} {φ ψ : U.Hom V}
    (hα : φ.α = ψ.α) (hf : ∀ i, HEq (φ.f i) (ψ.f i)) :
    φ = ψ := by
  cases φ with
  | mk αφ fφ =>
      cases ψ with
      | mk αψ fψ =>
          cases hα
          have hf' : fφ = fψ := by
            funext i
            exact eq_of_heq (hf i)
          cases hf'
          rfl

end Hom

/-- Semi-representable families form a category by composing index maps and component morphisms. -/
instance instCategory : Category (SemiRepresentableFamily C) where
  Hom U V := Hom U V
  id := Hom.id
  comp φ ψ := Hom.comp φ ψ
  id_comp := by
    intro X Y f
    refine Hom.ext (by funext i; rfl) ?_
    intro i
    simp [Hom.comp, Hom.id]
  comp_id := by
    intro X Y f
    refine Hom.ext (by funext i; rfl) ?_
    intro i
    simp [Hom.comp, Hom.id]
  assoc := by
    intro W X Y Z f g h
    refine Hom.ext (by funext i; rfl) ?_
    intro i
    simp [Hom.comp, Category.assoc]

/-- Applying a functor componentwise to a semi-representable family. -/
def map {D : Type u'} [Category.{v'} D] (F : C ⥤ D) :
    SemiRepresentableFamily C ⥤ SemiRepresentableFamily D where
  obj U :=
    { index := U.index
      obj := fun i ↦ F.obj (U.obj i) }
  map φ :=
    { α := φ.α
      f := fun i ↦ F.map (φ.f i) }
  map_id := by
    intro X
    refine Hom.ext rfl ?_
    intro i
    exact heq_of_eq (F.map_id (X.obj i))
  map_comp := by
    intro X Y Z φ ψ
    refine Hom.ext rfl ?_
    intro i
    exact heq_of_eq (F.map_comp (φ.f i) (ψ.f (φ.α i)))

@[simp] theorem map_obj_obj {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    (U : SemiRepresentableFamily C) (i : U.index) :
    ((map F).obj U).obj i = F.obj (U.obj i) :=
  rfl

/-- For `X : C`, the category `SR(C, X)` of semi-representable objects over `X` is `SR(C / X)`. -/
abbrev Over (X : C) :=
  SR(CategoryTheory.Over X)

end SemiRepresentableFamily

namespace SemiRepresentableFamily

scoped syntax "SR(" term ", " term ")" : term

scoped macro_rules
  | `(SR($_, $x)) => `(SemiRepresentableFamily.Over $x)

end SemiRepresentableFamily

namespace SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace Over

/-- The fixed-target family over `X` defined by an indexed family of arrows `π i : Uᵢ i ⟶ X`. -/
abbrev ofArrows {X : C} {I : Type w} (Uᵢ : I → C) (π : ∀ i : I, Uᵢ i ⟶ X) : SR(C, X) where
  index := I
  obj := fun i ↦ CategoryTheory.Over.mk (π i)

/-- Forgetting the structure maps to `X` sends a family in `SR(C, X)` to its underlying family in
`SR(C)`. -/
def forget {X : C} : SR(C, X) ⥤ SR(C) :=
  SemiRepresentableFamily.map (CategoryTheory.Over.forget X)

@[simp] theorem forget_obj_obj {X : C} (K : SR(C, X)) (i : K.index) :
    (forget.obj K).obj i = (K.obj i).left :=
  rfl

@[simp] theorem forget_map_α {X : C} {K L : SR(C, X)} (φ : K ⟶ L) :
    (forget.map φ).α = φ.α :=
  rfl

@[simp] theorem forget_map_f {X : C} {K L : SR(C, X)} (φ : K ⟶ L) (i : K.index) :
    (forget.map φ).f i = (φ.f i).left :=
  rfl

end Over
end SemiRepresentableFamily

end CategoryTheory

/-! ### Definition_25_2_2 (from Chap25) -/
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

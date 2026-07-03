import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory SheafOfModules

noncomputable section

universe v u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD RingCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JC RingCat.{u})
variable (ℱ : SheafOfModules 𝒪)
variable (𝒢 : SheafOfModules ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪))

/- Domain-style sampling for Lemma 18.12.4:
- primary domain: pullback/pushforward of sheaves of modules along a morphism of topoi, together
  with same-site change of rings along the counit `f⁻¹ f_* 𝒪 ⟶ 𝒪`;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `pullbackPushforwardAdjunction`,
  `pushforwardComp`,
  `pushforwardCongr`,
  and the nearby bridge item `Lemma_18_12_3` for the unit-adjunction Hom equivalence;
- best owner abstraction: the source-facing tensor-pullback functor
  `𝒪 ⊗_{f⁻¹ f_* 𝒪} f⁻¹ (-)`, presented canonically as the composite of the two owner pullback
  functors induced by the unit and counit of
  `F.sheafAdjunctionContinuous RingCat JD JC`;
- primitive data: the unit
  `η_{f_* 𝒪} : f_* 𝒪 ⟶ f_* f⁻¹ f_* 𝒪`
  and counit
  `ε_𝒪 : f⁻¹ f_* 𝒪 ⟶ 𝒪`;
- derived API: the resulting Hom-set equivalence.

Source/core/bridge triage:
- `source-facing`: the tensor-pullback functor
  `𝒪 ⊗_{f⁻¹ f_* 𝒪} f⁻¹ (-)` and the induced Hom-set equivalence with morphisms into the direct
  image `f_* ℱ`;
- `core/canonical`: `pullbackPushforwardAdjunction` for the unit and counit maps, together with
  `pushforwardComp` and `SheafOfModules.pullback`;
- `bridge/view`: the identification of the composite right adjoint with pushforward along the
  identity via the triangle identity.

Primitive-vs-derived decision:
- the unit and counit maps are the only primitive local data;
- the pullback functors and right adjoints come from the owner API, so local duplicate unit/counit
  wrappers should be deleted;
- the only local derived construction worth naming publicly is the source-facing tensor-pullback
  functor itself. -/

/- Lemma 18.12.4, owner ingredients: the relevant adjunctions are the canonical
`pullbackPushforwardAdjunction` instances for the unit and counit ring maps, and the comparison of
their composite right adjoint with the identity-ring pushforward comes from `pushforwardComp`
together with the right triangle identity for `F.sheafAdjunctionContinuous`. -/
recall pullbackPushforwardAdjunction
recall pushforwardComp
recall pushforwardCongr

/-- The extension-of-scalars functor corresponding to
`𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1}(-)`. -/
noncomputable def morphism_of_topoi_module_tensor_functor (𝒪 : Sheaf JC RingCat.{u}) :
    SheafOfModules ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪) ⥤
      SheafOfModules 𝒪 :=
  let η :=
    (F.sheafAdjunctionContinuous RingCat.{u} JD JC).unit.app
      ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪)
  let ε :
      (F.sheafPushforwardContinuous RingCat.{u} JD JC ⋙
        F.sheafPullback RingCat.{u} JD JC).obj 𝒪 ⟶
        ((𝟭 C).sheafPushforwardContinuous RingCat.{u} JC JC).obj 𝒪 :=
    (F.sheafAdjunctionContinuous RingCat.{u} JD JC).counit.app 𝒪
  pullback η ⋙ pullback ε

-- Proof sketch: `pushforwardComp` identifies the composite right adjoint
-- `pushforward ε_𝒪 ⋙ pushforward η_{f_* 𝒪}`
-- with pushforward along
-- `η_{f_*𝒪} ≫ f_*(ε_𝒪)`, and this ring map is `𝟙_{f_*𝒪}` by the right triangle identity for
-- `F.sheafAdjunctionContinuous RingCat JD JC`.
/-- The composite right adjoint for the counit and unit ring maps is canonically the ordinary
pushforward along the identity of `f_* 𝒪`. -/
private noncomputable def morphism_of_topoi_module_pushforwardCompIso
    (𝒪 : Sheaf JC RingCat.{u}) :
    let η :=
      (F.sheafAdjunctionContinuous RingCat.{u} JD JC).unit.app
        ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪)
    let ε :
        (F.sheafPushforwardContinuous RingCat.{u} JD JC ⋙
          F.sheafPullback RingCat.{u} JD JC).obj 𝒪 ⟶
          ((𝟭 C).sheafPushforwardContinuous RingCat.{u} JC JC).obj 𝒪 :=
      (F.sheafAdjunctionContinuous RingCat.{u} JD JC).counit.app 𝒪
    pushforward ε ⋙ pushforward η ≅
    pushforward (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪)) :=
  let η :=
    (F.sheafAdjunctionContinuous RingCat.{u} JD JC).unit.app
      ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪)
  let ε :
      (F.sheafPushforwardContinuous RingCat.{u} JD JC ⋙
        F.sheafPullback RingCat.{u} JD JC).obj 𝒪 ⟶
        ((𝟭 C).sheafPushforwardContinuous RingCat.{u} JC JC).obj 𝒪 :=
    (F.sheafAdjunctionContinuous RingCat.{u} JD JC).counit.app 𝒪
  pushforwardComp η ε ≪≫
    pushforwardCongr (by
      exact
        (F.sheafAdjunctionContinuous RingCat.{u} JD JC).right_triangle_components 𝒪)

/-- Lemma 18.12.4: the tensor-pullback object
`𝒪 ⊗_{f^{-1}f_*𝒪} f^{-1} \mathcal{G}` represents morphisms into `ℱ` exactly as morphisms from
`𝒢` into the direct image `f_* ℱ`. -/
noncomputable def morphism_of_topoi_module_tensor_hom_equiv
    (𝒪 : Sheaf JC RingCat.{u}) (ℱ : SheafOfModules 𝒪)
    (𝒢 : SheafOfModules ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪)) :
    ((morphism_of_topoi_module_tensor_functor JC JD F 𝒪).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶
        (pushforward
          (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪))).obj ℱ) :=
  let η :=
    (F.sheafAdjunctionContinuous RingCat.{u} JD JC).unit.app
      ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪)
  let ε :
      (F.sheafPushforwardContinuous RingCat.{u} JD JC ⋙
        F.sheafPullback RingCat.{u} JD JC).obj 𝒪 ⟶
        ((𝟭 C).sheafPushforwardContinuous RingCat.{u} JC JC).obj 𝒪 :=
    (F.sheafAdjunctionContinuous RingCat.{u} JD JC).counit.app 𝒪
  ((pullbackPushforwardAdjunction ε).homEquiv ((pullback η).obj 𝒢) ℱ).trans
    (((pullbackPushforwardAdjunction η).homEquiv 𝒢 ((pushforward ε).obj ℱ)).trans
      ((Iso.refl 𝒢).homCongr
        ((morphism_of_topoi_module_pushforwardCompIso JC JD F 𝒪).app ℱ)))

-- Proof sketch: `morphism_of_topoi_module_tensor_hom_equiv` is an equivalence of hom-sets, so
-- its underlying function is bijective.
omit [HasWeakSheafify JD RingCat.{u}] [HasWeakSheafify JD AddCommGrpCat.{u}]
  [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
/-- The morphism correspondence of `morphism_of_topoi_module_tensor_hom_equiv` is bijective. -/
theorem morphism_of_topoi_module_tensor_hom_equiv_bijective
    (𝒪 : Sheaf JC RingCat.{u}) (ℱ : SheafOfModules 𝒪)
    (𝒢 : SheafOfModules ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪)) :
    Function.Bijective
      (morphism_of_topoi_module_tensor_hom_equiv JC JD F 𝒪 ℱ 𝒢) :=
  (morphism_of_topoi_module_tensor_hom_equiv JC JD F 𝒪 ℱ 𝒢).bijective

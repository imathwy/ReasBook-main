import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_12_1 (from Chap18) -/
/- Lemma 18.12.1: for a site presentation of a morphism of topoi by a continuous functor
`F : C ⥤ D` and a map of sheaves of rings `φ : \mathcal O' \to F_* \mathcal O`, the direct image
of sheaves of `\mathcal O`-modules is the canonical functor
`SheafOfModules.pushforward φ : Mod(\mathcal O) ⥤ Mod(\mathcal O')`. Its type already records
that the underlying sheaf of sets is pushed forward and that the construction is functorial in the
module sheaf. -/
recall SheafOfModules.pushforward

/-! ### Lemma_18_12_2 (from Chap18) -/
open CategoryTheory

universe u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC RingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JD RingCat.{u})

/- Lemma 18.12.2: for a morphism of topoi presented by a continuous functor `F : D ⥤ C`,
the inverse image of a sheaf of `𝒪`-modules on `D` is the canonical pullback functor on
sheaves of modules along the unit map `𝒪 ⟶ f_* f^{-1} 𝒪`. Its values are sheaves of modules over
the pulled-back ring `f^{-1} 𝒪`, so the construction is functorial in `\mathcal G`. -/
#check
  (SheafOfModules.pullback
    ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪) :
      SheafOfModules 𝒪 ⥤ _)

/-! ### Lemma_18_12_3 (from Chap18) -/
open CategoryTheory

noncomputable section

universe v u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC RingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JD RingCat.{u})
variable (𝒢 : SheafOfModules 𝒪)
variable (ℱ : SheafOfModules ((F.sheafPullback RingCat.{u} JD JC).obj 𝒪))

/- Domain-style sampling for Lemma 18.12.3:
- primary domain: pullback/pushforward of sheaves of modules along a morphism of topoi presented
  by a continuous functor;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Lemma_18_13_2`'s recall of the same owner abstraction for a general ringed-site morphism;
- best owner abstraction: `SheafOfModules.pullbackPushforwardAdjunction` for the unit map
  `((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪) : 𝒪 ⟶ f_* f⁻¹ 𝒪`;
- primitive data: the continuous functor `F` and the induced structure-sheaf map
  `𝒪 ⟶ f_* f⁻¹ 𝒪`;
- derived API: the Hom-set bijection obtained from that adjunction via `.homEquiv`.

Source/core/bridge triage:
- `source-facing`: the textbook Hom-set bijection
  `Mor_{Mod(f^{-1} 𝒪)}(f^{-1} 𝒢, ℱ) ≃ Mor_{Mod(𝒪)}(𝒢, f_* ℱ)`;
- `core/canonical`: the adjunction
  `SheafOfModules.pullbackPushforwardAdjunction
    ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪)`;
- `bridge/view`: the specialization of `.homEquiv` to `𝒢` and `ℱ`.

This item should therefore recall the owner adjunction directly and keep the Hom-bijection only as
its thin derived companion. -/

/- Lemma 18.12.3, owner form: the inverse-image functor on `𝒪`-modules is left adjoint to the
direct-image functor on `f^{-1} 𝒪`-modules, for the unit map `𝒪 ⟶ f_* f^{-1} 𝒪` induced by the
continuous functor `F`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 18.12.3: for a morphism of topoi presented by a continuous functor `F : D ⥤ C`, a sheaf
of rings `𝒪` on `D`, a sheaf of `𝒪`-modules `𝒢`, and a sheaf of `f^{-1} 𝒪`-modules `ℱ`, the
adjunction between pullback and pushforward of sheaves of modules induces the canonical bijection
`Mor_{Mod(f^{-1} 𝒪)}(f^{-1} 𝒢, ℱ) ≃ Mor_{Mod(𝒪)}(𝒢, f_* ℱ)`, where `f_* ℱ` is viewed as an
`𝒪`-module through the unit map `𝒪 ⟶ f_* f^{-1} 𝒪`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪)).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback
        ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪)).obj ℱ))

/-! ### Lemma_18_12_4 (from Chap18) -/
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

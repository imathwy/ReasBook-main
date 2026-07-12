import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules

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
recall pullbackPushforwardAdjunction

/- Lemma 18.12.3: for a morphism of topoi presented by a continuous functor `F : D ⥤ C`, a sheaf
of rings `𝒪` on `D`, a sheaf of `𝒪`-modules `𝒢`, and a sheaf of `f^{-1} 𝒪`-modules `ℱ`, the
adjunction between pullback and pushforward of sheaves of modules induces the canonical bijection
`Mor_{Mod(f^{-1} 𝒪)}(f^{-1} 𝒢, ℱ) ≃ Mor_{Mod(𝒪)}(𝒢, f_* ℱ)`, where `f_* ℱ` is viewed as an
`𝒪`-module through the unit map `𝒪 ⟶ f_* f^{-1} 𝒪`. -/
#check
  (((pullbackPushforwardAdjunction
      ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪)).homEquiv 𝒢 ℱ) :
    ((pullback
        ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (pushforward
        ((F.sheafAdjunctionContinuous RingCat JD JC).unit.app 𝒪)).obj ℱ))

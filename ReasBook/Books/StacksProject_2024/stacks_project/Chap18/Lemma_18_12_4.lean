import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe v u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JC RingCat.{u})
variable (𝒢 : SheafOfModules ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪))
variable (ℱ : SheafOfModules 𝒪)

/- Domain-style sampling for Lemma 18.12.4:
- primary domain: pullback/pushforward of sheaves of modules along a morphism of topoi, together
  with the identity-ring specialization over the direct-image ring sheaf `f_* 𝒪`;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  and the sheaf-level identity-ring specialization `Chap06/Lemma_6_24_8`;
- best owner abstraction:
  `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((F.sheafPushforwardContinuous RingCat JD JC).obj 𝒪))`;
- primitive data: the continuous functor `F`, the sheaf of rings `𝒪`, and the module sheaves
  `𝒢 : Mod(f_* 𝒪)` and `ℱ : Mod(𝒪)`;
- derived API: the specialized Hom-equivalence `.homEquiv 𝒢 ℱ` and its bijectivity theorem.

Source/core/bridge triage:
- `source-facing`: the tensor-pullback/direct-image correspondence
  `Hom_𝒪(𝒪 ⊗_{f^{-1} f_* 𝒪} f^{-1} 𝒢, ℱ) ≃ Hom_{f_* 𝒪}(𝒢, f_* ℱ)`;
- `core/canonical`: `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((F.sheafPushforwardContinuous RingCat JD JC).obj 𝒪))`;
- `bridge/view`: the source tensor-pullback notation is exactly the pullback functor
  `SheafOfModules.pullback (𝟙 (f_* 𝒪))`, so the adjunction should be reused directly instead of
  being rebuilt through separate unit/counit comparison functors.

Primitive-vs-derived decision:
- the source tensor-pullback functor should not remain as a parallel local owner;
- the canonical owner functors `SheafOfModules.pullback` and `SheafOfModules.pushforward` already
  supply the needed construction and Hom correspondence;
- the refined file should therefore keep only the direct owner specialization and its canonical
  bijectivity companion. -/

private abbrev pushforwardRingSheaf : Sheaf JD RingCat.{u} :=
  (F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪

/- Lemma 18.12.4, owner form: for the identity morphism `f_* 𝒪 ⟶ f_* 𝒪`, the canonical pullback
functor
`SheafOfModules.pullback (𝟙 (f_* 𝒪)) : Mod(f_* 𝒪) ⥤ Mod(𝒪)`
is left adjoint to the direct-image functor
`SheafOfModules.pushforward (𝟙 (f_* 𝒪)) : Mod(𝒪) ⥤ Mod(f_* 𝒪)`. -/
recall SheafOfModules.pullbackPushforwardAdjunction

/- Lemma 18.12.4: the tensor-pullback object
`𝒪 ⊗_{f^{-1} f_* 𝒪} f^{-1} 𝒢`,
which is the canonical pullback object
`(SheafOfModules.pullback (𝟙 (f_* 𝒪))).obj 𝒢`,
represents morphisms into `ℱ` exactly as morphisms from `𝒢` into the direct image `f_* ℱ`. -/
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (pushforwardRingSheaf JC JD F 𝒪))).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback (𝟙 (pushforwardRingSheaf JC JD F 𝒪))).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward (𝟙 (pushforwardRingSheaf JC JD F 𝒪))).obj ℱ))

/- Lemma 18.12.4 companion: the source bijection statement is exactly the canonical bijectivity
theorem for this specialized adjunction equivalence. -/
#check
  ((((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (pushforwardRingSheaf JC JD F 𝒪))).homEquiv 𝒢 ℱ).bijective) :
    Function.Bijective
      ((SheafOfModules.pullbackPushforwardAdjunction
        (𝟙 (pushforwardRingSheaf JC JD F 𝒪))).homEquiv 𝒢 ℱ))

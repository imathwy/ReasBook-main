import Mathlib
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory
open Functor.OplaxMonoidal

noncomputable section

universe u

section

variable {C : Type u} [SmallCategory C]
variable {D : Type u} [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable {F : D ⥤ C}
variable [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪C : Sheaf JC CommRingCat.{u}} {𝒪D : Sheaf JD CommRingCat.{u}}
local notation "ModD" => ringedSiteModuleCategory JD 𝒪D
local notation "ModC" => ringedSiteModuleCategory JC 𝒪C
variable
  (φ :
    ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪D) ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JD JC).obj
        ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪C))
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]
variable [MonoidalCategory (SheafOfModules ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪D))]
variable [MonoidalCategory (SheafOfModules ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪C))]
variable [(SheafOfModules.pushforward φ).LaxMonoidal]

local notation "fStar" => SheafOfModules.pullback φ

local instance : (SheafOfModules.pullback φ).OplaxMonoidal :=
  (SheafOfModules.pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal

/- Domain-style sampling for Lemma 18.26.2:
- primary domain: pullback of sheaves of modules along a morphism of ringed topoi, viewed as a
  monoidal comparison between inverse image and tensor product;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `Functor.OplaxMonoidal.δ`,
  `Adjunction.leftAdjointOplaxMonoidal`;
- best owner abstraction: the canonical adjunction-induced oplax monoidal structure on the
  pullback functor `fStar`, so the source-facing comparison is the owner morphism
  `δ fStar ℱ 𝒢`;
- primitive data: the ringed-site module categories `ModD` and `ModC`, the canonical pullback
  functor `SheafOfModules.pullback φ`, its adjunction with `SheafOfModules.pushforward φ`, and
  the ambient lax monoidal structure on the pushforward;
- derived API: the source-facing comparison is exactly the owner morphism `δ fStar ℱ 𝒢`, and its
  invertibility is exposed directly as an `IsIso` instance on that owner morphism rather than by
  a parallel local theorem.

Source/core/bridge triage:
- `source-facing`: the claim that the pullback-tensor comparison for module sheaves is invertible;
- `core/canonical`: the owner functor `SheafOfModules.pullback φ` together with the canonical
  adjunction-induced oplax tensor map `Functor.OplaxMonoidal.δ`;
- `bridge/view`: downstream use of `asIso (δ fStar ℱ 𝒢)` when the source wording wants the
  comparison written as an isomorphism. -/

variable (ℱ 𝒢 : ModD)

/- Lemma 18.26.2: the canonical pullback-tensor comparison morphism
`f^*(\mathcal F \otimes \mathcal G) \to f^*\mathcal F ⊗ f^*\mathcal G`,
namely `δ fStar ℱ 𝒢`, is an isomorphism. In the canonical owner API this is the direct
`IsIso` instance attached to the comparison morphism itself, with downstream isomorphism data
recovered as `asIso (δ fStar ℱ 𝒢)`. -/
instance : IsIso (δ fStar ℱ 𝒢) := by
  sorry

end

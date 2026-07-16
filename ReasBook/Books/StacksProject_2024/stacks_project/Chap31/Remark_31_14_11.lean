import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_14_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_14_8
import StacksProject_2024.stacks_project.Chap31.Lemma_31_14_2

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced only ambient scheme-module / short-exact owners,
-- not this exact remark. The source-facing rows are therefore recorded directly through the local
-- Chapter 31 owners `zeroIdealSheaf`, `effectiveCartierDivisorAssociatedSheaf`,
-- `immersionConormalSheaf`, `Scheme.Modules.pullback`, and `Scheme.Modules.pushforward`.

variable {X : Scheme.{u}}

local notation "ModX" => X.Modules
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation "EffectiveCartierIdeal" =>
  (fun I : Subobject 𝒪X ↦
    Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))

/-- Helper comparison: the sheafification model of the structure sheaf module on `X` is the
ambient tensor unit in `ModX`. -/
private theorem tensorUnit_eq_sheafification_unit_model
    [MonoidalCategory X.Modules] :
    ((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)) ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj 𝒪X =
      (𝟙_ ModX) := sorry

/-- Helper comparison isomorphism from the structure sheaf module on `X` to the ambient tensor
unit in `ModX`. -/
private noncomputable def unitIsoTensorUnit
    [MonoidalCategory X.Modules] :
    𝒪X ≅ (𝟙_ ModX) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app 𝒪X)).symm ≪≫
    eqToIso tensorUnit_eq_sheafification_unit_model

/-- The morphism `\mathcal L^{\otimes -1} \to \mathcal O_X` induced by a global section
`s : \Gamma(X, \mathcal L)`; this is the left map in the zero-scheme structure-sheaf row. -/
private noncomputable def zeroSchemeInverseSectionMap
    [MonoidalCategory X.Modules] [SymmetricCategory X.Modules] [MonoidalClosed X.Modules]
    (ℒ : ModX) (s : ℒ.sections) :
    ((ihom ℒ).obj 𝒪X) ⟶ 𝒪X :=
  (((ρ_ ((ihom ℒ).obj 𝒪X)).symm) ≪≫
      ((Iso.refl ((ihom ℒ).obj 𝒪X) ⊗ᵢ unitIsoTensorUnit).symm)).hom ≫
    tensorHom (𝟙 ((ihom ℒ).obj 𝒪X)) (ℒ.unitHomEquiv.symm s) ≫
    (β_ ((ihom ℒ).obj 𝒪X) ℒ).hom ≫
    ((ihom.ev ℒ).app 𝒪X)

/-- Remark 31.14.11 (1): if `s` is a regular section of an invertible `\mathcal O_X`-module
`\mathcal L`, then the canonical row
`0 \to \mathcal O_X \to \mathcal L \to i_* (\mathcal L|_{Z(s)}) \to 0`
is short exact, where `i : Z(s) \to X` is the zero-scheme immersion. -/
@[stacks 0C6K]
theorem exists_zeroScheme_restriction_shortExact
    [MonoidalCategory X.Modules] [SymmetricCategory X.Modules] [MonoidalClosed X.Modules]
    (ℒ : ModX) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections)
    (hs : Mono (ℒ.unitHomEquiv.symm s : 𝒪X ⟶ ℒ)) :
    ∃ hcomp :
      (ℒ.unitHomEquiv.symm s : 𝒪X ⟶ ℒ) ≫
          (Scheme.Modules.pullbackPushforwardAdjunction (zeroSchemeι ℒ s)).unit.app
            ℒ =
        0,
      (ShortComplex.mk
          (ℒ.unitHomEquiv.symm s : 𝒪X ⟶ ℒ)
          ((Scheme.Modules.pullbackPushforwardAdjunction (zeroSchemeι ℒ s)).unit.app
            ℒ)
          hcomp).ShortExact := sorry

/-- Remark 31.14.11 (2): if `s` is a regular section of an invertible `\mathcal O_X`-module
`\mathcal L`, then the canonical row
`0 \to \mathcal L^{\otimes -1} \to \mathcal O_X \to i_* \mathcal O_{Z(s)} \to 0`
is short exact, where the inverse sheaf is the internal-Hom model `(ihom ℒ).obj \mathcal O_X`
and `i : Z(s) \to X` is the zero-scheme immersion. -/
@[stacks 0C6K]
theorem exists_zeroScheme_structureSheaf_shortExact
    [MonoidalCategory X.Modules] [SymmetricCategory X.Modules] [MonoidalClosed X.Modules]
    (ℒ : ModX) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections)
    (hs : Mono (ℒ.unitHomEquiv.symm s : 𝒪X ⟶ ℒ)) :
    ∃ hcomp :
      zeroSchemeInverseSectionMap ℒ s ≫
          SheafOfModules.unitToPushforwardObjUnit
            (zeroSchemeι ℒ s).toRingCatSheafHom =
        0,
      (ShortComplex.mk
          (zeroSchemeInverseSectionMap ℒ s)
          (SheafOfModules.unitToPushforwardObjUnit
            (zeroSchemeι ℒ s).toRingCatSheafHom)
          hcomp).ShortExact := sorry

/-- Remark 31.14.11 (3): for an effective Cartier divisor `D \subset X`, the canonical section
`1_D` of `\mathcal O_X(D)` and Lemma 31.14.2 identify the quotient term in the short exact row
`0 \to \mathcal O_X \to \mathcal O_X(D) \to i_* (\mathcal N_{D/X}) \to 0`
with the pushforward of the normal sheaf along `i : D \to X`. -/
@[stacks 0C6K]
theorem exists_effectiveCartierDivisor_normalSheaf_shortExact
    [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
    [SymmetricCategory (SheafOfModules X.ringCatSheaf)]
    [MonoidalClosed (SheafOfModules X.ringCatSheaf)]
    [MonoidalCategory X.Modules]
    [SymmetricCategory X.Modules]
    [MonoidalClosed X.Modules]
    (D : X.IdealSheafData)
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) (Type u)]
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) CommRingCat.{u}]
    [(Opens.grothendieckTopology ↥D.subscheme).HasSheafCompose
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology ↥D.subscheme).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify (Opens.grothendieckTopology ↥D.subscheme) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology ↥D.subscheme).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [Limits.HasBinaryCoproducts
      (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥D.subscheme) CommRingCat.{u})]
    [MonoidalCategory D.subscheme.Modules]
    [MonoidalClosed D.subscheme.Modules]
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject D.subschemeι))] :
    ∃ e :
      ((Scheme.Modules.pullback D.subschemeι).obj
          (effectiveCartierDivisorAssociatedSheaf
            (closedImmersionIdealSubobject D.subschemeι))) ≅
        (ihom (immersionConormalSheaf D.subschemeι)).obj
          (SheafOfModules.unit D.subscheme.ringCatSheaf : D.subscheme.Modules),
      ∃ hcomp :
        ((effectiveCartierDivisorAssociatedSheaf
              (closedImmersionIdealSubobject D.subschemeι)).unitHomEquiv.symm
            (effectiveCartierDivisorCanonicalSection
              (closedImmersionIdealSubobject D.subschemeι)) : 𝒪X ⟶
            effectiveCartierDivisorAssociatedSheaf
              (closedImmersionIdealSubobject D.subschemeι)) ≫
            ((Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app
              (effectiveCartierDivisorAssociatedSheaf
                (closedImmersionIdealSubobject D.subschemeι)) ≫
              (Scheme.Modules.pushforward D.subschemeι).map e.hom) =
          0,
        (ShortComplex.mk
            ((effectiveCartierDivisorAssociatedSheaf
                  (closedImmersionIdealSubobject D.subschemeι)).unitHomEquiv.symm
                (effectiveCartierDivisorCanonicalSection
                  (closedImmersionIdealSubobject D.subschemeι)) : 𝒪X ⟶
                effectiveCartierDivisorAssociatedSheaf
                  (closedImmersionIdealSubobject D.subschemeι))
            (((Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app
                (effectiveCartierDivisorAssociatedSheaf
                  (closedImmersionIdealSubobject D.subschemeι))) ≫
              (Scheme.Modules.pushforward D.subschemeι).map e.hom)
            hcomp).ShortExact := sorry

/-- Remark 31.14.11 (4): for an effective Cartier divisor `D \subset X`, the ideal sheaf
`\mathcal O_X(-D)` and the quotient map to the structure sheaf of `D` fit into the canonical row
`0 \to \mathcal O_X(-D) \to \mathcal O_X \to i_* \mathcal O_D \to 0`,
where `i : D \to X` is the closed immersion. -/
@[stacks 0C6K]
theorem exists_effectiveCartierDivisor_structureSheaf_shortExact
    [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
    [SymmetricCategory (SheafOfModules X.ringCatSheaf)]
    [MonoidalClosed (SheafOfModules X.ringCatSheaf)]
    (D : X.IdealSheafData)
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject D.subschemeι))] :
    ∃ hcomp :
      (closedImmersionIdealSubobject D.subschemeι).arrow ≫
          SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom =
        0,
      (ShortComplex.mk
          (closedImmersionIdealSubobject D.subschemeι).arrow
          (SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)
          hcomp).ShortExact := sorry

end AlgebraicGeometry.Scheme

import Mathlib
import stacks_proof.stacks_project.Chap07.Lemma_7_21_2
import stacks_proof.stacks_project.Chap18.Lemma_18_33_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation RingedSite.Hom

noncomputable section

universe u

namespace RingedSite.Hom

section

variable {CX : Type u} [Category.{u} CX] {CX' : Type u} [Category.{u} CX']
variable {CY : Type u} [Category.{u} CY] {CY' : Type u} [Category.{u} CY']
variable {JX : GrothendieckTopology CX} {JX' : GrothendieckTopology CX'}
variable {JY : GrothendieckTopology CY} {JY' : GrothendieckTopology CY'}
variable [JX.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JX'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JY.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JY'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JX CommRingCat.{u}]
variable [HasWeakSheafify JX AddCommGrpCat.{u}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JX' CommRingCat.{u}]
variable [HasWeakSheafify JX' AddCommGrpCat.{u}]
variable [JX'.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪X : Sheaf JX CommRingCat.{u}} {𝒪X' : Sheaf JX' CommRingCat.{u}}
variable {𝒪Y : Sheaf JY CommRingCat.{u}} {𝒪Y' : Sheaf JY' CommRingCat.{u}}

variable
  (f :
    RingedSite.ofCommRingSheaf JX' 𝒪X' ⟶ RingedSite.ofCommRingSheaf JX 𝒪X)
  (g :
    RingedSite.ofCommRingSheaf JY' 𝒪Y' ⟶ RingedSite.ofCommRingSheaf JY 𝒪Y)
  (h :
    RingedSite.ofCommRingSheaf JX 𝒪X ⟶ RingedSite.ofCommRingSheaf JY 𝒪Y)
  (h' :
    RingedSite.ofCommRingSheaf JX' 𝒪X' ⟶ RingedSite.ofCommRingSheaf JY' 𝒪Y')

scoped[RingedSite.Hom] notation:max f:max "^*" =>
  SheafOfModules.pullback (RingedSite.Hom.structureSheafMap f)

/-- Helper for Lemma 18.33.11: local owner for the inverse-image structure-sheaf map `φ^♯`,
again kept file-local to avoid importing the broken Chapter 18 bridge module. -/
private abbrev inverseImageStructureSheafMap
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify JC CommRingCat.{u}]
    {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
    (φ : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪')
    [Functor.IsContinuous φ.base JD JC] :
    ((φ.base.sheafPullback CommRingCat JD JC).obj 𝒪') ⟶ 𝒪 :=
  ((φ.base.sheafAdjunctionContinuous CommRingCat JD JC).homEquiv _ _).symm
    (Functor.preimage (sheafCompose JD (forget₂ CommRingCat RingCat))
      (show (sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
          (sheafCompose JD (forget₂ CommRingCat RingCat)).obj
            ((φ.base.sheafPushforwardContinuous CommRingCat JD JC).obj 𝒪) from
        φ.structureSheafMap))

scoped[RingedSite.Hom] notation:max f:max "^♯" =>
  inverseImageStructureSheafMap f

/-- Helper for Lemma 18.33.11: local owner for the sheaf of relative differentials, kept here to
avoid importing the broader Chapter 18 notation wrapper file. -/
private abbrev relativeDifferentials
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify JC AddCommGrpCat.{u}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify JC CommRingCat.{u}]
    {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
    (φ : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪')
    [Functor.IsContinuous φ.base JD JC] :
    ringedSiteModuleCategory JC 𝒪 :=
  SheafOfModules.RingedSite.relativeDifferentials (φ^♯)

/-- Helper for Lemma 18.33.11: local owner for the universal derivation `d[f]`, again avoiding
the broader notation-wrapper import chain. -/
private abbrev relativeDifferential
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify JC AddCommGrpCat.{u}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify JC CommRingCat.{u}]
    {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
    (φ : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪')
    [Functor.IsContinuous φ.base JD JC] :
    Der[φ^♯ ; relativeDifferentials φ] :=
  SheafOfModules.RingedSite.relativeDifferential (φ^♯)

scoped[RingedSite.Hom] notation3:max "Ω[" f "]" =>
  relativeDifferentials f

scoped[RingedSite.Hom] notation3:max "d[" f "]" =>
  relativeDifferential f

local instance hom_base_isContinuous {A B : RingedSite.{u, u}} (φ : A ⟶ B) :
    Functor.IsContinuous φ.base B.siteTopology A.siteTopology :=
  φ.isMorphismOfSites.toIsContinuous

local instance f_base_isContinuous : Functor.IsContinuous f.base JX JX' :=
  f.isMorphismOfSites.toIsContinuous

local instance g_base_isContinuous : Functor.IsContinuous g.base JY JY' :=
  g.isMorphismOfSites.toIsContinuous

local instance h_base_isContinuous : Functor.IsContinuous h.base JY JX :=
  h.isMorphismOfSites.toIsContinuous

local instance h'_base_isContinuous : Functor.IsContinuous h'.base JY' JX' :=
  h'.isMorphismOfSites.toIsContinuous

local instance homComm_base_isContinuous
    (φ : RingedSite.ofCommRingSheaf JX 𝒪X ⟶ RingedSite.ofCommRingSheaf JY 𝒪Y) :
    Functor.IsContinuous φ.base JY JX :=
  φ.isMorphismOfSites.toIsContinuous

local instance h_comp_f_base_isContinuous :
    Functor.IsContinuous (h.base ⋙ f.base) JY JX' := by
  simpa using (show Functor.IsContinuous (RingedSite.Hom.base (f ≫ h)) JY JX' from
    (f ≫ h).isMorphismOfSites.toIsContinuous)

/- Internal bridge for the inverse-image structure-sheaf map `h^\sharp : h^{-1}\mathcal O_Y ⟶
\mathcal O_X`. The public owner layer in this file remains `Ω[h]` and `d[h]`. -/
private noncomputable abbrev hSharp
    (φ : RingedSite.ofCommRingSheaf JX 𝒪X ⟶ RingedSite.ofCommRingSheaf JY 𝒪Y) :
    ((φ.base.sheafPullback CommRingCat JY JX).obj 𝒪Y) ⟶ 𝒪X :=
  inverseImageStructureSheafMap φ

private abbrev pushedForwardDifferentialsSection
    (U : CXᵒᵖ) :=
  ((SheafOfModules.pushforward f.structureSheafMap).obj Ω[h']).val.obj U

private abbrev baseObj (U : CXᵒᵖ) :=
  let fOp := f.base.op
  fOp.obj U

private abbrev fSharpApp (U : CXᵒᵖ) :=
  let fSharp := f.structureSheafMap.hom
  fSharp.app U

private abbrev hSharpApp (U : CXᵒᵖ) :=
  (hSharp h).hom.app U

private instance pushedForwardDifferentialsSection_sourceModule
    (U : CXᵒᵖ) :
    Module (((f.base.sheafPushforwardContinuous RingCat JX JX').obj
        (RingedSite.ofCommRingSheaf JX' 𝒪X').structureSheaf).obj.obj U)
      ↑(Ω[h'].val.obj (baseObj f U)) := by
  change Module
      (((RingedSite.ofCommRingSheaf JX' 𝒪X').structureSheaf).obj.obj (baseObj f U))
      ↑(Ω[h'].val.obj (baseObj f U))
  infer_instance

/- Domain-style sampling for Lemma 18.33.11:
- primary domain: base change for relative differentials in a commutative square of morphisms of
  ringed topoi presented by sites;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `RingedSite.Hom.(^*)`,
  `RingedSite.Hom.Ω[_]`,
  `RingedSite.Hom.d[_]`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the bundled square of morphisms
  `f : X' ⟶ X`, `g : Y' ⟶ Y`, `h : X ⟶ Y`, `h' : X' ⟶ Y'` with
  `sq : CommSq f h' h g`;
- primitive data: the four bundled morphisms and the canonical commutative-square witness `sq`;
- derived API: the canonical comparison map `c_f : fStar.obj Ω[h] ⟶ Ω[h']` and its
  characterization on
  universal differentials of local sections.

Source/core/bridge triage:
- `source-facing`: the base-change morphism `c_f : fStar.obj Ω[h] ⟶ Ω[h']`;
- `core/canonical`: the owner surface `Ω[h]`, `d[h]`, and the pullback-pushforward adjunction for
  `f.structureSheafMap`;
- `bridge/view`: the adjoint map `Ω[h] ⟶ f_* Ω[h']`, whose component on a section `t` sends
  `d[h](t)` to `d[h'](f^\sharp t)`.

This file should therefore stay on the bundled `RingedSite.Hom` surface. The generic auxiliary
derivation formerly exposed as primitive data is removed from the public API.
-/

/-- Helper for Lemma 18.33.11: the commutative square identifies the underlying site functors of
the two composites. -/
private theorem pullbackDifferentialsComparison_base_eq
    (sq : f ≫ h = h' ≫ g) :
    h.base ⋙ f.base = g.base ⋙ h'.base := by
  -- Taking the `base` field of the equality of bundled morphisms gives the required functor
  -- identity.
  simpa using congrArg RingedSite.Hom.base sq

/-- Helper for Lemma 18.33.11: in pushforward form, the commutative square identifies the two
structure-sheaf composites. -/
private theorem pullbackDifferentialsComparison_structureSheafMap_eq
    (sq : f ≫ h = h' ≫ g) :
    sq ▸ (f ≫ h).structureSheafMap = (h' ≫ g).structureSheafMap := by
  -- Transport the composite structure map along the equality of bundled morphisms, then the two
  -- sides are definitionally identical.
  cases sq
  rfl

-- Route correction: the previous proof surface compared maps after pulling back only along
-- `f.base`, which hides the source proof's common composite-pullback object. The next pass should
-- compare the two composites on that common source and then use adjunction injectivity there.
/-- Helper for Lemma 18.33.11: under the composite-base adjunction, the transported inverse-image
composite is exactly the pushforward-form composite structure-sheaf map. -/
private theorem ofNatIsoRight_homEquiv_apply
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
    {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    ((adj.ofNatIsoRight iso).homEquiv X Y) f =
      adj.homEquiv X Y f ≫ iso.hom.app Y := by
  -- Expanding `ofNatIsoRight` shows that its Hom-equivalence is the original transpose followed
  -- by the right-side comparison isomorphism.
  simp [Adjunction.homEquiv, Adjunction.ofNatIsoRight, Category.assoc]

/-- Helper for Lemma 18.33.11: transposing the inverse-image structure-sheaf map recovers the
pushforward-form structure-sheaf map. -/
private theorem inverseImageStructureSheafMap_homEquiv
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify JC CommRingCat.{u}]
    {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}
    (φ : RingedSite.ofCommRingSheaf JC 𝒪 ⟶ RingedSite.ofCommRingSheaf JD 𝒪')
    [Functor.IsContinuous φ.base JD JC] :
    let adj := φ.base.sheafAdjunctionContinuous CommRingCat JD JC
    adj.homEquiv _ _ (φ^♯) =
      Functor.preimage (sheafCompose JD (forget₂ CommRingCat RingCat))
        (show (sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
            (sheafCompose JD (forget₂ CommRingCat RingCat)).obj
              ((φ.base.sheafPushforwardContinuous CommRingCat JD JC).obj 𝒪) from
          φ.structureSheafMap) := by
  -- The inverse-image map `φ^♯` is defined as the transpose of the displayed structure-sheaf map.
  dsimp [inverseImageStructureSheafMap]
  exact Equiv.apply_symm_apply _ _

/-- Helper for Lemma 18.33.11: under the composite-base adjunction, the transported inverse-image
composite is exactly the pushforward-form composite structure-sheaf map. -/
private theorem sheafPullbackComp_inv_homEquiv_ofNatIsoRight
    {C₀ : Type u} [Category.{u} C₀] {C₁ : Type u} [Category.{u} C₁] {C₂ : Type u}
    [Category.{u} C₂]
    {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    [J₀.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J₁.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J₂.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J₀ CommRingCat.{u}]
    [HasWeakSheafify J₁ CommRingCat.{u}]
    {𝒪₀ : Sheaf J₀ CommRingCat.{u}} {𝒪₁ : Sheaf J₁ CommRingCat.{u}}
    {𝒪₂ : Sheaf J₂ CommRingCat.{u}}
    (p : RingedSite.ofCommRingSheaf J₀ 𝒪₀ ⟶ RingedSite.ofCommRingSheaf J₁ 𝒪₁)
    (q : RingedSite.ofCommRingSheaf J₁ 𝒪₁ ⟶ RingedSite.ofCommRingSheaf J₂ 𝒪₂)
    (m : ((p.base.sheafPullback CommRingCat J₁ J₀).obj
        ((q.base.sheafPullback CommRingCat J₂ J₁).obj 𝒪₂)) ⟶ 𝒪₀) :
    (((q.base ⋙ p.base).sheafAdjunctionContinuous CommRingCat J₂ J₀).homEquiv _ _)
      (((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := J₂) (K := J₁)
          (L := J₀) (u := q.base) (v := p.base) (euv := Iso.refl _)).inv.app 𝒪₂) ≫ m) =
      ((((Adjunction.comp
          (q.base.sheafAdjunctionContinuous CommRingCat J₂ J₁)
          (p.base.sheafAdjunctionContinuous CommRingCat J₁ J₀)).ofNatIsoRight
            (CategoryTheory.Functor.sheafPushforwardContinuousComp' (Iso.refl _)
              CommRingCat J₂ J₁ J₀)).homEquiv _ _) m := by
  -- `sheafPullbackComp'` is the canonical `leftAdjointUniq` isomorphism, so its inverse
  -- component is characterized by agreement of the two Hom-equivalences.
  simp [CategoryTheory.Functor.sheafPullbackComp']

/-- Helper for Lemma 18.33.11: rewriting the `sheafPullbackComp'` transpose on the raw composite
adjunction surface exposes the pushforward-composition comparison explicitly. -/
private theorem sheafPullbackComp_inv_homEquiv
    {C₀ : Type u} [Category.{u} C₀] {C₁ : Type u} [Category.{u} C₁] {C₂ : Type u}
    [Category.{u} C₂]
    {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    [J₀.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J₁.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J₂.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J₀ CommRingCat.{u}]
    [HasWeakSheafify J₁ CommRingCat.{u}]
    {𝒪₀ : Sheaf J₀ CommRingCat.{u}} {𝒪₁ : Sheaf J₁ CommRingCat.{u}}
    {𝒪₂ : Sheaf J₂ CommRingCat.{u}}
    (p : RingedSite.ofCommRingSheaf J₀ 𝒪₀ ⟶ RingedSite.ofCommRingSheaf J₁ 𝒪₁)
    (q : RingedSite.ofCommRingSheaf J₁ 𝒪₁ ⟶ RingedSite.ofCommRingSheaf J₂ 𝒪₂)
    (m : ((p.base.sheafPullback CommRingCat J₁ J₀).obj
        ((q.base.sheafPullback CommRingCat J₂ J₁).obj 𝒪₂)) ⟶ 𝒪₀) :
    (((q.base ⋙ p.base).sheafAdjunctionContinuous CommRingCat J₂ J₀).homEquiv _ _)
      (((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := J₂) (K := J₁)
          (L := J₀) (u := q.base) (v := p.base) (euv := Iso.refl _)).inv.app 𝒪₂) ≫ m) =
      (((Adjunction.comp
          (q.base.sheafAdjunctionContinuous CommRingCat J₂ J₁)
          (p.base.sheafAdjunctionContinuous CommRingCat J₁ J₀)).homEquiv _ _) m) ≫
        (CategoryTheory.Functor.sheafPushforwardContinuousComp' (Iso.refl _)
          CommRingCat J₂ J₁ J₀).hom.app 𝒪₀ := by
  -- Rewrite the previous transpose through the right natural isomorphism on the pushforward side.
  rw [sheafPullbackComp_inv_homEquiv_ofNatIsoRight]
  simpa using
    (ofNatIsoRight_homEquiv_apply
      (Adjunction.comp
        (q.base.sheafAdjunctionContinuous CommRingCat J₂ J₁)
        (p.base.sheafAdjunctionContinuous CommRingCat J₁ J₀))
      (CategoryTheory.Functor.sheafPushforwardContinuousComp' (Iso.refl _)
        CommRingCat J₂ J₁ J₀)
      m)

/-- Helper for Lemma 18.33.11: under the composite-base adjunction, the transported inverse-image
composite is exactly the pushforward-form composite structure-sheaf map. -/
private theorem inverseImageStructureSheafMap_comp_homEquiv
    {C₀ : Type u} [Category.{u} C₀] {C₁ : Type u} [Category.{u} C₁] {C₂ : Type u}
    [Category.{u} C₂]
    {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    [J₀.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J₁.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J₂.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J₀ CommRingCat.{u}]
    [HasWeakSheafify J₁ CommRingCat.{u}]
    {𝒪₀ : Sheaf J₀ CommRingCat.{u}} {𝒪₁ : Sheaf J₁ CommRingCat.{u}}
    {𝒪₂ : Sheaf J₂ CommRingCat.{u}}
    (p : RingedSite.ofCommRingSheaf J₀ 𝒪₀ ⟶ RingedSite.ofCommRingSheaf J₁ 𝒪₁)
    (q : RingedSite.ofCommRingSheaf J₁ 𝒪₁ ⟶ RingedSite.ofCommRingSheaf J₂ 𝒪₂) :
    (((q.base ⋙ p.base).sheafAdjunctionContinuous CommRingCat J₂ J₀).homEquiv _ _)
      (((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := J₂) (K := J₁)
          (L := J₀) (u := q.base) (v := p.base) (euv := Iso.refl _)).inv.app 𝒪₂) ≫
        (p.base.sheafPullback CommRingCat J₁ J₀).map (q^♯) ≫ p^♯) =
      Functor.preimage (sheafCompose J₂ (forget₂ CommRingCat RingCat))
        (show (sheafCompose J₂ (forget₂ CommRingCat RingCat)).obj 𝒪₂ ⟶
            (sheafCompose J₂ (forget₂ CommRingCat RingCat)).obj
              ((q.base.sheafPushforwardContinuous CommRingCat J₂ J₁).obj
                ((p.base.sheafPushforwardContinuous CommRingCat J₁ J₀).obj 𝒪₀)) from
          q.structureSheafMap ≫
            (q.base.sheafPushforwardContinuous RingCat J₂ J₁).map p.structureSheafMap) := by
  -- Normalize the common-source inverse-image composite on the adjunction surface, then rewrite
  -- the two inverse-image maps by their defining transposes.
  rw [sheafPullbackComp_inv_homEquiv]
  simp [Adjunction.comp_homEquiv, inverseImageStructureSheafMap_homEquiv, Category.assoc]

/-- Helper for Lemma 18.33.11: for composable morphisms of commutative ringed sites, the
inverse-image composite on the common pullback source is the inverse-image structure-sheaf map of
the composite morphism. -/
private theorem inverseImageStructureSheafMap_comp_common
    {C₀ : Type u} [Category.{u} C₀] {C₁ : Type u} [Category.{u} C₁] {C₂ : Type u}
    [Category.{u} C₂]
    {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
    [J₀.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J₁.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [J₂.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify J₀ CommRingCat.{u}]
    [HasWeakSheafify J₁ CommRingCat.{u}]
    {𝒪₀ : Sheaf J₀ CommRingCat.{u}} {𝒪₁ : Sheaf J₁ CommRingCat.{u}}
    {𝒪₂ : Sheaf J₂ CommRingCat.{u}}
    (p : RingedSite.ofCommRingSheaf J₀ 𝒪₀ ⟶ RingedSite.ofCommRingSheaf J₁ 𝒪₁)
    (q : RingedSite.ofCommRingSheaf J₁ 𝒪₁ ⟶ RingedSite.ofCommRingSheaf J₂ 𝒪₂) :
    ((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := J₂) (K := J₁)
        (L := J₀) (u := q.base) (v := p.base) (euv := Iso.refl _)).inv.app 𝒪₂) ≫
      (p.base.sheafPullback CommRingCat J₁ J₀).map (q^♯) ≫ p^♯ =
    (p ≫ q)^♯ := by
  -- Compare both morphisms after transposing to the pushforward side of the composite-base
  -- adjunction.
  apply (((q.base ⋙ p.base).sheafAdjunctionContinuous CommRingCat J₂ J₀).homEquiv _ _).injective
  rw [inverseImageStructureSheafMap_comp_homEquiv]
  simpa using inverseImageStructureSheafMap_homEquiv (φ := p ≫ q)

/-- Helper for Lemma 18.33.11: the common-source inverse-image composite for `(f, h)` is the
inverse-image structure-sheaf map of the composite morphism `f ≫ h`. -/
private theorem pullback_inverseImageStructureSheafMap_left_comp :
    ((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JX)
        (L := JX') (u := h.base) (v := f.base) (euv := Iso.refl _)).inv.app 𝒪Y) ≫
      (f.base.sheafPullback CommRingCat JX JX').map (h^♯) ≫ f^♯ =
    (f ≫ h)^♯ := by
  -- Specialize the owner-level composite comparison to `(f, h)`.
  simpa using inverseImageStructureSheafMap_comp_common (p := f) (q := h)

/-- Helper for Lemma 18.33.11: the common-source inverse-image composite for `(h', g)` is the
inverse-image structure-sheaf map of the composite morphism `h' ≫ g`. -/
private theorem pullback_inverseImageStructureSheafMap_right_comp :
    ((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JY')
        (L := JX') (u := g.base) (v := h'.base) (euv := Iso.refl _)).inv.app 𝒪Y) ≫
      (h'.base.sheafPullback CommRingCat JY' JX').map (g^♯) ≫ h'^♯ =
    (h' ≫ g)^♯ := by
  -- Specialize the same owner-level comparison to `(h', g)`.
  simpa using inverseImageStructureSheafMap_comp_common (p := h') (q := g)

/-- Helper for Lemma 18.33.11: after transporting to the common composite-pullback source, the
inverse-image composites attached to the square agree on `X'`. -/
private theorem pullback_inverseImageStructureSheafMap_eq
    (sq : f ≫ h = h' ≫ g) :
    ((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JX)
        (L := JX') (u := h.base) (v := f.base) (euv := Iso.refl _)).inv.app 𝒪Y) ≫
      (f.base.sheafPullback CommRingCat JX JX').map (h^♯) ≫ f^♯ =
      ((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JY')
          (L := JX') (u := g.base) (v := h'.base) (uv := h.base ⋙ f.base)
          (euv := eqToIso (pullbackDifferentialsComparison_base_eq f g h h' sq).symm)).inv.app
        𝒪Y) ≫
        (h'.base.sheafPullback CommRingCat JY' JX').map (g^♯) ≫ h'^♯ := by
  -- Both common-source composites are the inverse-image map of the same composite morphism.
  calc
    ((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JX)
        (L := JX') (u := h.base) (v := f.base) (euv := Iso.refl _)).inv.app 𝒪Y) ≫
        (f.base.sheafPullback CommRingCat JX JX').map (h^♯) ≫ f^♯ =
        (f ≫ h)^♯ := by
          exact pullback_inverseImageStructureSheafMap_left_comp f g h h'
    _ = (h' ≫ g)^♯ := by
      cases sq
      rfl
    _ =
        ((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JY')
            (L := JX') (u := g.base) (v := h'.base) (uv := h.base ⋙ f.base)
            (euv := eqToIso (pullbackDifferentialsComparison_base_eq f g h h' sq).symm)).inv.app
          𝒪Y) ≫
          (h'.base.sheafPullback CommRingCat JY' JX').map (g^♯) ≫ h'^♯ := by
            symm
            simpa [pullbackDifferentialsComparison_base_eq f g h h' sq] using
              pullback_inverseImageStructureSheafMap_right_comp f g h h'

/-- Helper for Lemma 18.33.11: the square transports a base section of `h^{-1}𝒪_Y` over `U` to the
corresponding base section of `h'^{-1}𝒪_{Y'}` over `baseObj f U`. -/
private noncomputable abbrev pullback_inverseImageStructureSheafMap_section
    (sq : f ≫ h = h' ≫ g) {U : CXᵒᵖ}
    (a : ((h.base.sheafPullback CommRingCat JY JX).obj 𝒪Y).obj.obj U) :
    ((h'.base.sheafPullback CommRingCat JY' JX').obj 𝒪Y').obj.obj (baseObj f U) :=
  let U' := baseObj f U
  let η :=
    (((f.base.sheafAdjunctionContinuous CommRingCat JX JX').unit.app
      ((h.base.sheafPullback CommRingCat JY JX).obj 𝒪Y)).hom.app U)
  let commonSourceMap :=
    (((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JX)
        (L := JX') (u := h.base) (v := f.base) (euv := Iso.refl _)).hom.app 𝒪Y).hom.app U')
  let targetMap :=
    ((((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JY')
        (L := JX') (u := g.base) (v := h'.base) (uv := h.base ⋙ f.base)
        (euv := eqToIso (pullbackDifferentialsComparison_base_eq f g h h' sq).symm)).inv.app 𝒪Y) ≫
        (h'.base.sheafPullback CommRingCat JY' JX').map (g^♯)).hom.app U')
  targetMap (commonSourceMap (η a))

/-- Helper for Lemma 18.33.11: evaluating the transported inverse-image equality gives the
sectionwise rewrite needed for the base-vanishing check. -/
private theorem pullback_inverseImageStructureSheafMap_app
    (sq : f ≫ h = h' ≫ g) {U : CXᵒᵖ}
    (a : ((h.base.sheafPullback CommRingCat JY JX).obj 𝒪Y).obj.obj U) :
    fSharpApp f U (hSharpApp h U a) =
      hSharpApp h' (baseObj f U)
        (pullback_inverseImageStructureSheafMap_section f g h h' sq a) := by
  let U' := baseObj f U
  let η :=
    (((f.base.sheafAdjunctionContinuous CommRingCat JX JX').unit.app
      ((h.base.sheafPullback CommRingCat JY JX).obj 𝒪Y)).hom.app U)
  let commonSourceMap :=
    (((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JX)
        (L := JX') (u := h.base) (v := f.base) (euv := Iso.refl _)).hom.app 𝒪Y).hom.app U')
  let b := commonSourceMap (η a)
  -- Evaluate the common-source comparison on the transported base section.
  have hcomp :
      (((((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JX)
          (L := JX') (u := h.base) (v := f.base) (euv := Iso.refl _)).inv.app 𝒪Y) ≫
          (f.base.sheafPullback CommRingCat JX JX').map (h^♯) ≫ f^♯)).hom.app U') b =
        (((((CategoryTheory.Functor.sheafPullbackComp' (A := CommRingCat.{u}) (J := JY) (K := JY')
            (L := JX') (u := g.base) (v := h'.base) (uv := h.base ⋙ f.base)
            (euv := eqToIso (pullbackDifferentialsComparison_base_eq f g h h' sq).symm)).inv.app
            𝒪Y) ≫
            (h'.base.sheafPullback CommRingCat JY' JX').map (g^♯) ≫ h'^♯)).hom.app U') b := by
    exact congrArg (fun k ↦ k.hom.app U' b) (pullback_inverseImageStructureSheafMap_eq f g h h' sq)
  -- Simplify both sides to the sectionwise comparison statement.
  simpa [U', η, commonSourceMap, b, pullback_inverseImageStructureSheafMap_section,
    baseObj, fSharpApp, hSharpApp, hSharp, Category.assoc] using hcomp

/-- Helper for Lemma 18.33.11: after the sectionwise rewrite, the universal derivation vanishes on
the transported base section. -/
private theorem pullbackDifferentialsComparisonDerivationApp_d_map
    (sq : f ≫ h = h' ≫ g) {U : CXᵒᵖ}
    (a : ((h.base.sheafPullback CommRingCat JY JX).obj 𝒪Y).obj.obj U) :
    ((d[h']).app (baseObj f U)).d
        (fSharpApp f U (hSharpApp h U a)) = 0 := by
  -- Rewrite the input as an `h'^\sharp`-image over `baseObj f U`, then apply the defining
  -- vanishing of the universal derivation on base sections.
  rw [pullback_inverseImageStructureSheafMap_app f g h h' sq a]
  simpa using
    ((d[h']).app (baseObj f U)).d_map
      (pullback_inverseImageStructureSheafMap_section f g h h' sq a)

private noncomputable abbrev pullbackDifferentialsComparisonDerivationApp
    (sq : f ≫ h = h' ≫ g) (U : CXᵒᵖ) :
      (pushedForwardDifferentialsSection f h' U).Derivation (hSharpApp h U) :=
  let U' := baseObj f U
  let fSharpU := fSharpApp f U
  let _ : Module (𝒪X.obj.obj U) (Ω[h'].val.obj U') :=
    Module.compHom (Ω[h'].val.obj U') fSharpU.hom
  ModuleCat.Derivation.mk
    (fun t ↦
      show pushedForwardDifferentialsSection f h' U from
        ((d[h']).app U').d (fSharpU t))
    (fun t₁ t₂ ↦ by
      change ((d[h']).app U').d (fSharpU (t₁ + t₂)) =
        ((d[h']).app U').d (fSharpU t₁) + ((d[h']).app U').d (fSharpU t₂)
      rw [show (ConcreteCategory.hom fSharpU) (t₁ + t₂) =
          (ConcreteCategory.hom fSharpU) t₁ + (ConcreteCategory.hom fSharpU) t₂ by
          exact fSharpU.hom.map_add t₁ t₂]
      simpa using ModuleCat.Derivation.d_add ((d[h']).app U') (fSharpU t₁) (fSharpU t₂))
    (fun t₁ t₂ ↦ by
      change ((d[h']).app U').d (fSharpU (t₁ * t₂)) =
        fSharpU t₁ • ((d[h']).app U').d (fSharpU t₂) +
          fSharpU t₂ • ((d[h']).app U').d (fSharpU t₁)
      rw [show (ConcreteCategory.hom fSharpU) (t₁ * t₂) =
          (ConcreteCategory.hom fSharpU) t₁ * (ConcreteCategory.hom fSharpU) t₂ by
          exact fSharpU.hom.map_mul t₁ t₂]
      simpa using ModuleCat.Derivation.d_mul ((d[h']).app U') (fSharpU t₁) (fSharpU t₂))
    (fun a ↦ by
      simpa [U', fSharpU] using
        pullbackDifferentialsComparisonDerivationApp_d_map f g h h' sq a)

private theorem pullbackDifferentialsComparisonDerivationApp_naturality
    (sq : f ≫ h = h' ≫ g) {U V : CXᵒᵖ} (ρ : U ⟶ V) (t : 𝒪X.obj.obj U) :
    (pullbackDifferentialsComparisonDerivationApp f g h h' sq V).d (𝒪X.obj.map ρ t) =
      (((SheafOfModules.pushforward f.structureSheafMap).obj Ω[h']).val.map ρ)
        ((pullbackDifferentialsComparisonDerivationApp f g h h' sq U).d t) := by
  let U' := baseObj f U
  let V' := baseObj f V
  let fSharpU := fSharpApp f U
  let fSharpV := fSharpApp f V
  have hf :
      fSharpV (𝒪X.obj.map ρ t) =
        𝒪X'.obj.map (f.base.op.map ρ) (fSharpU t) := by
    -- Naturality of `f^♯` identifies restriction before and after applying the structure map.
    exact congrArg (fun k ↦ k t) <|
      f.structureSheafMap.hom.naturality ρ
  -- Rewrite the input by naturality of `f^♯`, then use naturality of `d[h']`.
  change ((d[h']).app V').d (fSharpV (𝒪X.obj.map ρ t)) =
    (ConcreteCategory.hom
      (((SheafOfModules.pushforward f.structureSheafMap).obj Ω[h']).val.map ρ))
        ((pullbackDifferentialsComparisonDerivationApp f g h h' sq U).d t)
  rw [hf]
  simpa [U', V'] using (d[h']).d_map (f.base.op.map ρ) (fSharpU t)

private noncomputable def pullbackDifferentialsComparisonDerivation
    (sq : f ≫ h = h' ≫ g) :
    Der[hSharp h ;
      (SheafOfModules.pushforward f.structureSheafMap).obj Ω[h']] :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ pullbackDifferentialsComparisonDerivationApp f g h h' sq U)
    (fun _ _ ρ t ↦
      pullbackDifferentialsComparisonDerivationApp_naturality f g h h' sq ρ t)

private noncomputable abbrev pullbackDifferentialsComparisonAdjoint
    (sq : f ≫ h = h' ≫ g) :
    Ω[h] ⟶ (SheafOfModules.pushforward f.structureSheafMap).obj Ω[h'] :=
  relativeDifferentialDesc (hSharp h)
    (pullbackDifferentialsComparisonDerivation f g h h' sq)

-- Proof sketch: the commutative square `sq : CommSq f h' h g` identifies the composite
-- `f^\sharp ≫ f_* d[h']` as a `Y`-derivation on `𝒪_X`. Apply the universal property of
-- `Ω[h]`, then transpose the resulting map `Ω[h] ⟶ f_* Ω[h']` across
-- `f^* ⊣ f_*`. Uniqueness follows because the sections `d[h](t)` generate `Ω[h]`.
/-- The canonical base-change morphism on relative differentials attached to a commutative square
of morphisms of ringed topoi. -/
noncomputable def pullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    (f^*).obj Ω[h] ⟶ Ω[h'] :=
  ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv _ _).symm
    (pullbackDifferentialsComparisonAdjoint f g h h' sq.w)

/-- The source-facing sectionwise characterization property for the base-change morphism on
relative differentials. -/
def pullbackDifferentialsComparisonProperty
    (τ : (f^*).obj Ω[h] ⟶ Ω[h']) : Prop :=
  ∀ {U : CXᵒᵖ} (t : 𝒪X.obj.obj U),
    let U' := baseObj f U
    let fSharpU := fSharpApp f U
    let adjτ :=
      ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv _ _) τ
    adjτ.val.app U (((d[h]).app U).d t) = ((d[h']).app U').d (fSharpU t)

/-- The canonical comparison morphism is characterized by sending `d[h](t)` to
`d[h'](f^\sharp t)` after passage to the adjoint map `Ω[h] ⟶ f_* Ω[h']`. -/
theorem pullbackDifferentialsComparison_characterizing
    (sq : CommSq f h' h g) :
    pullbackDifferentialsComparisonProperty f h h'
      (pullbackDifferentialsComparison f g h h' sq) := by
  intro U t
  -- Transport the canonical comparison back across the adjunction to recover the descended map.
  have hadj :
      ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv _ _)
          (pullbackDifferentialsComparison f g h h' sq) =
        pullbackDifferentialsComparisonAdjoint f g h h' sq.w := by
    simpa [pullbackDifferentialsComparison] using
      (Equiv.apply_symm_apply
        ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv _ _)
        (pullbackDifferentialsComparisonAdjoint f g h h' sq.w))
  -- The adjoint map is characterized by `relativeDifferentialDesc_fac`.
  have hfac :
      (pullbackDifferentialsComparisonAdjoint f g h h' sq.w).val.app U
          (((d[h]).app U).d t) =
        ((pullbackDifferentialsComparisonDerivation f g h h' sq.w).app U).d t := by
    simpa [pullbackDifferentialsComparisonAdjoint] using
      congrArg (fun D ↦ D.d t)
        (relativeDifferentialDesc_fac (hSharp h)
          (pullbackDifferentialsComparisonDerivation f g h h' sq.w))
  -- Unfold the descended derivation on the generator `d[h](t)`.
  rw [hadj]
  simpa [pullbackDifferentialsComparisonDerivation,
    pullbackDifferentialsComparisonDerivationApp, baseObj, fSharpApp] using hfac

/-- A morphism `f^* Ω[h] ⟶ Ω[h']` is the canonical base-change map once it carries the universal
differentials `d[h](t)` to `d[h'](f^\sharp t)` on local sections after adjunction. -/
theorem pullbackDifferentialsComparison_unique
    (sq : CommSq f h' h g)
    (τ : (f^*).obj Ω[h] ⟶ Ω[h'])
    (hτ : pullbackDifferentialsComparisonProperty f h h' τ) :
    τ = pullbackDifferentialsComparison f g h h' sq := by
  -- Compare both morphisms after transporting them to adjoint maps `Ω[h] ⟶ f_* Ω[h']`.
  apply ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv _ _).injective
  -- The universal property of `Ω[h]` reduces equality to checking the images of `d[h](t)`.
  apply relativeDifferential_postcomp_injective (hSharp h)
  ext U t
  -- The assumed characterization for `τ` and the canonical one for `c_f` agree on generators.
  exact Eq.trans (hτ (U := U) t) <|
    (pullbackDifferentialsComparison_characterizing f g h h' sq (U := U) t).symm

-- Proof sketch: existence is given by the canonical owner morphism above, and uniqueness is
-- `pullbackDifferentialsComparison_unique`.
/-- Lemma 18.33.11: for a commutative square of morphisms of ringed topoi presented by sites,
there exists a unique base-change morphism
`c_f : f^* Ω[h] ⟶ Ω[h']`
whose adjoint sends `d[h](t)` to `d[h'](f^\sharp t)` on every local section `t` of `𝒪_X`. -/
@[stacks 04BR]
theorem existsUnique_pullbackDifferentialsComparison
    (sq : CommSq f h' h g) :
    ∃! τ : (f^*).obj Ω[h] ⟶ Ω[h'],
      pullbackDifferentialsComparisonProperty f h h' τ := by
  refine ⟨pullbackDifferentialsComparison f g h h' sq, ?_, ?_⟩
  · exact pullbackDifferentialsComparison_characterizing f g h h' sq
  · intro τ hτ
    exact pullbackDifferentialsComparison_unique f g h h' sq τ hτ

end

end RingedSite.Hom

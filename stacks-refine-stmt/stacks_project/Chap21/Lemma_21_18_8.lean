import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on a ringed site with
structure sheaf `\mathcal O`. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u}) :=
  DerivedCategory (RingedSiteModules J 𝒪)

/-- The underlying `RingCat`-valued structure map attached to the site-presented morphism of
ringed topoi determined by `φ`. -/
abbrev ringedSiteUnderlyingStructureMap
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    (sheafCompose JC (forget₂ CommRingCat RingCat)).obj 𝒪' ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj 𝒪) :=
  (sheafCompose JC (forget₂ CommRingCat RingCat)).map φ

/-- The inverse-image functor on module sheaves attached to the site-presented morphism of ringed
topoi determined by `φ`. -/
abbrev pullbackFunctor
    (F : C ⥤ D) [Functor.IsContinuous F JC JD]
    {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
    (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪) :
    RingedSiteModules JC 𝒪' ⥤ RingedSiteModules JD 𝒪 :=
  SheafOfModules.pullback (ringedSiteUnderlyingStructureMap F φ)

variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{u}} {𝒪 : Sheaf JD CommRingCat.{u}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} JC JD).obj 𝒪)
variable [Abelian (RingedSiteModules JC 𝒪')]
variable [Abelian (RingedSiteModules JD 𝒪)]

local notation "TargetModules" => RingedSiteModules JC 𝒪'
local notation "SourceModules" => RingedSiteModules JD 𝒪
local notation "TargetDerived" => RingedSiteDerived JC 𝒪'
local notation "SourceDerived" => RingedSiteDerived JD 𝒪

/-- Pullback of a cochain complex along the underlying pullback functor on module sheaves. -/
private abbrev pulledBackComplex
    (K : CochainComplex TargetModules ℤ) :
    CochainComplex SourceModules ℤ :=
  ((pullbackFunctor F φ).mapHomologicalComplex (up ℤ)).obj K

variable
  (targetTensorComplex :
    CochainComplex TargetModules ℤ →
      CochainComplex TargetModules ℤ →
        CochainComplex TargetModules ℤ)
  (sourceTensorComplex :
    CochainComplex SourceModules ℤ →
      CochainComplex SourceModules ℤ →
        CochainComplex SourceModules ℤ)
  (targetComplexToDerived : CochainComplex TargetModules ℤ → TargetDerived)
  (sourceComplexToDerived : CochainComplex SourceModules ℤ → SourceDerived)
  (leftDerivedPullback : TargetDerived ⥤ SourceDerived)
  (derivedTensorTarget :
    TargetDerived ⥤ TargetDerived ⥤ TargetDerived)
  (derivedTensorSource :
    SourceDerived ⥤ SourceDerived ⥤ SourceDerived)

-- Proof sketch: choose K-flat resolutions with flat terms for `K` and `M` as in Lemma `21.17.11`.
-- The top horizontal and bottom horizontal arrows are the counits computing the two derived tensor
-- products on those resolutions, the right vertical arrow is the counit computing derived
-- pullback on `Tot(K ⊗ M)`, the left vertical arrow is the comparison from Lemma `21.18.4`, and
-- the remaining comparison is the ordinary pullback-tensor compatibility on the chosen total
-- tensor complexes. The resolution-level square then commutes by functoriality, and the equality
-- descends to the derived categories.
/-- Lemma 21.18.8: for a site-presented morphism of ringed topoi, the canonical comparison
ladder from `Lf^*(K^\bullet \otimes_{\mathcal O_\mathcal D}^{\mathbf L} M^\bullet)` to
`\mathrm{Tot}(f^*K^\bullet \otimes_{\mathcal O_\mathcal C} f^*M^\bullet)` obtained from derived
tensor counits, the derived pullback counit, the pullback-tensor comparison, and the comparison
of Lemma `21.18.4` is commutative. -/
theorem leftDerivedPullback_tensor_counit_ladder_commutes
    (derivedPullbackTensorComparison :
      ∀ (K M : CochainComplex TargetModules ℤ),
        leftDerivedPullback.obj
            ((derivedTensorTarget.obj (targetComplexToDerived M)).obj
              (targetComplexToDerived K)) ⟶
          ((derivedTensorSource.obj
              (leftDerivedPullback.obj (targetComplexToDerived M))).obj
            (leftDerivedPullback.obj (targetComplexToDerived K))))
    (targetTensorCounit :
      ∀ (K M : CochainComplex TargetModules ℤ),
        ((derivedTensorTarget.obj (targetComplexToDerived M)).obj
          (targetComplexToDerived K)) ⟶
          targetComplexToDerived (targetTensorComplex K M))
    (pullbackCounit :
      ∀ (K : CochainComplex TargetModules ℤ),
        leftDerivedPullback.obj (targetComplexToDerived K) ⟶
          sourceComplexToDerived (pulledBackComplex F φ K))
    (sourceTensorCounit :
      ∀ (K M : CochainComplex SourceModules ℤ),
        ((derivedTensorSource.obj (sourceComplexToDerived M)).obj
          (sourceComplexToDerived K)) ⟶
          sourceComplexToDerived (sourceTensorComplex K M))
    (underivedPullbackTensorComparison :
      ∀ (K M : CochainComplex TargetModules ℤ),
        sourceComplexToDerived
            (pulledBackComplex F φ (targetTensorComplex K M)) ⟶
          sourceComplexToDerived
            (sourceTensorComplex (pulledBackComplex F φ K)
              (pulledBackComplex F φ M)))
    (K M : CochainComplex TargetModules ℤ) :
    leftDerivedPullback.map (targetTensorCounit K M) ≫
        pullbackCounit (targetTensorComplex K M) ≫
        underivedPullbackTensorComparison K M =
      derivedPullbackTensorComparison K M ≫
        ((derivedTensorSource.map (pullbackCounit M)).app
          (leftDerivedPullback.obj (targetComplexToDerived K))) ≫
        ((derivedTensorSource.obj
          (sourceComplexToDerived (pulledBackComplex F φ M))).map
            (pullbackCounit K)) ≫
        sourceTensorCounit (pulledBackComplex F φ K) (pulledBackComplex F φ M) := sorry

end

end SheafOfModules.RingedSite

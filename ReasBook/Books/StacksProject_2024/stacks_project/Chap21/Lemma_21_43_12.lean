import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import StacksProject_2024.stacks_project.Chap21.Definition_21_43_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_43_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

/- Domain-style sampling:
- primary domain: `ObjectProperty` owners on derived categories, their full subcategories, and
  inverse-image transport along a functor;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `CategoryTheory.ObjectProperty.inverseImage`,
  `CategoryTheory.ObjectProperty.ι`,
  `CategoryTheory.ObjectProperty.lift`;
- best owner abstraction:
  `source-facing`: the Section `21.43` owner `isQuasiCoherent` and its full subcategory `QC`;
  `core/canonical`: `ObjectProperty.inverseImage`, `ObjectProperty.lift`, and the canonical
    inclusions of the corresponding full subcategories;
  `bridge/view`: the target-side inverse-image property along `Rε_*` and the owner-level
    landing/unit hypotheses on the restricted pullback `ε^*`;
- primitive data: `RGamma`, `derivedRestrict`, `comparison`, `epsilonPullback`, and
  `rEpsilonPushforward`;
- derived API: the inverse-image full subcategory and the canonical restricted pullback functor.

Source/core/bridge triage:
- `source-facing`: the Section `21.43` quasi-coherent full subcategory `QC(𝒪)`;
- `core/canonical`: the `ObjectProperty` viewpoint together with `ObjectProperty.inverseImage` and
  `ObjectProperty.lift`;
- `bridge/view`: this file records the equivalence after the textbook K-flat comparison input has
  already been translated into the owner-level landing and unit-isomorphism data on `QC`. Because
  the ambient category here is expressed through the sheaf-specialized owner
  `ringedSiteModuleCategory`, the theorem keeps the public surface directly on `QC` and the
  inverse-image owner under `Rε_*`, rather than introducing a second wrapper declaration.
-/

variable {C : Type u} [Category C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

variable [Abelian (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)]
variable [HasDerivedCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪)]

variable
  (RGamma :
    ∀ U : C,
      DerivedCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪) ⥤
        DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
  (derivedRestrict :
    ∀ {U V : C}, (U ⟶ V) →
      DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
        DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

variable {Dτ : Type w} [Category Dτ]
variable
  (epsilonPullback :
    DerivedCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪) ⥤ Dτ)
  (rEpsilonPushforward :
    Dτ ⥤ DerivedCategory (ringedSiteModuleCategory (⊥ : GrothendieckTopology C) 𝒪))

-- Proof sketch: Section `21.27` provides the adjunction `ε^* ⊣ Rε_*` with `Rε_*` fully faithful,
-- so the counit identifies every object on the target side with one coming from `ε^*`. The
-- textbook K-flat comparison hypothesis is used through the resulting unit isomorphisms on
-- `QC(𝒪)`. The landing statement into the inverse-image full subcategory is derived from
-- those unit isomorphisms, and the restricted pullback is then realized by the canonical
-- `ObjectProperty.lift`.
/-- The target-side object property cutting out those `K` for which `Rε_* K` lies in `QC(𝒪)`.
This is the source-facing full-subcategory condition in Lemma `21.43.12`. -/
abbrev rEpsilonPushforwardInverseQC : ObjectProperty Dτ :=
  ObjectProperty.inverseImage
    (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison) rEpsilonPushforward

private abbrev sourceRingSheaf
    (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat) :
    Cᵒᵖ ⥤ CommRingCat :=
  𝒪.1

local notation "SrcQCP" => isQuasiCoherent (sourceRingSheaf 𝒪) RGamma derivedRestrict comparison
local notation "SrcQC" => QC (sourceRingSheaf 𝒪) RGamma derivedRestrict comparison
local notation "TgtQCP" =>
  rEpsilonPushforwardInverseQC 𝒪 RGamma derivedRestrict comparison rEpsilonPushforward
local notation "TgtQC" => ObjectProperty.FullSubcategory TgtQCP

/-- Source-facing membership test for the inverse-image quasi-coherent owner from
Lemma `21.43.12`. -/
theorem mem_rEpsilonPushforwardInverseQC_iff (K : Dτ) :
    TgtQCP K ↔ SrcQCP (rEpsilonPushforward.obj K) := by
  rfl

private abbrev epsilonPullbackToInverseQCFromMem
    (hε_mem : ∀ K : SrcQC, TgtQCP ((ObjectProperty.ι SrcQCP ⋙ epsilonPullback).obj K)) :
    SrcQC ⥤ TgtQC :=
  ObjectProperty.lift
    TgtQCP (ObjectProperty.ι SrcQCP ⋙ epsilonPullback)
    hε_mem

/-- The canonical restriction of `Rε_*` to the full subcategory of target objects whose
pushforward already lies in `QC(𝒪)`. This is the intended quasi-inverse in
Lemma `21.43.12`. -/
abbrev rEpsilonPushforwardOnInverseQC : TgtQC ⥤ SrcQC :=
  ObjectProperty.lift
    SrcQCP (ObjectProperty.ι TgtQCP ⋙ rEpsilonPushforward) fun K ↦ K.property

-- Proof sketch: if the unit `K ⟶ Rε_* ε^* K` is an isomorphism for a quasi-coherent object `K`,
-- then `Rε_* ε^* K` lies again in `QC(𝒪)` because the source-facing quasi-coherent owner is
-- closed under isomorphisms. This is the derived landing statement needed to restrict `ε^*`.
/-- The K-flat comparison consequence used in Lemma `21.43.12`: if the adjunction unit
`K ⟶ Rε_* ε^* K` is an isomorphism for `K ∈ QC(𝒪)`, then `ε^* K` lies in the inverse-image full
subcategory cut out by `Rε_*`. -/
theorem epsilonPullback_obj_mem_rEpsilonPushforwardInverseQC_of_unitIso
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    (K : SrcQC)
    (hK : IsIso (adj.unit.app K.obj)) :
    TgtQCP ((ObjectProperty.ι SrcQCP ⋙ epsilonPullback).obj K) := by
  let e :
      K.obj ≅
        rEpsilonPushforward.obj (epsilonPullback.obj K.obj) :=
    @asIso _ _ _ _ (adj.unit.app K.obj) hK
  exact
    (mem_rEpsilonPushforwardInverseQC_iff
      𝒪 RGamma derivedRestrict comparison rEpsilonPushforward
      ((ObjectProperty.ι SrcQCP ⋙ epsilonPullback).obj K)).2 <|
      (isQuasiCoherent 𝒪.1 RGamma derivedRestrict comparison).prop_of_iso e K.property

/-- The canonical restriction of `ε^*` from `QC(𝒪)` to the full subcategory of objects `K`
with `Rε_* K ∈ QC(𝒪)`, expressed under the K-flat comparison hypothesis from
Lemma `21.43.12`. -/
abbrev epsilonPullbackToInverseQC
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj)) :
    SrcQC ⥤ TgtQC :=
  epsilonPullbackToInverseQCFromMem
    𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward
    (fun K ↦
      epsilonPullback_obj_mem_rEpsilonPushforwardInverseQC_of_unitIso
        𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj K
        (hkFlatComparison K))

private noncomputable abbrev epsilonPullbackToInverseQCObjIso
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj))
    (K : SrcQC) :
    K.obj ≅ rEpsilonPushforward.obj (epsilonPullback.obj K.obj) :=
  @asIso _ _ _ _ (adj.unit.app K.obj) (hkFlatComparison K)

/-- Helper for Lemma `21.43.12`: the restricted unit components are natural after restricting
`ε^*` and `Rε_*` to the quasi-coherent full subcategories. -/
private theorem epsilonPullbackToInverseQCObjIso_naturality
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj))
    {X Y : SrcQC} (f : X ⟶ Y) :
    (epsilonPullbackToInverseQC
        𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
        hkFlatComparison ⋙
      rEpsilonPushforwardOnInverseQC
        𝒪 RGamma derivedRestrict comparison rEpsilonPushforward).map f ≫
        (ObjectProperty.isoMk SrcQCP
          (epsilonPullbackToInverseQCObjIso
            𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
            hkFlatComparison Y).symm).hom =
      (ObjectProperty.isoMk SrcQCP
        (epsilonPullbackToInverseQCObjIso
          𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
          hkFlatComparison X).symm).hom ≫
        f := by
  apply ObjectProperty.hom_ext
  let eX :=
    epsilonPullbackToInverseQCObjIso
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison X
  let eY :=
    epsilonPullbackToInverseQCObjIso
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison Y
  change
    rEpsilonPushforward.map (epsilonPullback.map f.hom) ≫ eY.inv =
      eX.inv ≫ f.hom
  rw [eY.comp_inv_eq]
  calc
    rEpsilonPushforward.map (epsilonPullback.map f.hom) =
        eX.inv ≫ (eX.hom ≫ rEpsilonPushforward.map (epsilonPullback.map f.hom)) := by
      simp
    _ = (eX.inv ≫ f.hom) ≫ eY.hom := by
      simpa [eX, eY, Category.assoc] using
        congrArg (fun g ↦ eX.inv ≫ g) (adj.unit.naturality f.hom).symm

/-- Under the K-flat comparison hypothesis, the restricted pullback `ε^*` followed by the
restricted pushforward `Rε_*` is naturally isomorphic to the identity on `QC(𝒪)`. -/
noncomputable def epsilonPullbackToInverseQCCompREpsilonPushforwardOnInverseQCIso
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj)) :
    epsilonPullbackToInverseQC
        𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
        hkFlatComparison ⋙
      rEpsilonPushforwardOnInverseQC
        𝒪 RGamma derivedRestrict comparison rEpsilonPushforward ≅
        𝟭 SrcQC :=
  NatIso.ofComponents
    (fun K ↦
      ObjectProperty.isoMk SrcQCP
        (epsilonPullbackToInverseQCObjIso
          𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
          hkFlatComparison K).symm)
    (fun f ↦
      epsilonPullbackToInverseQCObjIso_naturality
        𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
        hkFlatComparison f)

/-- If `Rε_*` is fully faithful, then the restricted pushforward followed by the canonical
restricted pullback is naturally isomorphic to the identity on the inverse-image quasi-coherent
full subcategory. -/
private noncomputable def rEpsilonPushforwardOnInverseQCCompEpsilonPullbackToInverseQCIsoSymm
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj)) :
    rEpsilonPushforwardOnInverseQC
          𝒪 RGamma derivedRestrict comparison rEpsilonPushforward ⋙
        epsilonPullbackToInverseQC
          𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
          hkFlatComparison ≅
      𝟭 TgtQC :=
  NatIso.ofComponents
    (fun K ↦ by
      letI : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
      exact ObjectProperty.isoMk TgtQCP ((asIso adj.counit).app K.obj))
    (fun {X Y} f ↦ by
      apply ObjectProperty.hom_ext
      simpa [epsilonPullbackToInverseQC, epsilonPullbackToInverseQCFromMem,
        rEpsilonPushforwardOnInverseQC, Category.assoc] using
        adj.counit.naturality f.hom)

/-- If `Rε_*` is fully faithful, then the restricted pushforward followed by the canonical
restricted pullback is naturally isomorphic to the identity on the inverse-image quasi-coherent
full subcategory. -/
noncomputable def rEpsilonPushforwardOnInverseQCCompEpsilonPullbackToInverseQCIso
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj)) :
    𝟭 TgtQC ≅
      rEpsilonPushforwardOnInverseQC
          𝒪 RGamma derivedRestrict comparison rEpsilonPushforward ⋙
        epsilonPullbackToInverseQC
          𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
          hkFlatComparison :=
  (rEpsilonPushforwardOnInverseQCCompEpsilonPullbackToInverseQCIsoSymm
    𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
    hkFlatComparison).symm

/-- Lemma 21.43.12, source-facing quasi-inverse form: let
`ε : (𝒞_τ, 𝒪_τ) ⟶ (𝒞_{τ'}, 𝒪_{τ'})` be the topology-change morphism of Section `21.27`, and
assume `τ'` is the chaotic topology on `𝒞`. Formalizing the textbook K-flat comparison by the
resulting unit isomorphisms `K ⟶ Rε_* ε^* K` on `QC(𝒪)`, the restricted functor `Rε_*` on the
full subcategory of objects `K` with `Rε_* K ∈ QC(𝒪)` is an equivalence, with quasi-inverse the
canonical restriction of `ε^*`. -/
@[stacks 0GZS]
theorem rEpsilonPushforwardOnInverseQC_isEquivalence_of_kFlatComparison
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj)) :
    Functor.IsEquivalence
      (rEpsilonPushforwardOnInverseQC
        𝒪 RGamma derivedRestrict comparison rEpsilonPushforward) :=
  Functor.IsEquivalence.mk'
    (epsilonPullbackToInverseQC
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison)
    (rEpsilonPushforwardOnInverseQCCompEpsilonPullbackToInverseQCIso
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison)
    (epsilonPullbackToInverseQCCompREpsilonPushforwardOnInverseQCIso
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison)

/-- Companion instance for Lemma `21.43.12`: under the same K-flat comparison hypothesis, the
restricted functor `Rε_*` is inferred as an equivalence. -/
instance instREpsilonPushforwardOnInverseQCIsEquivalenceOfKFlatComparison
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj)) :
    Functor.IsEquivalence
      (rEpsilonPushforwardOnInverseQC
        𝒪 RGamma derivedRestrict comparison rEpsilonPushforward) :=
  rEpsilonPushforwardOnInverseQC_isEquivalence_of_kFlatComparison
    𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj hkFlatComparison

/-- Companion to Lemma `21.43.12`: under the same K-flat comparison hypothesis, the canonical
restriction of `ε^*` from `QC(𝒪)` to the inverse-image full subcategory cut out by `Rε_*`
is an equivalence. -/
theorem epsilonPullbackToInverseQC_isEquivalence_of_kFlatComparison
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj)) :
    Functor.IsEquivalence (epsilonPullbackToInverseQC
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison) :=
  Functor.IsEquivalence.mk'
    (rEpsilonPushforwardOnInverseQC
      𝒪 RGamma derivedRestrict comparison rEpsilonPushforward)
    (epsilonPullbackToInverseQCCompREpsilonPushforwardOnInverseQCIso
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison).symm
    (rEpsilonPushforwardOnInverseQCCompEpsilonPullbackToInverseQCIso
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison).symm

/-- Companion instance to Lemma `21.43.12`: under the same K-flat comparison hypothesis, the
restricted functor `ε^*` is inferred as an equivalence. -/
instance instEpsilonPullbackToInverseQCIsEquivalenceOfKFlatComparison
    (adj : epsilonPullback ⊣ rEpsilonPushforward)
    [rEpsilonPushforward.Full] [rEpsilonPushforward.Faithful]
    (hkFlatComparison : ∀ K : SrcQC, IsIso (adj.unit.app K.obj)) :
    Functor.IsEquivalence (epsilonPullbackToInverseQC
      𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj
      hkFlatComparison) :=
  epsilonPullbackToInverseQC_isEquivalence_of_kFlatComparison
    𝒪 RGamma derivedRestrict comparison epsilonPullback rEpsilonPushforward adj hkFlatComparison

end CategoryTheory.ModulesOnCategory

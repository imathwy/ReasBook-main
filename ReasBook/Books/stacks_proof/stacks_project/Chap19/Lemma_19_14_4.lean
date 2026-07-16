import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import stacks_proof.stacks_project.Chap13.Lemma_13_31_7
import stacks_proof.stacks_project.Chap13.Lemma_13_30_1
import stacks_proof.stacks_project.Chap19.AdditiveFunctorTotalRightDerived
import stacks_proof.stacks_project.Chap19.Theorem_19_12_6
import stacks_proof.stacks_project.Chap19.Theorem_19_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-
Domain-style sampling:
* primary domain: derived Gabriel-Popescu theory for Grothendieck abelian categories.
* sampled owner declarations:
  `tensorObj_exact`,
  `mapHomologicalComplexQ_hasRightDerivedFunctor`,
  `Functor.mapDerivedCategory`,
  `additiveFunctorTotalRightDerived`,
  `Adjunction.fullyFaithfulROfIsIsoCounit`.
* best owner abstraction: the canonical functor pair on derived categories built from
  `tensorObj (separator C)` and the chapter-level owner
  `additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))`.
* source/core/bridge triage:
  - `source-facing`: the existence of the derived Gabriel-Popescu adjunction and the identity
    comparison `RG ⋙ F ≅ 𝟭`;
  - `core/canonical`: `Adjunction`, `Functor.mapDerivedCategory`, and
    `additiveFunctorTotalRightDerived`;
  - `bridge/view`: the fully faithful consequence obtained from
    `Adjunction.fullyFaithfulROfIsIsoCounit`.
* primitive data: the separator `separator C` and the underived Gabriel-Popescu functors.
* derived API: exactness of `tensorObj (separator C)`, the induced derived functor
  `Functor.mapDerivedCategory`, the canonical right derived functor
  `additiveFunctorTotalRightDerived`, and the adjunction consequences.
-/

local notation "RMod" => ModuleCat ((End (separator C))ᵐᵒᵖ)
/-- The standard derived-category model used for `C` in this item file. -/
local instance : HasDerivedCategory C :=
  HasDerivedCategory.standard C

/-- The standard derived-category model used for the Gabriel-Popescu module category. -/
local instance : HasDerivedCategory RMod :=
  HasDerivedCategory.standard RMod

/-- The Gabriel-Popescu left adjoint `tensorObj (separator C)` preserves finite limits. -/
local instance tensorObj_separator_preservesFiniteLimits :
    PreservesFiniteLimits (tensorObj (separator C)) :=
  (exactFunctor_iff _).1 (tensorObj_exact (separator C) (isSeparator_separator C)) |>.1

/-- The Gabriel-Popescu left adjoint `tensorObj (separator C)` preserves finite colimits. -/
local instance tensorObj_separator_preservesFiniteColimits :
    PreservesFiniteColimits (tensorObj (separator C)) :=
  (exactFunctor_iff _).1 (tensorObj_exact (separator C) (isSeparator_separator C)) |>.2

/-- The Gabriel-Popescu left adjoint `tensorObj (separator C)` is additive. -/
local instance tensorObj_separator_additive :
    (tensorObj (separator C)).Additive := by
  have : PreservesBinaryBiproducts (tensorObj (separator C)) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Helper for Lemma 19.14.4: fix a functorial K-injective replacement on cochain complexes of
`C`. -/
private noncomputable abbrev gabrielPopescuKInjectiveResolution :
    CochainComplex.FunctorialComplexApproximation C :=
  Classical.choose (CochainComplex.exists_functorial_kInjective_resolution C)

/-- Helper for Lemma 19.14.4: the chosen functorial replacement lands in K-injective complexes. -/
private theorem gabrielPopescuKInjectiveResolution_isKInjective
    (K : CochainComplex C ℤ) :
    ((gabrielPopescuKInjectiveResolution (C := C)).toFunctor.obj K).IsKInjective := by
  -- Proof comment: the Chapter 19 functorial replacement theorem records K-injectivity for every
  -- chosen target complex.
  exact
    (Classical.choose_spec
      (CochainComplex.exists_functorial_kInjective_resolution C)).2 K

/-- Helper for Lemma 19.14.4: the chosen functorial replacement map is a quasi-isomorphism. -/
private theorem gabrielPopescuKInjectiveResolution_quasiIso
    (K : CochainComplex C ℤ) :
    QuasiIso ((gabrielPopescuKInjectiveResolution (C := C)).ι.app K) := by
  -- Proof comment: the replacement theorem packages the comparison morphism as a quasi-isomorphism.
  exact (gabrielPopescuKInjectiveResolution (C := C)).quasiIso_app K

private noncomputable abbrev gabrielPopescuLeftDerived :
    DerivedCategory RMod ⥤ DerivedCategory C :=
  (tensorObj (separator C)).mapDerivedCategory

private abbrev tensorObjComplex :
    CochainComplex RMod ℤ ⥤ CochainComplex C ℤ :=
  (tensorObj (separator C)).mapHomologicalComplex (up ℤ)

private abbrev preadditiveCoyonedaComplex :
    CochainComplex C ℤ ⥤ CochainComplex RMod ℤ :=
  (preadditiveCoyonedaObj (separator C)).mapHomologicalComplex (up ℤ)

-- Route correction: instead of the broken Chapter 19 wrapper, use the earlier Chapter 13
-- K-injective replacement theorem directly to build the required total right derived functor.
/-- Helper for Lemma 19.14.4: the cochain-level Gabriel-Popescu right adjoint admits a total
right derived functor because every complex has a quasi-isomorphic K-injective replacement. -/
local instance preadditiveCoyonedaComplex_hasRightDerivedFunctor :
    (preadditiveCoyonedaComplex ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso C (up ℤ)) :=
  by
    -- TODO: derive this cochain-level right-derived existence from the homotopy-category route
    -- using the functorial K-injective replacement owner and `DerivedCategory.quotientCompQhIso`.
    sorry

private noncomputable abbrev gabrielPopescuRightDerived :
    DerivedCategory C ⥤ DerivedCategory RMod :=
  additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))

local notation "QMod" => (DerivedCategory.Q : CochainComplex RMod ℤ ⥤ DerivedCategory RMod)
local notation "QC" => (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
local notation "QisMod" => HomologicalComplex.quasiIso RMod (up ℤ)
local notation "QisC" => HomologicalComplex.quasiIso C (up ℤ)

/-- The unit of the Gabriel-Popescu adjunction on cochain complexes. -/
private abbrev gabrielPopescuComplexUnit :
    𝟭 (CochainComplex RMod ℤ) ⟶ tensorObjComplex ⋙ preadditiveCoyonedaComplex :=
  (Functor.mapHomologicalComplexIdIso RMod (up ℤ)).hom ≫
    NatTrans.mapHomologicalComplex
      (tensorObjPreadditiveCoyonedaObjAdjunction (separator C)).unit
      (up ℤ)

/-- The counit of the Gabriel-Popescu adjunction on cochain complexes. -/
private abbrev gabrielPopescuComplexCounit :
    preadditiveCoyonedaComplex ⋙ tensorObjComplex ⟶ 𝟭 (CochainComplex C ℤ) :=
  NatTrans.mapHomologicalComplex
      (tensorObjPreadditiveCoyonedaObjAdjunction (separator C)).counit
      (up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso C (up ℤ)).hom

/-- The Gabriel-Popescu adjunction lifted to cochain complexes. -/
private noncomputable def gabrielPopescuComplexAdjunction :
    ((tensorObj (separator C)).mapHomologicalComplex (up ℤ)) ⊣
      ((preadditiveCoyonedaObj (separator C)).mapHomologicalComplex (up ℤ)) :=
  -- Proof comment: use the canonical owner that lifts any adjunction to cochain complexes.
  CategoryTheory.Adjunction.mapHomologicalComplex
    (tensorObjPreadditiveCoyonedaObjAdjunction (separator C))
    (up ℤ)

/-- The comparison morphism exhibiting the right derived Gabriel-Popescu functor. -/
private abbrev gabrielPopescuRightDerivedUnit :
    preadditiveCoyonedaComplex ⋙ QMod ⟶ QC ⋙ gabrielPopescuRightDerived :=
  (preadditiveCoyonedaComplex ⋙ QMod).totalRightDerivedUnit QC QisC

/-- The exact-functor lift on derived categories is the left derived Gabriel-Popescu functor. -/
private theorem gabrielPopescuLeftDerived_isLeftDerivedFunctor :
    gabrielPopescuLeftDerived.IsLeftDerivedFunctor
      ((tensorObj (separator C)).mapDerivedCategoryFactors.hom)
      QisMod := by
  -- Proof comment: the exact Gabriel-Popescu left adjoint preserves quasi-isomorphisms, so the
  -- canonical exact lift to the derived category is its left derived functor.
  simpa [gabrielPopescuLeftDerived] using
    (Functor.isLeftDerivedFunctor_of_inverts
      QisMod
      ((tensorObj (separator C)).mapDerivedCategory : DerivedCategory RMod ⥤ DerivedCategory C)
      ((tensorObj (separator C)).mapDerivedCategoryFactors))

attribute [local instance] gabrielPopescuLeftDerived_isLeftDerivedFunctor

/-- The chapter-level right derived Gabriel-Popescu functor is the right derived functor of the
cochain-level embedding. -/
private theorem gabrielPopescuRightDerived_isRightDerivedFunctor :
    gabrielPopescuRightDerived.IsRightDerivedFunctor
      gabrielPopescuRightDerivedUnit
      QisC := by
  dsimp [gabrielPopescuRightDerived, gabrielPopescuRightDerivedUnit,
    additiveFunctorTotalRightDerived]
  infer_instance

attribute [local instance] gabrielPopescuRightDerived_isRightDerivedFunctor

/-- The composite `F ⋙ RG` carries the left-derived structure required by `Adjunction.derived`. -/
private theorem gabrielPopescu_leftDerived_rightDerived_comp_isLeftDerivedFunctor :
    (gabrielPopescuLeftDerived ⋙ gabrielPopescuRightDerived).IsLeftDerivedFunctor
      ((Functor.associator QMod gabrielPopescuLeftDerived gabrielPopescuRightDerived).inv ≫
        Functor.whiskerRight
          ((tensorObj (separator C)).mapDerivedCategoryFactors.hom)
          gabrielPopescuRightDerived)
      QisMod := by
  -- TODO: derive this composite left-derived structure from the eventual homotopy-level
  -- Gabriel-Popescu right-derived owner, rather than relying on typeclass search over the current
  -- cochain-level wrapper.
  sorry

attribute [local instance] gabrielPopescu_leftDerived_rightDerived_comp_isLeftDerivedFunctor

/-- The composite `RG ⋙ F` carries the right-derived structure required by `Adjunction.derived`. -/
private theorem gabrielPopescu_rightDerived_leftDerived_comp_isRightDerivedFunctor :
    (gabrielPopescuRightDerived ⋙ gabrielPopescuLeftDerived).IsRightDerivedFunctor
      (Functor.whiskerRight gabrielPopescuRightDerivedUnit gabrielPopescuLeftDerived ≫
        (Functor.associator QC gabrielPopescuRightDerived gabrielPopescuLeftDerived).hom)
      QisC := by
  -- TODO: once the right-derived Gabriel-Popescu functor is rebuilt via the homotopy/K-injective
  -- route, transport its canonical comparison through the exact left-derived lift here.
  sorry

attribute [local instance] gabrielPopescu_rightDerived_leftDerived_comp_isRightDerivedFunctor

-- Proof sketch: apply `Adjunction.derived` to the cochain-level Gabriel-Popescu adjunction
-- induced by `tensorObjPreadditiveCoyonedaObjAdjunction (separator C)`. The left derived functor
-- is the exact-functor owner `gabrielPopescuLeftDerived`, and the right derived functor is the
-- chapter-level owner `gabrielPopescuRightDerived`.
/-- Lemma 19.14.4: for the canonical Gabriel-Popescu functors attached to the separator of a
Grothendieck abelian category, the induced functor
`F : D(\operatorname{Mod}_{(End(\mathrm{separator}\, C))^{op}}) ⥤ D(C)` is left adjoint to the
right derived Gabriel-Popescu embedding `RG`. This is the owner-level derived adjunction attached
to the fixed Gabriel-Popescu functor pair. -/
@[stacks 0F5V]
noncomputable def gabriel_popescu_derived_adjunction :
    ((tensorObj (separator C)).mapDerivedCategory) ⊣
      (additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))) :=
  Adjunction.derived
    gabrielPopescuComplexAdjunction
    QisMod
    QisC
    ((tensorObj (separator C)).mapDerivedCategoryFactors.hom)
    gabrielPopescuRightDerivedUnit

/-- Helper for Lemma 19.14.4: the underived Gabriel-Popescu counit is a natural isomorphism. -/
private theorem gabrielPopescuCounit_isIso :
    IsIso (tensorObjPreadditiveCoyonedaObjAdjunction (separator C)).counit := by
  -- Proof comment: Gabriel-Popescu makes `preadditiveCoyonedaObj (separator C)` fully faithful,
  -- so the underived counit is an isomorphism by the standard adjunction criterion.
  letI : (preadditiveCoyonedaObj (separator C)).Full :=
    GabrielPopescu.full (separator C) (isSeparator_separator C)
  letI : (preadditiveCoyonedaObj (separator C)).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj (separator C)).1
      (isSeparator_separator C)
  exact
    (tensorObjPreadditiveCoyonedaObjAdjunction (separator C)).counit_isIso_of_R_fully_faithful

/-- Helper for Lemma 19.14.4: the right-derived comparison is an isomorphism on K-injective
complexes. -/
private theorem gabrielPopescuRightDerivedUnit_app_isIso_of_isKInjective
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso (gabrielPopescuRightDerivedUnit.app I) := by
  -- TODO: prove this from the rebuilt right-derived owner by showing `DerivedCategory.Q ⋙ RG`
  -- inverts quasi-isomorphisms and then applying
  -- `Functor.isIso_of_isRightDerivedFunctor_of_inverts`.
  sorry

/-- Helper for Lemma 19.14.4: the derived Gabriel-Popescu counit is an isomorphism on a
K-injective representative complex. -/
private theorem derivedCounit_app_isIso_onKInjective
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((gabriel_popescu_derived_adjunction.counit).app (DerivedCategory.Q.obj I)) := by
  -- TODO: specialize `Adjunction.derivedε_fac_app` after the right-derived comparison map is
  -- stabilized; the normalized right-hand side should factor through the underived Gabriel-
  -- Popescu counit and the K-injective comparison isomorphism above.
  sorry

/-- Helper for Lemma 19.14.4: the chosen functorial K-injective replacement still represents the
original derived object. -/
private noncomputable def gabrielPopescuFunctorialKInjectiveModelIso
    (K : DerivedCategory C) :
    DerivedCategory.Q.obj
        ((gabrielPopescuKInjectiveResolution (C := C)).toFunctor.obj
          (DerivedCategory.Q.objPreimage K)) ≅
      K := by
  let L := DerivedCategory.Q.objPreimage K
  letI :
      IsIso
        (DerivedCategory.Q.map ((gabrielPopescuKInjectiveResolution (C := C)).ι.app L)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C
      ((gabrielPopescuKInjectiveResolution (C := C)).ι.app L)).2
      (gabrielPopescuKInjectiveResolution_quasiIso (C := C) L)
  -- Proof comment: invert the derived image of the functorial replacement map and compose with
  -- the canonical representative comparison.
  exact
    (asIso (DerivedCategory.Q.map
      ((gabrielPopescuKInjectiveResolution (C := C)).ι.app L))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso K

/-- Helper for Lemma 19.14.4: every component of the derived Gabriel-Popescu counit is an
isomorphism. -/
private theorem gabrielPopescuDerivedCounit_app_isIso
    (K : DerivedCategory C) :
    IsIso ((gabriel_popescu_derived_adjunction.counit).app K) := by
  let L := DerivedCategory.Q.objPreimage K
  let I := (gabrielPopescuKInjectiveResolution (C := C)).toFunctor.obj L
  let _ : I.IsKInjective := gabrielPopescuKInjectiveResolution_isKInjective (C := C) L
  let e : DerivedCategory.Q.obj I ≅ K :=
    gabrielPopescuFunctorialKInjectiveModelIso (C := C) K
  have hComp :
      IsIso
        (((gabrielPopescuRightDerived ⋙ gabrielPopescuLeftDerived).map e.hom) ≫
          (gabriel_popescu_derived_adjunction.counit.app K)) := by
    -- Proof comment: counit naturality transports the K-injective computation along the chosen
    -- isomorphism from the representative `QC.obj I` to `K`.
    rw [(gabriel_popescu_derived_adjunction.counit).naturality e.hom]
    let _ :
        IsIso ((gabriel_popescu_derived_adjunction.counit).app (DerivedCategory.Q.obj I)) :=
      derivedCounit_app_isIso_onKInjective I
    infer_instance
  exact
    (isIso_comp_left_iff
      ((gabrielPopescuRightDerived ⋙ gabrielPopescuLeftDerived).map e.hom)
      ((gabriel_popescu_derived_adjunction.counit).app K)).1 hComp

-- Proof sketch: compute the derived counit on K-injective representatives and compare it with the
-- underived Gabriel-Popescu counit `preadditiveCoyonedaObj (separator C) ⋙ tensorObj
-- (separator C) ⟶ 𝟭 C`, which is an isomorphism because `preadditiveCoyonedaObj (separator C)` is
-- fully faithful by Theorem `19.14.3`.
/-- The counit `RG ⋙ F ⟶ 𝟭_{D(C)}` of the derived Gabriel-Popescu adjunction is an isomorphism. -/
theorem gabriel_popescu_derived_counit_isIso :
    IsIso
      (gabriel_popescu_derived_adjunction.counit :
        (additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))) ⋙
            ((tensorObj (separator C)).mapDerivedCategory) ⟶
          𝟭 (DerivedCategory C)) := by
  -- Proof comment: a natural transformation is an isomorphism once all of its components are.
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  exact gabrielPopescuDerivedCounit_app_isIso K

-- Proof sketch: by the previous theorem, `F` is left adjoint to `RG` and the counit
-- `RG ⋙ F ⟶ 𝟭` is an isomorphism. The standard adjunction criterion then yields the `Full` and
-- `Faithful` properties of `RG` from the canonical owner construction
-- `Adjunction.fullyFaithfulROfIsIsoCounit`.
/-- The derived Gabriel-Popescu embedding `RG : D(C) ⥤ D(\operatorname{Mod}_R)` is full and
faithful. -/
noncomputable def gabriel_popescu_rightDerived_fullyFaithful :
    (additiveFunctorTotalRightDerived
      (preadditiveCoyonedaObj (separator C))).FullyFaithful := by
  letI :
      IsIso
        (gabriel_popescu_derived_adjunction.counit :
          (additiveFunctorTotalRightDerived (preadditiveCoyonedaObj (separator C))) ⋙
              ((tensorObj (separator C)).mapDerivedCategory) ⟶
            𝟭 (DerivedCategory C)) :=
    gabriel_popescu_derived_counit_isIso
  exact gabriel_popescu_derived_adjunction.fullyFaithfulROfIsIsoCounit

end CategoryTheory.IsGrothendieckAbelian

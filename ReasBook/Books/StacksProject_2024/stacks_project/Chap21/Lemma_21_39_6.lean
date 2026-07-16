import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap10.Lemma_10_76_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_39_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable {B : Type w} [CommRing B] {B' : Type w} [CommRing B']
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B')]

/- Domain-style sampling for Lemma 21.39.6:
- primary domain: derived base change for the category-over-a-point lower shriek on
  module-valued presheaves;
- sampled owner declarations:
  `categoryOverPointColimitToDerived`,
  `categoryOverPointDerivedColimit`,
  `CategoryTheory.derivedTensorWithAlgebra`,
  `CategoryTheory.Limits.preservesColimitNatIso`,
  `Functor.leftDerivedNatTrans`;
- best owner abstraction: the chapter owner for `Lπ_!` is already
  `categoryOverPointDerivedColimit`, the module-side change-of-rings owner is already
  `derivedTensorWithAlgebra φ`, and the presheaf side only needs the private bridge obtained by
  deriving the whiskered scalar-extension functor. This file should therefore state the
  source-facing base-change comparison directly in terms of those owners, not via a parallel
  wrapper API.

Primitive-vs-derived split:
- primitive data: the ring map `φ : B →+* B'`, extension of scalars on modules and on
  `B`-module-valued presheaves, and the four left-derived-existence hypotheses;
- derived API: the base-change comparison theorem below.

Source/core/bridge triage:
- `source-facing`: the change-of-rings comparison theorem of Lemma 21.39.6;
- `core/canonical`: `categoryOverPointDerivedColimit` and the module-side owner
  `derivedTensorWithAlgebra`;
- `bridge/view`: whiskering `ModuleCat.extendScalars φ` along `Cᵒᵖ` to obtain the presheaf-level
  change-of-rings functor. -/

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "BPrimePresheaf" => Cᵒᵖ ⥤ ModuleCat B'
local notation "KB" => HomotopyCategory (ModuleCat B) (up ℤ)
local notation "KBPrime" => HomotopyCategory (ModuleCat B') (up ℤ)
local notation "KBPresheaf" => HomotopyCategory BPresheaf (up ℤ)
local notation "KBPrimePresheaf" => HomotopyCategory BPrimePresheaf (up ℤ)
local notation "QB" => (DerivedCategory.Qh : KB ⥤ DerivedCategory (ModuleCat B))
local notation "QBPrime" => (DerivedCategory.Qh : KBPrime ⥤ DerivedCategory (ModuleCat B'))
local notation "QBPresheaf" => (DerivedCategory.Qh : KBPresheaf ⥤ DerivedCategory BPresheaf)
local notation "QBPrimePresheaf" =>
  (DerivedCategory.Qh : KBPrimePresheaf ⥤ DerivedCategory BPrimePresheaf)
local notation "QisB" => HomotopyCategory.quasiIso (ModuleCat B) (up ℤ)
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "QisBPrimePresheaf" => HomotopyCategory.quasiIso BPrimePresheaf (up ℤ)
local notation "ModuleColimitToDerived" =>
  (categoryOverPointColimitToDerived C (ModuleCat B) :
    KBPresheaf ⥤ DerivedCategory (ModuleCat B))
local notation "ModuleColimitToDerived'" =>
  (categoryOverPointColimitToDerived C (ModuleCat B') :
    KBPrimePresheaf ⥤ DerivedCategory (ModuleCat B'))

local instance presheafChangeOfRings_additive (φ : B →+* B') :
    ((Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
      (ModuleCat.extendScalars.{w, w, w} φ)).Additive :=
  Functor.instAdditiveObjWhiskeringRight (ModuleCat.extendScalars.{w, w, w} φ)

variable (φ : B →+* B')

/-- Extension of scalars on `B`-module-valued presheaves along `φ : B →+* B'`. -/
abbrev presheafTensorWithAlgebra :
    BPresheaf ⥤ BPrimePresheaf :=
  (Functor.whiskeringRight (Cᵒᵖ) (ModuleCat B) (ModuleCat B')).obj
    (ModuleCat.extendScalars.{w, w, w} φ)

private abbrev presheafTensorWithAlgebraHot :
    KBPresheaf ⥤ KBPrimePresheaf :=
  (presheafTensorWithAlgebra φ).mapHomotopyCategory (up ℤ)

private abbrev presheafTensorWithAlgebraHomotopyToDerived :
    KBPresheaf ⥤ DerivedCategory BPrimePresheaf :=
  mapHomotopyCategoryToDerived (presheafTensorWithAlgebra φ)

/-- The derived change-of-rings functor on `B`-module-valued presheaves induced by
extension of scalars along `φ : B →+* B'`. This is the source-facing `Lh^*` owner in
Lemma `21.39.6`. -/
noncomputable def presheafDerivedTensorWithAlgebra
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (presheafTensorWithAlgebra φ)) QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory BPrimePresheaf :=
  Functor.totalLeftDerived
    (mapHomotopyCategoryToDerived (presheafTensorWithAlgebra φ))
    QBPresheaf
    QisBPresheaf

private abbrev pointChangeOfRingsHot :
    KB ⥤ KBPrime :=
  (ModuleCat.extendScalars.{w, w, w} φ).mapHomotopyCategory (up ℤ)

private abbrev pointChangeOfRingsToDerived :
    KB ⥤ DerivedCategory (ModuleCat B') :=
  mapHomotopyCategoryToDerived (ModuleCat.extendScalars.{w, w, w} φ)

private theorem pointChangeOfRingsToDerived_hasLeftDerivedFunctor :
    (pointChangeOfRingsToDerived φ).HasLeftDerivedFunctor QisB := by
  simpa [pointChangeOfRingsToDerived, mapHomotopyCategoryToDerived] using
    (extendScalarsToDerived_hasLeftDerivedFunctor φ)

private noncomputable def presheafTensorWithAlgebraThenColimitToDerived :
    KBPresheaf ⥤ DerivedCategory (ModuleCat B') :=
  presheafTensorWithAlgebraHot φ ⋙ ModuleColimitToDerived'

private noncomputable def colimitThenPointChangeOfRingsToDerived :
    KBPresheaf ⥤ DerivedCategory (ModuleCat B') :=
  ((colim : BPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ)) ⋙
    pointChangeOfRingsToDerived φ

private noncomputable def categoryOverPointColimit_changeOfRingsIso :
    (presheafTensorWithAlgebra φ) ⋙ (colim : BPrimePresheaf ⥤ ModuleCat B') ≅
      (colim : BPresheaf ⥤ ModuleCat B) ⋙ ModuleCat.extendScalars.{w, w, w} φ :=
  show
    (presheafTensorWithAlgebra φ) ⋙ (colim : BPrimePresheaf ⥤ ModuleCat B') ≅
      (colim : BPresheaf ⥤ ModuleCat B) ⋙ ModuleCat.extendScalars.{w, w, w} φ
  from
    (preservesColimitNatIso (ModuleCat.extendScalars.{w, w, w} φ)).symm

private noncomputable def presheafTensorWithAlgebraThenColimitToDerivedAssocIso :
    presheafTensorWithAlgebraThenColimitToDerived φ ≅
      ((presheafTensorWithAlgebra φ) ⋙ (colim : BPrimePresheaf ⥤ ModuleCat B')).mapHomotopyCategory
          (up ℤ) ⋙
        QBPrime :=
  (Functor.associator
      (presheafTensorWithAlgebraHot φ)
      ((colim : BPrimePresheaf ⥤ ModuleCat B').mapHomotopyCategory (up ℤ))
      QBPrime).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (presheafTensorWithAlgebra φ)
        (colim : BPrimePresheaf ⥤ ModuleCat B')).symm
      QBPrime

private noncomputable def colimitThenPointChangeOfRingsToDerivedAssocIso :
    ((colim : BPresheaf ⥤ ModuleCat B) ⋙ ModuleCat.extendScalars.{w, w, w} φ).mapHomotopyCategory
        (up ℤ) ⋙
      QBPrime ≅
      ((colim : BPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ)) ⋙
        pointChangeOfRingsToDerived φ :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (colim : BPresheaf ⥤ ModuleCat B)
        (ModuleCat.extendScalars.{w, w, w} φ))
      QBPrime ≪≫
    (Functor.associator
      ((colim : BPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ))
      (pointChangeOfRingsHot φ)
      QBPrime)

private noncomputable def categoryOverPointColimitToDerived_changeOfRingsIso :
    presheafTensorWithAlgebraThenColimitToDerived φ ≅
      ((colim : BPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ)) ⋙
        pointChangeOfRingsToDerived φ :=
  presheafTensorWithAlgebraThenColimitToDerivedAssocIso φ ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso
        (categoryOverPointColimit_changeOfRingsIso φ))
      QBPrime ≪≫
    colimitThenPointChangeOfRingsToDerivedAssocIso φ

/-- The canonical counit exhibiting
`presheafDerivedTensorWithAlgebra φ ⋙ Lπ'_!`
as a left derived functor of the homotopy-level change-of-rings functor followed by colimit. -/
private noncomputable abbrev categoryOverPointDerivedLowerShriek_changeOfRingsSourceCounit
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (presheafTensorWithAlgebra φ)) QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived' QisBPrimePresheaf] :
    QBPresheaf ⋙ (presheafDerivedTensorWithAlgebra φ ⋙ Lπ![C, (ModuleCat B')]) ⟶
      presheafTensorWithAlgebraThenColimitToDerived φ :=
  (Functor.associator
      QBPresheaf
      (presheafDerivedTensorWithAlgebra φ)
      Lπ![C, (ModuleCat B')]).inv ≫
    Functor.whiskerRight
      (Functor.totalLeftDerivedCounit
        (presheafTensorWithAlgebraHomotopyToDerived φ)
        QBPresheaf
        QisBPresheaf)
      Lπ![C, (ModuleCat B')] ≫
    (Functor.associator
      (presheafTensorWithAlgebraHot φ)
      QBPrimePresheaf
      Lπ![C, (ModuleCat B')]).hom ≫
    Functor.whiskerLeft
      (presheafTensorWithAlgebraHot φ)
      (Functor.totalLeftDerivedCounit
        ModuleColimitToDerived'
        QBPrimePresheaf
        QisBPrimePresheaf)

private theorem categoryOverPointDerivedLowerShriek_changeOfRingsSource_isLeftDerivedFunctor
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (presheafTensorWithAlgebra φ)) QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived' QisBPrimePresheaf] :
    (presheafDerivedTensorWithAlgebra φ ⋙ Lπ![C, (ModuleCat B')]).IsLeftDerivedFunctor
      (categoryOverPointDerivedLowerShriek_changeOfRingsSourceCounit φ)
      QisBPresheaf := by
  -- Route correction: the source proof suggests an adjunction argument, but `Adjunction.derived`
  -- still needs this composite left-derived witness as input. The remaining task is therefore to
  -- identify the canonical "composition of left derived functors" instance for this counit shape.
  -- TODO: prove this by a dedicated composition lemma for `IsLeftDerivedFunctor`, or by
  -- transporting the canonical witness for the total left derived functor of
  -- `presheafTensorWithAlgebraThenColimitToDerived φ` across the comparison isomorphism from
  -- Lemma `13.14.16`.
  sorry

/-- The canonical counit exhibiting
`Lπ_! ⋙ derivedTensorWithAlgebra φ`
as a left derived functor of the homotopy-level colimit followed by change-of-rings. -/
private noncomputable abbrev categoryOverPointDerivedLowerShriek_changeOfRingsTargetCounit
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (presheafTensorWithAlgebra φ)) QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived' QisBPrimePresheaf] :
    QBPresheaf ⋙ (Lπ![C, (ModuleCat B)] ⋙ derivedTensorWithAlgebra φ) ⟶
      colimitThenPointChangeOfRingsToDerived φ :=
  letI : Functor.HasLeftDerivedFunctor (pointChangeOfRingsToDerived φ) QisB :=
    pointChangeOfRingsToDerived_hasLeftDerivedFunctor φ
  (Functor.associator
      QBPresheaf
      Lπ![C, (ModuleCat B)]
      (derivedTensorWithAlgebra φ)).inv ≫
    Functor.whiskerRight
      (Functor.totalLeftDerivedCounit
        ModuleColimitToDerived
        QBPresheaf
        QisBPresheaf)
      (derivedTensorWithAlgebra φ) ≫
    (Functor.associator
      ((colim : BPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ))
      QB
      (derivedTensorWithAlgebra φ)).hom ≫
    Functor.whiskerLeft
      ((colim : BPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ))
      (Functor.totalLeftDerivedCounit
        (pointChangeOfRingsToDerived φ)
        QB
        QisB)

private theorem categoryOverPointDerivedLowerShriek_changeOfRingsTarget_isLeftDerivedFunctor
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (presheafTensorWithAlgebra φ)) QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived' QisBPrimePresheaf] :
    (Lπ![C, (ModuleCat B)] ⋙ derivedTensorWithAlgebra φ).IsLeftDerivedFunctor
      (categoryOverPointDerivedLowerShriek_changeOfRingsTargetCounit φ)
      QisBPresheaf := by
  letI : Functor.HasLeftDerivedFunctor (pointChangeOfRingsToDerived φ) QisB :=
    pointChangeOfRingsToDerived_hasLeftDerivedFunctor φ
  -- The target side has the same structural blocker: `Adjunction.derived` and the Kan-extension
  -- API both require an explicit composite left-derived witness for `Lπ_! ⋙ Lf^*`.
  -- TODO: derive this from the exactness of restriction of scalars on the point side together with
  -- a reusable lemma stating that postcomposing a left derived functor with an exact
  -- `mapDerivedCategory` functor again yields a left derived functor of the whiskered source.
  sorry

-- Proof sketch: both composites are canonical left derived functors of homotopy-to-derived
-- functors, and `preservesColimitNatIso (ModuleCat.extendScalars φ)` supplies the underived
-- colimit-change-of-rings comparison. Applying `Functor.leftDerivedNatIso` yields the canonical
-- derived base-change isomorphism, whose source-facing public surface is recorded below as
-- `IsIsomorphic` rather than by exporting the concrete `Iso` datum.
/-- Lemma 21.39.6: in the category-over-a-point situation of Example 21.39.1, for a ring map
`φ : B →+* B'`, the derived base-change comparison
`Lh^* ⋙ Lπ'_!` and `Lπ_! ⋙ Lf^*` are functorially isomorphic; this is the canonical left-derived
transform of the colimit-change-of-rings comparison for extension of scalars on
`B`-module-valued presheaves. -/
@[stacks 08Q8]
theorem categoryOverPointDerivedLowerShriek_changeOfRingsIso
    [Functor.HasLeftDerivedFunctor
      (mapHomotopyCategoryToDerived (presheafTensorWithAlgebra φ)) QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf]
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived' QisBPrimePresheaf] :
    IsIsomorphic
      (presheafDerivedTensorWithAlgebra φ ⋙ Lπ![C, (ModuleCat B')])
      (Lπ![C, (ModuleCat B)] ⋙ derivedTensorWithAlgebra φ) := by
  let _ :
      (presheafDerivedTensorWithAlgebra φ ⋙ Lπ![C, (ModuleCat B')]).IsLeftDerivedFunctor
      (categoryOverPointDerivedLowerShriek_changeOfRingsSourceCounit φ)
      QisBPresheaf :=
    categoryOverPointDerivedLowerShriek_changeOfRingsSource_isLeftDerivedFunctor φ
  let _ :
      (Lπ![C, (ModuleCat B)] ⋙ derivedTensorWithAlgebra φ).IsLeftDerivedFunctor
      (categoryOverPointDerivedLowerShriek_changeOfRingsTargetCounit φ)
      QisBPresheaf :=
    categoryOverPointDerivedLowerShriek_changeOfRingsTarget_isLeftDerivedFunctor φ
  exact ⟨Functor.leftDerivedNatIso
    (presheafDerivedTensorWithAlgebra φ ⋙ Lπ![C, (ModuleCat B')])
    (Lπ![C, (ModuleCat B)] ⋙ derivedTensorWithAlgebra φ)
    (categoryOverPointDerivedLowerShriek_changeOfRingsSourceCounit φ)
    (categoryOverPointDerivedLowerShriek_changeOfRingsTargetCounit φ)
    QisBPresheaf
    (categoryOverPointColimitToDerived_changeOfRingsIso φ)⟩

end

end CategoryTheory

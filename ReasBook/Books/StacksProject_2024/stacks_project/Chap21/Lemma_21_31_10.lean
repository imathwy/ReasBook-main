import StacksProject_2024.Chap21.«21_31_0_1»
import StacksProject_2024.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.Chap21.Lemma_21_30_8

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open TopologicalSpace
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

attribute [local instance] HasDerivedCategory.standard
universe u

namespace CategoryTheory.GrothendieckTopology

attribute [local instance]
  comparisonTopologyPushforwardAb_additive
  comparisonTopologyPullbackAb_additive
  comparisonTopologyPullbackAb_preservesFiniteLimits
  comparisonTopologyPullbackAb_preservesFiniteColimits
  piInverseAb_additive
  piInverseAb_preservesFiniteLimits
  piInverseAb_preservesFiniteColimits
  aInverseAb_additive
  aInverseAb_preservesFiniteLimits
  aInverseAb_preservesFiniteColimits

/- Domain-style sampling for Lemma 21.31.10:
- primary domain: qc/Zariski comparison for abelian sheaves on `LC`, together with the proper
  higher-direct-image comparison and its derived-category counterpart;
- inspected owner declarations:
  `unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful`,
  `comparisonTopologyPullback_pushforward_unit`,
  `higherDirectImage_localizedTopologyComparison_isomorphic`,
  `comparisonTopologyPullback_localizedPushforwardDerived_isomorphic`;
- best owner abstraction: the comparison-only clauses should sit on the canonical unit morphisms
  of the qc/Zariski comparison adjunction, while the proper direct-image clauses remain
  source-facing bridge statements between the small-site and qc-site pushforward owners; for the
  derived comparison clause on `LCCat`, the public surface stays at theorem-level
  `IsIsomorphic`, because the ambient `comparisonTopologyPullback_pushforward_unit` owner is not
  universe-polymorphic enough to avoid explicit `@...` plumbing on `LCCat`;
- primitive vs derived: the primitive data are the actual Chapter 21 owners
  `π[τzar.over X, πFunctor X]⁻¹`, `a[hle, πFunctor X]⁻¹`,
  `comparisonTopologyPushforwardAb hle X`,
  `(Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)`, and
  `τqc.overMapPushforward AddCommGrpCat f`; the unit-isomorphism consequences and proper
  higher-direct-image comparisons are derived API of those owners.

Source/core/bridge triage:
- `source-facing`: the proper higher-direct-image and proper derived-pushforward clauses;
- `core/canonical`: the comparison unit
  `((𝟭 (Over X)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (τzar.over X) (τqc.over X)).unit.app`,
  the derived comparison owner `additiveFunctorTotalRightDerived
    (comparisonTopologyPushforwardAb hle X)`,
  and the direct-image owners `Functor.rightDerived` / `Functor.totalRightDerived`;
- `bridge/view`: the source-facing identifications
  `a_X^{-1} = ε_X^{-1} ∘ π_X^{-1}` and
  `a_Y^{-1}(Rf_* K) ≅ Rf_{qc,*}(a_X^{-1}K)`.
-/

section

variable (τzar τqc : GrothendieckTopology LCCat.{u})
variable (hle : τzar ≤ τqc)
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  ((πFunctor X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint]
variable [∀ X : LCCat.{u}, HasWeakSheafify (τqc.over X) AddCommGrpCat.{u + 1}]

section Objectwise

variable (X : LCCat.{u})

local notation "πX⁻¹" => π[τzar.over X, πFunctor X]⁻¹
local notation "aX⁻¹" => a[hle, πFunctor X]⁻¹

-- Proof sketch: the source comparison is the canonical unit of the localized comparison
-- adjunction on the Zariski sheaf `π_X⁻¹ ℱ`; its target is definitionally
-- `(comparisonTopologyPushforwardAb hle X).obj (aX⁻¹.obj ℱ)`.
/-- Lemma 21.31.10 (1), degree-`0` part: for `X ∈ LC_{qc}` and an abelian sheaf `ℱ` on
the small Zariski site of `X`, the canonical comparison unit
`π_X⁻¹ ℱ ⟶ ε_{X,*}(a_X⁻¹ ℱ)` is an isomorphism. -/
@[stacks 0DCY]
theorem comparisonPushforward_aInverseAb_isomorphic_piInverseAb
    (ℱ : SmallAbSheaf X) :
    IsIso
      ((comparisonTopologyAdjunction AddCommGrpCat.{u + 1} hle X).unit.app
        (πX⁻¹.obj ℱ)) := by
  simpa using
    (comparisonTopology_unit_isIso AddCommGrpCat.{u + 1} hle X (πX⁻¹.obj ℱ))

-- Proof sketch: the qc/Zariski comparison situation attached to the essential image of
-- `π_X^{-1}` satisfies `(V_n)` in every degree by Lemma `21.30.8 (1)`, so after identifying
-- `a_X⁻¹ ℱ` with an object whose `ε_{X,*}`-image is `π_X⁻¹ ℱ`, every positive
-- higher direct image of `ε_{X,*}` on `a_X⁻¹ ℱ` vanishes.
/-- Lemma 21.31.10 (1), positive-degree part: for `X ∈ LC_{qc}` and an abelian sheaf
`ℱ` on the small Zariski site of `X`, the positive higher direct images of
`a_X^{-1} ℱ` along `ε_X` vanish. -/
@[stacks 0DCY]
theorem comparisonPushforward_aInverseAb_higherDirectImage_isZero
    [HasInjectiveResolutions (LCZarAbSheaf (τqc.over X))]
    (ℱ : SmallAbSheaf X)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((comparisonTopologyPushforwardAb hle X).rightDerived i).obj (aX⁻¹.obj ℱ)) := by
  sorry

end Objectwise

section ProperHigherDirectImages

variable {X Y : LCCat.{u}}
variable [Abelian (SmallAbSheaf X)]
variable [IsGrothendieckAbelian (SmallAbSheaf X)]
variable [HasInjectiveResolutions (SmallAbSheaf X)]
variable [Abelian (SmallAbSheaf Y)]
variable [Abelian (LCZarAbSheaf (τqc.over X))]
variable [IsGrothendieckAbelian (LCZarAbSheaf (τqc.over X))]
variable [HasInjectiveResolutions (LCZarAbSheaf (τqc.over X))]
variable [Abelian (LCZarAbSheaf (τqc.over Y))]
variable (f : X ⟶ Y)
variable [HasPullbacksAlong f]

section ProperBaseChange

local notation "aX⁻¹" => a[hle, πFunctor X]⁻¹
local notation "aY⁻¹" => a[hle, πFunctor Y]⁻¹
variable [Functor.Additive
  ((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj))]
variable [Functor.Additive (τqc.overMapPushforward AddCommGrpCat f)]
local instance : Preadditive (SmallAbSheaf X) := Abelian.toPreadditive
local instance : Preadditive (SmallAbSheaf Y) := Abelian.toPreadditive
local instance : Preadditive (LCZarAbSheaf (τqc.over X)) := Abelian.toPreadditive
local instance : Preadditive (LCZarAbSheaf (τqc.over Y)) := Abelian.toPreadditive
local instance :
    Functor.Additive
      ((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)) :=
  inferInstanceAs
    (Functor.Additive
      ((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)))
local instance : Functor.Additive (τqc.overMapPushforward AddCommGrpCat f) :=
  inferInstanceAs (Functor.Additive (τqc.overMapPushforward AddCommGrpCat f))

-- Proof sketch: apply the proper comparison of Lemma `21.31.8 (3)` to the abelian sheaf
-- `ℱ`, then pass to the `i`-th higher direct image owners on the two direct-image
-- functors.
/-- Lemma 21.31.10 (2): for a proper morphism `f : X ⟶ Y` in `LC_{qc}`, an abelian sheaf
`ℱ` on the small site of `X`, and `i ≥ 0`, the inverse image `a_Y⁻¹` of the small
higher direct image `R^i f_* ℱ` is canonically isomorphic to the qc higher direct image
`R^i f_{qc,*}(a_X⁻¹ ℱ)`. -/
@[stacks 0DCY]
theorem proper_aInverse_higherDirectImage_smallPushforward_isomorphic_qcPushforward_higherDirectImage
    (hf : IsProperMap f.hom)
    (ℱ : SmallAbSheaf X)
    (i : ℕ) :
    IsIsomorphic
      (aY⁻¹.obj
        ((((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)).rightDerived
          i).obj ℱ))
      ((((τqc.overMapPushforward AddCommGrpCat f).rightDerived i).obj (aX⁻¹.obj ℱ))) :=
  sorry

end ProperBaseChange

end ProperHigherDirectImages

section DerivedComparison

variable (X : LCCat.{u})
variable [Abelian (SmallAbSheaf X)]
variable [IsGrothendieckAbelian (LCZarAbSheaf (τzar.over X))]
variable [IsGrothendieckAbelian (LCZarAbSheaf (τqc.over X))]
variable [∀ Z : LCCat.{u}, HasSheafify (τqc.over Z) AddCommGrpCat.{u + 1}]

local instance : Abelian (LCZarAbSheaf (τzar.over X)) := sheafIsAbelian
local instance : Abelian (LCZarAbSheaf (τqc.over X)) := sheafIsAbelian

local instance : Preadditive (LCZarAbSheaf (τzar.over X)) := Abelian.toPreadditive
local instance : Preadditive (LCZarAbSheaf (τqc.over X)) := Abelian.toPreadditive
local instance : Preadditive (SmallAbSheaf X) := Abelian.toPreadditive

section LocalizationComparison

variable [CategoryWithHomology (LCZarAbSheaf (τqc.over X))]
variable [HasInjectiveResolutions (LCZarAbSheaf (τqc.over X))]
variable [Functor.Additive (comparisonTopologyPushforwardAb hle X)]
variable [Functor.Additive (piInverseAb (τzar.over X) (πFunctor X))]
variable [PreservesFiniteLimits (piInverseAb (τzar.over X) (πFunctor X))]
variable [PreservesFiniteColimits (piInverseAb (τzar.over X) (πFunctor X))]
variable [∀ Z : LCCat.{u},
  Functor.HasRightDerivedFunctor
    (mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle Z))
    (HomotopyCategory.quasiIso
      (Sheaf (τqc.over Z) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]

local notation "πX⁻¹" => π[τzar.over X, πFunctor X]⁻¹
local notation "aX⁻¹" => a[hle, πFunctor X]⁻¹
local notation "RεX*" => additiveFunctorTotalRightDerived (comparisonTopologyPushforwardAb hle X)
local instance : Functor.Additive πX⁻¹ :=
  inferInstanceAs (Functor.Additive (piInverseAb (τzar.over X) (πFunctor X)))
local instance : PreservesFiniteLimits πX⁻¹ :=
  inferInstanceAs (PreservesFiniteLimits (piInverseAb (τzar.over X) (πFunctor X)))
local instance : PreservesFiniteColimits πX⁻¹ :=
  inferInstanceAs (PreservesFiniteColimits (piInverseAb (τzar.over X) (πFunctor X)))
local instance : Functor.Additive (comparisonTopologyPullbackAb hle X) :=
  inferInstanceAs (Functor.Additive (comparisonTopologyPullbackAb hle X))

-- Proof sketch: compare the derived Zariski inverse image `π_X⁻¹ K` with the canonical derived
-- qc/Zariski pushforward `R ε_{X,*}(a_X⁻¹ K)`. On `LCCat` this clause stays on the source-facing
-- theorem-level owner `IsIsomorphic`, avoiding explicit universe plumbing for the ambient
-- derived adjunction unit from Lemma `21.30.8`.
/-- Lemma 21.31.10 (3): for `X ∈ LC_{qc}` and `K ∈ D⁺(SmallAbSheaf X)`, the canonical
comparison map
`π_X⁻¹ K ⟶ R ε_{X,*}(a_X⁻¹ K)` is an isomorphism. -/
@[stacks 0DCY]
theorem piInverseDerived_isomorphic_rComparisonPushforward_aInverseDerived
    (K : D⁺((SmallAbSheaf X))) :
    IsIsomorphic
      ((πX⁻¹.mapDerivedCategory).obj K.toDerived)
      ((RεX*).obj ((aX⁻¹.mapDerivedCategory).obj K.toDerived)) := by
  sorry

end LocalizationComparison

end DerivedComparison

section ProperDerivedComparison

variable {X Y : LCCat.{u}}
variable [Abelian (SmallAbSheaf X)]
variable [IsGrothendieckAbelian (SmallAbSheaf X)]
variable [HasInjectiveResolutions (SmallAbSheaf X)]
variable [Abelian (SmallAbSheaf Y)]
variable [Abelian (LCZarAbSheaf (τqc.over X))]
variable [IsGrothendieckAbelian (LCZarAbSheaf (τqc.over X))]
variable [HasInjectiveResolutions (LCZarAbSheaf (τqc.over X))]
variable [Abelian (LCZarAbSheaf (τqc.over Y))]
variable [HasSheafify (τqc.over X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (τqc.over Y) AddCommGrpCat.{u + 1}]
variable (f : X ⟶ Y)
variable [HasPullbacksAlong f]

local instance : Preadditive (SmallAbSheaf X) := Abelian.toPreadditive
local instance : Preadditive (SmallAbSheaf Y) := Abelian.toPreadditive
local instance : Preadditive (LCZarAbSheaf (τqc.over X)) := Abelian.toPreadditive
local instance : Preadditive (LCZarAbSheaf (τqc.over Y)) := Abelian.toPreadditive

section ProperBaseChange

variable [Functor.Additive (piInverseAb (τzar.over X) (πFunctor X))]
variable [PreservesFiniteLimits (piInverseAb (τzar.over X) (πFunctor X))]
variable [PreservesFiniteColimits (piInverseAb (τzar.over X) (πFunctor X))]
variable [Functor.Additive (piInverseAb (τzar.over Y) (πFunctor Y))]
variable [PreservesFiniteLimits (piInverseAb (τzar.over Y) (πFunctor Y))]
variable [PreservesFiniteColimits (piInverseAb (τzar.over Y) (πFunctor Y))]
variable [Functor.Additive (aInverseAb hle (πFunctor X))]
variable [PreservesFiniteLimits (aInverseAb hle (πFunctor X))]
variable [PreservesFiniteColimits (aInverseAb hle (πFunctor X))]
variable [Functor.Additive (aInverseAb hle (πFunctor Y))]
variable [PreservesFiniteLimits (aInverseAb hle (πFunctor Y))]
variable [PreservesFiniteColimits (aInverseAb hle (πFunctor Y))]
variable [Functor.Additive
  ((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj))]
variable [Functor.Additive (τqc.overMapPushforward AddCommGrpCat f)]
variable [CategoryWithHomology (SmallAbSheaf X)]
variable [CategoryWithHomology (LCZarAbSheaf (τqc.over X))]

local notation "aX⁻¹" => a[hle, πFunctor X]⁻¹
local notation "aY⁻¹" => a[hle, πFunctor Y]⁻¹
local instance :
    Functor.Additive
      ((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)) :=
  inferInstanceAs
    (Functor.Additive
      ((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)))
local instance : Functor.Additive (τqc.overMapPushforward AddCommGrpCat f) :=
  inferInstanceAs (Functor.Additive (τqc.overMapPushforward AddCommGrpCat f))

-- Proof sketch: proper base change on the qc site identifies the inverse image of `Rf_* K` with
-- the qc direct image of `a_X^{-1}K`.
/-- Lemma 21.31.10 (4): for a proper morphism `f : X ⟶ Y` in `LC_{qc}` and
`K ∈ D⁺(SmallAbSheaf X)`, the inverse image `a_Y⁻¹(Rf_* K)` is canonically isomorphic to
`R f_{qc,*}(a_X⁻¹ K)`. -/
@[stacks 0DCY]
theorem proper_aInverseDerived_smallPushforward_isomorphic_qcPushforwardDerived
    (hf : IsProperMap f.hom)
    (K : D⁺((SmallAbSheaf X))) :
    IsIsomorphic
      ((aY⁻¹.mapDerivedCategory).obj
        ((additiveFunctorTotalRightDerived
            ((Opens.map f.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
              (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj))).obj
          K.toDerived))
      ((additiveFunctorTotalRightDerived (τqc.overMapPushforward AddCommGrpCat f)).obj
        ((aX⁻¹.mapDerivedCategory).obj K.toDerived)) := sorry

end ProperBaseChange

end ProperDerivedComparison

end

end CategoryTheory.GrothendieckTopology

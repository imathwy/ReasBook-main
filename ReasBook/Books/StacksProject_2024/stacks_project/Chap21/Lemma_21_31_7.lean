import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Sites.Sheafification
import StacksProject_2024.Chap07.Lemma_7_21_7
import StacksProject_2024.Chap07.Lemma_7_25_8
import StacksProject_2024.Chap07.Definition_7_42_3
import StacksProject_2024.Chap18.Lemma_18_15_3
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap19.AdditiveFunctorTotalRightDerived
import StacksProject_2024.Chap21.«21_30_0_1»
import StacksProject_2024.Chap21.«21_31_0_1»
import StacksProject_2024.Chap21.Lemma_21_31_1

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open TopologicalSpace
open scoped CategoryTheory
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.GrothendieckTopology

/- Domain-style sampling for Lemma 21.31.7:
- primary domain: the small-to-big Zariski morphism of sites
  `πX : Opens X.obj ⥤ Over X`, its inverse/direct image functors, and their compatibility with
  pullback, pushforward, cohomology, and derived pushforward;
- inspected owner declarations:
  `Functor.sheafPullback`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardContinuous_exact_of_isAlmostCocontinuous`,
  `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pushforward`,
  `GrothendieckTopology.overMapPullback`,
  `GrothendieckTopology.overMapPushforward`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPullbackComp'`,
  `additiveFunctorTotalRightDerived`;
- best owner abstraction: the public source-facing clauses should sit on the owner functors
  `π_X⁻¹`, `π_{X,*}`, and the canonical localized pullback/pushforward owners, not on new wrapper
  structures;
- primitive vs derived: the primitive data are `πX`, the localized topology `τzar.over X`,
  almost cocontinuity/full faithfulness for the small-to-big morphism of sites, and for the
  comparison clauses a family-level site square
  `π_Y ⋙ Over.pullback f ≅ Opens.map f.hom ⋙ π_X`;
  the induced direct-image comparison, cohomology comparisons, unit isomorphisms, exactness, and
  proper base-change comparisons are derived API of these owner functors.

Source/core/bridge triage:
- `source-facing`: the Chapter 21 comparison theorems recorded below;
- `core/canonical`: `piInverse`, `piPushforward`, `TopCat.Sheaf.pullback`,
  `TopCat.Sheaf.pushforward`, `GrothendieckTopology.overMapPullback`,
  `GrothendieckTopology.overMapPushforward`, and `Functor.sheafAdjunctionContinuous`;
- `bridge/view`: the chapter-local theorem statements specialize those canonical owners to the
  small/big Zariski situation without introducing a parallel owner layer.
-/

section Exactness

variable (τzar : GrothendieckTopology LCCat.{u})
variable {X : LCCat.{u}}
variable (πX : Opens X.obj ⥤ Over X)
variable [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [πX.IsAlmostCocontinuous (Opens.grothendieckTopology X.obj) (τzar.over X)]

local notation "πX*" => π[τzar.over X, πX]*

/- Lemma 21.31.7 (3): the small-to-big Zariski direct image `π_{X,*}` is exact on abelian
sheaves, assuming the small-to-big Zariski functor `πX` is almost cocontinuous. This is exactly
the canonical owner theorem
`Functor.sheafPushforwardContinuous_exact_of_isAlmostCocontinuous` specialized to `πX`. -/
recall Functor.sheafPushforwardContinuous_exact_of_isAlmostCocontinuous

end Exactness

section Unit

variable (τzar : GrothendieckTopology LCCat.{u})
variable {X : LCCat.{u}}
variable (πX : Opens X.obj ⥤ Over X)
variable [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) (τzar.over X)]

-- Proof sketch: this is the unit of the canonical adjunction
-- `π_X^{-1} ⊣ π_{X,*}` specialized to abelian sheaves on the small and big Zariski sites.
/- Lemma 21.31.7 (2): if `π_X` is fully faithful, then the canonical unit map
`ℱ ⟶ π_{X,*}(π_X^{-1} ℱ)` is an isomorphism. This is the direct small-to-big Zariski
specialization of the canonical owner theorem
`unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful`. -/
recall unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful

end Unit

section DerivedUnit

variable (τzar : GrothendieckTopology LCCat.{u})
variable {X : LCCat.{u}}
variable (πX : Opens X.obj ⥤ Over X)
variable [Functor.IsContinuous πX (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [((πX.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
  (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint)]
variable [Functor.Full πX] [Functor.Faithful πX]
variable [πX.IsAlmostCocontinuous (Opens.grothendieckTopology X.obj) (τzar.over X)]

variable [Abelian (SmallAbSheaf X)]
variable [Abelian (LCZarAbSheaf (τzar.over X))]
variable [IsGrothendieckAbelian (LCZarAbSheaf (τzar.over X))]

local instance : Preadditive (SmallAbSheaf X) := Abelian.toPreadditive

local instance : Preadditive (LCZarAbSheaf (τzar.over X)) := Abelian.toPreadditive

variable [hPiPushforwardAdd : Functor.Additive π[τzar.over X, πX]*]
variable [hPiInverseAdd : Functor.Additive (piInverseAb (τzar.over X) πX)]
variable [hPiInverseFinLim : PreservesFiniteLimits (piInverseAb (τzar.over X) πX)]
variable [hPiInverseFinColim : PreservesFiniteColimits (piInverseAb (τzar.over X) πX)]

local notation "πX*" => π[τzar.over X, πX]*
local notation "πX⁻¹" => π[τzar.over X, πX]⁻¹

local instance : πX*.Additive := hPiPushforwardAdd
local instance : πX⁻¹.Additive := hPiInverseAdd
local instance : PreservesFiniteLimits πX⁻¹ := hPiInverseFinLim
local instance : PreservesFiniteColimits πX⁻¹ := hPiInverseFinColim

local notation "RπX*" =>
  additiveFunctorTotalRightDerived πX*

-- Proof sketch: derive the fully faithful unit `Id ⟶ π_{X,*} π_X^{-1}` using the exactness of
-- `π_{X,*}` in the almost-cocontinuous small-to-big Zariski situation.
/-- Lemma 21.31.7 (4): on `D⁺(X)`, the canonical derived-unit map
`K ⟶ Rπ_{X,*}(π_X^{-1} K)` is an isomorphism. -/
@[stacks 0DCU]
theorem lcZar_pi_derived_unit_isomorphic
    (K : D⁺((SmallAbSheaf X))) :
    IsIsomorphic
      K.toDerived
      ((RπX*).obj ((πX⁻¹.mapDerivedCategory).obj K.toDerived)) := by
  sorry

end DerivedUnit

section SmallToBigComparison

variable (τzar : GrothendieckTopology LCCat.{u})
variable (πFunctor : ∀ X : LCCat.{u}, Opens X.obj ⥤ Over X)
variable [∀ X : LCCat.{u},
  Functor.IsContinuous (πFunctor X) (Opens.grothendieckTopology X.obj) (τzar.over X)]
variable [∀ X : LCCat.{u},
  (((πFunctor X).sheafPushforwardContinuous (Type u)
    (Opens.grothendieckTopology X.obj) (τzar.over X)).IsRightAdjoint)]
variable
  (πComp :
    ∀ {X Y : LCCat.{u}} (f : X ⟶ Y),
      (πFunctor Y) ⋙ Over.pullback f ≅ Opens.map f.hom ⋙ (πFunctor X))

section PullbackSquare

variable {X Y : LCCat.{u}}

local notation "πX⁻¹" => π[τzar.over X, πFunctor X]⁻¹
local notation "πY⁻¹" => π[τzar.over Y, πFunctor Y]⁻¹

include πComp

section PullbackSquareBridge

variable [HasWeakSheafify (τzar.over X) (Type u)]
variable [HasWeakSheafify (τzar.over Y) (Type u)]

-- Proof sketch: the primitive source data are the small-to-big site functors `π_X`, `π_Y`
-- together with the compatibility square `π_Y ⋙ Over.pullback f ≅ Opens.map f.hom ⋙ π_X`.
-- The direct-image comparison is the canonical specialization of
-- `Functor.sheafPushforwardContinuousComp'`, and the inverse-image statement is its left-adjoint
-- mate.
/-- Under weak sheafification on the localized Zariski sites, and assuming that
`(Over.pullback f).op` admits left Kan extensions on `Type u`-valued presheaves, Lemma 21.31.7
(5) has the canonical owner-level comparison isomorphism below, written with the cocontinuous
pullback owner attached to `Over.map f`. This is the bridge from the source-facing theorem to the
canonical pullback-composition owner. -/
noncomputable abbrev lcZar_smallTopoiSquareIso
    (πComp :
      ∀ {X Y : LCCat.{u}} (f : X ⟶ Y),
        (πFunctor Y) ⋙ Over.pullback f ≅ Opens.map f.hom ⋙ πFunctor X)
    (f : X ⟶ Y)
    [∀ F : (Over Y)ᵒᵖ ⥤ Type u, (Over.pullback f).op.HasLeftKanExtension F] :
    TopCat.Sheaf.pullback (Type u) f.hom ⋙ πX⁻¹ ≅
      πY⁻¹ ⋙ (Over.map f).sheafPullbackCocontinuous (Type u) (τzar.over X) (τzar.over Y) :=
  let _ : Functor.IsContinuous
      (πFunctor Y ⋙ Over.pullback f)
      (Opens.grothendieckTopology Y.obj)
      (τzar.over X) :=
    Functor.isContinuous_comp
      (πFunctor Y)
      (Over.pullback f)
      (Opens.grothendieckTopology Y.obj)
      (τzar.over Y)
      (τzar.over X)
  let e :
      (Over.pullback f).sheafPullback (Type u) (τzar.over Y) (τzar.over X) ≅
        (Over.map f).sheafPullbackCocontinuous (Type u) (τzar.over X) (τzar.over Y) :=
    sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint
      (Over.pullback f)
      (Over.map f)
      (Over.mapPullbackAdj f)
      (Type u)
  (Functor.sheafPullbackComp'
      (Opens.grothendieckTopology Y.obj)
      (Opens.grothendieckTopology X.obj)
      (τzar.over X)
      (Opens.map f.hom)
      (πFunctor X)
      ((πComp f).symm : Opens.map f.hom ⋙ πFunctor X ≅ πFunctor Y ⋙ Over.pullback f)) ≪≫
    (Functor.sheafPullbackComp'
      (Opens.grothendieckTopology Y.obj)
      (τzar.over Y)
      (τzar.over X)
      (πFunctor Y)
      (Over.pullback f)
      (Iso.refl (πFunctor Y ⋙ Over.pullback f))).symm ≪≫
    Functor.isoWhiskerLeft (piInverseType (τzar.over Y) (πFunctor Y)) e

end PullbackSquareBridge

/-- Lemma 21.31.7 (5): for a morphism `f : X ⟶ Y`, the small inverse image and the localized
Zariski inverse image fit into the canonical comparison square attached to a compatible family of
small-to-big Zariski site functors `πFunctor`. Under the stronger weak-sheafification
hypotheses on `τzar.over X` and `τzar.over Y`, the concrete bridge is
`lcZar_smallTopoiSquareIso`. -/
@[stacks 0DCU]
theorem lcZar_small_topoi_square_isomorphic
    (f : X ⟶ Y) :
    IsIsomorphic
      (TopCat.Sheaf.pullback (Type u) f.hom ⋙ πX⁻¹)
      (πY⁻¹ ⋙ τzar.overMapPullback (Type u) f) := by
  sorry
omit πComp

end PullbackSquare

section ProperPushforward

variable {X Y : LCCat.{u}}

local notation "πX⁻¹" => π[τzar.over X, πFunctor X]⁻¹
local notation "πY⁻¹" => π[τzar.over Y, πFunctor Y]⁻¹

include πComp

-- Proof sketch: specialize the site-level compatibility square `π_Y ⋙ Over.pullback f ≅
-- Opens.map f.hom ⋙ π_X` to the direct-image owners via
-- `Functor.sheafPushforwardContinuousComp'`, then apply the proper-map comparison on the small
-- and localized Zariski sites. The file keeps the source-facing statement at the theorem-level
-- `IsIsomorphic` surface until the corresponding right-adjoint mate is exported as a named
-- comparison morphism.
/-- Lemma 21.31.7 (7): if `f : X ⟶ Y` is proper, then `π_Y^{-1} ∘ f_*` is canonically
isomorphic to `f_{Zar,*} ∘ π_X^{-1}` for a compatible family of small-to-big Zariski site
functors `πFunctor`. -/
@[stacks 0DCU]
theorem proper_smallPushforward_piInverse_isomorphic_lcZarPushforward_piInverse
    (f : X ⟶ Y) (hf : IsProperMap f.hom) :
    IsIsomorphic
      (TopCat.Sheaf.pushforward (Type u) f.hom ⋙ πY⁻¹)
      (πX⁻¹ ⋙ τzar.overMapPushforward (Type u) f) := by
  sorry
omit πComp

end ProperPushforward

end SmallToBigComparison

end CategoryTheory.GrothendieckTopology

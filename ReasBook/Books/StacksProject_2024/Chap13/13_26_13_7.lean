import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.«13_26_13_1»
import StacksProject_2024.Chap13.Lemma_13_26_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} {ℬ : Type u}
  [Category.{v} 𝒜] [Category.{v} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)] [Abelian (finiteFilteredObjectCat ℬ)]
  [HasDerivedCategory (GradedObject ℤ 𝒜)] [HasDerivedCategory (GradedObject ℤ ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ ℬ) (up ℤ))]
  [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat ℬ) (up ℤ))]

/- Domain-style sampling for 13.26.13.7:
- primary domain: bounded-below filtered derived functors and the compatibility of their graded
  pieces with ordinary bounded-below right derived functors;
- sampled owner declarations in this domain:
  `Functor.rightDerivedUnique`,
  `mapBoundedBelowHomotopyCategory`,
  `filteredBoundedDerivedGradedPieceFunctor`,
  `Functor.totalRightDerived`;
- best owner abstraction: `Functor.rightDerivedUnique`, specialized to the chapter owners
  `DF⁺`, the `p`-th graded-piece functors, the filtered right derived functor built by
  `Functor.totalRightDerived` on the canonical bounded-below homotopy lift
  `mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T)`, and the plain
  bounded-below right derived functor
  `(mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜))
    (boundedBelowHomotopyQuasiIso 𝒜)`;
- primitive data: the actual Chapter `13` source functor on `K⁺(Fil^f(𝒜))` obtained from the
  canonical homotopy lift of `T` and then taking the `p`-th graded piece on the target side,
  together with comparison maps exhibiting the two chapter composites as right derived functors
  of that concrete source functor;
- derived API: the comparison isomorphism and its factorization identity, already owned by
  `Functor.rightDerivedUnique` and `Functor.rightDerived_fac`.

Source/core/bridge triage:
- `source-facing`: the graded-piece comparison from `(13.26.13.7)`;
- `core/canonical`: `Functor.rightDerivedUnique`;
- `bridge/view`: the defining factorization identity `Functor.rightDerived_fac`.

This item is therefore not a new generic schema: it is the Chapter `13` specialization of the
canonical uniqueness theorem for right derived functors, built from the bounded-below filtered
homotopy lift from `13.26.13.1` and the graded-piece owner from `Lemma_13_26_12`. -/

section

variable (T : 𝒜 ⥤ₗ ℬ)

local instance : PreservesFiniteLimits T.obj :=
  T.property

local instance : PreservesBinaryBiproducts T.obj :=
  preservesBinaryBiproducts_of_preservesBinaryProducts T.obj

local instance : T.obj.Additive :=
  Functor.additive_of_preservesBinaryBiproducts T.obj

variable (p : ℤ)

local notation "W" => FQis⁺(𝒜)
local notation "QFiltA" => mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜
local notation "QFiltB" => mapBoundedBelowFilteredHomotopyToDerivedBelow ℬ
local notation "Tplus" => mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T)

variable [hRTFilt : Functor.HasRightDerivedFunctor (Tplus ⋙ QFiltB) W]

local instance : Functor.IsLocalization QFiltA W :=
  mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization

local notation "Qplus" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "QMapT" => mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj

variable [hRT : Functor.HasRightDerivedFunctor QMapT QisPlus]

local instance : Functor.IsLocalization Qplus QisPlus :=
  mapBoundedBelowHomotopyToDerivedBelow_isLocalization

local notation "GrA" => filteredBoundedDerivedGradedPieceFunctor 𝒜 p
local notation "GrB" => filteredBoundedDerivedGradedPieceFunctor ℬ p
local notation "QGrB" => filteredBoundedHomotopyToDerivedByGradedPiece ℬ p
local notation "KGrA" =>
  mapBoundedBelowHomotopyCategory
    ((finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙
      GradedObject.eval p : finiteFilteredObjectCat 𝒜 ⥤ 𝒜))
local notation "GrSource" => Tplus ⋙ QGrB
local notation "RTFilt" =>
  @Functor.totalRightDerived _ _ _ _ _ _ (Tplus ⋙ QFiltB) QFiltA W inferInstance hRTFilt
local notation "RT" =>
  @Functor.totalRightDerived _ _ _ _ _ _ QMapT Qplus QisPlus inferInstance hRT
local notation "RTGr" => RTFilt ⋙ GrB
local notation "GrRT" => GrA ⋙ RT

/- Canonical owner recall: the graded-piece comparison in `13.26.13.7` is the specialized
uniqueness isomorphism for right derived functors. -/
recall Functor.rightDerivedUnique

/- 13.26.13.7: taking the `p`-th graded piece commutes with the filtered right derived functor
via the canonical comparison isomorphism between the two Chapter `13` right derived functors of
the same source functor on `K⁺(Fil^f(𝒜))`. -/
/- Implementation lemma for 13.26.13.7: the graded-piece comparison is the chapter specialization
of `Functor.rightDerivedUnique`. The public entry is the `def`
`graded_filtered_rightDerived_iso`, with the right-derived assumptions carried only by the ambient
instance context. -/
private theorem graded_filtered_rightDerived_iso_aux :
    RTGr ≅ GrRT := by
  let αgr : GrSource ⟶ QFiltA ⋙ RTGr :=
    (eqToHom (by
      change (GrSource : K⁺(Fil^f(𝒜)) ⥤ D⁺(ℬ)) =
        (((Tplus ⋙ QFiltB) ⋙ GrB) : K⁺(Fil^f(𝒜)) ⥤ D⁺(ℬ))
      -- Both sides are the same Chapter 13 composite after unfolding the bounded-below graded-piece
      -- bridge.
      sorry) :
        GrSource ⟶ (Tplus ⋙ QFiltB) ⋙ GrB) ≫
      (Functor.whiskerRight
        ((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W)
        GrB :
          ((Tplus ⋙ QFiltB) ⋙ GrB) ⟶ QFiltA ⋙ RTFilt ⋙ GrB) ≫
      (Functor.associator QFiltA RTFilt GrB).hom
  let βgr : GrSource ⟶ QFiltA ⋙ GrRT :=
    (eqToHom (by
      change (GrSource : K⁺(Fil^f(𝒜)) ⥤ D⁺(ℬ)) =
        ((KGrA ⋙ QMapT) : K⁺(Fil^f(𝒜)) ⥤ D⁺(ℬ))
      -- This is the Chapter 13 graded-piece comparison on the underived bounded-below homotopy
      -- level.
      sorry) :
        GrSource ⟶ KGrA ⋙ QMapT) ≫
      (Functor.whiskerLeft KGrA
        ((mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).totalRightDerivedUnit Qplus
          QisPlus) :
          (KGrA ⋙ QMapT) ⟶ KGrA ⋙ Qplus ⋙ RT) ≫
      (Functor.associator KGrA Qplus RT).hom ≫
      (Functor.whiskerRight ((eqToHom (by
        change (KGrA ⋙ Qplus : K⁺(Fil^f(𝒜)) ⥤ D⁺(𝒜)) =
          ((QFiltA ⋙ GrA) : K⁺(Fil^f(𝒜)) ⥤ D⁺(𝒜))
        -- This is the same bounded-below graded-piece functor viewed through the filtered and
        -- ordinary derived localization owners.
        sorry) :
          KGrA ⋙ Qplus ⟶ QFiltA ⋙ GrA)) RT :
          KGrA ⋙ Qplus ⋙ RT ⟶ QFiltA ⋙ GrA ⋙ RT) ≫
      (Functor.associator QFiltA GrA RT).hom
  letI : Functor.IsRightDerivedFunctor RTGr αgr W := by
    -- Route correction: the remaining blocker is to identify `αgr` with the canonical
    -- composition comparison for the bounded-below graded-piece functor on the target.
    sorry
  letI : Functor.IsRightDerivedFunctor GrRT βgr W := by
    -- Route correction: the remaining blocker is to transport the ordinary bounded-below
    -- right-derived unit across the Chapter 13 graded-piece bridge.
    sorry
  exact (RTGr).rightDerivedUnique GrRT αgr βgr W

/-- 13.26.13.7: taking the `p`-th graded piece commutes with the filtered right derived functor
via the canonical uniqueness isomorphism between the two Chapter `13` right derived functors of
the same source functor. -/
noncomputable def graded_filtered_rightDerived_iso :
    RTGr ≅ GrRT :=
  graded_filtered_rightDerived_iso_aux

end

end

end CategoryTheory

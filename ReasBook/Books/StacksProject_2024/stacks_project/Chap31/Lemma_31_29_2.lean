import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap31.Definition_31_26_7
import StacksProject_2024.Chap31.Lemma_31_15_8
import StacksProject_2024.Chap31.Remark_31_12_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall note: `lean_leansearch` surfaced the ring-theoretic Picard group API, while
local Chapter 31 inspection found the scheme-side owners `ReflexiveCoh`, `Cl(X)`, and the
codimension-two predicate `Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast`. -/

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

local notation "CohX" => RingedSpace.Coh X.toRingedSpace

/-- A coherent module is rank-one reflexive when it is reflexive and becomes finite locally free
of rank `1` on an open subset whose complement has irreducible components of codimension at
least `2`. -/
@[stacks 0EBM]
class IsRankOneReflexive (ℱ : X.Modules) [ℱ.IsCoherent] : Prop where
  /-- The coherent module is reflexive. -/
  isReflexive : IsReflexive ℱ
  /-- On a codimension-two-complement open subset, the module is finite locally free of rank `1`. -/
  exists_codimTwo_open_isFiniteLocallyFreeOfRank_one :
    ∃ U : X.Opens,
      Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast 2 ((U : Set X)ᶜ : Set X) ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank 1 ((Scheme.Modules.pullback U.ι).obj ℱ)

/-- A rank-one reflexive coherent module is reflexive. -/
@[stacks 0EBM, instance]
instance instIsReflexiveOfIsRankOneReflexive (ℱ : X.Modules) [ℱ.IsCoherent]
    [hℱ : IsRankOneReflexive X ℱ] :
    IsReflexive ℱ :=
  hℱ.isReflexive

/-- The defining conditions for a rank-one reflexive coherent module. -/
@[stacks 0EBM]
theorem isRankOneReflexive_iff (ℱ : X.Modules) [ℱ.IsCoherent] :
    IsRankOneReflexive X ℱ ↔
      IsReflexive ℱ ∧
        ∃ U : X.Opens,
          Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast 2 ((U : Set X)ᶜ : Set X) ∧
            SheafOfModules.IsFiniteLocallyFreeOfRank 1
              ((Scheme.Modules.pullback U.ι).obj ℱ) := sorry

/-- The object property on coherent modules selecting the rank-one reflexive coherent modules. -/
@[stacks 0EBM]
abbrev rankOneReflexiveCohProperty : ObjectProperty CohX :=
  fun ℱ : CohX ↦
    letI : ℱ.1.IsCoherent := ℱ.2
    IsRankOneReflexive X ℱ.1

/-- The category of rank-one coherent reflexive `\mathcal O_X`-modules on `X`. -/
@[stacks 0EBM]
abbrev RankOneReflexiveCoh :=
  (rankOneReflexiveCohProperty X).FullSubcategory

/-- The inclusion of rank-one coherent reflexive modules into coherent modules. -/
@[stacks 0EBM]
abbrev rankOneReflexiveCohInclusion : RankOneReflexiveCoh X ⥤ CohX :=
  (rankOneReflexiveCohProperty X).ι

/-- The class group of rank-one coherent reflexive modules, modeled as units in the skeleton of
the rank-one reflexive coherent subcategory for the reflexive tensor product. -/
@[stacks 0EBM]
abbrev RankOneReflexiveCohClassGroup
    [MonoidalCategory (RankOneReflexiveCoh X)] :=
  Additive ((Skeleton (RankOneReflexiveCoh X))ˣ)

/-- The skeleton-unit presentation of `RankOneReflexiveCohClassGroup`. -/
@[stacks 0EBM]
theorem rankOneReflexiveCohClassGroup_def
    [MonoidalCategory (RankOneReflexiveCoh X)] :
    RankOneReflexiveCohClassGroup X = Additive ((Skeleton (RankOneReflexiveCoh X))ˣ) := sorry

/-- Lemma 31.29.2: Let `X` be an integral locally Noetherian normal scheme. The group of rank `1`
coherent reflexive `\mathcal O_X`-modules is isomorphic to the Weil divisor class group `Cl(X)` of
`X`. The left-hand group is represented by the skeleton-unit group of rank-one reflexive coherent
modules for the reflexive tensor product. -/
@[stacks 0EBM]
theorem rankOneReflexiveCohClassGroup_addEquiv_weilDivisorClassGroup
    (hXnormal : X.isNormal) [Scheme.PrimeDivisorDiscreteValuationRings X]
    [MonoidalCategory (RankOneReflexiveCoh X)] [SymmetricCategory (RankOneReflexiveCoh X)]
    [AddCommGroup (RankOneReflexiveCohClassGroup X)] :
    Nonempty (RankOneReflexiveCohClassGroup X ≃+ Cl(X)) := sorry

end AlgebraicGeometry.Scheme.Modules

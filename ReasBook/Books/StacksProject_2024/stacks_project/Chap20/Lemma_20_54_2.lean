import StacksProject_2024.stacks_project.Chap17.Definition_17_14_1
import StacksProject_2024.stacks_project.Chap20.«20_2_0_4»

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y

variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalCategory (RingedSpace.Modules Y)]

/- Lemma 20.54.2 is source-facing at the higher-direct-image level. The canonical derived
projection-formula morphism belongs to `20.54.2.1` and its perfect-object isomorphism criterion
to `20.54.3`; this file keeps the textbook `R^q f_*` statement itself as the public owner. -/

/-- Lemma 20.54.2: if `f : X ⟶ Y` is a morphism of ringed spaces, `ℱ` is a `Modules X`-object,
and `ℰ` is a finite locally free `Modules Y`-object, then for every `q ≥ 0` there is an isomorphism
`ℰ ⊗ R^q f_* ℱ ≅ R^q f_* (f^* ℰ ⊗ ℱ)`. -/
@[stacks 01E8]
theorem finiteLocallyFree_projectionFormula_higherDirectImage
    (f : X ⟶ Y) [(f _*).Additive]
    [HasInjectiveResolutions ModX]
    (ℰ : ModY) [ℰ.IsFiniteLocallyFree] (ℱ : ModX) (q : ℕ) :
    IsIsomorphic
      (ℰ ⊗ R^{q}_[f](ℱ))
      (R^{q}_[f](((f^*).obj ℰ) ⊗ ℱ)) := by
  sorry

end

end AlgebraicGeometry.RingedSpace

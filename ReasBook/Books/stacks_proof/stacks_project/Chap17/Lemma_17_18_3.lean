import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_17_1
import stacks_proof.stacks_project.Chap17.Lemma_17_18_2
import stacks_proof.stacks_project.Chap18.Lemma_18_29_3

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "IsLocallyDirectSummandOfFiniteFreeX" =>
  @SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree _ _
    (Opens.grothendieckTopology X) _ X.sheaf

/-- Lemma 17.18.3: if `\mathcal F` is a flat `\mathcal O_X`-module of finite presentation on a
ringed space `(X, \mathcal O_X)`, then around any point `x : X` there is an open neighbourhood
`U` such that `\mathcal F|_U` is a direct summand of a finite free `\mathcal O_U`-module. -/
@[stacks 08BL]
theorem exists_open_neighborhood_direct_summand_of_finite_free_of_isFinitePresentation_of_flat
    (ℱ : ModX)
    [ℱ.IsFinitePresentation] [ℱ.IsFlat] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u) (_ : Finite I)
      (ι : ℱ.over U ⟶ SheafOfModules.free.{u} I)
      (π : SheafOfModules.free.{u} I ⟶ ℱ.over U),
        ι ≫ π = 𝟙 (ℱ.over U) := by
  let _ : SheafOfModules.RingedSite.IsFlat X.sheaf ℱ :=
    (SheafOfModules.isFlat_iff_ringedSite_isFlat (X := X) ℱ).mp inferInstance
  let _ : IsLocallyDirectSummandOfFiniteFreeX ℱ :=
    SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_flat
      (J := Opens.grothendieckTopology X) (𝒪 := X.sheaf) ℱ
  rcases
      RingedSite.IsLocallyDirectSummandOfFiniteFree.exists_open_neighborhood_retract_free
        ℱ x with
    ⟨U, hxU, I, hI, ⟨r⟩⟩
  -- Proof comment: the Chapter 18 owner theorem already produces a local retract of a finite free
  -- sheaf, and unpacking that retract gives the required split maps.
  exact ⟨U, hxU, I, hI, r.i, r.r, r.retract⟩

end AlgebraicGeometry.RingedSpace

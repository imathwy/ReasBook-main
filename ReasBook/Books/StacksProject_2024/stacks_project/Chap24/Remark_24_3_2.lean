import StacksProject_2024.Chap24.Definition_24_3_1
import StacksProject_2024.Chap24.Lemma_24_9_1

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace RingedSite.Hom

section

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪X : Sheaf JC CommRingCat.{max u v}} {𝒪Y : Sheaf JD CommRingCat.{max u v}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪X
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪Y

variable (f : X ⟶ Y)
variable [HasWeakSheafify JC AddCommGrpCat.{max u v}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]

local notation "ModX" => ringedSiteModuleCategory JC 𝒪X
local notation "ModY" => ringedSiteModuleCategory JD 𝒪Y
local notation "GModX" => GradedObject ℤ ModX
local notation "GModY" => GradedObject ℤ ModY
local notation "GAlgX" => SheafOfModules.RingedSite.GradedAlgebraSheaf 𝒪X
local notation "GAlgY" => SheafOfModules.RingedSite.GradedAlgebraSheaf 𝒪Y
open SheafOfModules.RingedSite.GradedAlgebraSheaf

/- Source/core/bridge triage for Remark 24.3.2:
- `source-facing`: the forgetful passage from graded algebra sheaves to their underlying graded
  module sheaves, together with the induced degreewise pushforward/pullback comparison on those
  underlying graded objects;
- `core/canonical`: `RingedSite.Hom.gradedPushforward`, `RingedSite.Hom.gradedPullback`, and
  `RingedSite.Hom.gradedPushforwardPullbackHomEquiv` from Lemma 24.9.1;
- `bridge/view`: the forgetful functor
  `SheafOfModules.RingedSite.GradedAlgebraSheaf.forgetToGraded` and the resulting specialization
  of the graded module adjunction to graded algebra sheaves.

This remark therefore keeps the graded-algebra forgetful functor as the public owner in this file
and reuses the graded-module pushforward/pullback API from Lemma 24.9.1 directly. -/

/-- The graded pullback/pushforward Hom-equivalence on module sheaves, rewritten in the source
orientation used for the underlying graded objects of graded algebra sheaves. -/
abbrev gradedPullbackPushforwardHomEquiv
    (ℬ : GModY) (𝒜 : GModX) :
    ((gradedPullback f).obj ℬ ⟶ 𝒜) ≃
      (ℬ ⟶ (gradedPushforward f).obj 𝒜) :=
  (gradedPushforwardPullbackHomEquiv f ℬ 𝒜).symm

/-- Applying `gradedPullbackPushforwardHomEquiv` in degree `n` is the usual module-sheaf
pullback/pushforward adjunction on the degree-`n` graded piece. -/
@[simp] theorem gradedPullbackPushforwardHomEquiv_apply_apply
    (ℬ : GModY) (𝒜 : GModX)
    (g : (gradedPullback f).obj ℬ ⟶ 𝒜) (n : ℤ) :
    (gradedPullbackPushforwardHomEquiv f ℬ 𝒜 g) n =
      ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv
        (ℬ n) (𝒜 n)) (g n) := by
  simpa [gradedPullbackPushforwardHomEquiv] using
    (gradedPushforwardPullbackHomEquiv_symm_apply_apply
      (f := f) (ℬ := ℬ) (𝒜 := 𝒜) g n)

/-- The underlying graded module sheaf of a graded algebra sheaf can be pushed forward degreewise
along a morphism of commutative ringed sites. -/
@[simp] theorem gradedPushforward_forgetToGraded_obj_apply (𝒜 : GAlgX) (n : ℤ) :
    ((gradedPushforward f).obj ((forgetToGraded 𝒪X).obj 𝒜)) n =
        (SheafOfModules.pushforward f.structureSheafMap).obj (𝒜 n) :=
  rfl

/-- In degree `n`, the underlying pulled-back graded object of a graded algebra sheaf is the
pullback of its degree-`n` module sheaf. -/
@[simp] theorem gradedPullback_forgetToGraded_obj_apply (ℬ : GAlgY) (n : ℤ) :
    ((gradedPullback f).obj ((forgetToGraded 𝒪Y).obj ℬ)) n =
        (SheafOfModules.pullback f.structureSheafMap).obj (ℬ n) :=
  rfl

/-- The induced map on the underlying pushed-forward graded objects is degreewise the module
pushforward of the degree-`n` algebra component map. -/
@[simp] theorem gradedPushforward_forgetToGraded_map_apply
    {𝒜 ℬ : GAlgX} (φ : 𝒜 ⟶ ℬ) (n : ℤ) :
    ((gradedPushforward f).map ((forgetToGraded 𝒪X).map φ)) n =
        (SheafOfModules.pushforward f.structureSheafMap).map (φ.hom n) :=
  rfl

/-- The induced map on the underlying pulled-back graded objects is degreewise the module
pullback of the degree-`n` algebra component map. -/
@[simp] theorem gradedPullback_forgetToGraded_map_apply
    {ℬ₁ ℬ₂ : GAlgY} (φ : ℬ₁ ⟶ ℬ₂) (n : ℤ) :
    ((gradedPullback f).map ((forgetToGraded 𝒪Y).map φ)) n =
        (SheafOfModules.pullback f.structureSheafMap).map (φ.hom n) :=
  rfl

/-- In degree `n`, specializing the canonical graded-module pullback/pushforward Hom-equivalence
to the underlying graded objects of graded algebra sheaves applies the usual module-sheaf
adjunction to the degree-`n` component. -/
@[simp] theorem gradedPullbackPushforwardHomEquiv_forgetToGraded_apply_apply
    (ℬ : GAlgY) (𝒜 : GAlgX)
    (g : (gradedPullback f).obj ((forgetToGraded 𝒪Y).obj ℬ) ⟶ (forgetToGraded 𝒪X).obj 𝒜)
    (n : ℤ) :
    (gradedPullbackPushforwardHomEquiv f
      ((forgetToGraded 𝒪Y).obj ℬ) ((forgetToGraded 𝒪X).obj 𝒜) g) n =
      ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv
        (ℬ n) (𝒜 n)) (g n) := by
  simpa using
    (gradedPullbackPushforwardHomEquiv_apply_apply
      (f := f) (ℬ := (forgetToGraded 𝒪Y).obj ℬ) (𝒜 := (forgetToGraded 𝒪X).obj 𝒜) g n)

end

end RingedSite.Hom

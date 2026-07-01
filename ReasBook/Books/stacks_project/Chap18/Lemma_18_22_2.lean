import Mathlib
import stacks_project.Chap07.Lemma_7_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

noncomputable section

/- Lemma 18.22.2: let
`f : (\mathit{Sh}(\mathcal C), \mathcal O) ⟶ (\mathit{Sh}(\mathcal D), \mathcal O')`
be a morphism of ringed topoi, let `𝒢` be a sheaf on `𝒟`, and set `ℱ = f⁻¹ 𝒢`. If `f` is
presented by a continuous functor `u : 𝒟 ⥤ 𝒞` and `𝒢 = h_V^#`, then via the identifications
of Lemma `18.21.3` the commutative squares of Lemma `18.20.1` and Lemma `18.22.1` are the same.
On underlying topoi this is exactly the canonical slice-topos comparison isomorphism from
Sites, Lemma `7.31.2`. -/
#check
  (fun
    {C : Type u} [Category.{u} C]
    {D : Type u} [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (f : D ⥤ C)
    [f.IsContinuous JD JC]
    (U : D) ↦
      (Over.post f).sheafPushforwardContinuousComp (Over.forget (f.obj U))
          RingCat.{u} (JD.over U) (JC.over (f.obj U)) JC ≪≫
        eqToIso (by rfl) ≪≫
        ((Over.forget U).sheafPushforwardContinuousComp f
          RingCat.{u} (JD.over U) JD JC).symm :
      JC.overPullback RingCat.{u} (f.obj U) ⋙
          (Over.post f).sheafPushforwardContinuous RingCat.{u}
            (JD.over U) (JC.over (f.obj U)) ≅
        f.sheafPushforwardContinuous RingCat.{u} JD JC ⋙
          JD.overPullback RingCat.{u} U)

section

variable {C : Type u} [Category.{v} C] [CategoryTheory.Limits.HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable (𝒪 : Sheaf J RingCat.{max u v}) (U : C)

/- Companion recall: under the representable identifications of Lemma `18.21.3`, the ringed part
of the localization square is the canonical map from the structure sheaf to the pushforward of its
localization on the slice site. This is the `j_U^♯` used in the ringed refinement of the
comparison. -/
#check (SheafOfModules.pushforwardOver (R := 𝒪) U)

end

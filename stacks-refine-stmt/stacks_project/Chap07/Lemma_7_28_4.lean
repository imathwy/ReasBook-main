import Mathlib
import stacks_project.Chap07.Lemma_7_21_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (U : C)

/- Domain-style sampling for Lemma 7.28.4:
- primary domain: localized cocontinuous functors between slice sites and their induced
  direct-image functors on sheaf categories;
- sampled owner API:
  `Functor.IsCocontinuous`,
  `GrothendieckTopology.over`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousComp`,
  `Functor.sheafPushforwardCocontinuousComp'`;
- source/core/bridge triage:
  `source-facing`: cocontinuity of the induced slice functor `Over.post u`;
  `core/canonical`: `Functor.IsCocontinuous` together with
  `Functor.sheafPushforwardCocontinuous`;
- bridge/view: the slice specialization of `Functor.sheafPushforwardCocontinuousComp'` for
  `Over.post u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u`.

Primitive data are only the sites `J`, `K`, the cocontinuous functor `u`, and the object `U`.
The sheaf-level comparison square is derived API from the owner comparison theorems of
Lemma `7.21.2`, so the refined file keeps the localized cocontinuity instance and reuses that
canonical bridge directly, treating the right-hand composite Kan-extension hypothesis as derived
data from the left-hand one rather than exporting any separate local wrapper.
-/

/-- Lemma 7.28.4: a cocontinuous functor between sites induces a cocontinuous functor on the
corresponding localized sites. -/
-- Proof sketch: pull a covering sieve on `Over (u.obj U)` back along `Over.post u`; under the
-- equivalence between sieves on a slice object and sieves on its domain, this reduces to pulling
-- back the corresponding covering sieve in `D` along `u`, and then transporting the resulting
-- cover back to the slice site.
instance overPost_isCocontinuous [u.IsCocontinuous J K] :
    Functor.IsCocontinuous (Over.post u) (J.over U) (K.over (u.obj U)) := sorry

section

variable [u.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over (u.obj U))ᵒᵖ ⥤ Type w,
  (Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.post u).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ Type w,
  (Over.post u ⋙ Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F]

/- Lemma 7.28.4: on sheaves of sets, the localized direct-image square is exactly the slice
specialization of the owner comparison theorems
`Functor.sheafPushforwardCocontinuousComp'` and
`Functor.sheafPushforwardCocontinuousComp`. The right-hand composite
`(Over.forget U ⋙ u).op` has pointwise right Kan extensions by transport across the definitional
identity `Over.post u ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u`, so no local wrapper is
needed. -/
#check
  (by
    letI : Functor.IsCocontinuous (Over.forget U ⋙ u) (J.over U) K :=
      isCocontinuous_comp (Over.forget U) u (J.over U) J
    letI : ∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U ⋙ u).op.HasPointwiseRightKanExtension F := by
      intro F
      change (Over.post u ⋙ Over.forget (u.obj U)).op.HasPointwiseRightKanExtension F
      infer_instance
    exact
      (Functor.sheafPushforwardCocontinuousComp'
          (J.over U) (K.over (u.obj U)) K (Over.post u) (Over.forget (u.obj U))
          (show Over.post u ⋙ Over.forget (u.obj U) ≅ Over.forget U ⋙ u from Iso.refl _) ≪≫
        (Functor.sheafPushforwardCocontinuousComp
          (J.over U) J K (Over.forget U) u).symm :
        (Over.post u).sheafPushforwardCocontinuous (Type w) (J.over U) (K.over (u.obj U)) ⋙
            (Over.forget (u.obj U)).sheafPushforwardCocontinuous (Type w)
              (K.over (u.obj U)) K ≅
          (Over.forget U).sheafPushforwardCocontinuous (Type w) (J.over U) J ⋙
            u.sheafPushforwardCocontinuous (Type w) J K))

end

end

end CategoryTheory

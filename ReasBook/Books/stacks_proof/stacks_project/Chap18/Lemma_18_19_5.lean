import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap07.Lemma_7_25_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v w

noncomputable section

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 18.19.5:
- primary domain: relocalization of a ringed site along a map `f : V ⟶ U` and the induced
  comparison on sheaf inverse/direct images over slice sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `Functor.sheafPushforwardCocontinuousComp'`,
  `GrothendieckTopology.overPullback`,
  `GrothendieckTopology.overMapPullback`;
- source/core/bridge triage:
  `source-facing`: the localization triangle for `(Sh(C), 𝒪)` and its relocalization at `f`;
  `core/canonical`: the slice-site comparison owners already recorded in Chapter 7;
  `bridge/view`: the structure-sheaf identification obtained by evaluating the inverse-image
  comparison at `𝒪`.

Primitive data are only `J`, `𝒪`, and `f`. The inverse-image and direct-image comparisons are
already canonically owned by the Chapter 7 slice-site comparison machinery, and the
structure-sheaf comparison is derived by applying that owner isomorphism to `𝒪`, so this file
should remain a direct recall/use file rather than introduce chapter-local wrappers.
-/

/- Lemma 18.19.5: on inverse-image functors, the relocalization triangle
`j_U⁻¹ ⋙ j⁻¹ ≅ j_V⁻¹` is exactly the canonical slice-site comparison attached to
`Over.mapForget f`. -/
recall Functor.sheafPushforwardContinuousComp'

section InverseImage

variable (𝒪 : Sheaf J RingCat.{v}) {U V : C} (f : V ⟶ U)

#check
  (Functor.sheafPushforwardContinuousComp' (Over.mapForget f) (Type w) (J.over V) (J.over U) J :
    J.overPullback (Type w) U ⋙ J.overMapPullback (Type w) f ≅ J.overPullback (Type w) V)

/- Applying the inverse-image comparison to the structure sheaf gives the canonical
identification `j^{-1}(𝒪_U) ≅ 𝒪_V`. -/
#check
  ((Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
      RingCat.{v} (J.over V) (J.over U) J).app 𝒪 :
    (J.overMapPullback RingCat.{v} f).obj (𝒪.over U) ≅ 𝒪.over V)

end InverseImage

/- The direct-image comparison in the same triangle is the cocontinuous owner isomorphism for
`Over.map f ⋙ Over.forget U ≅ Over.forget V`; no extra Chapter 18 owner is needed. -/
recall Functor.sheafPushforwardCocontinuousComp'

section DirectImage

variable {U V : C} (f : V ⟶ U)
variable [∀ F : (Over V)ᵒᵖ ⥤ RingCat.{v}, (Over.map f).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over U)ᵒᵖ ⥤ RingCat.{v}, (Over.forget U).op.HasPointwiseRightKanExtension F]
variable [∀ F : (Over V)ᵒᵖ ⥤ RingCat.{v}, (Over.forget V).op.HasPointwiseRightKanExtension F]

#check
  (Functor.sheafPushforwardCocontinuousComp'
    (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
      (Over.map f).sheafPushforwardCocontinuous RingCat.{v} (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPushforwardCocontinuous RingCat.{v} (J.over U) J ≅
        (Over.forget V).sheafPushforwardCocontinuous RingCat.{v} (J.over V) J)

end DirectImage

end

end GrothendieckTopology
end CategoryTheory

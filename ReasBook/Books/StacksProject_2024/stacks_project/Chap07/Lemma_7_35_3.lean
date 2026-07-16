import Mathlib
import StacksProject_2024.stacks_project.Chap07.Lemma_7_25_2
import StacksProject_2024.stacks_project.Chap07.Lemma_7_35_1
import StacksProject_2024.stacks_project.Chap07.Remark_7_25_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory

open GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

/- Domain-style sampling for Lemma 7.35.3:
- primary domain: fiber functors of points on Grothendieck sites, together with localization of
  sites and the lower-shriek functor on sheaves;
- sampled owner API:
  `Functor.sheafPullback`,
  `Functor.sheafPullbackConstruction.sheafPullbackIso`,
  `Functor.sheafPushforwardContinuous`,
  `localization_lowerShriek_associatedSheafIso`,
  `GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`,
  `localization_leftKanExtension_objIsoSigma`,
  `point_over_sheafFiberObjIso`;
- best owner abstraction: the point-fiber owner `p.sheafFiber`, the localized point owner
  `p.over x`, together with the owner-level right-adjoint hypothesis on
  `(Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J`, whose left adjoint is the
  canonical lower-shriek owner `((Over.forget U).sheafPullback (Type w) (J.over U) J)`;
- primitive data: the point `p`, the object `U`, the localized sheaf `𝒢`, and the owner-level
  right-adjoint structure on localization pushforward;
- derived API: the sigma-type left-Kan-extension presentation of `j_{U!} 𝒢`, the comparison
  from the abstract pullback owner to that concrete model via
  `Functor.sheafPullbackConstruction.sheafPullbackIso`, the comparison between presheaf and sheaf
  fibers at a point, and the localized-point fiber comparison `point_over_sheafFiberObjIso`.

Source/core/bridge triage:
- `source-facing`: the stalk decomposition of `j_{U!} 𝒢` as a sigma-type coproduct over
  `x : p.fiber.obj U`;
- `core/canonical`: `p.sheafFiber`, `p.over x`, the owner predicate
  `((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).IsRightAdjoint`, and the
  resulting lower-shriek owner `((Over.forget U).sheafPullback (Type w) (J.over U) J)`;
- `bridge/view`: `Functor.sheafPullbackConstruction.sheafPullbackIso`, the left-Kan sigma
  presentation, and the presheaf-to-sheaf fiber comparison.

The source-facing statement is a canonical stalk decomposition, so the main public entry should be
the actual `Iso`; the proposition-level `IsIsomorphic` form is only a trivial companion.
-/

variable (U : C)
variable [((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).IsRightAdjoint]

-- Proof sketch: work on the canonical owner
-- `((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢`. One proof route transports this
-- owner to a chosen left-Kan/sheafification model via
-- `Functor.sheafPullbackConstruction.sheafPullbackIso`, then identifies that concrete model with
-- the sigma-type left Kan extension presheaf
-- `V ↦ Σ (φ : V ⟶ U), 𝒢(V/_φ U)` via
-- `localization_lowerShriek_associatedSheafIso`, replaces the stalk of the resulting associated
-- sheaf by the stalk of the presheaf using `p.presheafToSheafCompSheafFiberIso (Type w)`, and
-- finally decomposes the filtered colimit by the elements `x : p.fiber.obj U`, identifying each
-- summand with `(p.over x).sheafFiber.obj 𝒢`.
/-- Lemma 7.35.3: for a point `p` of the site `(C, J)`, an object `U : C`, and a sheaf `𝒢` on the
localized site `(C/U, J.over U)`, the stalk of `j_{U!} 𝒢` at `p` is isomorphic to the coproduct
of the stalks of `𝒢` at the localized points `p.over x` attached to elements
`x : p.fiber.obj U`. -/
noncomputable def localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w)) :
    p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) ≅
      (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) := sorry

-- Proof sketch: this is the canonical `Iso`-to-`IsIso` companion attached to the main
-- decomposition isomorphism.
/-- The morphism underlying the stalk decomposition of Lemma 7.35.3 is an isomorphism. -/
theorem localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber_hom_isIso
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w)) :
    IsIso (localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber U p 𝒢).hom := sorry

-- Proof sketch: package the canonical `Iso` from Lemma 7.35.3 as an `IsIsomorphic` statement.
/-- Proposition-level corollary of `localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber`.
-/
theorem localizationLowerShriek_sheafFiber_isomorphic_sigma_pointOver_sheafFiber
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w)) :
    IsIsomorphic
      (p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢))
      (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) := sorry

end

end CategoryTheory

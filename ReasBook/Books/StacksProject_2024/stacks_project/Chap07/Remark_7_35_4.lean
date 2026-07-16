import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped MorphismOfTopoiIn

universe v u

namespace CategoryTheory

open GrothendieckTopology

section

/- 
Domain-style sampling for Remark 7.35.4:
- primary domain: localization morphisms of topoi and the stalks of their direct images on a
  Grothendieck site;
- sampled owner API:
  `GrothendieckTopology.over`,
  `Over.forget`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`,
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.over`,
  `localizationLowerShriek_sheafFiber_isomorphic_sigma_pointOver_sheafFiber`;
- best owner abstraction: the canonical localization morphism from Definition `7.25.1`,
  `((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J : MorphismOfTopoiIn J (J.over U))`,
  together with its direct image `j_{U,*}`, the point-fiber owner `p.sheafFiber`, and the
  localized-point owner `p.over x`;
- primitive data: a site `(C, J)`, an object `U`, a point `p`, and a sheaf `𝒢` on
  `(C/U, J.over U)`;
- derived API: the sigma-type stalk formula from Lemma `7.35.3` for `j_{U!}`.

Source/core/bridge triage:
- `source-facing`: the remark that the stalk decomposition of Lemma `7.35.3` does not remain
  valid after replacing `j_{U!}` by `j_{U,*}`;
- `core/canonical`: the localization owner
  `((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*`,
  `p.sheafFiber`, and `p.over x`;
- `bridge/view`: the cocontinuous site-level realization of `j_{U,*}` by
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward` and the proposition-level
  `IsIsomorphic` formulation of the would-be sigma decomposition.

This remark introduces no new owner construction. The file should therefore keep only the
owner-level negative statement for the localization direct image `j_{U,*}`, leaving any
right-Kan-extension presentation of that owner to a separate bridge theorem if needed.
-/

-- Proof sketch: use a counterexample site where the direct image functor for localization does
-- not admit the stalk decomposition from Lemma `7.35.3`. This shows that replacing `j_{U!}` by
-- `j_{U,*}` in that statement does not produce a theorem valid for all sites, points, and
-- localized sheaves.
/-- Remark 7.35.4: the direct analogue of
`localizationLowerShriek_sheafFiber_isomorphic_sigma_pointOver_sheafFiber` obtained by replacing
`j_{U!}` with the localization direct image functor `j_{U,*}` is not valid in general. -/
theorem localizationPushforward_sheafFiber_isomorphic_sigma_pointOver_sheafFiber_not_forall :
    ¬ ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{max u v} C]
        (U : C) (p : Point.{max u v} J) (𝒢 : Sheaf (J.over U) (Type (max u v))),
        IsIsomorphic
          (p.sheafFiber.obj
            (((((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J) _*).obj 𝒢)))
          (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) := sorry

end

end CategoryTheory

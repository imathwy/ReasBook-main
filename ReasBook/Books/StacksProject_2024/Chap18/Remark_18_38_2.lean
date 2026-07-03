import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: localized direct image of sheaves of modules on a ringed site and the induced
  stalk functors at points;
- sampled owner declarations:
  `ringSheaf`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.pushforwardOver`,
  `point_sheaf_module_stalk_underlying_functor`;
- best owner abstraction: the canonical localized direct-image functor
  `SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)` between
  `ringedSiteModuleCategory (J.over U) (𝒪.over U)` and `ringedSiteModuleCategory J 𝒪`;
- primitive data: the structure sheaf `𝒪`, the object `U`, the point `p`, and the localized
  module `𝒢`;
- derived API: the source-facing universal stalk formula obtained by replacing `j_{U!}` with
  `j_{U,*}` in Lemma `18.38.1`, and the global counterexample theorem negating that universal
  statement;
- source/core/bridge triage:
  `source-facing`: the remark that the shriek-style stalk coproduct formula fails for `j_{U,*}`;
  `core/canonical`: `ringSheaf`, `ringedSiteModuleCategory`,
    `SheafOfModules.pushforwardOver`, `SheafOfModules.pushforward`, and
    `point_sheaf_module_stalk_underlying_functor`;
  `bridge/view`: the universal formula appearing directly under the outer negation in the theorem
    below.

The previous local aliases for the underlying `RingCat`-valued sheaf, the module category, and
the localized direct image were duplicate wheels of these chapter/mathlib owners, so the public
surface below now uses the canonical declarations directly. -/

-- Proof sketch: forget the module structure and compare with the site-level warning from Remark
-- `7.35.4`, which already shows that the analogous stalk decomposition fails for localization
-- direct image on underlying sheaves. A universally quantified module-level formula of the same
-- shape would force that forbidden sheaf-level statement.
/-- Remark 18.38.2: the coproduct decomposition of stalks proved in Lemma `18.38.1` for
`j_{U!}` does not extend to the localization direct-image functor `j_{U,*}`. Equivalently, the
naive statement obtained by replacing `j_{U!}` with `j_{U,*}` in Lemma `18.38.1` is not valid in
general. -/
theorem ringedSiteLocalizedDirectImage_not_hasShriekStyleStalkFormula
    : ¬ ∀ {C : Type u} [Category.{u} C] [HasBinaryProducts C] (J : GrothendieckTopology C)
        [LocallySmall.{u} C]
        [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
        (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (p : GrothendieckTopology.Point.{u} J)
        (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)),
        IsIsomorphic
          ((point_sheaf_module_stalk_underlying_functor p
              (ringSheaf J 𝒪)).obj
            ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)).obj 𝒢))
          (∐ fun x : p.fiber.obj U ↦
            (point_sheaf_module_stalk_underlying_functor (p.over x)
              (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢) := sorry

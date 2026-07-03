import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_18_38_1 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [LocallySmall.{u} C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)
variable (p : GrothendieckTopology.Point.{u} J)

/- Domain-style sampling:
- primary domain: stalks of sheaves of modules on ringed sites, especially the localized
  lower-shriek functor `j_{U!}` on `\mathcal O_U`-modules;
- sampled owner declarations:
  `ringSheaf`,
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `point_sheaf_module_stalk_underlying_functor`;
- best owner abstraction: the canonical localized extension-by-zero owner
  `SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))` between the chapter owners
  `ringedSiteModuleCategory (J.over U) (𝒪.over U)` and `ringedSiteModuleCategory J 𝒪`;
- primitive data: the structure sheaf `𝒪`, the object `U`, the point `p`, and the localized
  module `𝒢`;
- derived API: the coproduct decomposition of the stalk of `j_{U!} 𝒢`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma computing the stalk of `j_{U!} 𝒢` as a coproduct over
    localized points `p.over x`;
  `core/canonical`: `ringSheaf J 𝒪`, `ringedSiteModuleCategory J 𝒪`, and
    `SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))`;
  `bridge/view`: the stalk formula below, which expresses the source-facing decomposition using
    the canonical chapter owners. -/

-- Proof sketch: use Lemma `18.19.2` to identify `j_{U!}` with extension by zero, compute its
-- underlying presheaf objectwise as the coproduct over arrows into `U`, and then apply the stalk
-- functor from Lemma `18.36.3`. The filtered colimit defining the stalk decomposes by the fiber
-- elements `x : p.fiber.obj U`, and each summand is the underlying abelian-group stalk at the
-- localized point `p.over x`.
/-- Lemma 18.38.1: for a ringed site `(\mathcal C, \mathcal O)`, a point `p` of `\mathcal C`,
an object `U : \mathcal C`, and an `\mathcal O_U`-module `\mathcal G`, the stalk at `p` of
`j_{U!} \mathcal G`, viewed as an abelian group, is canonically isomorphic to the coproduct of
the stalks of `\mathcal G` at the localized points `p.over x` for `x : p.fiber.obj U`; by Sites,
Lemma `7.35.2`, this is equivalently the coproduct over the points of `\mathcal C / U` lying
over `p`. -/
theorem ringedSiteLocalizedExtensionByZero_stalk_isIsomorphic_coproduct_of_localizedPointStalks
    (𝒢 : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    IsIsomorphic
      ((point_sheaf_module_stalk_underlying_functor p
          (ringSheaf J 𝒪)).obj
        ((SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))).obj 𝒢))
      (∐ fun x : p.fiber.obj U ↦
        (point_sheaf_module_stalk_underlying_functor (p.over x)
          (ringSheaf (J.over U) (𝒪.over U))).obj 𝒢) := sorry

end

/-! ### Remark_18_38_2 (from Chap18) -/
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

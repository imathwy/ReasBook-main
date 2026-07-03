import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/-
Domain-style sampling for Lemma 18.19.3:
- primary domain: exactness of extension by zero for sheaves of modules on the localized ringed
  site `(C/U, J.over U, 𝒪.over U)`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `exactFunctor`;
- best owner abstraction:
  `SheafOfModules.pullback
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`;
- primitive data: only `J`, `𝒪`, and `U`;
- derived API: the exactness statement for the source-facing localized extension-by-zero functor
  `j_{U!}`.

Source/core/bridge triage:
- `source-facing`: exactness of `j_{U!}` for the chosen object `U`;
- `core/canonical`: the identity-structure-map pullback owner on sheaves of modules;
- `bridge/view`: the source notation `j_{U!}` for this canonical owner.

This file should therefore keep the specialized exactness theorem, but express it directly in terms
of the canonical pullback owner and the upstream module-category alias from `Lemma_18.19.2`.
-/

-- Proof sketch: `ringedSiteLocalizedExtensionByZero J 𝒪 U` is the lower shriek `j_{U!}` from
-- the localized ringed site, i.e. the pullback functor for the identity map on `𝒪_U`, hence a
-- left adjoint to restriction and therefore right exact. For left exactness, compute sections
-- objectwise as the direct sum over morphisms into `U`, which sends monomorphisms to
-- monomorphisms, and then use exactness of sheafification as in Lemma `18.11.2`.
/-- Lemma 18.19.3: for a ringed site `(\mathcal C, \mathcal O)` and an object `U : \mathcal C`,
the extension-by-zero functor
`j_{U!} : \mathrm{Mod}(\mathcal O_U) ⥤ \mathrm{Mod}(\mathcal O)` is exact. In canonical
mathlib form, this is the exactness of the pullback functor on sheaves of modules induced by the
identity map of the localized ringed site `(C/U, J.over U, \mathcal O_U)`. -/
lemma ringedSiteLocalizedExtensionByZero_exact :
    exactFunctor
      (ringedSiteModuleCategory (J.over U) (𝒪.over U))
      (ringedSiteModuleCategory J 𝒪)
      (SheafOfModules.pullback
        (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))) := sorry

end

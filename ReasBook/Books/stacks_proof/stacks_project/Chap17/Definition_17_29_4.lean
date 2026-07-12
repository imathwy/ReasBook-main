import Mathlib
import StacksProject_2024.Chap17.Lemma_17_29_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat.Sheaf

noncomputable section

universe u

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X} (varphi : 𝒪₁ ⟶ 𝒪₂)

local notation "ModO₂" =>
  SheafOfModules.RingedSite.ringedSiteModuleCategory (Opens.grothendieckTopology X) 𝒪₂

variable (ℱ : ModO₂)
variable (k : ℕ)

/- Domain-style sampling for Definition 17.29.4:
- primary domain: sheaf-level principal parts relative to `𝒪₁ ⟶ 𝒪₂`;
- sampled owner declarations:
  `TopCat.Sheaf.principalParts`,
  `TopCat.Sheaf.principalParts_is_principal_parts_module_of_order`,
  `SheafOfModules.RingedSite.differentialOperatorsFunctor`,
  `SheafOfModules.RingedSite.exists_principal_parts_of_order`;
- best owner abstraction: the source-facing sheaf owner `TopCat.Sheaf.principalParts`, with
  corepresentability kept as the companion bridge property.

Primitive-vs-derived split:
- primitive data here: the distinguished sheaf `P^{k}_[varphi](ℱ)` defined in
  `TopCat.Sheaf.principalParts`;
- derived API: its defining sheafification presentation `principalParts_def` and the companion
  corepresentability theorem `principalParts_is_principal_parts_module_of_order`.

Source/core/bridge triage:
- `source-facing`: the distinguished sheaf `TopCat.Sheaf.principalParts varphi ℱ k`,
  written `P^{k}_[varphi](ℱ)`;
- `core/canonical`: the differential-operator functor
  `SheafOfModules.RingedSite.differentialOperatorsFunctor varphi ℱ k`;
- `bridge/view`: the theorem `principalParts_is_principal_parts_module_of_order`.

This numbered definition names the distinguished principal-parts sheaf, so the main entry should
recall that owner directly rather than the broader fixed-object corepresentability predicate.
-/
/- Definition 17.29.4: the module of principal parts of order `k` of `\mathcal F` relative to
`\mathcal O_1 \to \mathcal O_2` is the sheaf `P^{k}_[varphi](ℱ)`. -/
#check P^{k}_[varphi](ℱ)

/- Companion bridge: the distinguished sheaf `P^{k}_[varphi](ℱ)` corepresents the functor of
order-`k` differential operators out of `ℱ`. -/
#check principalParts_is_principal_parts_module_of_order

end

end TopCat.Sheaf

import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap17.Definition_17_29_1
import stacks_proof.stacks_project.Chap18.Lemma_18_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X}
variable {ℱ 𝒢 ℋ : SheafOfModules (ringSheaf 𝒪₂)}

/- Domain-style sampling for Lemma 17.29.2:
- primary domain: differential operators between sheaves of modules relative to a morphism of ring
  sheaves;
- sampled owner declarations:
  `TopCat.Sheaf.IsDifferentialOperatorOfOrder`,
  `SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder`,
  `SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_comp`,
  `LinearMap.isDifferentialOperatorOfOrder_comp`;
- best owner abstraction: the site-level owner theorem
  `SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_comp`, specialized to the opens site
  of `X`;
- primitive data: a morphism
  `D : (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj ℱ ⟶
    (SheafOfModules.restrictScalars (ringSheafMap varphi)).obj 𝒢`;
- derived API: the opens-site specialization obtained through
  `SheafOfModules.RingedSite.restrictionAlong`.

Source/core/bridge triage:
- `source-facing`: Lemma 17.29.2 for `TopCat.Sheaf`;
- `core/canonical`: `SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_comp`;
- `bridge/view`: the identification of the opens-site restriction functor with
  `SheafOfModules.restrictScalars (ringSheafMap varphi)`.
-/

/- Lemma 17.29.2: the composite of differential operators of orders `k` and `k'` between sheaves
of `\mathcal O_2`-modules is the opens-site specialization of the site-level composition theorem
`SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_comp`. -/
recall SheafOfModules.RingedSite.isDifferentialOperatorOfOrder_comp

end

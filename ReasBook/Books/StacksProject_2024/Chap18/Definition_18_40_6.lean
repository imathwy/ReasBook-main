import Mathlib.Tactic.Recall
import stacks_project.Chap18.Definition_18_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

end CategoryTheory

/- Domain-style sampling for Definition 18.40.6:
- primary domain: locally ringed Grothendieck sites and their site-presented ringed topoi;
- sampled relevant declarations:
  `CategoryTheory.IsLocallyRingedSite`,
  `CategoryTheory.oneNeverZeroEqualizerMap`,
  `CategoryTheory.instIsLocallyRingedSiteOfConditions`,
  `CategoryTheory.ringed_site_local_unit_tfae`;
- owner abstraction: the chapter owner is `CategoryTheory.IsLocallyRingedSite`, introduced in
  `Definition_18_40_4`;
- primitive data: the empty-equalizer isomorphism from `18.40.2.1` and the local unit dichotomy;
- derived API: the site-presented topos reading of the same owner, and TFAE reformulations of the
  local unit dichotomy.

Source/core/bridge triage:
- `source-facing`: the Stacks definition that a site-presented ringed topos is locally ringed;
- `core/canonical`: `CategoryTheory.IsLocallyRingedSite`;
- `bridge/view`: the observation that for a presented topos `(\mathit{Sh}(\mathcal C), \mathcal O)`,
  no second owner beyond the presenting site predicate is needed.

The reusable auxiliary owner `CategoryTheory.HasLocalUnitDichotomy` already lives in
`Definition_18_40_4`, so this numbered item is recall-only: it reuses the existing owner
`CategoryTheory.IsLocallyRingedSite` instead of introducing parallel `IsLocallyRingedSite` or
`IsLocallyRingedTopos` declarations. -/

/- Definition 18.40.6: a ringed topos `(\mathit{Sh}(\mathcal C), \mathcal O)` is locally ringed
exactly when the presenting ringed site `(\mathcal C, \mathcal O)` satisfies the canonical chapter
owner predicate `CategoryTheory.IsLocallyRingedSite`. -/
recall CategoryTheory.IsLocallyRingedSite

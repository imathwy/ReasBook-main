import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite

variable (X : RingedSite.{u, v}) (U : X)

/- Domain-style sampling for Definition 18.19.1:
- primary domain: localization of a ringed site to the slice site over an object;
- sampled owner declarations:
  `RingedSite.ofRingSheaf`,
  `GrothendieckTopology.over`,
  `Sheaf.over`;
- best owner abstraction: the source-facing owner `RingedSite.localization`, implemented as the
  thin source wrapper around the chapter owner `RingedSite.ofRingSheaf` on the slice topology and
  restricted structure sheaf;
- primitive data: the slice topology `X.siteTopology.over U` and the restricted ring sheaf
  `X.structureSheaf.over U`;
- derived API: the localized module pushforward and adjunction owners
  `SheafOfModules.pushforwardOver U` and `SheafOfModules.overPushforwardOverAdj U`.

Source/core/bridge triage:
- `source-facing`: `RingedSite.localization`;
- `core/canonical`: `RingedSite.ofRingSheaf`, `GrothendieckTopology.over`, and `Sheaf.over`;
- `bridge/view`: the later module-theoretic localization owners built on the same slice site.
-/
/-- Definition 18.19.1: the localization of a ringed site `(\\mathcal C, \\mathcal O)` at an
object `U` is the slice ringed site `(\\mathcal C/U, \\mathcal O_U)`. -/
@[stacks 04IX]
abbrev localization : RingedSite.{max u v, v} :=
  RingedSite.ofRingSheaf (X.siteTopology.over U) (X.structureSheaf.over U)

end RingedSite

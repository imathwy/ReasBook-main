import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v

namespace RingedSite

variable (X : RingedSite.{u, v}) (U : X)

/-- Definition 18.19.1: the localization of a ringed site `(\\mathcal C, \\mathcal O)` at an
object `U` is the slice ringed site `(\\mathcal C/U, \\mathcal O_U)`. -/
def localization : RingedSite.{max u v, v} where
  carrier := Over U
  str := inferInstance
  siteTopology := X.siteTopology.over U
  structureSheaf := X.structureSheaf.over U

-- Proof sketch: `localization X U` is defined by specifying its carrier to be `Over U`, so
-- this is the corresponding definitional identification recorded as a theorem-level API.
/-- The underlying category of the localized ringed site `X.localization U` is the slice
category `Over U`. -/
theorem localization_carrier :
    (X.localization U).carrier = Over U := rfl

-- Proof sketch: `localization X U` is defined using the restricted structure sheaf
-- `X.structureSheaf.over U`, so this is the defining description of its structure sheaf.
/-- The structure sheaf on `X.localization U` is the restricted sheaf `\mathcal O_U`. -/
theorem localization_structureSheaf :
    (X.localization U).structureSheaf = X.structureSheaf.over U := rfl

/- Companion recall: restriction of `\mathcal O_X`-modules to the slice ringed site
`X.localization U` is the canonical pushforward along the identity on `X.structureSheaf.over U`.
The right adjoint back to `X` and the adjunction itself are the canonical mathlib constructions
`SheafOfModules.pushforwardOver U` and `SheafOfModules.overPushforwardOverAdj U`. -/

end RingedSite

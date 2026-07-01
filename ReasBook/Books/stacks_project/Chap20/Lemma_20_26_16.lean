import Mathlib
import stacks_project.Chap17.Definition_17_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasProjectiveResolutions (RingedSpace.Modules X)]

/- Domain-style sampling for Lemma 20.26.16:
- primary domain: flat sheaves of modules on a ringed space and the first left-derived tensor
  functor on the ambient monoidal abelian category `(RingedSpace.Modules X)`;
- inspected owner declarations:
  `SheafOfModules.IsFlat`,
  `CategoryTheory.Tor`,
  `CategoryTheory.isZero_Tor_succ_of_projective`;
- best owner abstraction: flatness is already owned by `SheafOfModules.IsFlat`, while the Tor side
  of the criterion is already owned by the canonical derived functor `CategoryTheory.Tor` on
  `(RingedSpace.Modules X)`; this item should therefore stay a source-facing criterion theorem and not
  introduce a parallel local Tor owner;
- primitive data: the module sheaf `ℱ : (RingedSpace.Modules X)`;
- derived API: the vanishing criterion `∀ 𝒢, IsZero (((Tor (RingedSpace.Modules X) 1).obj ℱ).obj 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the flatness criterion stated as vanishing of `Tor₁`;
- `core/canonical`: `SheafOfModules.IsFlat` and `CategoryTheory.Tor`;
- `bridge/view`: the specialization of those owners to the ringed-space module category
  `(RingedSpace.Modules X)`. -/

-- Proof sketch: if `ℱ` is flat, then tensoring with `ℱ` is exact, so its first left derived
-- functor vanishes and hence `Tor₁` is zero against every `𝒢`. Conversely, apply the long exact
-- `Tor` sequence to a short exact sequence `0 ⟶ 𝒢 ⟶ ℋ ⟶ 𝒬 ⟶ 0`; vanishing of `Tor₁(ℱ, 𝒬)` forces
-- tensoring with `ℱ` to preserve monomorphisms, which is the flatness criterion.
/-- Lemma 20.26.16: an `\mathcal O_X`-module `\mathcal F` on a ringed space `(X, \mathcal O_X)`
is flat if and only if `\operatorname{Tor}_1^{\mathcal O_X}(\mathcal F, \mathcal G)` vanishes for
every `\mathcal O_X`-module `\mathcal G`. -/
theorem isFlat_iff_isZero_tor_one
    (ℱ : (RingedSpace.Modules X)) :
    ℱ.IsFlat ↔
      ∀ 𝒢 : (RingedSpace.Modules X), IsZero (((Tor (RingedSpace.Modules X) 1).obj ℱ).obj 𝒢) := sorry

end AlgebraicGeometry.RingedSpace

import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_13
import StacksProject_2024.Chap17.Definition_17_17_3
import StacksProject_2024.Chap17.Lemma_17_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact
open AlgebraicGeometry

universe u

/- Domain-style sampling for Lemma 17.17.9:
- primary domain: flatness propagation in short exact sequences of sheaves of modules on a ringed
  space;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₂`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₁`,
  `SheafOfModules.isFlat_of_stalkwise`,
  `SheafOfModules.isFlat_stalk`,
  `SheafOfModules.flat_at`;
  `S : ShortComplex (RingedSpace.Modules X)`, with the Chapter 10 owner theorems applied to the
  canonical stalk short complex `RingedSpace.stalkShortComplex S x`;
- primitive data: the short complex `S` and its short exactness proof `hS`;
- derived API: the stalkwise companion lemmas `flat_at_X₂` and `flat_at_X₁`.

Source/core/bridge triage:
- `source-facing`: Lemma 17.17.9 asserts global flatness propagation for a short exact sequence of
  `\mathcal O_X`-modules;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat X.sheaf` together with the module-theoretic
  owners `CategoryTheory.ShortComplex.ShortExact.flat_X₂` and `flat_X₁`;
- `bridge/view`: stalkwise flatness, used only to pass between the global owner and the stalk short
  complexes. -/

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable {S : ShortComplex (RingedSpace.Modules X)}

-- Proof sketch: use the canonical global owner `SheafOfModules.RingedSite.IsFlat X.sheaf` and
-- prove stalkwise flatness of `S.X₂`. For each `x : X`, the stalk short complex is short exact;
-- apply the module-theoretic owner theorem `CategoryTheory.ShortComplex.ShortExact.flat_X₂` to the
-- stalk modules of `S.X₁`, `S.X₂`, and `S.X₃`.
/-- Lemma 17.17.9 (1): in a short exact sequence of `\mathcal O_X`-modules on a ringed space, if
the left and right terms are flat, then the middle term is flat. -/
theorem isFlat_X₂ (hS : S.ShortExact)
    (h₁ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₁)
    (h₃ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₃) :
    SheafOfModules.RingedSite.IsFlat X.sheaf S.X₂ := by
  letI := h₁
  letI := h₃
  refine isFlat_of_stalkwise S.X₂ ?_
  intro x
  letI : Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat S.X₁ x) := isFlat_stalk x
  letI : Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat S.X₃ x) := isFlat_stalk x
  simpa [RingedSpace.stalkShortComplex] using flat_X₂ (hS.stalkShortComplex x)

-- Proof sketch: apply `isFlat_X₂` stalkwise to the short exact stalk complex induced by `hS`, then
-- project back to the pointwise source-facing predicate `flat_at`.
/-- Companion bridge: under the hypotheses of `isFlat_X₂`, the middle term is flat at every
point. -/
theorem flat_at_X₂ (hS : S.ShortExact)
    (h₁ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₁)
    (h₃ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₃) :
    ∀ x : X, S.X₂.flat_at x := by
  letI := isFlat_X₂ hS h₁ h₃
  intro x
  simpa [flat_at] using isFlat_stalk x

-- Proof sketch: again use the global flatness owner and check stalkwise flatness. For each point,
-- pass to the induced short exact sequence on stalks and apply the module-theoretic owner theorem
-- `CategoryTheory.ShortComplex.ShortExact.flat_X₁`.
/-- Lemma 17.17.9 (2): in a short exact sequence of `\mathcal O_X`-modules on a ringed space, if
the middle and right terms are flat, then the left term is flat. -/
theorem isFlat_X₁ (hS : S.ShortExact)
    (h₂ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₂)
    (h₃ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₃) :
    SheafOfModules.RingedSite.IsFlat X.sheaf S.X₁ := by
  letI := h₂
  letI := h₃
  refine isFlat_of_stalkwise S.X₁ ?_
  intro x
  letI : Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat S.X₂ x) := isFlat_stalk x
  letI : Module.Flat (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat S.X₃ x) := isFlat_stalk x
  simpa [RingedSpace.stalkShortComplex] using flat_X₁ (hS.stalkShortComplex x)

-- Proof sketch: derive the stalkwise statement from the global owner theorem `isFlat_X₁` via the
-- canonical projection `isFlat_stalk`.
/-- Companion bridge: under the hypotheses of `isFlat_X₁`, the left term is flat at every point. -/
theorem flat_at_X₁ (hS : S.ShortExact)
    (h₂ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₂)
    (h₃ : SheafOfModules.RingedSite.IsFlat X.sheaf S.X₃) :
    ∀ x : X, S.X₁.flat_at x := by
  letI := isFlat_X₁ hS h₂ h₃
  intro x
  simpa [flat_at] using isFlat_stalk x

end SheafOfModules

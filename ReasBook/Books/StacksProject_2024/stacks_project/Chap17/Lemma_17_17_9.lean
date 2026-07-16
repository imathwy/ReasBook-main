import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_13
import StacksProject_2024.stacks_project.Chap17.Definition_17_17_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_17_3
import StacksProject_2024.stacks_project.Chap17.Lemma_17_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ShortComplex.ShortExact
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

universe u

/- Domain-style sampling for Lemma 17.17.9:
- primary domain: flatness propagation in short exact sequences of sheaves of modules on a ringed
  space;
- inspected owner declarations:
  `SheafOfModules.IsFlat`,
  `SheafOfModules.isFlat_stalk`,
  `SheafOfModules.isFlat_of_stalkwise`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₂`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₁`,
  `RingedSpace.stalkShortComplex`,
  `SheafOfModules.flat_at`;
- best owner abstraction: the chapter owner for global flatness on ringed spaces is
  `SheafOfModules.IsFlat`, and the short-exact propagation step is owned stalkwise by
  `CategoryTheory.ShortComplex.ShortExact.flat_X₂` and `flat_X₁` on the canonical stalk complex
  `stalkShortComplex S x`;
- primitive data: the short complex `S` and its short exactness proof `hS`;
- derived API: the pointwise companion lemmas `flat_at_X₂` and `flat_at_X₁`.

Source/core/bridge triage:
- `source-facing`: the two directional clauses of the Stacks-project ringed-space lemma;
- `core/canonical`: `SheafOfModules.IsFlat` together with the module-theoretic owner theorems
  `CategoryTheory.ShortComplex.ShortExact.flat_X₂` and `flat_X₁`;
- `bridge/view`: the existing chapter bridge theorems `isFlat_stalk`, `isFlat_of_stalkwise`, and
  the pointwise predicate `flat_at`.

This file should therefore keep only the source-facing ringed-space wrappers, with the actual
flatness propagation delegated to the existing owner theorems on stalk-module short complexes.
-/

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable {S : ShortComplex (RingedSpace.Modules X)}

-- Proof sketch: prove stalkwise flatness of `S.X₂` and then rebuild the global owner via
-- `isFlat_of_stalkwise`. At each point `x`, apply the module-theoretic owner theorem
-- `flat_X₂` to the canonical stalk short complex `stalkShortComplex S x`.
/-- Lemma 17.17.9 (1): in a short exact sequence of `\mathcal O_X`-modules on a ringed space, if
the left and right terms are flat, then the middle term is flat. -/
theorem isFlat_X₂ (hS : S.ShortExact)
    (h₁ : S.X₁.IsFlat)
    (h₃ : S.X₃.IsFlat) :
    S.X₂.IsFlat := by
  refine isFlat_of_stalkwise S.X₂ ?_
  intro x
  letI : S.X₁.flat_at x := by
    simpa [flat_at] using isFlat_stalk h₁ x
  letI : S.X₃.flat_at x := by
    simpa [flat_at] using isFlat_stalk h₃ x
  simpa [RingedSpace.stalkShortComplex] using flat_X₂ (hS.stalkShortComplex x)

-- Proof sketch: again prove stalkwise flatness, this time applying the module-theoretic owner
-- theorem `flat_X₁` to the canonical stalk short complex.
/-- Lemma 17.17.9 (2): in a short exact sequence of `\mathcal O_X`-modules on a ringed space, if
the middle and right terms are flat, then the left term is flat. -/
theorem isFlat_X₁ (hS : S.ShortExact)
    (h₂ : S.X₂.IsFlat)
    (h₃ : S.X₃.IsFlat) :
    S.X₁.IsFlat := by
  refine isFlat_of_stalkwise S.X₁ ?_
  intro x
  letI : S.X₂.flat_at x := by
    simpa [flat_at] using isFlat_stalk h₂ x
  letI : S.X₃.flat_at x := by
    simpa [flat_at] using isFlat_stalk h₃ x
  simpa [RingedSpace.stalkShortComplex] using flat_X₁ (hS.stalkShortComplex x)

/-- Companion bridge: under the hypotheses of `isFlat_X₂`, the middle term is flat at every
point. -/
theorem flat_at_X₂ (hS : S.ShortExact)
    (h₁ : S.X₁.IsFlat)
    (h₃ : S.X₃.IsFlat) :
    ∀ x : X, S.X₂.flat_at x := by
  intro x
  simpa [flat_at] using isFlat_stalk (isFlat_X₂ hS h₁ h₃) x

/-- Companion bridge: under the hypotheses of `isFlat_X₁`, the left term is flat at every point. -/
theorem flat_at_X₁ (hS : S.ShortExact)
    (h₂ : S.X₂.IsFlat)
    (h₃ : S.X₃.IsFlat) :
    ∀ x : X, S.X₁.flat_at x := by
  intro x
  simpa [flat_at] using isFlat_stalk (isFlat_X₁ hS h₂ h₃) x

end SheafOfModules

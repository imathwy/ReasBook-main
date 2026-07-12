import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_13_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open ConvexERealFunction
open scoped Rockafellar

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

local instance : HasPairing E E ℝ := instHasPairingOfHasLinearPairing
local instance : HasPairing E E (WithTopBot ℝ) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.4.1 says that closed proper convex functions related by Fenchel
  conjugation have the same rank.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.rank`, `convexConjugate`, and the Chapter 3 owner predicate
  `Function.IsClosedProperConvex`.
- `bridge/view`: the textbook phrase "conjugate to each other" is rendered canonically by the
  direct comparison between `f` and its Fenchel conjugate `convexConjugate f`.

Domain-style sampling used here:
- `Function.rank` and `Function.rank_eq` from `Definition_8_9_2`;
- `Function.IsClosedProperConvex` from `Text_12_3_6`;
- `lineality_convexConjugate_eq_ambientDim_sub_effectiveDomain_affineDim` from `Theorem_13_4`;
- `effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality` from `Theorem_13_4`.

Layer target: `source-facing`, stated directly in the canonical conjugation and rank API without
introducing an auxiliary wrapper for conjugate pairs or a parallel closed/proper/convex hypothesis
bundle.
-/

-- Proof sketch: rewrite both sides using `Function.rank_eq`, then apply the two
-- dimension formulas already exposed by Theorem 13.4 for `dom f⋆` and
-- `lineality[ℝ](f⋆)`. The
-- resulting arithmetic identity is exactly `rank[ℝ](f)`.
/-- Corollary 13.4.1: a closed proper convex function and its Fenchel conjugate have the same
rank. -/
theorem rank_convexConjugate_eq_rank (f : E → WithTopBot ℝ) (hf : IsClosedProperConvex[ℝ] f) :
    rank[ℝ]((f⋆ : E → WithTopBot ℝ)) = rank[ℝ](f) := by
  rw [Function.rank_eq (𝕜 := ℝ) (f := (f⋆ : E → WithTopBot ℝ)),
    Function.rank_eq (𝕜 := ℝ) (f := f)]
  rw [effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality f hf]
  rw [lineality_convexConjugate_eq_ambientDim_sub_effectiveDomain_affineDim f hf.convex hf.proper]
  omega

end

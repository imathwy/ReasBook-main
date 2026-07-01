import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.6 states that the convex hull of a family of functions is the
  greatest convex function lying below every member of the family.
- `core/canonical`: the owner abstractions already available in this section are
  `Function.convexHull : (E → WithBotTop 𝕜) → E → WithBotTop 𝕜` and
  `Function.IsConvex : (E → WithBotTop 𝕜) → Prop`.
- `bridge/view`: the family statement is expressed directly on the canonical owner
  `conv(⨅ i, f i)` and the canonical convex-minorant owner
  `Function.convexMinorants (⨅ i, f i)`.
- Primitive data vs derived API: the family `f` is primitive; convexity of `conv(⨅ i, f i)` and
  the universal maximality property are derived. The pointwise convexity and minorant
  consequences are just projections of the canonical single-function maximality owner theorem
  specialized to `⨅ i, f i`.

Domain-style sampling used here:
- `Function.convexHull`;
- `Function.isGreatest_conv_minorant_of_isConvex`;
- `Function.IsConvex`;
- `Function.convexMinorants`;
- `IsGreatest`;
- Layer target: `bridge/view`; the source-facing family statement is retained as a direct
  specialization of the canonical single-function hull owner theorem.
- Ambient minimization: the theorem only uses the chapter owner constructions on
  `WithBotTop 𝕜`-valued
  functions and pointwise order against a family infimum, so the canonical ambient level is the
  same arbitrary `𝕜`-module `E` already used by `Function.convexHull` and
  `conv(⨅ i, f i)`.
-/
section

variable {E : Type u} {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

namespace Function

-- Proof sketch: specialize the canonical single-function theorem
-- `isGreatest_conv_minorant` to `g := ⨅ i, f i`.
/-- Text 5.5.6: `conv {f_i | i ∈ I}`, represented by `conv(⨅ i, f i)`, is the greatest convex
minorant of the family infimum `⨅ i, f i`. -/
theorem isGreatest_conv_iInf_minorant
    {ι : Sort v} (f : ι → E → WithBotTop 𝕜) :
    IsGreatest (convexMinorants (⨅ i, f i)) (conv(⨅ i, f i)) := by
  simpa using isGreatest_conv_minorant (g := (⨅ i : ι, f i))

end Function

end

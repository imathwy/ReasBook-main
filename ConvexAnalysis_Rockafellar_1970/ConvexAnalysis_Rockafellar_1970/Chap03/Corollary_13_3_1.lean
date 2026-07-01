import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_3_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

universe u v w

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommMonoid EStar] [Module 𝕜 EStar]
variable [HasLinearPairing E EStar 𝕜] [HasContinuousPairing E EStar 𝕜]

local notation "IsCofinite[" 𝕜 "]" => Function.IsCofinite (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.3.1 characterizes when the Fenchel conjugate `f*` of a closed
  convex function is finite everywhere.
- `core/canonical`: the project owner abstractions already present are `convexConjugate` for the
  conjugate, written on the theorem surface by the chapter notation `f⋆`, and
  `Function.IsCofinite` for Rockafellar's co-finite condition.
- `bridge/view`: on the chapter-facing codomain `WithBotTop 𝕜`, the textbook phrase
  "`f*` is finite at every point" is rendered intrinsically by the pointwise strict bounds
  `⊥ < f⋆ xStar` and `f⋆ xStar < ⊤` on the paired dual carrier `EStar`. This implies
  `dom(f⋆) = Set.univ`, but the converse alone would allow the spurious value `-∞`.

Domain-style sampling used here:
- `convexConjugate` and the chapter notation `f⋆`;
- `Function.IsCofinite`;
- `Function.IsClosedProperConvex`;
- `Function.isProper_iff`.
- Theorem 12.2's owner equivalence `Function.IsConvex.convexConjugate_isProper_iff`.

Primitive data vs derived API:
- primitive inputs: the function `f` together with the source hypotheses that `f` is closed and
  convex;
- derived API: the equivalence between pointwise finite-valuedness of the conjugate and
  co-finiteness.

Layer target: `source-facing`, stated directly in the canonical project language of Fenchel
conjugation and the already introduced co-finite predicate, without adding a surrogate domain
wrapper. The project owner `Function.IsClosedProperConvex` is deliberately not used as the public
hypothesis package here, because it would strengthen the source-facing statement by adding
properness; `Function.IsCofinite` remains the canonical owner on the conclusion side.
-/

/- `EStar` carries no topological assumptions here; the theorem surface uses only the
paired-linear owner layer.
-/

-- Proof sketch: first translate textbook finiteness of `f*` into the intrinsic pointwise bounds
-- `⊥ < f⋆ xStar ∧ f⋆ xStar < ⊤`, not merely the condition `< ⊤`. The support-function description
-- of the finite-value set
-- `dom(f⋆)` and the recession characterization from
-- Text 13.3.1 identify the everywhere-defined part with co-finiteness, while the lower bound
-- `⊥ < f⋆ xStar` rules out the spurious `-∞` case and hence matches the textbook meaning of
-- "finite".
/-- Corollary 13.3.1: for a closed convex function on a finite-dimensional topological vector space
over an ordered scalar field, paired continuously and linearly with a dual carrier `EStar`, the
Fenchel conjugate `f⋆` takes finite values at every point if and only if the function is
co-finite. -/
theorem convexConjugate_finite_everywhere_iff_isCofinite
    (f : E → WithBotTop 𝕜) (hf_convex : f.IsConvex 𝕜) (hf_closed : LowerSemicontinuous f) :
    (∀ xStar : EStar, ⊥ < f⋆ xStar ∧ f⋆ xStar < ⊤) ↔ IsCofinite[𝕜] f := sorry

end

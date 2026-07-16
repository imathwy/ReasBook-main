import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_17_2_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

open Bornology Function
open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [TopologicalSpace E]
variable [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {S : Set E} {f : E → 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 17.2.3 fixes a nonempty compact set `S`, a continuous
  scalar-valued function on `S`, lets `h` be the Definition 17.2.2 restricted conjugate of that
  branch, and asserts that `h` is finite everywhere and that `h⋆` is the convex hull of the
  extension by `+∞` off `S`.
- `core/canonical`: the relevant owner declarations already present in the project are
  `convexConjugateOn`, `toWithBotTopOn`, and `conv(·)`.
- `bridge/view`: the source-facing restricted conjugate owner
  `convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))` is canonically identified with the
  ambient conjugate of the extension-by-`+∞` owner `toWithBotTopOn f S`.

Domain-style sampling used here:
- `convexConjugateOn` from `Definition_17_2_2`;
- `convexConjugateOn_eq_convexConjugate_extendByTop` from `Definition_17_2_2`;
- `toWithBotTopOn` from `Remark_4_4_5`;
- `conv_toWithTopBotOn_isClosedProperConvex_of_nonempty_of_isCompact`
  from `Corollary_17_2_1`;

Primitive data vs derived API:
- primitive source data: the set `S` and the scalar-valued branch `f`;
- source-facing owner: the restricted conjugate
  `convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))`;
- canonical bridge object: the ambient extension `toWithBotTopOn f S`;
- derived API: pointwise finiteness and continuity of the restricted conjugate, plus the
  conjugacy identity with `conv(toWithBotTopOn f S)`.

Layer target:
- primary owner surface: compact-domain (`IsCompact`) statements on
  `convexConjugateOn`, matching the intrinsic compactness layer already present upstream;
- bridge surface: closed-and-bounded statements only as thin companions in proper pseudo-metric
  spaces, derived from the compact owner via
  `Metric.isCompact_iff_isClosed_bounded`.
-/

-- Proof sketch: bridge the source-facing owner
-- `convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))`
-- to the ambient conjugate of the `⊤`-extension of `f|S`. Corollary 17.2.1 shows that
-- `conv(toWithBotTopOn f S)` is closed proper convex, so the Chapter 12/13 conjugacy API applied
-- to that ambient bridge yields pointwise scalar-valuedness of the restricted conjugate.
/-- Proposition 17.2.3, intrinsic compact form: if `S` is nonempty compact and `f` is continuous
on `S`,
then the Definition 17.2.2 restricted conjugate `h` of the scalar-valued branch `f|S` is finite at
every point. -/
theorem convexConjugateOn_realValued_everywhere_of_nonempty_of_isCompact_of_continuousOn
    (hS_nonempty : S.Nonempty) (hS_compact : IsCompact S)
    (hf : ContinuousOn f S) (y : E) :
    ∃ r : 𝕜, convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜)) y = r := sorry

-- Proof sketch: the source-facing restricted conjugate owner is canonically the ambient conjugate
-- of the extension-by-`⊤` function, hence convex. If `S = ∅`, this restricted conjugate is the
-- constant `⊥` function, so continuity is immediate. Otherwise the previous theorem supplies the
-- everywhere scalar-valued hypothesis required by the Chapter 10 continuity owner theorem.
/-- The restricted conjugate is continuous everywhere under compact-domain hypotheses.
When `S = ∅`, it is the constant `⊥` function. -/
theorem
    continuous_convexConjugateOn_of_isCompact_of_continuousOn
    (hS_compact : IsCompact S)
    (hf : ContinuousOn f S)
    : Continuous ((convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))) : E → WithBotTop 𝕜) := sorry

-- Proof sketch: use `convexConjugateOn_eq_convexConjugate_extendByTop` to identify the
-- source-facing restricted conjugate with the ambient conjugate of the extension-by-`⊤` function.
-- If `S = ∅`, that restricted conjugate is constant `⊥`, hence its conjugate is constant `⊤`,
-- which agrees with `conv(toWithBotTopOn f S)`. Otherwise Corollary 17.2.1 makes
-- `conv(toWithBotTopOn f S)` closed proper convex, so the Chapter 12 biconjugacy theorem yields
-- the textbook identity `h⋆ = conv f`.
/-- The Fenchel conjugate of the restricted conjugate equals the convex hull of the extension of
`f` by `+∞` outside `S` under compact-domain hypotheses. When `S = ∅`, both sides
are the constant `⊤` function. -/
theorem
    convexConjugateOn_conjugate_eq_conv_toWithBotTopOn_of_isCompact_of_continuousOn
    [OrderTopology 𝕜] [HasPairingSwap E E 𝕜]
    (hS_compact : IsCompact S)
    (hf : ContinuousOn f S)
    : ((((convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))) : E → WithBotTop 𝕜)⋆)) =
        conv(toWithBotTopOn f S) := sorry

end

section

open Bornology Function
open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [PseudoMetricSpace E] [T2Space E] [ProperSpace E]
variable [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {S : Set E} {f : E → 𝕜}

/-- Proper-space bridge form of Proposition 17.2.3: nonempty closed bounded sets are compact, so
the compact-domain finite-valued statement applies directly. -/
theorem convexConjugateOn_realValued_everywhere_of_nonempty_of_isClosed_of_isBounded_of_continuousOn
    (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_bounded : IsBounded S)
    (hf : ContinuousOn f S) (y : E) :
    ∃ r : 𝕜, convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜)) y = r := by
  have hS_compact : IsCompact S :=
    (Metric.isCompact_iff_isClosed_bounded).2 ⟨hS_closed, hS_bounded⟩
  exact convexConjugateOn_realValued_everywhere_of_nonempty_of_isCompact_of_continuousOn
    (S := S) (f := f) hS_nonempty hS_compact hf y

/-- Proper-space bridge form: continuity of the restricted conjugate from closed bounded domain
hypotheses follows by compactness reduction. -/
theorem
    continuous_convexConjugateOn_of_isClosed_of_isBounded_of_continuousOn
    (hS_closed : IsClosed S) (hS_bounded : IsBounded S)
    (hf : ContinuousOn f S)
    : Continuous ((convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))) : E → WithBotTop 𝕜) := by
  have hS_compact : IsCompact S :=
    (Metric.isCompact_iff_isClosed_bounded).2 ⟨hS_closed, hS_bounded⟩
  exact continuous_convexConjugateOn_of_isCompact_of_continuousOn
    (S := S) (f := f) hS_compact hf

/-- Proper-space bridge form: the conjugacy identity from closed bounded domain hypotheses follows
from the compact-domain owner theorem. -/
theorem
    convexConjugateOn_conjugate_eq_conv_toWithBotTopOn_of_isClosed_of_isBounded_of_continuousOn
    [OrderTopology 𝕜] [HasPairingSwap E E 𝕜]
    (hS_closed : IsClosed S) (hS_bounded : IsBounded S)
    (hf : ContinuousOn f S)
    : ((((convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))) : E → WithBotTop 𝕜)⋆)) =
        conv(toWithBotTopOn f S) := by
  have hS_compact : IsCompact S :=
    (Metric.isCompact_iff_isClosed_bounded).2 ⟨hS_closed, hS_bounded⟩
  exact convexConjugateOn_conjugate_eq_conv_toWithBotTopOn_of_isCompact_of_continuousOn
    (S := S) (f := f) hS_compact hf

end

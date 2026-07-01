import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_3_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.4.1 says that a finite convex function on `R^n`, hence an ordinary
  real-valued convex function on all of `R^n`, is Lipschitzian on every bounded subset and
  therefore uniformly continuous there. As elsewhere in the chapter, the coordinate model is
  refined to the canonical owner layer of arbitrary finite-dimensional real normed spaces.
- `core/canonical`: the bounded-subset extraction is owner-primitive at the level
  `LocallyLipschitz f`; convexity enters only as the upstream bridge
  `ConvexOn.locallyLipschitz`.
- `bridge/view`: the source wording "finite convex function on `R^n`" is represented by
  `ConvexOn ℝ univ f`; bounded subsets are handled by compactness of `closure S` in proper
  metric spaces, then restriction back to `S`.

Domain-style sampling used here:
- `LocallyLipschitz.exists_lipschitzOnWith_of_isBounded`;
- `ConvexOn.locallyLipschitz`;
- `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`;
- `LipschitzOnWith.uniformContinuousOn`.

Primitive data vs derived API:
- primitive bounded-set theorem input: `LocallyLipschitz f` and `Bornology.IsBounded S`;
- source-facing convex input: `ConvexOn ℝ univ f`, used only to derive local Lipschitz regularity;
- intermediate owner data: local Lipschitz regularity on the ambient space, then compactness of
  `closure S`;
- derived API: existence of a Lipschitz constant for `f` on `S`, and the resulting uniform
  continuity on `S`.

Layer target: this item is `source-facing`, but its clean main statement is the canonical
existential-`LipschitzOnWith` bounded-set extraction from `LocallyLipschitz`, with
`ConvexOn ℝ univ f` as a downstream bridge input.

Scalar/codomain design decision:
- the primitive bounded-set theorem is generalized to arbitrary metric codomain `Y`;
- the source-facing convex corollaries intentionally keep `f : E → ℝ`, with
  `[NormedSpace ℝ E] [FiniteDimensional ℝ E]` inherited from `ConvexOn.locallyLipschitz`.
-/

namespace LocallyLipschitz

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [ProperSpace X]

/-- Core owner theorem: on proper metric domains, local Lipschitz regularity implies
Lipschitz control on every bounded subset. -/
theorem exists_lipschitzOnWith_of_isBounded
    {f : X → Y} (hf : LocallyLipschitz f)
    {S : Set X} (hS_bounded : Bornology.IsBounded S) :
    ∃ α : NNReal, LipschitzOnWith α f S := by
  have hS_compact_closure : IsCompact (closure S) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hS_bounded.closure
  have hlocal : LocallyLipschitzOn (closure S) f :=
    hf.locallyLipschitzOn
  rcases LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS_compact_closure hlocal with
    ⟨α, hα⟩
  exact ⟨α, hα.mono subset_closure⟩

end LocallyLipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace ConvexOn

/-- Theorem 10.4.1 in canonical owner form: a finite convex function on a finite-dimensional real
normed space, represented by `ConvexOn ℝ univ f`, is Lipschitzian on every bounded subset. -/
theorem exists_lipschitzOnWith_of_isBounded_univ
    {f : E → ℝ} (hf_convex : ConvexOn ℝ univ f)
    {S : Set E} (hS_bounded : Bornology.IsBounded S) :
    ∃ α : NNReal, LipschitzOnWith α f S := by
  exact hf_convex.locallyLipschitz.exists_lipschitzOnWith_of_isBounded hS_bounded

/-- A finite convex function on a finite-dimensional real normed space is uniformly continuous on
every bounded subset. -/
-- Proof sketch: extract a bounded-set `LipschitzOnWith` constant from the first theorem and apply
-- the owner theorem `LipschitzOnWith.uniformContinuousOn`.
theorem uniformContinuousOn_of_isBounded_univ
    {f : E → ℝ} (hf_convex : ConvexOn ℝ univ f)
    {S : Set E} (hS_bounded : Bornology.IsBounded S) :
    UniformContinuousOn f S := by
  rcases hf_convex.exists_lipschitzOnWith_of_isBounded_univ hS_bounded with
    ⟨α, hα⟩
  exact hα.uniformContinuousOn

end ConvexOn

end

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_10_4_1 (from Chap02) -/
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

/-! ### Theorem_10_4 (from Chap02) -/
noncomputable section

open scoped Rockafellar

variable {E : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: this file exposes the compact/closed-bounded existential
  `LipschitzOnWith` consequences on subsets of `riDom(f)` from explicit local-Lipschitz owner input
  on `riDom(f)`.
- `core/canonical`: the owner abstractions are mathlib's relative interior
  `intrinsicInterior ℝ`, the local owner
  predicate `LocallyLipschitzOn`, compactness `IsCompact`, boundedness `Bornology.IsBounded`, and
  the source-facing subset owner `∃ α, LipschitzOnWith α _ _`.
- `bridge/view`: Rockafellar's `ri (dom f)` is represented by `riDom(f)`. The finite branch is
  represented by the chapter owner `Function.realBranch`.

Domain-style sampling used here:
- `Function.realBranch` for finite-value branches of `WithTopBot ℝ`-valued owners;
- `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`;
- `Metric.isCompact_of_isClosed_isBounded`;
- the intrinsic domain owner `riDom(f)` and subset-form owner
  `∃ α : NNReal, LipschitzOnWith α f.realBranch S`.

Primitive data vs derived API:
- core primitive input: local Lipschitz control of `f.realBranch` on `riDom(f)`;
- source-facing bridge input: the function `f` together with explicit local-Lipschitz control on
  `riDom(f)`;
- derived API: compact-subset and closed/bounded-subset existential `LipschitzOnWith`
  consequences on
  `S ⊆ riDom(f)`.

Scalar note:
- the theorem formalizes the extended-real (`WithTopBot ℝ`) convex-analysis branch and its finite
  real branch `f.realBranch : E → ℝ`, so the scalar in `riDom(f)` is part of the mathematical
  owner itself, not proof-local scaffolding.
-/

namespace Function

variable [PseudoMetricSpace E] [AddCommGroup E] [Module ℝ E]

/-- Core owner consequence used in Theorem 10.4: local Lipschitz control of `f.realBranch` on
`riDom(f)` yields an existential `LipschitzOnWith` witness on each compact subset of `riDom(f)`.
-/
theorem lipschitzOn_realBranch_on_compact_subset_riDom_of_locallyLipschitzOn
    {f : E → WithTopBot ℝ}
    (hri_lipschitz : LocallyLipschitzOn (riDom(f)) f.realBranch)
    {S : Set E} (hS_compact : IsCompact S) (hS_subset : S ⊆ riDom(f)) :
    ∃ α : NNReal, LipschitzOnWith α f.realBranch S := by
  exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hS_compact
    (hri_lipschitz.mono hS_subset)

/-- Closed/bounded bridge form of the compact-subset owner consequence above. -/
theorem lipschitzOn_realBranch_on_closed_bounded_subset_riDom_of_locallyLipschitzOn
    {f : E → WithTopBot ℝ} [ProperSpace E]
    (hri_lipschitz : LocallyLipschitzOn (riDom(f)) f.realBranch)
    {S : Set E} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ riDom(f)) :
    ∃ α : NNReal, LipschitzOnWith α f.realBranch S := by
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  exact lipschitzOn_realBranch_on_compact_subset_riDom_of_locallyLipschitzOn
    hri_lipschitz hS_compact hS_subset

end Function

namespace Function

/-- Canonical compact-subset owner consequence of Theorem 10.4: if `S` is compact and
`S ⊆ ri (dom f)`, represented by `riDom(f)`, and local Lipschitz control is known on `riDom(f)`,
then `f.realBranch` is Lipschitzian on `S`.
-/
-- Proof sketch: restrict local Lipschitz control from `riDom(f)` to `S`, then upgrade to an
-- existential `LipschitzOnWith` witness using compactness.
theorem lipschitzOn_realBranch_on_compact_subset_riDom
    {f : E → WithTopBot ℝ}
    (hri_lipschitz : LocallyLipschitzOn (riDom(f)) f.realBranch)
    {S : Set E} (hS_compact : IsCompact S) (hS_subset : S ⊆ riDom(f)) :
    ∃ α : NNReal, LipschitzOnWith α f.realBranch S := by
  exact Function.lipschitzOn_realBranch_on_compact_subset_riDom_of_locallyLipschitzOn
    hri_lipschitz hS_compact hS_subset

/-- Closed/bounded bridge corollary of the compact-subset owner theorem above.
-/
-- Proof sketch: convert the closed bounded hypothesis to compactness and apply the compact-subset
-- owner theorem.
theorem lipschitzOn_realBranch_on_closed_bounded_subset_riDom
    {f : E → WithTopBot ℝ} [ProperSpace E]
    (hri_lipschitz : LocallyLipschitzOn (riDom(f)) f.realBranch)
    {S : Set E} (hS_closed : IsClosed S) (hS_bounded : Bornology.IsBounded S)
    (hS_subset : S ⊆ riDom(f)) :
    ∃ α : NNReal, LipschitzOnWith α f.realBranch S := by
  exact Function.lipschitzOn_realBranch_on_closed_bounded_subset_riDom_of_locallyLipschitzOn
    hri_lipschitz hS_closed hS_bounded hS_subset

end Function

end

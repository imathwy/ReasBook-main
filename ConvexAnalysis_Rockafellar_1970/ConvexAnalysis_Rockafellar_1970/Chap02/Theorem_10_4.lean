import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_3_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_3

-- Declarations for this item will be appended below by the statement pipeline.

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

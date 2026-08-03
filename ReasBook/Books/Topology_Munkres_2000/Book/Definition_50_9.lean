module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.ContinuousMap.CocompactMap

public section

open Filter

/- Definition 50.9. A continuous map tends to infinity when it is a cocompact map. -/
#check CocompactMap

/-- Helper for Definition 50.9: convergence to `atTop` along the cocompact filter means
exceeding every real bound away from a compact set. -/
private lemma Filter.tendsto_cocompact_atTop_iff_exists_compact
    {X : Type*} [TopologicalSpace X] (g : X → ℝ) :
    Tendsto g (cocompact X) atTop ↔
      ∀ r : ℝ, ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, r < g x := by
  -- Translate both filters through their standard compact-complement and open-ray bases.
  rw [Filter.hasBasis_cocompact.tendsto_iff Filter.atTop_basis_Ioi]
  simp only [true_implies, Set.mem_compl_iff, Set.mem_Ioi]

/-- Helper for Definition 50.9: in a proper seminormed additive group, cocompact convergence
is equivalent to divergence of the norm to `atTop`. -/
private lemma Filter.tendsto_cocompact_iff_norm_atTop
    {X E : Type*} [TopologicalSpace X] [SeminormedAddGroup E] [ProperSpace E]
    (g : X → E) :
    Tendsto g (cocompact X) (cocompact E) ↔
      Tendsto (fun x ↦ ‖g x‖) (cocompact X) atTop := by
  -- Properness identifies cocompact and cobounded filters, where the norm criterion is canonical.
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]

/-- A continuous map to a proper seminormed additive group is cocompact exactly when its norm
eventually exceeds every real bound outside a compact subset. Definition 50.9 is the special case
of finite-dimensional Euclidean space. -/
theorem ContinuousMap.tendsto_cocompact_iff_norm_eventually
    {X E : Type*} [TopologicalSpace X] [SeminormedAddGroup E] [ProperSpace E]
    (f : C(X, E)) :
    Tendsto f (cocompact X) (cocompact E) ↔
      ∀ r : ℝ, ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, r < ‖f x‖ := by
  -- First pass to norm divergence, then unpack cocompact convergence on the domain.
  exact (Filter.tendsto_cocompact_iff_norm_atTop f).trans
    (Filter.tendsto_cocompact_atTop_iff_exists_compact fun x ↦ ‖f x‖)

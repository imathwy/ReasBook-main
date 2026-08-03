module

import Topology_Munkres_2000.Book.Lemma_80_2
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting

public section

universe u v w

/-- Theorem 80.3. A surjective covering map from a simply connected space factors
through every surjective covering map of the same base by a surjective covering map. -/
theorem exists_coveringMap_lift {E : Type u} {Y : Type v} {B : Type w}
    [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace B]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace Y] [LocallyPathConnectedSpace B]
    (p : E → B) (hp : IsCoveringMap p) (hp_surjective : Function.Surjective p)
    (r : Y → B) (hr : IsCoveringMap r) (hr_surjective : Function.Surjective r) :
    ∃ q : E → Y, IsCoveringMap q ∧ Function.Surjective q ∧ r ∘ q = p := by
  obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
  obtain ⟨y₀, hy₀⟩ := hr_surjective (p e₀)
  obtain ⟨q, hq, _⟩ :=
    hr.existsUnique_continuousMap_lifts ⟨p, hp.continuous⟩ e₀ y₀ hy₀
  obtain ⟨hq_covering, hq_surjective⟩ :=
    coveringMap_of_comp_right q.continuous hq.2.symm hp hp_surjective hr
  exact ⟨q, hq_covering, hq_surjective, hq.2⟩

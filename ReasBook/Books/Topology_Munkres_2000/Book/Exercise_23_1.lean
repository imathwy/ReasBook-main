module

import Topology_Munkres_2000.Book.Example_23_1.Instances
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.WithTopology

public section

namespace TopologicalSpace

/-- Connectedness for an explicitly selected topology. -/
abbrev IsConnected {X : Type u} (t : TopologicalSpace X) : Prop :=
  ConnectedSpace (WithTopology X t)

/-- The explicit-topology predicate agrees with mathlib's `ConnectedSpace` class. -/
theorem isConnected_iff_connectedSpace {X : Type u} [t : TopologicalSpace X] :
    t.IsConnected ↔ ConnectedSpace X :=
  ⟨fun _ ↦ (WithTopology.ofTopology_surjective t).connectedSpace
      (WithTopology.continuous_ofTopology t),
    fun _ ↦ (WithTopology.toTopology_surjective t).connectedSpace
      (WithTopology.continuous_toTopology t)⟩

end TopologicalSpace

/-- Exercise 23.1 (1): If `t'` is finer than `t`, then connectedness for `t'`
implies connectedness for the coarser topology `t`. -/
theorem connectedSpace_of_finer {X : Type u} (t t' : TopologicalSpace X) (h : t' ≤ t)
    (hc : t'.IsConnected) : t.IsConnected := by
  apply ((WithTopology.toTopology_surjective t).comp
    (WithTopology.ofTopology_surjective t')).connectedSpace
  rw [continuous_def]
  intro s hs
  exact h _ hs

/-- Exercise 23.1 (2): Connectedness for a coarser topology does not in general
imply connectedness for a finer topology. -/
theorem exists_connectedSpace_not_connectedSpace_of_finer :
    ∃ (X : Type) (t t' : TopologicalSpace X),
      t' ≤ t ∧ t.IsConnected ∧ ¬ t'.IsConnected := by
  refine ⟨Fin 2, ⊤, ⊥, bot_le, ?_, ?_⟩
  · infer_instance
  intro h
  have h_inter :
      (({WithTopology.toTopology ⊥ 0} : Set (WithTopology (Fin 2) ⊥)) ∩
        ({WithTopology.toTopology ⊥ 1} : Set (WithTopology (Fin 2) ⊥))).Nonempty := by
    simpa using h.toPreconnectedSpace.isPreconnected_univ
      ({WithTopology.toTopology ⊥ 0} : Set (WithTopology (Fin 2) ⊥))
      ({WithTopology.toTopology ⊥ 1} : Set (WithTopology (Fin 2) ⊥))
      (by trivial) (by trivial)
      (by
        intro x _
        have hx : x.ofTopology = 0 ∨ x.ofTopology = 1 := by omega
        rcases hx with hx | hx
        · left
          simpa using WithTopology.ofTopology_injective _ hx
        · right
          simpa using WithTopology.ofTopology_injective _ hx)
      ⟨WithTopology.toTopology ⊥ 0, by simp⟩
      ⟨WithTopology.toTopology ⊥ 1, by simp⟩
  simp at h_inter

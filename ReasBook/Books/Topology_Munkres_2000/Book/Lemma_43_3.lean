module

public import Mathlib.Topology.Constructions

public section

universe u v

/-- Lemma 43.3: a sequence in a product space converges if and only if each
coordinate sequence converges to the corresponding coordinate. -/
theorem tendsto_pi_sequence_iff {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] (x : ℕ → ∀ i, X i) (a : ∀ i, X i) :
    Filter.Tendsto x Filter.atTop (nhds a) ↔
      ∀ i, Filter.Tendsto (fun n ↦ x n i) Filter.atTop (nhds (a i)) :=
  tendsto_pi_nhds

module

public import Topology_Munkres_2000.Book.Exercise_46_10.CompactExhaustible
public import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Bases

public section

open Set

universe u

/-- A weakly locally compact second-countable space is compactly exhaustible. -/
instance compactlyExhaustibleSpace_of_weaklyLocallyCompact_secondCountable (X : Type u)
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [SecondCountableTopology X] :
    CompactlyExhaustibleSpace X := by
  by_cases hX : (univ : Set X).Nonempty
  · choose x₀ hx₀ using hX
    choose K hKc hxK using fun x : X ↦ exists_compact_mem_nhds x
    rcases TopologicalSpace.countable_cover_nhds
        (fun x ↦ interior_mem_nhds.2 (hxK x)) with ⟨s, hsc, hsU⟩
    have hx₀' : x₀ ∈ ⋃ x ∈ s, interior (K x) := by
      rw [hsU]
      exact hx₀
    simp only [mem_iUnion] at hx₀'
    rcases hx₀' with ⟨x, hxs, _⟩
    obtain ⟨f, hf⟩ := hsc.exists_surjective ⟨x, hxs⟩
    refine ⟨fun n ↦ K (f n), fun n ↦ hKc (f n), ?_⟩
    apply eq_univ_of_forall
    intro y
    have hy : y ∈ ⋃ x ∈ s, interior (K x) := by
      rw [hsU]
      exact mem_univ y
    simp only [mem_iUnion] at hy ⊢
    rcases hy with ⟨x, hxs, hyx⟩
    obtain ⟨n, hn⟩ := hf ⟨x, hxs⟩
    exact ⟨n, hn ▸ hyx⟩
  · refine ⟨fun _ ↦ ∅, fun _ ↦ isCompact_empty, ?_⟩
    simp only [interior_empty, iUnion_empty]
    exact (not_nonempty_iff_eq_empty.mp hX).symm

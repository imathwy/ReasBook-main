module

public import Topology_Munkres_2000.Book.Theorem_50_1.ClosedSubspace

public section

open scoped CoveringDimension

universe u

/-- Helper for Theorem 50.1: a closed subspace of a finite-covering-dimensional space
has finite covering dimension. -/
theorem IsClosed.finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] {Y : Set X}
    (hY : IsClosed Y) (hX : FiniteCoveringDimension X) :
    FiniteCoveringDimension Y := by
  rw [finiteCoveringDimension_iff] at hX ⊢
  obtain ⟨n, hn⟩ := hX
  -- Transfer the selected finite ambient bound through the closed-subtype interface.
  exact ⟨n, hn.closedSubtype hY⟩

namespace HasCoveringDimensionLT

/-- Helper for Theorem 50.1: a strict covering-dimension bound remains valid on a closed
subtype. -/
lemma closedSubtype {X : Type u} [TopologicalSpace X] {Y : Set X} {n : ℕ}
    (hX : HasCoveringDimensionLT X n) (hY : IsClosed Y) :
    HasCoveringDimensionLT Y n := by
  -- At zero, emptiness of the ambient space immediately gives emptiness of the subtype.
  cases n with
  | zero =>
      exact ⟨fun y ↦ hX.false y.1⟩
  | succ n =>
      -- At a successor, transfer the corresponding non-strict bound.
      exact HasCoveringDimensionLE.closedSubtype hX hY

end HasCoveringDimensionLT

/-- Theorem 50.1. The covering dimension of a closed subspace is at most
the covering dimension of the ambient space. -/
theorem IsClosed.coveringDimension_le
    {X : Type u} [TopologicalSpace X] {Y : Set X}
    (hY : IsClosed Y) :
    dim Y ≤ dim X := by
  -- Compare the defining infima by transporting every ambient strict bound to the subtype.
  rw [coveringDimension]
  refine sInf_le_sInf ?_
  intro d hd n hdn
  exact (hd n hdn).closedSubtype hY

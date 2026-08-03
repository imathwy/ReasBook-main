module

public import Topology_Munkres_2000.Book.Exercise_46_10.CompactExhaustible
public import Topology_Munkres_2000.Book.Exercise_46_10.SigmaCompact
public import Topology_Munkres_2000.Book.Exercise_46_10.CompactConvergence

public section

open Set

universe u v

variable (X : Type u)

/- Exercise 46.10 defines local compactness by the condition that every point has a compact
neighborhood. -/
#check WeaklyLocallyCompactSpace

/- Exercise 46.10 defines σ-compactness by a countable family of compact subspaces whose
interiors cover the space. -/
#check CompactlyExhaustibleSpace

/- Exercise 46.10 (a): A locally compact second-countable space is σ-compact in the book's
sense. -/
#check compactlyExhaustibleSpace_of_weaklyLocallyCompact_secondCountable

namespace CompactlyExhaustibleSpace

/-- Exercise 46.10: Compact exhaustibility is equivalent to the conjunction of mathlib's
σ-compactness and weak local compactness. -/
theorem iff_sigmaCompact_and_weaklyLocallyCompact (X : Type u) [TopologicalSpace X] :
    CompactlyExhaustibleSpace X ↔ SigmaCompactSpace X ∧ WeaklyLocallyCompactSpace X := by
  -- The forward implication follows from the canonical conversion instances.
  constructor
  · intro h
    letI : CompactlyExhaustibleSpace X := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hSigma, hLocal⟩
    letI : SigmaCompactSpace X := hSigma
    letI : WeaklyLocallyCompactSpace X := hLocal
    -- Mathlib's compact exhaustion supplies the required compact family and interior cover.
    let K := CompactExhaustion.choice X
    exact ⟨⟨K, K.isCompact, K.iUnion_interior_eq_univ⟩⟩

end CompactlyExhaustibleSpace

variable (Y : Type v) [TopologicalSpace X] [CompactlyExhaustibleSpace X] [MetricSpace Y]

/- Exercise 46.10 (b): Compact convergence on `Y ^ X` is metrizable when `X` is σ-compact in
the book's sense. -/
#check (inferInstance :
  TopologicalSpace.MetrizableSpace (UniformOnFun X Y {K : Set X | IsCompact K}))

variable [CompleteSpace Y]

/- Exercise 46.10 (b): If `Y` is complete, compact convergence on `Y ^ X` is complete for its
canonical uniform structure. -/
#check (inferInstance : CompleteSpace (UniformOnFun X Y {K : Set X | IsCompact K}))

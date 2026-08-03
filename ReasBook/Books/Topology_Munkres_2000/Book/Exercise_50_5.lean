module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open scoped BigOperators

universe u

/-- The partition-of-unity map used for `m = 1` lies pointwise on a segment between
two selected points when at most two partition coefficients are nonzero. -/
theorem partitionMap_mem_segment {X : Type u} [TopologicalSpace X] (n : ℕ)
    (ρ : PartitionOfUnity (Fin n) X Set.univ)
    (z : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : X → EuclideanSpace ℝ (Fin 3))
    (hg : ∀ x, g x = ∑ i, (ρ i) x • z i)
    (hcard : ∀ x, (ρ.finsupport x).card ≤ 2) :
    ∀ x, ∃ i j, g x ∈ segment ℝ (z i) (z j) := sorry

/-- The range of the partition-of-unity map lies in the union of the segments joining
the selected points when at most two partition coefficients are nonzero. -/
theorem partitionMap_range_subset_iUnion_segment {X : Type u} [TopologicalSpace X]
    (n : ℕ)
    (ρ : PartitionOfUnity (Fin n) X Set.univ)
    (z : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : X → EuclideanSpace ℝ (Fin 3))
    (hg : ∀ x, g x = ∑ i, (ρ i) x • z i)
    (hcard : ∀ x, (ρ.finsupport x).card ≤ 2) :
    Set.range g ⊆ ⋃ i, ⋃ j, segment ℝ (z i) (z j) := sorry

/- Exercise 50.5 is blocked: the available API does not expose the finite segment graph
constructed from the map `g` or a carrier specification for the simultaneously active
pairs. The stated "onto" conclusion additionally requires a non-circular edge-filling
theorem not supplied by the preceding formalized embedding result. -/

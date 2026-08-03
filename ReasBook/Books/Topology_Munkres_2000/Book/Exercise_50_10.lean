module

public import Topology_Munkres_2000.Book.Definition_50_8.FiniteClosedUnion
public import Topology_Munkres_2000.Book.Exercise_46_10.SigmaCompact
public import Topology_Munkres_2000.Book.Exercise_50_8
public import Topology_Munkres_2000.Book.Theorem_50_6

public section

open scoped CoveringDimension

/-- Helper for Exercise 50.10: a compact subset of a Euclidean subtype has covering
dimension at most the dimension of the ambient Euclidean space. -/
private lemma compactSubset_euclideanSubtype_hasCoveringDimensionLE {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (K : Set X) (hK : IsCompact K) :
    HasCoveringDimensionLE K N := by
  -- Send the compact subset into the ambient Euclidean space.
  have hImageCompact :
      IsCompact (((↑) : X → EuclideanSpace ℝ (Fin N)) '' K) :=
    hK.image continuous_subtype_val
  have hImageDimension :
      HasCoveringDimensionLE
        (((↑) : X → EuclideanSpace ℝ (Fin N)) '' K) N :=
    compactSubset_euclideanSpace_hasCoveringDimensionLE _ hImageCompact
  let e : K ≃ₜ (((↑) : X → EuclideanSpace ℝ (Fin N)) '' K) :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage K
  -- Pull the ambient bound back through the canonical image homeomorphism.
  exact hImageDimension.homeomorph e.symm

/-- Exercise 50.10. Every closed subspace of `EuclideanSpace ℝ (Fin N)` has
covering dimension at most `N`. -/
theorem closedSubset_euclideanSpace_hasCoveringDimensionLE {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsClosed X) :
    HasCoveringDimensionLE X N := by
  -- Closedness supplies local compactness; second countability then supplies an exhaustion.
  letI : LocallyCompactSpace X := hX.locallyCompactSpace
  -- Exercise 50.8 globalizes the uniform bound on all compact subspaces.
  exact hasCoveringDimensionLE_of_compact_subspaces fun K hK ↦
    compactSubset_euclideanSubtype_hasCoveringDimensionLE X K hK

/-- The numerical covering-dimension form of Exercise 50.10. -/
theorem closedSubset_euclideanSpace_coveringDimension_le {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsClosed X) :
    dim X ≤ N := by
  rw [coveringDimension_le_iff]
  exact closedSubset_euclideanSpace_hasCoveringDimensionLE X hX

import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- A `σ`-compact Hausdorff space locally modelled on `ℝ^n` carries the canonical
`TopologicalManifold` structure. -/
@[reducible] def topologicalManifold_of_sigmaCompactSpace (n : ℕ) {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SigmaCompactSpace M] : TopologicalManifold n M :=
  let _ : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  topologicalManifoldOfChartedSpace n M

/-- A topological manifold is `σ`-compact. -/
theorem sigmaCompactSpace_of_topologicalManifold (n : ℕ) {M : Type u} [TopologicalSpace M]
    [TopologicalManifold n M] : SigmaCompactSpace M := by
  letI : LocallyCompactSpace M :=
    TopologicalManifold.locallyCompactSpace_of_topologicalManifold n M
  infer_instance

/-- Problem 1-3: for a Hausdorff space locally modelled on `ℝ^n`, second countability is
equivalent to `σ`-compactness. -/
theorem secondCountableTopology_iff_sigmaCompactSpace_of_t2_euclidean_chartedSpace {n : ℕ}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    SecondCountableTopology M ↔ SigmaCompactSpace M := by
  constructor
  · intro hM
    letI : SecondCountableTopology M := hM
    letI : TopologicalManifold n M := topologicalManifoldOfChartedSpace n M
    exact sigmaCompactSpace_of_topologicalManifold n
  · intro hM
    letI : SigmaCompactSpace M := hM
    letI : TopologicalManifold n M := topologicalManifold_of_sigmaCompactSpace n
    infer_instance

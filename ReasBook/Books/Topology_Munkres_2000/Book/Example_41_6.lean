module

public import Topology_Munkres_2000.Book.Exercise_32_9.RealPower
public import Mathlib.Topology.Compactness.Paracompact

public section

universe u

/- Every product `J → ℝ` is Hausdorff, without a countability assumption on `J`. -/
#check fun J : Type u ↦ (inferInstance : T2Space (J → ℝ))

/- For uncountable `J`, the product `J → ℝ` is not normal in the book's
`T4Space` convention. -/
#check realPower_notT4

/-- Example 41.6. The product space `J → ℝ` is not paracompact when `J` is
uncountable. -/
theorem realPower_not_paracompact {J : Type u} [Uncountable J] :
    ¬ ParacompactSpace (J → ℝ) := by
  -- Assume paracompactness so that, together with Hausdorffness, it yields `T4Space`.
  intro hparacompact
  letI : ParacompactSpace (J → ℝ) := hparacompact
  -- The resulting separation instance contradicts the uncountable-power obstruction.
  exact realPower_notT4 (inferInstance : T4Space (J → ℝ))

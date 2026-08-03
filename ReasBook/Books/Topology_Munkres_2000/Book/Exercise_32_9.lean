module

public import Topology_Munkres_2000.Book.Exercise_32_9.RealPower

public section

/-- Exercise 32.9: If `J` is uncountable, then the product space `J → ℝ` is not normal. -/
theorem realPower_notNormal {J : Type u} [Uncountable J] :
    ¬ NormalSpace (J → ℝ) := by
  -- Apply the Stone-space separation argument developed in the support module.
  exact uncountableRealPower_notNormal

/- The same product is not normal in the book's `T4Space` convention. -/
#check realPower_notT4

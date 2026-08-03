module

public import Topology_Munkres_2000.Book.Example_24_7
public import Topology_Munkres_2000.Book.Exercise_24_8.Union
public import Mathlib.Analysis.Convex.PathConnected

public section

/- Exercise 24.8 (1): An indexed product of path-connected spaces is path connected. -/
#check Pi.instPathConnectedSpace

namespace TopologistsSineCurve

/-- Helper for Exercise 24.8: the oscillating-graph parametrization is continuous on its
positive parameter interval. -/
lemma curveParam_continuousOn :
    ContinuousOn (fun x : ℝ ↦ (x, Real.sin (1 / x))) (Set.Ioc 0 1) := by
  -- Positivity on the interval removes the only singularity of the reciprocal.
  apply continuousOn_id.prodMk
  apply Real.continuous_sin.comp_continuousOn
  apply continuousOn_const.div continuousOn_id
  intro x hx
  exact ne_of_gt hx.1

/-- Helper for Exercise 24.8: the parameter interval `(0, 1]` is path connected. -/
lemma parameterInterval_isPathConnected : IsPathConnected (Set.Ioc (0 : ℝ) 1) := by
  -- Convexity gives path connectedness once an endpoint witnesses nonemptiness.
  have one_mem : (1 : ℝ) ∈ Set.Ioc 0 1 := by
    simp
  exact (convex_Ioc (0 : ℝ) 1).isPathConnected ⟨1, one_mem⟩

/-- Helper for Exercise 24.8: the image defining the oscillating graph is path connected. -/
lemma oscillatingGraphImage_isPathConnected :
    IsPathConnected ((fun x : ℝ ↦ (x, Real.sin (1 / x))) '' Set.Ioc 0 1) := by
  -- Transport path connectedness through the continuous graph parametrization.
  exact parameterInterval_isPathConnected.image' curveParam_continuousOn

/-- Exercise 24.8 (2): The oscillating graph is path connected. -/
theorem curve_isPathConnected : IsPathConnected curve := by
  -- Route correction: expose the owner definition once, then normalize the completed image proof.
  simpa only [curve] using oscillatingGraphImage_isPathConnected

/- Exercise 24.8 (2): The closure of the oscillating graph need not be path connected. -/
#check carrier_not_isPathConnected

end TopologistsSineCurve

/- Exercise 24.8 (3): The image of a path-connected space under a continuous map is
path connected. -/
#check isPathConnected_range

/- Exercise 24.8 (4): A union of path-connected subspaces with nonempty total
intersection is path connected. -/
#check isPathConnected_iUnion

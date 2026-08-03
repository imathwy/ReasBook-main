module

public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Instances.Real.Lemmas

import Topology_Munkres_2000.Book.Exercise_48_7.CountableDense
import Topology_Munkres_2000.Book.Theorem_48_5
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.GDelta.MetrizableSpace

public section

open Filter

/-- Exercise 48.8. If a sequence of continuous functions `F n : ℝ → ℝ` converges
pointwise to `f`, then `f` is continuous at uncountably many points of `ℝ`. -/
theorem continuousAtSet_uncountable_of_tendsto
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (hF : ∀ n, Continuous (F n))
    (hlim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    ¬ {x : ℝ | ContinuousAt f x}.Countable := fun hcountable ↦
  hcountable.not_isGδ_of_dense (dense_continuousAt_of_tendsto F f hF hlim)
    (IsGδ.setOf_continuousAt f)

end

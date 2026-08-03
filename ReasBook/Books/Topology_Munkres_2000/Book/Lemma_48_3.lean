module

public import Topology_Munkres_2000.Book.Exercise_43_4

public section

open Filter Set

universe u

/-- Lemma 48.3: In a complete metric space, an antitone sequence of nonempty closed
bounded sets whose diameters tend to zero has nonempty intersection. The boundedness
hypothesis records the textbook convention that diameter is defined for bounded sets. -/
theorem nestedClosed_iInter_nonempty {X : Type u} [MetricSpace X] [CompleteSpace X]
    {C : ℕ → Set X} (hC : Antitone C) (hne : ∀ n, (C n).Nonempty)
    (hclosed : ∀ n, IsClosed (C n)) (hbounded : ∀ n, Bornology.IsBounded (C n))
    (hdiam : Tendsto (fun n ↦ Metric.diam (C n)) atTop (nhds 0)) :
    (⋂ n, C n).Nonempty := by
  exact completeSpace_iff_nested_closed_iInter.mp inferInstance C hC hne hclosed hbounded hdiam

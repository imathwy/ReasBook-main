module

public import Mathlib.Topology.MetricSpace.Bounded

public section

/- Definition 20.5 (1): A subset of a metric space is bounded when all pairwise
distances admit a common real upper bound. -/
#check Bornology.IsBounded
#check Metric.isBounded_iff

namespace Metric

/-- Definition 20.5 (2): The diameter of a bounded nonempty subset is the supremum
of its pairwise distances. With mathlib's conventions for `diam` and `sSup`, the
formula holds for every subset. -/
theorem diam_eq_sSup_dist {X : Type u} [PseudoMetricSpace X] (A : Set X) :
    diam A = sSup (Set.image2 dist A A) := by
  rw [diam, ediam_eq_sSup, ENNReal.toReal_sSup]
  · congr 1
    ext r
    simp only [Set.mem_image, Set.mem_image2, dist_edist]
    constructor
    · rintro ⟨d, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨edist x y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  · rintro d ⟨x, _, y, _, rfl⟩
    exact edist_ne_top x y

end Metric

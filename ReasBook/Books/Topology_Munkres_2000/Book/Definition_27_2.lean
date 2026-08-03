module

import Topology_Munkres_2000.Book.Definition_20_5

public section

/- Definition 27.2: The diameter of a bounded subset `A` of a metric space is
the supremum of the distances `dist a₁ a₂` for `a₁, a₂ ∈ A`. -/
#check Metric.diam
#check Metric.diam_eq_sSup_dist

module

public import Topology_Munkres_2000.Book.Definition_43_11.Distance

public section

universe u

open scoped CauchySequences

namespace CauchySequences.Quotient

variable {X : Type u} [PseudoMetricSpace X]

/-- Definition 43.11: The distance between two classes of Cauchy sequences is the limit of the
pointwise distances between representatives, and this distance defines a metric on the quotient. -/
noncomputable instance instMetricSpace : MetricSpace (CauchySequences.Quotient X) where
  toDist := instDist
  dist_self := dist_self
  dist_comm := dist_comm
  dist_triangle := dist_triangle
  eq_of_dist_eq_zero := fun h ↦ (dist_eq_zero_iff _ _).mp h

#check CauchySequences.Quotient.dist_mk
#synth MetricSpace (CauchySequences.Quotient X)


end CauchySequences.Quotient

end

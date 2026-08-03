module

import Topology_Munkres_2000.Book.Exercise_43_6.Instances
import Mathlib.Topology.Baire.CompleteMetrizable

public section

/- Exercise 48.6. The subtype of irrational real numbers is a Baire space. -/
#check (inferInstance : BaireSpace {x : ℝ // Irrational x})

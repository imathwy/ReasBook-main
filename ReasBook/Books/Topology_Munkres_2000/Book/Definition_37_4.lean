module

import Topology_Munkres_2000.Book.Exercise_25_10.Quasicomponent

/- Definition 37.4: Two points belong to the same quasicomponent exactly when no clopen
set contains the first and excludes the second; such a set and its complement form the
separation in the source definition. -/
#check mem_quasicomponent_iff_no_clopen_separation

module

import Topology_Munkres_2000.Book.Exercise_36_4.PointFinite
import Topology_Munkres_2000.Book.Exercise_36_4.Shrinking

/- Exercise 36.4: An indexed family `A : ι → Set X` is point-finite if each
`x : X` belongs to `A i` for only finitely many indices `i`. -/
#check PointFinite
#check pointFinite_iff

/- Exercise 36.4 (Shrinking lemma). A point-finite indexed open cover of a
normal space admits an indexed open shrinking whose closures refine the
original cover. The source's sequence is the specialization to `ι = ℕ`. -/
#check TopologicalSpace.IsOpenCover.exists_shrinking

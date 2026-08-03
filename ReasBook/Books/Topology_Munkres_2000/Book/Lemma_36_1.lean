module

import Topology_Munkres_2000.Book.Exercise_36_4.Shrinking

/- Lemma 36.1 (Shrinking lemma). A point-finite indexed open cover of a normal
space admits an indexed open shrinking whose closures refine the original
cover. The source's sequence is the specialization to `ι = ℕ`. -/
#check TopologicalSpace.IsOpenCover.exists_shrinking

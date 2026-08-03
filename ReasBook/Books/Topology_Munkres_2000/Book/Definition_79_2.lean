module

import Topology_Munkres_2000.Book.Definition_79_2.Conjugacy

public section

/- Definition 79.2: Two subgroups are conjugate when one is carried to the other by an inner
automorphism. This is the orbit equivalence relation on subgroups, and the orbit of a subgroup is
its conjugacy class. -/
#check Subgroup.IsConj
#check Subgroup.isConj_iff_exists
#check Subgroup.isConj_refl
#check Subgroup.isConj_symm
#check Subgroup.isConj_trans
#check Subgroup.conjugacyClass
#check Subgroup.ConjClasses

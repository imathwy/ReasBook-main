module

public import Topology_Munkres_2000.Book.Theorem_69_1.Subgroup

public section

universe u

namespace Module.Free

/-- Theorem 69.1. If `H` is a subgroup of a free abelian group `G`, then `H` is
itself a free abelian group. -/
instance addSubgroup {G : Type u} [AddCommGroup G] [Module.Free ℤ G]
    (H : AddSubgroup G) : Module.Free ℤ H :=
  ofAddSubgroup H

end Module.Free

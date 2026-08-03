module

public import Topology_Munkres_2000.Book.Theorem_69_7.Instances

public section

universe u

variable {G : Type u} [AddCommGroup G] [AddGroup.FG G]

/- Theorem 69.7. The canonical torsion subgroup of a finitely generated abelian group
is additively equivalent to a finite direct sum of finite cyclic groups of prime-power order. -/
#check AddCommGroup.equiv_directSum_zmod_of_finite (AddCommGroup.torsion G)

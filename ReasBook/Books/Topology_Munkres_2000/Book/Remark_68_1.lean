module

public import Topology_Munkres_2000.Book.Definition_67_4.ExternalDirectSum

public section

universe u v

/- Remark 68.1. The external direct sum of a family of abelian groups is modeled by the
finitely supported dependent functions `DirectSum ι G`. Each summand is additively equivalent to
the range of its canonical inclusion, whose elements vanish in every other coordinate. -/
#check DirectSum
#check DFinsupp.finite_support
#check DirectSum.inclusion
#check DirectSum.inclusion_injective
#check DirectSum.inclusion_apply_same
#check DirectSum.inclusion_apply_of_ne
#check DirectSum.mem_inclusion_range_iff
#check fun {ι : Type u} (G : ι → Type v) [∀ α, AddCommGroup (G α)] (β : ι) ↦
  AddMonoidHom.ofInjective (DirectSum.inclusion_injective G β)
#check DirectSum.instIsExternalDirectSum

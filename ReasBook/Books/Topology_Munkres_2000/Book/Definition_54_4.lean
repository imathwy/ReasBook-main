module

public import Topology_Munkres_2000.Book.Definition_54_4.Classification
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup

public section

/- Definition 54.4 (1): The cardinality of a group is also called its order. -/
#check Cardinal.mk

/- Definition 54.4 (2): A group is cyclic of infinite order if and only if it
is isomorphic to the additive group of integers. -/
#check isCyclic_infinite_iff_nonempty_equiv_int

/- Definition 54.4 (3): A group is cyclic of order `k` if and only if it is
isomorphic to the group of integers modulo `k`. For `k = 0`, `ZMod k` is `ℤ`,
so this includes the infinite cyclic case. -/
#check isCyclic_card_eq_iff_nonempty_equiv_zmod

namespace Circle

/-- Definition 54.4 (4): The fundamental group of the circle at `1` is cyclic. -/
instance instIsCyclicFundamentalGroup : IsCyclic (FundamentalGroup Circle 1) :=
  fundamentalGroupEquivInt.isCyclic.mpr inferInstance

/-- Definition 54.4 (5): The fundamental group of the circle at `1` has infinite
order. -/
instance instInfiniteFundamentalGroup : Infinite (FundamentalGroup Circle 1) :=
  Infinite.of_injective fundamentalGroupEquivInt.symm fundamentalGroupEquivInt.symm.injective

/-- The fundamental group of the circle at `1` is infinite cyclic. -/
theorem fundamentalGroup_isCyclic_and_infinite :
    IsCyclic (FundamentalGroup Circle 1) ∧ Infinite (FundamentalGroup Circle 1) :=
  ⟨inferInstance, inferInstance⟩

end Circle

end

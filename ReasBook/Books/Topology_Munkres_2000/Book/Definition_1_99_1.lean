module

public import Topology_Munkres_2000.Book.Remark_9_4.ChoiceFunction
public import Topology_Munkres_2000.Book.Definition_1_99_1.Tower

public section

/- Definition 1.99.1: A tower in `X`, relative to a fixed choice function, is a
well-ordered subset whose elements are selected from the complements of their
strict-predecessor sections. -/
#check Tower
#check Tower.strictSection
#check Tower.choice_eq
#check Tower.spec

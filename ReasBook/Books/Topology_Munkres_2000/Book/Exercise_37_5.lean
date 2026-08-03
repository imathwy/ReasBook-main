module

public import Topology_Munkres_2000.Book.Lemma_37_4

public section

/- Exercise 37.5 (1). A rectangular family with no finite subcover of `X × Y`
has a slice `{x} ×ˢ Set.univ` with no finite subcover from the family. -/
#check CompactSpace.existsSliceNotFinitelyCovered

/- Exercise 37.5 (2). An arbitrary dependent product of compact spaces is compact
in the product topology. -/
#check Pi.compactSpace

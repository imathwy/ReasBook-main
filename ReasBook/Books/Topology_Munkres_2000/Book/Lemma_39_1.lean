module

public import Topology_Munkres_2000.Book.Lemma_39_1.LocallyFinite

public section

/- Lemma 39.1 (1): Every subcollection of a locally finite collection is
locally finite. -/
#check Set.LocallyFinite.mono

/- Lemma 39.1 (2): The collection of closures of the members of a locally
finite collection is locally finite. -/
#check Set.LocallyFinite.closure_image

/- Lemma 39.1 (3): Closure commutes with the union of a locally finite
collection. -/
#check Set.LocallyFinite.closure_sUnion

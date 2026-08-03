module

import Mathlib.Topology.Homeomorph.Lemmas

/- Definition 18.6: An injective continuous map `f : X → Y` is a topological
imbedding when its codomain restriction to `Set.range f`, with the subspace topology,
is a homeomorphism. -/
#check Topology.IsEmbedding
#check Topology.IsEmbedding.toHomeomorph

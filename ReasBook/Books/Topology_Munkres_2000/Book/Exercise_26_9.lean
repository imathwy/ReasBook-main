module

import Mathlib.Topology.Compactness.Compact

public section

/- Exercise 26.9. If compact sets `A ⊆ X` and `B ⊆ Y` have `A ×ˢ B` contained
in an open set `N ⊆ X × Y`, then they have open neighborhoods `U` and `V` such
that `A ×ˢ B ⊆ U ×ˢ V ⊆ N`. -/
#check generalized_tube_lemma

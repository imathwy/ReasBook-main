module

public import Topology_Munkres_2000.Book.Definition_76_6.Renumbering

public section

open LabellingScheme.PolygonalRegions.Renumbering

/- Definition 76.8: replacing `y₀ ++ y₁` by `y₁ ++ y₀` is the canonical cyclic
renumbering of the selected polygonal region, and renumbering preserves the quotient
realization up to homeomorphism. -/
#check ofAppend
#check realizationHomeomorph

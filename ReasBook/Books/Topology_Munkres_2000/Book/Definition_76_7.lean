module

public import Topology_Munkres_2000.Book.Definition_76_6.RelabelRealization

public section

/- Definition 76.7 (1): For a distinct fresh label, `renameLabel` has the source's
replacement behavior; the underlying canonical relabelling preserves the pasting map. -/
#check LabellingScheme.renameLabel_spec
#check LabellingScheme.PolygonalRegions.realizes_renameLabel_iff

/- Definition 76.7 (2): Reversing the orientation sign of every occurrence of one label
preserves the pasting map under the canonical equivalence of polygonal-region sources. -/
#check LabellingScheme.PolygonalRegions.realizes_reverseLabel_iff

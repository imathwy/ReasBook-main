module

public import Topology_Munkres_2000.Book.Definition_76_6.Flip
public import Topology_Munkres_2000.Book.Definition_76_6.Permutation
public import Topology_Munkres_2000.Book.Definition_76_6.Realization
public import Topology_Munkres_2000.Book.Definition_76_6.Relabel
public import Topology_Munkres_2000.Book.Definition_76_6.RelabelRealization
public import Topology_Munkres_2000.Book.Definition_76_6.Renumbering

public section

universe u v

namespace LabellingScheme.PolygonalRegions

variable {α : Type u} {word : PolygonWord α} {rest : LabellingScheme α}

/-- Definition 76.6 (5): flipping a polygon preserves and reflects direct labelled-edge
pairings under the canonical source equivalence. -/
theorem edgeRelated_flip_iff (original : PolygonalRegions.{u, v} (word ::ₘ rest))
    (x y : original.Source) :
    original.EdgeRelated x y ↔
      original.flipped.EdgeRelated (original.flipSourceEquiv x)
        (original.flipSourceEquiv y) := by
  -- Apply the direct-pairing compatibility established by the flip construction.
  exact original.edgeRelated_flipped_iff x y

end LabellingScheme.PolygonalRegions

/- Definition 76.6 (1): pasting two polygon words along opposite occurrences of a fresh
label replaces them by their concatenation. -/
#check LabellingScheme.Paste.of

/- Definition 76.6 (2): replacing one label by a distinct fresh label has the stated
effect on the scheme and preserves the pasting map and quotient realization. -/
#check LabellingScheme.renameLabel_spec
#check LabellingScheme.PolygonalRegions.realizes_renameLabel_iff
#check LabellingScheme.PolygonalRegions.renameLabelRealizationHomeomorph

/- Definition 76.6 (3): reversing all orientations bearing one label is involutive and
preserves the pasting map and quotient realization. -/
#check LabellingScheme.reverseLabel_reverseLabel
#check LabellingScheme.PolygonalRegions.realizes_reverseLabel_iff
#check LabellingScheme.PolygonalRegions.reverseLabelRealizationHomeomorph

/- Definition 76.6 (4): cyclically permuting one polygon word is a scheme permutation and
preserves its quotient realization. -/
#check LabellingScheme.Permute.ofAppend
#check LabellingScheme.PolygonalRegions.Renumbering.realizationHomeomorph

/- Definition 76.6 (5): replacing one polygon word by its formal inverse is a flip step and
preserves its quotient realization. -/
#check LabellingScheme.Flip.of
#check LabellingScheme.PolygonalRegions.flipRealizationHomeomorph

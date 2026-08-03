module

import Topology_Munkres_2000.Book.Proposition_76_1
import Topology_Munkres_2000.Book.Definition_76_5

public section

/-
Remark 76.1. Cutting a polygon word into two polygon words introduces a fresh label on
both cut edges with opposite signs: `LabellingScheme.Cut.of` inserts `(c, !b)` in one
word and `(c, b)` in the other. The reverse additional edge pasting is recorded by
`LabellingScheme.Paste.of`. With compatible polygonal-region realizations, the additional
pasting followed by the remaining edge identifications gives the original quotient space,
as stated by `cutSchemeRealizesSameSpace`.
-/
#check LabellingScheme.Cut.of
#check LabellingScheme.Paste.of
#check cutSchemeRealizesSameSpace

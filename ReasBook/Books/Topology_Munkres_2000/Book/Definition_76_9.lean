module

public import Topology_Munkres_2000.Book.Definition_76_9.Uncancel

public section

/- Definition 76.9: Uncancel replaces `y₀ ++ y₁` by
`y₀ ++ [(a, true), (a, false)] ++ y₁` for a label `a` used nowhere else; it is the reverse
of the cancel operation. -/
#check LabellingScheme.Uncancel.ofPositiveNegative

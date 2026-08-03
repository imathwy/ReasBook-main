module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Topology_Munkres_2000.Book.Lemma_38_1.InducedCompactification

public section

open Set

/- Remark 38.2: A space can admit many compactifications. The following examples study
several elements of the canonical type of compactifications of the open interval `(0, 1)`. -/
#check Compactification (Ioo (0 : ℝ) 1)

/- The next examples use the one-point space and the closed interval as compactification targets. -/
#check OnePoint (Ioo (0 : ℝ) 1)
#check Icc (0 : ℝ) 1

/- They also use the preceding closure-of-range construction to build induced compactifications. -/
#check InducedCompactification.compactification

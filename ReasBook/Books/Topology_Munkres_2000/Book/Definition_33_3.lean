module

public import Mathlib.Topology.GDelta.Basic

public section

/- Definition 33.3: A subset of a topological space is a `Gδ` set when it is the
intersection of a countable collection of open sets. This is mathlib's `IsGδ`. -/
#check IsGδ

/- The equivalent presentation as an intersection of a sequence of open sets. -/
#check isGδ_iff_eq_iInter_nat

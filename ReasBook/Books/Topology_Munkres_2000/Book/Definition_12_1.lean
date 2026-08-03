module

public import Mathlib.Topology.Defs.Basic

/- Definition 12.1: A topology on a type `X` is exactly a `TopologicalSpace X`.
The constructor records that `Set.univ` is open and that open sets are closed
under binary intersections and arbitrary unions; these equivalent axioms imply
that `∅` is open and that finite intersections are open. -/
#check TopologicalSpace
#check TopologicalSpace.mk

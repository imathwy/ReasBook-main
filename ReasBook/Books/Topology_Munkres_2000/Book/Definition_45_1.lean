module

public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

public section

/-
Definition 45.1: A metric space is totally bounded when its universal set is
`TotallyBounded`; `Metric.totallyBounded_iff` gives the finite-cover-by-balls
characterization from the source.
-/
#check fun (X : Type*) [MetricSpace X] ↦ TotallyBounded (Set.univ : Set X)
#check Metric.totallyBounded_iff

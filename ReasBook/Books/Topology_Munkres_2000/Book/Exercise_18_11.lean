module

public import Topology_Munkres_2000.Book.Definition_18_9.SeparateContinuity
public import Mathlib.Topology.Constructions.SumProd

public section

/-- Exercise 18.11: A continuous map `F : X × Y → Z` is continuous in each
variable separately. -/
theorem Continuous.separatelyContinuous {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {F : X × Y → Z}
    (hF : Continuous F) :
    SeparatelyContinuous F where
  continuous_fst y₀ := hF.comp (Continuous.prodMk_left y₀)
  continuous_snd x₀ := hF.comp (Continuous.prodMk_right x₀)

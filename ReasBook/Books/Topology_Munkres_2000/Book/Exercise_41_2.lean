module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Topology_Munkres_2000.Book.Example_32_2.Separation
public import Topology_Munkres_2000.Book.Exercise_29_7.Compactification
public import Mathlib.Topology.Compactness.Paracompact

public section

universe u v

/- Exercise 41.2 (a): The product of a paracompact space and a compact space
is paracompact. -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ParacompactSpace X] [CompactSpace Y] ↦
  (inferInstance : ParacompactSpace (X × Y))

/-- Exercise 41.2 (b): The open first-uncountable ordinal `S_Ω` is not
paracompact. -/
theorem OpenOmegaOne.notParacompact : ¬ ParacompactSpace OpenOmegaOne := by
  intro hParacompact
  letI : ParacompactSpace OpenOmegaOne := hParacompact
  -- The compact second factor would make the deleted ordinal plank paracompact,
  -- hence normal, contradicting its established nonnormality.
  exact OpenOmegaOne.prodClosedOmegaOne_notNormal inferInstance

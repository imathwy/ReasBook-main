module

public import Topology_Munkres_2000.Book.Example_32_2.Separation
public import Topology_Munkres_2000.Book.Exercise_29_7.Compactification
public import Mathlib.Topology.Compactness.Paracompact

public section

universe u

/- Example 41.3 (1): The closed first-uncountable ordinal square is compact. -/
#check (inferInstance : CompactSpace (ClosedOmegaOne.{u} × ClosedOmegaOne.{u}))

/- Example 41.3 (2): The closed first-uncountable ordinal square is therefore
paracompact. -/
#check (inferInstance : ParacompactSpace (ClosedOmegaOne.{u} × ClosedOmegaOne.{u}))

/-- Example 41.3 (3): The canonical inclusion of `OpenOmegaOne × ClosedOmegaOne`
into the closed first-uncountable ordinal square is a topological embedding. -/
theorem OpenOmegaOne.isEmbedding_prodToClosed :
    Topology.IsEmbedding (fun p : OpenOmegaOne.{u} × ClosedOmegaOne.{u} ↦
      (OpenOmegaOne.toClosed p.1, p.2)) := by
  change Topology.IsEmbedding (Prod.map OpenOmegaOne.toClosed id)
  exact OpenOmegaOne.isEmbedding_toClosed.prodMap Topology.IsEmbedding.id

/-- Example 41.3 (4): The Hausdorff but nonnormal space
`OpenOmegaOne × ClosedOmegaOne` is not paracompact. -/
theorem OpenOmegaOne.prodClosedOmegaOne_notParacompact :
    ¬ ParacompactSpace (OpenOmegaOne.{u} × ClosedOmegaOne.{u}) := by
  intro
  exact OpenOmegaOne.prodClosedOmegaOne_notNormal inferInstance

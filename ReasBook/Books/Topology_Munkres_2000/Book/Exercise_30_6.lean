module

public import Topology_Munkres_2000.Book.Exercise_30_5
public import Topology_Munkres_2000.Book.Example_30_3.Countability
public import Topology_Munkres_2000.Book.Example_30_5

public section

universe u

/-- Helper for Exercise 30.6: a Lindelöf space that is not second-countable is not
metrizable. -/
private lemma notMetrizable_of_notSecondCountable {X : Type u} [TopologicalSpace X]
    [LindelofSpace X] (hNotSecondCountable : ¬ SecondCountableTopology X) :
    ¬ TopologicalSpace.MetrizableSpace X := by
  -- An assumed metric makes Exercise 30.5's second-countability instance available.
  intro hMetrizable
  letI : TopologicalSpace.MetrizableSpace X := hMetrizable
  exact hNotSecondCountable inferInstance

/-- Helper for Exercise 30.6: a Lindelöf space with a non-Lindelöf subspace is not
metrizable. -/
private lemma notMetrizable_of_nonLindelof_subspace {X : Type u} [TopologicalSpace X]
    [LindelofSpace X] {s : Set X} (hNotLindelof : ¬ LindelofSpace s) :
    ¬ TopologicalSpace.MetrizableSpace X := by
  -- Metrizability and Lindelöfness make the ambient space second-countable.
  intro hMetrizable
  letI : TopologicalSpace.MetrizableSpace X := hMetrizable
  letI : SecondCountableTopology X := inferInstance
  -- Second countability passes to the subtype, which is therefore Lindelöf.
  exact hNotLindelof inferInstance

/-- Exercise 30.6 (1): The Sorgenfrey line `ℝₗ` is not metrizable. -/
theorem SorgenfreyLine.notMetrizable :
    ¬ TopologicalSpace.MetrizableSpace SorgenfreyLine := by
  -- Apply the Lindelöf/second-countability obstruction to the Sorgenfrey line.
  exact notMetrizable_of_notSecondCountable SorgenfreyLine.notSecondCountable

/-- Exercise 30.6 (2): The ordered square `Iₒ²` is not metrizable. -/
theorem OrderedSquare.notMetrizable :
    ¬ TopologicalSpace.MetrizableSpace Iₒ² := by
  -- Its horizontal boundary supplies a non-Lindelöf subspace obstruction.
  exact notMetrizable_of_nonLindelof_subspace
    OrderedSquare.openHorizontalStrip_notLindelof

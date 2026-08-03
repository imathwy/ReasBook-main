module

public import Topology_Munkres_2000.Book.Exercise_34_4.Discrete
public import Topology_Munkres_2000.Book.Theorem_34_1
public import Topology_Munkres_2000.Book.Theorem_27_2

public section

open TopologicalSpace

universe u

/- Exercise 34.4 (1): A locally compact Hausdorff space with a countable basis is metrizable. -/
#check fun (X : Type u) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] ↦ (inferInstance : MetrizableSpace X)

/- Exercise 34.4 (2): The uncountable discrete space `WithDiscreteTopology ℝ` is locally compact,
Hausdorff, and metrizable. -/
#check (inferInstance : LocallyCompactSpace (WithDiscreteTopology ℝ))
#check (inferInstance : T2Space (WithDiscreteTopology ℝ))
#check (inferInstance : MetrizableSpace (WithDiscreteTopology ℝ))

/-- The uncountable discrete space `WithDiscreteTopology ℝ` has no countable basis. -/
theorem discreteReal_not_secondCountable :
    ¬ SecondCountableTopology (WithDiscreteTopology ℝ) := by
  intro h
  have hcountable : Countable (WithDiscreteTopology ℝ) :=
    DiscreteTopology.countable_of_secondCountable h
  have : Countable ℝ := (WithTopology.equiv ℝ ⊥).countable_iff.mp hcountable
  exact not_countable this

end

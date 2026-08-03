module

public import Mathlib.Topology.ContinuousOn

public section

universe u v

/-- Theorem 18.2 (1): A function with a single constant value is continuous. -/
theorem continuous_of_eq_const
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {y₀ : Y} (hf : ∀ x, f x = y₀) :
    Continuous f :=
  continuous_const.congr fun x ↦ (hf x).symm

/- Theorem 18.2 (2): The inclusion of a subspace into its ambient space is continuous. -/
#check continuous_subtype_val

/- Theorem 18.2 (3): A composite of continuous functions is continuous. -/
#check Continuous.comp

namespace Continuous

/-- Theorem 18.2 (4): Restricting the domain of a continuous function to a subspace
is continuous. -/
theorem restrictDomain
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (s : Set X) :
    Continuous (s.restrict f) :=
  hf.continuousOn.restrict

end Continuous

/- Theorem 18.2 (5): Restricting the range of a continuous function to a subspace
containing its image preserves continuity. -/
#check Continuous.codRestrict

/- Theorem 18.2 (6): Expanding the range of a continuous subtype-valued function to
the ambient space preserves continuity. -/
#check Continuous.subtype_val

/- Theorem 18.2 (7): A function continuous on every member of an open cover is
continuous. -/
#check continuous_of_continuousOn_iUnion_of_isOpen

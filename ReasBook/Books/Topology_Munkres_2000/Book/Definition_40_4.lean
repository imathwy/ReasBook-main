module

public import Topology_Munkres_2000.Book.Definition_40_3.LocallyDiscreteFamily

public section

open Set

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- Definition 40.4: A family is sigma-locally discrete if its index type is covered by
countably many pieces whose restricted families are locally discrete. -/
def SigmaLocallyDiscreteFamily (f : ι → Set X) : Prop :=
  ∃ pieces : ℕ → Set ι,
    ⋃ n, pieces n = Set.univ ∧
      ∀ n, LocallyDiscreteFamily (fun i : pieces n ↦ f i)

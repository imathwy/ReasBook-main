module

import Mathlib.Topology.Separation.Regular

public section

universe u v

/- Theorem 31.2 (a), first statement: A subspace of a Hausdorff space is Hausdorff. -/
#check fun {X : Type u} [TopologicalSpace X] [T2Space X] (A : Set X) ↦
  (inferInstance : T2Space A)

/- Theorem 31.2 (a), second statement: A product of Hausdorff spaces is Hausdorff. -/
#check fun {ι : Type u} {X : ι → Type v} [(i : ι) → TopologicalSpace (X i)]
    [(i : ι) → T2Space (X i)] ↦
  (inferInstance : T2Space ((i : ι) → X i))

/- Theorem 31.2 (b), first statement: A subspace of a regular space is regular. -/
#check fun {X : Type u} [TopologicalSpace X] [T3Space X] (A : Set X) ↦
  (inferInstance : T3Space A)

/- Theorem 31.2 (b), second statement: A product of regular spaces is regular. -/
#check fun {ι : Type u} {X : ι → Type v} [(i : ι) → TopologicalSpace (X i)]
    [(i : ι) → T3Space (X i)] ↦
  (inferInstance : T3Space ((i : ι) → X i))

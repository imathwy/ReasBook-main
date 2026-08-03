module

public import Topology_Munkres_2000.Book.Definition_2_10

import Mathlib.Data.Set.Basic

/- Remark 2.4: If no point of `A` maps into `B₀`, then `f ⁻¹' B₀ = ∅`. -/
#check (fun {A : Type*} {B : Type*} (f : A → B) (B₀ : Set B)
    (h : ∀ a, f a ∉ B₀) ↦
  (Set.eq_empty_of_forall_notMem h : f ⁻¹' B₀ = ∅))

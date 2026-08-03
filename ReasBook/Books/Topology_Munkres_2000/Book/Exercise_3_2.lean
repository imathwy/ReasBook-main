module

public import Topology_Munkres_2000.Book.Exercise_3_2.Restriction

public section

universe u

/-- Exercise 3.2: The restriction of an equivalence relation `C` on `A` to a
subset `A₀` is an equivalence relation on `A₀`. -/
theorem equivalence_subrel {A : Type u} (C : A → A → Prop) (A₀ : Set A)
    (hC : Equivalence C) :
    Equivalence (Subrel C A₀) := hC.subrel A₀

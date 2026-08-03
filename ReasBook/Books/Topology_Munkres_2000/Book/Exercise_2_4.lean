module

public import Topology_Munkres_2000.Book.Exercise_2_1

public section

/- Exercise 2.4 (a): The preimage under a composite is the iterated preimage. -/
#check Set.preimage_comp

/- Exercise 2.4 (b): A composite of injective functions is injective. -/
#check Function.Injective.comp

/- Exercise 2.4 (c): If a composite is injective, then its inner function is injective. -/
#check Function.Injective.of_comp

/-- Exercise 2.4 (c): Injectivity of a composite does not force injectivity of its
outer function. -/
theorem injectiveCompDoesNotForceOuter :
    Function.Injective ((fun _ : Bool ↦ ()) ∘ (fun _ : Unit ↦ true)) ∧
      ¬ Function.Injective (fun _ : Bool ↦ ()) := by
  constructor
  · intro x y _
    exact Subsingleton.elim x y
  · intro h
    exact Bool.false_ne_true (h rfl).symm

/- Exercise 2.4 (d): A composite of surjective functions is surjective. -/
#check Function.Surjective.comp

/- Exercise 2.4 (e): If a composite is surjective, then its outer function is surjective. -/
#check Function.Surjective.of_comp

/-- Exercise 2.4 (e): Surjectivity of a composite does not force surjectivity of its
inner function. -/
theorem surjectiveCompDoesNotForceInner :
    Function.Surjective ((fun _ : Bool ↦ ()) ∘ (fun _ : Unit ↦ true)) ∧
      ¬ Function.Surjective (fun _ : Unit ↦ true) := by
  constructor
  · intro y
    exact ⟨(), Subsingleton.elim _ y⟩
  · rintro h
    obtain ⟨x, hx⟩ := h false
    exact Bool.false_ne_true hx.symm

/- Exercise 2.4 (f): Parts (b)-(e) are summarized by the four canonical results above. -/

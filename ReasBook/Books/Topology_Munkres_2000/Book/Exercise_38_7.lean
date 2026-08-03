module

public import Topology_Munkres_2000.Book.Exercise_38_7.ExtremallyDisconnected

public section

open Set

universe u

namespace StoneCech

/-- Exercise 38.7 (1): For a subset `A` of a discrete space `X`, the closures in
`StoneCech X` of the images of `A` and `Aᶜ` are disjoint. -/
theorem disjoint_closure_image_compl {X : Type u} [TopologicalSpace X]
    [DiscreteTopology X] (A : Set X) :
    Disjoint (closure (stoneCechUnit '' A)) (closure (stoneCechUnit '' Aᶜ)) := by
  classical
  -- Separate `A` and its complement by their Boolean characteristic function.
  let characteristic : X → Bool := fun x ↦ if x ∈ A then true else false
  have characteristic_continuous : Continuous characteristic := continuous_of_discreteTopology
  let extension : StoneCech X → Bool := stoneCechExtend characteristic_continuous
  have extension_continuous : Continuous extension := by
    simpa only [extension] using continuous_stoneCechExtend characteristic_continuous
  -- The extension maps the two embedded subsets into distinct singleton fibers.
  have maps_image_A : MapsTo extension (stoneCechUnit '' A) {true} := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [extension, stoneCechExtend_stoneCechUnit, characteristic, if_pos hx,
      mem_singleton_iff]
  have maps_image_compl : MapsTo extension (stoneCechUnit '' Aᶜ) {false} := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [mem_compl_iff] at hx
    simp only [extension, stoneCechExtend_stoneCechUnit, characteristic, if_neg hx,
      mem_singleton_iff]
  -- Closedness of the Boolean fibers extends these inclusions to both closures.
  have maps_closure_A : MapsTo extension (closure (stoneCechUnit '' A)) {true} :=
    maps_image_A.closure_left extension_continuous isClosed_singleton
  have maps_closure_compl : MapsTo extension (closure (stoneCechUnit '' Aᶜ)) {false} :=
    maps_image_compl.closure_left extension_continuous isClosed_singleton
  -- Pull back the disjoint Boolean fibers and restrict to the two closures.
  have boolean_values_ne : (true : Bool) ≠ false := fun h ↦ Bool.false_ne_true h.symm
  have disjoint_fibers : Disjoint (extension ⁻¹' {true}) (extension ⁻¹' {false}) :=
    Disjoint.preimage extension (Set.disjoint_singleton.mpr boolean_values_ne)
  exact disjoint_fibers.mono maps_closure_A maps_closure_compl

/-- Exercise 38.7 (2): The closure of every open subset of `StoneCech X` is open
when `X` is discrete. -/
theorem isOpen_closure {X : Type u} [TopologicalSpace X] [DiscreteTopology X]
    {U : Set (StoneCech X)} (hU : IsOpen U) : IsOpen (closure U) :=
  ExtremallyDisconnected.open_closure U hU

/- Exercise 38.7 (3): The Stone–Čech compactification of a discrete space is
totally disconnected. -/
variable (X : Type u) [TopologicalSpace X] [DiscreteTopology X]

#synth TotallyDisconnectedSpace (StoneCech X)

end StoneCech

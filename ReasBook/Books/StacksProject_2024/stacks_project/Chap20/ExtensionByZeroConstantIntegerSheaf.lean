import StacksProject_2024.stacks_project.Chap06.Extension_by_zero_by_the_initial_object
import StacksProject_2024.stacks_project.Chap20.ConstantIntegerSheaf

open CategoryTheory TopCat TopologicalSpace

noncomputable section

/-
The lower-shriek sheaf `j!ℤ[U]` attached to an open subset `U ⊆ X`, written directly in terms of
the canonical extension-by-zero and constant-integer-sheaf owners. This stays as pure notation so
the Chapter 20 public surface does not introduce a new data-bearing alias for the sheaf itself.
-/
notation:max "j!ℤ[" U:max "]" =>
  CategoryTheory.Functor.obj
    (j! U) (constantIntegerSheaf (extensionByZeroOpenSubsetSpace U))

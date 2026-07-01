import Mathlib
import stacks_project.Chap06.Definition_6_7_1
import stacks_project.Chap06.Extension_by_zero_by_the_initial_object

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}

/-- The lower-shriek image `j_{U!}\underline{S}` of the constant sheaf with value `S` on the open
subspace `U`. -/
abbrev extensionByZeroConstantSheaf (U : Opens X) (S : Type u) :
    Sh(X) :=
  ((j! U).obj
    ((constantSheaf (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Type u)).obj S) :
    Sh(X))

notation:max "j![" U ", " S "]" => extensionByZeroConstantSheaf U S

/-- A family of sheaves of the form `j_{U_i!}\underline{A_i}` admits its coproduct in
`Sh(X, Type)`. -/
private noncomputable instance lowerShriekConstantSheaf_hasCoproduct
    {I : Type u} (U : I → Opens X) (S : I → Type u) :
    HasCoproduct (fun i : I ↦ j![U i, S i]) := by
  let _ : HasColimitsOfShape (Discrete I) (Type u) := inferInstance
  let _ : HasColimitsOfShape (Discrete I) (Sh(X)) :=
    (Sheaf.instHasColimitsOfShape :
      HasColimitsOfShape (Discrete I) (Sh(X)))
  infer_instance

-- Proof sketch: for each stalk element `s ∈ ℱ_x`, choose a basis open `U(x,s)` and a section of
-- `ℱ` over `U(x,s)` representing `s`; Lemma 6.31.4 identifies such a section with a morphism
-- `j_{U(x,s)!}\underline{*} ⟶ ℱ`, and the induced coproduct map is stalkwise surjective, hence
-- epimorphic.
/-- Lemma 17.19.1: every sheaf of sets on `X` is an epimorphic image of a coproduct of lower-shriek
images `j_{U_i!}\underline{S_i}` with each `U_i` in the basis `B` and each `S_i` finite. -/
theorem exists_epi_from_coproduct_of_basis_extension_by_empty_constant_sheaves
    (B : Set (Opens X)) (hB : Opens.IsBasis B) (ℱ : Sh(X)) :
    ∃ (I : Type u) (U : I → Opens X) (S : I → Type u)
      (hU : ∀ i, U i ∈ B) (hS : ∀ i, Finite (S i))
      (φ : (∐ fun i : I ↦ j![U i, S i]) ⟶ ℱ), Epi φ := sorry

end

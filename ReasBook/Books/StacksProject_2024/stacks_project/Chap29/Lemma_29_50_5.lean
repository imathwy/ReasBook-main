import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_49_11
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_49_12

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the open-restriction API in
-- `Mathlib.AlgebraicGeometry.Restrict`; the source-facing owners needed here are the local
-- chapter predicates `IsBirational` and `BirationalOver`.

private instance finiteIrreducibleComponents_of_irreducible (X : Scheme.{u}) [IrreducibleSpace X] :
    Finite (irreducibleComponents X) := by
  letI : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  infer_instance

/- Lemma 29.50.5 (1): let `f : X ⟶ Y` be a birational morphism of schemes having finitely many
irreducible components. Assume either that `f` is locally of finite type and `Y` is reduced, or
that `f` is locally of finite presentation. Then there exist dense opens `U ⊆ X` and `V ⊆ Y`
such that `f(U) ⊆ V` and the induced morphism `U ⟶ V` is an isomorphism. -/
@[stacks 0BAC]
theorem exists_dense_opens_restrict_isIso_of_isBirational
    {X Y : Scheme.{u}}
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    (f : X ⟶ Y) [IsBirational f]
    (hfiniteType_or_finitePresentation :
      (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ (U : X.Opens) (V : Y.Opens),
      Dense (U : Set X) ∧ Dense (V : Set Y) ∧ ∃ hUV : U ≤ f ⁻¹ᵁ V, IsIso (f.resLE V U hUV) :=
  sorry

/-- In the irreducible case, the dense opens from Lemma 29.50.5 (1) are nonempty and therefore
give the standard Chapter 29 witness that `X` and `Y` have isomorphic nonempty opens over `S`. -/
@[stacks 0BAC]
theorem hasIsomorphicNonemptyOpenSubschemesOver_of_isBirational_of_irreducible
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsBirational f]
    (hf_over : f ≫ (Y ↘ S) = (X ↘ S))
    (hfiniteType_or_finitePresentation :
      (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    HasIsomorphicNonemptyOpenSubschemesOver S X Y := by
  sorry

/-- Lemma 29.50.5 (2): if in addition `X` and `Y` are irreducible, then they are
`S`-birational. -/
@[stacks 0BAC]
theorem birationalOver_of_isBirational_of_irreducible
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsBirational f]
    (hf_over : f ≫ (Y ↘ S) = (X ↘ S))
    (hfiniteType_or_finitePresentation :
      (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    BirationalOver S X Y := by
  sorry

end AlgebraicGeometry

import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap14.Definition_14_26_6
import StacksProject_2024.Chap21.CategoryOverPointDerivedColimitBasic

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open ComplexShape
open Opposite
open SSet.stdSimplex (isTerminalObj₀)
open scoped CategoryTheory Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section Generic

variable {C : Type u} [Category.{v} C]

/- Shared owner layer for Lemmas `21.39.7` and `21.39.8`:
- the source-facing pointlike-hom-spaces hypothesis on a cosimplicial object;
- its simplicial-evaluation functors and derived-category realization;
- the category-over-a-point derived lower shriek owner `Lπ!`.

These declarations form the reusable chapter-level core; the later Stacks-numbered lemma files add
their source-facing comparison theorems on top of this owner layer. -/

/-- The simplicial set whose `n`-simplices are the morphisms from the `n`-th term of the
cosimplicial object `U_•` to an object `U` of `C`. -/
abbrev cosimplicialHomSSet (Ubullet : CosimplicialObject C) (U : C) :
    SSet.{v} :=
  ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).obj
      ((CategoryTheory.cosimplicialSimplicialEquiv C).functor.obj (op Ubullet))).obj
    (yoneda.obj U)

/-- Every simplicial set of maps from `U_•` to an object of `C` is homotopy equivalent to the
singleton simplicial set `Δ[0]`. This is the hypothesis appearing in Lemma `21.39.7`. -/
def CosimplicialObjectHasPointlikeHomSpaces (Ubullet : CosimplicialObject C) : Prop :=
  ∀ U : C,
    Nonempty (SimplicialObject.HomotopyEquiv
      (cosimplicialHomSSet Ubullet U)
      (Δ[0] : SSet))

/-- Canonical companion for `CosimplicialObjectHasPointlikeHomSpaces`: since `Δ[0]` is terminal,
the source-facing pointlike-hom-spaces hypothesis can be reformulated using the canonical terminal
morphism to `Δ[0]`. -/
theorem cosimplicialObjectHasPointlikeHomSpaces_iff_terminal_from_isHomotopyEquivalence
    (Ubullet : CosimplicialObject C) :
    CosimplicialObjectHasPointlikeHomSpaces Ubullet ↔
      ∀ U : C,
        SimplicialObject.IsHomotopyEquivalence
          (isTerminalObj₀.from (cosimplicialHomSSet Ubullet U)) := by
  constructor
  · intro h U
    rcases h U with ⟨e⟩
    refine ⟨e, ?_⟩
    exact isTerminalObj₀.hom_ext e.hom (isTerminalObj₀.from _)
  · intro h U
    rcases h U with ⟨e, _⟩
    exact ⟨e⟩

end Generic

section Evaluation

variable {C : Type u} [Category.{v} C]

/-- Evaluating an `A`-valued presheaf on the simplicial object attached to `U_•` produces a
simplicial object of `A`. -/
abbrev cosimplicialEvaluationSimplicialObject
    (A : Type w) [Category A] (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ SimplicialObject A :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ A).obj
    ((CategoryTheory.cosimplicialSimplicialEquiv C).functor.obj (op Ubullet))

variable (A : Type w) [Category A] [Abelian A]

/-- The chain complex associated to evaluating a presheaf on the cosimplicial object `U_•` in an
abelian target category `A`. -/
abbrev cosimplicialEvaluationComplex (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ ChainComplex A ℕ :=
  cosimplicialEvaluationSimplicialObject A Ubullet ⋙
    alternatingFaceMapComplex A

variable [HasDerivedCategory A]

/-- The derived-category realization of the simplicial object obtained by evaluating a presheaf on
`U_•`. -/
noncomputable abbrev cosimplicialEvaluationToDerived (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  cosimplicialEvaluationComplex A Ubullet ⋙
    ComplexShape.embeddingDownNat.extendFunctor A ⋙
    DerivedCategory.Q

end Evaluation

end CategoryTheory

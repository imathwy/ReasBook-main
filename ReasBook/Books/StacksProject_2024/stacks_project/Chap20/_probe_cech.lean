import StacksProject_2024.Chap20.Lemma_20_9_3

open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace HomologicalComplex
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open scoped BigOperators ZeroObject

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v}

example (U : Opens X) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (hcover : U = iSup 𝒰) :
    cechAugmentationMap U 𝒰 F hcover ≫ (cechComplex 𝒰 F).d 0 1 = 0 := by
  rw [cechComplexFunctor_d_eq_objD]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  trace_state
  sorry

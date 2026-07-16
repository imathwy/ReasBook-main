import stacks_proof.stacks_project.Chap10.Lemma_10_75_3_Support.RowCycle

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ ComplexShape

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

-- Proof sketch: filter the total complex by horizontal degree. The associated graded pieces are
-- the rows of `A`, and the induced augmentation on the `j`-th graded piece is exactly
-- `rowAugmentation A j`. Since each row augmentation is a quasi-isomorphism by hypothesis, the
-- total comparison map is a quasi-isomorphism.
/-- If the rows of `A` resolve `R(A)_•`, then the canonical map from `Tot(A)` to `R(A)_•` is a
quasi-isomorphism. -/
theorem totalToRowCokernel_quasiIso
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) :
    QuasiIso (totalToRowCokernel A) :=
  -- TODO: Rebuild the fixed-degree filtration argument from the repaired `RowCycle` staircase
  -- recursion and the row augmentation exactness lemmas.
  sorry

end

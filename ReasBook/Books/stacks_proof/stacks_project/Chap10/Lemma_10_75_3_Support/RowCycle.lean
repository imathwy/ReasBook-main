import stacks_proof.stacks_project.Chap10.Lemma_10_75_3_Support.Core

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ ComplexShape

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

/-- Helper for Chap10 Lemma 10 75 3: once one staircase step is known, the next vertical defect
is a positive-degree row cycle. -/
private theorem zigzagSuccessorVerticalDefect_rowCycle
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ) {m : ℕ} (i : Fin (m + 1))
    {zPrev : T ⟶ (A.X i.castSucc.1).X (n + 1 - i.castSucc.1)}
    {zNext : T ⟶ (A.X i.succ.1).X (n + 1 - i.succ.1)}
    (hz :
      zNext ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simp)
            (succSub_castSucc_eq n i)).hom =
        zPrev ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1)) :
    (zNext ≫ (A.X i.succ.1).d (n + 1 - i.succ.1) (n - i.succ.1)) ≫
        (A.d i.succ.1 i.castSucc.1).f (n - i.succ.1) = 0 := by
  -- Postcompose the staircase step by the next vertical differential.
  have hpost := congrArg
    (fun f ↦ f ≫ (A.X i.1).d (n - i.1) (n - i.succ.1)) hz
  -- Rewrite the left side through bicomplex commutativity and kill the right side by `d ≫ d = 0`.
  calc
    (zNext ≫ (A.X i.succ.1).d (n + 1 - i.succ.1) (n - i.succ.1)) ≫
        (A.d i.succ.1 i.castSucc.1).f (n - i.succ.1)
      =
        (zNext ≫
            (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
              (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
                (by simp)
                (succSub_castSucc_eq n i)).hom) ≫
          (A.X i.1).d (n - i.1) (n - i.succ.1) := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ zNext ≫ f) (staircaseTransport_comm A n i).symm
    _ =
        (zPrev ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1)) ≫
          (A.X i.1).d (n - i.1) (n - i.succ.1) := by
            simpa [Category.assoc] using hpost
    _ = 0 := by
          simpa [Category.assoc] using
            congrArg (fun f ↦ zPrev ≫ f)
              ((A.X i.1).d_comp_d (n + 1 - i.1) (n - i.1) (n - i.succ.1))

/-- Helper for Chap10 Lemma 10 75 3: one positive row-exactness refinement appends the next
entry to an unsigned staircase prefix while preserving the earlier equations after precomposition.
-/
private theorem extendUnsignedStaircasePrefix
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (n m : ℕ)
    {T : ModuleCat R}
    (z : ∀ i : Fin (m + 2), T ⟶ (A.X i.1).X (n + 1 - i.1))
    (hz : ∀ i : Fin (m + 1),
      z i.succ ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simp)
            (antidiagonalSuccVertical_eq n i)).hom =
        z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1)) :
    ∃ (T' : ModuleCat R) (σ : T' ⟶ T) (_ : Epi σ)
      (z' : ∀ i : Fin (m + 3), T' ⟶ (A.X i.1).X (n + 1 - i.1)),
        (∀ i : Fin (m + 2), z' i.castSucc = σ ≫ z i) ∧
          ∀ i : Fin (m + 2),
            z' i.succ ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
                (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
                  (by simp)
                  (antidiagonalSuccVertical_eq n i)).hom =
              z' i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1) :=
  -- TODO: Reconcile the support split with the staircase-extension proof by normalizing the last
  -- index to `m`/`m + 1`, then reuse `rowPositiveBoundary_refinement` and the cast-successor
  -- transport lemmas without relying on hidden definitional equalities.
  sorry

/-- Helper for Chap10 Lemma 10 75 3: a row cocycle in positive total degree lifts, after a single
refinement, to the full unsigned staircase family on the antidiagonal. -/
private theorem refinedRowCycleZigzag
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (n : ℕ)
    {T : ModuleCat R} (y₂ : T ⟶ (rowCokernelComplex A).X (n + 1))
    (hy₂ : y₂ ≫ rowCokernelDifferential A n = 0) :
    ∃ (T' : ModuleCat R) (π : T' ⟶ T) (_ : Epi π)
      (z : ∀ i : Fin (n + 2), T' ⟶ (A.X i.1).X (n + 1 - i.1)),
        π ≫ y₂ = z 0 ≫ cokernel.π ((A.d 1 0).f (n + 1)) ∧
          ∀ i : Fin (n + 1),
            z i.succ ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
                (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
                  (by simp)
                  (antidiagonalSuccVertical_eq n i)).hom =
              z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1) :=
  -- TODO: First normalize the head lift from `rowCokernelProjection_refinement`, then rebuild
  -- the initial two-term staircase family in total degree `n + 1` and iterate
  -- `extendUnsignedStaircasePrefix` to length `n + 2`.
  sorry

/-- Helper for Chap10 Lemma 10 75 3: the row comparison satisfies the refinement criterion for
surjectivity on homology in total degree `n`. -/
private theorem totalToRowCokernel_epi_refinement_condition_zero
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) :
    ∀ ⦃T : ModuleCat R⦄ (y₂ : T ⟶ (rowCokernelComplex A).X 0)
      (_ : y₂ ≫ (rowCokernelComplex A).d 0 ((down ℕ).next 0) = 0),
        ∃ (T' : ModuleCat R) (π : T' ⟶ T) (_ : Epi π)
          (x₂ : T' ⟶ (A.total (down ℕ)).X 0)
          (_ : x₂ ≫ (A.total (down ℕ)).d 0 ((down ℕ).next 0) = 0)
          (y₁ : T' ⟶ (rowCokernelComplex A).X 1),
            π ≫ y₂ =
              x₂ ≫ (totalToRowCokernel A).f 0 +
                y₁ ≫ (rowCokernelComplex A).d 1 0 := by
  intro T y₂ hy₂
  -- In total degree `0`, the row comparison sees only the single summand `A_{0,0}`, so the
  -- surjectivity criterion is exactly the degree-zero row-cokernel lift.
  obtain ⟨T', π, hπ, a₀, ha₀⟩ := rowCokernelProjection_refinement A hrows 0 y₂
  let xFamily : ∀ i : Fin 1, T' ⟶ (A.X i.1).X (0 - i.1) :=
    degreeZeroAntidiagonalFamily A a₀
  let x₂ : T' ⟶ (A.total (down ℕ)).X 0 := totalAntidiagonalLift A 0 xFamily
  refine ⟨T', π, hπ, x₂, ?_, 0, ?_⟩
  · -- The degree-zero differential in a chain complex indexed by `down ℕ` vanishes.
    have hshape : ¬ (down ℕ).Rel 0 ((down ℕ).next 0) := by
      simpa [ChainComplex.next_nat_zero, ComplexShape.down, ComplexShape.down']
    dsimp [x₂]
    rw [(A.total (down ℕ)).shape 0 ((down ℕ).next 0) hshape]
    simp
  · -- The assembled total map has the prescribed row-cokernel image, and no correction term is
    -- needed in degree zero.
    rw [zero_comp]
    rw [add_zero]
    change π ≫ y₂ = x₂ ≫ totalToRowCokernelComponent A 0
    calc
      π ≫ y₂ = a₀ ≫ cokernel.π ((A.d 1 0).f 0) := ha₀
      _ = x₂ ≫ totalToRowCokernelComponent A 0 := by
        dsimp [x₂, xFamily]
        simpa using (totalAntidiagonalLift_totalToRowCokernelComponent A 0 xFamily).symm

end

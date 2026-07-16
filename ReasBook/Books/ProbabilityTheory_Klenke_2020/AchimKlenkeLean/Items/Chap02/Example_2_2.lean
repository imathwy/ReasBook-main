import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Example_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory ProbabilityTheory

noncomputable section

/-- The sample space of three successive die rolls. -/
abbrev ThreeRolls := Fin 3 → Die

/-- The law of three independent fair die rolls. -/
abbrev threeRollsMeasure : Measure ThreeRolls :=
  Measure.pi fun _ : Fin 3 ↦ dieMeasure

/-- The three coordinate projections on the product space of die rolls are independent. -/
theorem threeRolls_iIndepFun :
    iIndepFun Function.eval threeRollsMeasure := by
  simpa [Function.eval, threeRollsMeasure] using
    (iIndepFun_pi (fun _ : Fin 3 ↦ measurable_id.aemeasurable) :
      iIndepFun (fun i (ω : ThreeRolls) ↦ ω i) (Measure.pi fun _ : Fin 3 ↦ dieMeasure))

/-- The three diagonal events `ω₀ = ω₁`, `ω₁ = ω₂`, and `ω₀ = ω₂`. -/
def diagonalEqualityEvents : Fin 3 → Set ThreeRolls
  | 0 => {ω : ThreeRolls | ω 0 = ω 1}
  | 1 => {ω : ThreeRolls | ω 1 = ω 2}
  | 2 => {ω : ThreeRolls | ω 0 = ω 2}

-- Proof sketch: `threeRollsMeasure` is a product measure, so the coordinate maps are independent;
-- apply this to the measurable sets `S i`.
/-- Events depending separately on the first, second, and third die roll are independent. -/
theorem coordinatePreimage_iIndepSet (S : Fin 3 → Set Die) :
    iIndepSet (fun i ↦ Function.eval i ⁻¹' S i) threeRollsMeasure := by
  rw [iIndepSet_iff_meas_biInter]
  · intro s
    simpa [Function.eval] using
      threeRolls_iIndepFun.measure_inter_preimage_eq_mul s
        (fun i _ ↦ (Set.toFinite (S i)).measurableSet)
  · intro i
    exact (measurable_pi_apply i) ((Set.toFinite (S i)).measurableSet)

-- Proof sketch: compute the probabilities of the pairwise intersections by counting outcomes in
-- the `216`-point sample space.
/-- The three diagonal equality events are pairwise independent. -/
theorem diagonalEqualityEvents_pairwise :
    Pairwise fun i j ↦ IndepSet (diagonalEqualityEvents i) (diagonalEqualityEvents j)
      threeRollsMeasure := sorry

-- Proof sketch: all three diagonal equalities hold exactly when all three rolls coincide, so the
-- probability of the triple intersection is `1 / 36`, whereas the product of the three marginal
-- probabilities is `1 / 216`.
/-- The three diagonal equality events are not independent as a family. -/
theorem diagonalEqualityEvents_not_iIndep :
    ¬ iIndepSet diagonalEqualityEvents threeRollsMeasure := sorry

-- Proof sketch: for the first clause, use that `threeRollsMeasure` is the uniform product measure
-- on `Fin 3 → Fin 6`, so events depending on disjoint coordinates are independent. For the second
-- clause, compute the probabilities of the three diagonal events and of their intersections by
-- counting outcomes.
/-- Example 2.2: For three fair die rolls, events depending separately on the first, second, and
third coordinate are independent, while the events `ω₁ = ω₂`, `ω₂ = ω₃`, and `ω₁ = ω₃` are
pairwise independent but not independent as a triple. -/
theorem roll_three_times_independence_examples :
    (∀ S : Fin 3 → Set Die,
      iIndepSet (fun i ↦ Function.eval i ⁻¹' S i) threeRollsMeasure) ∧
    Pairwise (fun i j ↦ IndepSet (diagonalEqualityEvents i) (diagonalEqualityEvents j)
      threeRollsMeasure) ∧
    ¬ iIndepSet diagonalEqualityEvents threeRollsMeasure := by
  exact ⟨coordinatePreimage_iIndepSet, diagonalEqualityEvents_pairwise,
    diagonalEqualityEvents_not_iIndep⟩

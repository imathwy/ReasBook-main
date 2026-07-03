import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_20_36 (from Items/Chap20) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  refine ⟨by
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
    exact AddCircle.measure_univ (1 : ℝ)
  ⟩

/-- The half-circle corresponding to the interval `[1 / 2, 1)` in the `[0,1)` model. -/
noncomputable def unitAddCircleRightHalf : Set UnitAddCircle :=
  (fun x : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) ⁻¹' Set.Ico (1 / 2 : ℝ) 1

private theorem measurableSet_unitAddCircleRightHalf : MeasurableSet unitAddCircleRightHalf := by
  simpa [unitAddCircleRightHalf] using
    (MeasurableSet.preimage measurableSet_Ico
      (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable))

private noncomputable def unitAddCircleRightHalfSet :
    Subtype (MeasurableSet : Set UnitAddCircle → Prop) :=
  ⟨unitAddCircleRightHalf, measurableSet_unitAddCircleRightHalf⟩

private noncomputable def unitAddCircleLeftHalfSet :
    Subtype (MeasurableSet : Set UnitAddCircle → Prop) :=
  ⟨unitAddCircleRightHalfᶜ, measurableSet_unitAddCircleRightHalf.compl⟩

/-- The two-atom partition of `AddCircle 1` into the left and right half-circles. -/
noncomputable def unitAddCircleHalfPartition : MeasurableFinpartition UnitAddCircle := by
  classical
  refine Finpartition.ofErase {unitAddCircleRightHalfSet, unitAddCircleLeftHalfSet} ?_ ?_
  · refine Finset.supIndep_iff_pairwiseDisjoint.mpr ?_
    intro a ha b hb hab
    simp at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · intro s hs_right hs_left x hx
      exact (hs_left hx) (hs_right hx)
    · intro s hs_left hs_right x hx
      exact (hs_left hx) (hs_right hx)
    · exact (hab rfl).elim
  · ext x
    simp [unitAddCircleRightHalfSet, unitAddCircleLeftHalfSet, Finset.sup_insert,
      Finset.sup_singleton]

private noncomputable def unitAddCircleHalfBlockCode
    (r : ℝ) (n : ℕ+) (x : UnitAddCircle) : Fin n → Bool :=
  letI : DecidablePred fun y : UnitAddCircle ↦ y ∈ unitAddCircleRightHalf := Classical.decPred _
  fun i ↦ if ((((· + (r : UnitAddCircle)))^[i]) x ∈ unitAddCircleRightHalf) then true else false

-- Proof sketch: `MeasurableFinpartition.block` is the canonical joined partition from
-- Definition 20.34, while `unitAddCircleHalfBlockCode` is the same block data viewed through the
-- textbook Boolean coding of the two half-circle atoms.
/-- The canonical block partition of the half-circle partition has exactly the same distinct
length-`n` words as the textbook binary coding. -/
private theorem unitAddCircleHalfPartition_block_proj (r : ℝ) (n : ℕ+) :
    Nat.card ↥((unitAddCircleHalfPartition.block
      ((· + (r : UnitAddCircle)))
      (measurePreserving_add_right volume (r : UnitAddCircle)).measurable n).parts) =
      Nat.card ↥(Set.range (unitAddCircleHalfBlockCode r n)) := sorry

-- Proof sketch: write `r = a / b` with `b > 0`, take `n = b`, and use that `n • r` is an
-- integer, so translation by `r` has finite order on `AddCircle 1`.
/-- Example 20.36 (1): if `r` is rational, then the rotation `x ↦ x + r` on `AddCircle 1` is
periodic. -/
private theorem unitAddCircleRotation_iterate_eq_id_of_rational (r : ℝ)
    (hr : ∃ q : ℚ, (q : ℝ) = r) :
    ∃ n : ℕ, 0 < n ∧ (((· + (r : UnitAddCircle)))^[n] = id) := sorry

-- Proof sketch: if some iterate of the rotation is the identity, then every length-`n` block
-- partition of a finite measurable partition is eventually periodic in `n`, so the normalized
-- block entropies tend to `0`.
/-- Example 20.36 (1): if `r` is rational, then every finite measurable partition has dynamical
entropy `0` for the rotation `x ↦ x + r` on `AddCircle 1`. -/
theorem unitAddCircleRotation_dynamicalEntropy_eq_zero_of_rational
    (r : ℝ) (hr : ∃ q : ℚ, (q : ℝ) = r) (part : MeasurableFinpartition UnitAddCircle) :
    h(volume, ((· + (r : UnitAddCircle))),
      (measurePreserving_add_right volume (r : UnitAddCircle)).measurable; part) = 0 := sorry

-- Proof sketch: the rational rotation case gives entropy `0` for every finite measurable
-- partition, so the supremum in `kolmogorov_sinai_entropy` is also `0`.
/-- Example 20.36 (1): if `r` is rational, then the Kolmogorov--Sinai entropy of the rotation
`x ↦ x + r` on `AddCircle 1` is `0`. -/
theorem unitAddCircleRotation_kolmogorov_sinai_entropy_eq_zero_of_rational
    (r : ℝ) (hr : ∃ q : ℚ, (q : ℝ) = r) :
    h(volume, ((· + (r : UnitAddCircle))),
      (measurePreserving_add_right volume (r : UnitAddCircle)).measurable) = 0 := sorry

-- Proof sketch: follow the textbook coding argument for the half-circle partition. As the
-- starting point moves around the circle, each coordinate changes only when an orbit point crosses
-- one of the two partition endpoints, yielding at most `2 n` distinct words of positive length
-- `n`.
/-- Example 20.36 (2): if `r` is irrational, then the canonical length-`n` block partition of the
half-circle partition has at most `2 n` atoms, equivalently the half-interval coding has at most
`2 n` distinct binary words of positive length `n`. -/
private theorem unitAddCircleHalfPartition_block_card_le_two_mul_of_irrational
    (r : ℝ) (hr : Irrational r) (n : ℕ+) :
    Nat.card ↥((unitAddCircleHalfPartition.block
      ((· + (r : UnitAddCircle)))
      (measurePreserving_add_right volume (r : UnitAddCircle)).measurable n).parts) ≤
      2 * (n : ℕ) := sorry

-- Proof sketch: for irrational `r`, the backward iterates of the two half-circles separate points
-- on `AddCircle 1`, so they generate the Borel σ-algebra.
/-- For irrational `r`, the canonical half-circle partition is a generator for the rotation
`x ↦ x + r` on `AddCircle 1`. -/
theorem unitAddCircleHalfPartition_is_generator_of_irrational
    (r : ℝ) (hr : Irrational r) :
    is_generator ((· + (r : UnitAddCircle))) unitAddCircleHalfPartition := sorry

-- Proof sketch: the block cardinality bound `#𝒫ₙ ≤ 2 n` forces the normalized block entropies of
-- the half-circle partition to tend to `0`, hence its dynamical entropy is `0`.
/-- Example 20.36 (2): if `r` is irrational, then the dynamical entropy of the canonical
half-circle partition is `0`. -/
theorem unitAddCircleHalfPartition_dynamicalEntropy_eq_zero_of_irrational
    (r : ℝ) (hr : Irrational r) :
    h(volume, ((· + (r : UnitAddCircle))),
      (measurePreserving_add_right volume (r : UnitAddCircle)).measurable;
      unitAddCircleHalfPartition) = 0 := sorry

-- Proof sketch: combine the generator theorem for the half-circle partition with
-- `kolmogorov_sinai_of_generator`, then insert that the partition dynamical entropy is `0`.
/-- Example 20.36 (2): if `r` is irrational, then the Kolmogorov--Sinai entropy of the rotation
`x ↦ x + r` on `AddCircle 1` is `0`. -/
theorem unitAddCircleRotation_kolmogorov_sinai_entropy_eq_zero_of_irrational
    (r : ℝ) (hr : Irrational r) :
    h(volume, ((· + (r : UnitAddCircle))),
      (measurePreserving_add_right volume (r : UnitAddCircle)).measurable) = 0 := sorry

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter ContinuousLinearMap lp
open scoped ENNReal lp Topology

noncomputable section

local notation "countℕ" => (Measure.count : Measure ℕ)

private theorem l1SequenceMemLp_count
    (b : lp (fun _ : ℕ ↦ ℝ) 1) :
    MemLp b 1 countℕ := by
  rw [memLp_one_iff_integrable, integrable_count_iff]
  simpa using (lp.hasSum_norm (show 0 < (1 : ℝ≥0∞).toReal by norm_num) b).summable

private def l1SequenceToCountLp
    (b : lp (fun _ : ℕ ↦ ℝ) 1) :
    Lp ℝ 1 countℕ :=
  (l1SequenceMemLp_count b).toLp b

private theorem l1SequenceToCountLp_apply
    (b : lp (fun _ : ℕ ↦ ℝ) 1) (n : ℕ) :
    l1SequenceToCountLp b n = b n := by
  exact
    ae_iff_of_countable.mp (MemLp.coeFn_toLp (l1SequenceMemLp_count b)) n (by simp)

private theorem l1SequenceToCountLp_norm
    (b : lp (fun _ : ℕ ↦ ℝ) 1) :
    ‖l1SequenceToCountLp b‖ = ‖b‖ := by
  rw [l1SequenceToCountLp, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm, lintegral_count]
  rw [ENNReal.tsum_toReal_eq fun _ ↦ by simp]
  simpa using (lp.hasSum_norm (show 0 < (1 : ℝ≥0∞).toReal by norm_num) b).tsum_eq

private def l1SequenceToCountLpCLM :
    lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] Lp ℝ 1 countℕ :=
  (LinearMap.mkContinuous
      { toFun := l1SequenceToCountLp
        map_add' := fun b₁ b₂ ↦ by
          rw [l1SequenceToCountLp]
          exact (MemLp.toLp_congr (l1SequenceMemLp_count (b₁ + b₂))
            ((l1SequenceMemLp_count b₁).add (l1SequenceMemLp_count b₂)) Filter.EventuallyEq.rfl).trans
            (MemLp.toLp_add (l1SequenceMemLp_count b₁) (l1SequenceMemLp_count b₂))
        map_smul' := fun c b ↦ by
          rw [l1SequenceToCountLp]
          exact (MemLp.toLp_congr (l1SequenceMemLp_count (c • b))
            ((l1SequenceMemLp_count b).const_smul c) Filter.EventuallyEq.rfl).trans
            (MemLp.toLp_const_smul c (l1SequenceMemLp_count b)) }
      1 fun b ↦ by
        simpa [one_mul] using le_of_eq (l1SequenceToCountLp_norm b))

private theorem boundedSequenceMemLp_count
    (x : ℓ^∞(ℕ, ℝ)) :
    MemLp x ∞ countℕ := by
  refine memLp_top_of_bound (measurable_of_countable fun n : ℕ ↦ x n).aestronglyMeasurable ‖x‖ ?_
  exact Filter.Eventually.of_forall fun n ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero x n

private def boundedSequenceToCountLp
    (x : ℓ^∞(ℕ, ℝ)) :
    Lp ℝ ∞ countℕ :=
  (boundedSequenceMemLp_count x).toLp x

private theorem boundedSequenceToCountLp_apply
    (x : ℓ^∞(ℕ, ℝ)) (n : ℕ) :
    boundedSequenceToCountLp x n = x n := by
  exact
    ae_iff_of_countable.mp (MemLp.coeFn_toLp (boundedSequenceMemLp_count x)) n (by simp)

private theorem boundedSequenceToCountLp_norm_le
    (x : ℓ^∞(ℕ, ℝ)) :
    ‖boundedSequenceToCountLp x‖ ≤ ‖x‖ := by
  rw [boundedSequenceToCountLp, Lp.norm_toLp, eLpNorm_exponent_top]
  calc
    ENNReal.toReal (eLpNormEssSup x countℕ)
      ≤ ENNReal.toReal (ENNReal.ofReal ‖x‖) := by
          apply ENNReal.toReal_mono (by simp)
          exact eLpNormEssSup_le_of_ae_bound <|
            Filter.Eventually.of_forall fun n ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero x n
    _ = ‖x‖ := by simp

private def boundedSequenceToCountLpCLM :
    ℓ^∞(ℕ, ℝ) →L[ℝ] Lp ℝ ∞ countℕ :=
  (LinearMap.mkContinuous
      { toFun := boundedSequenceToCountLp
        map_add' := fun x y ↦ by
          rw [boundedSequenceToCountLp]
          exact (MemLp.toLp_congr (boundedSequenceMemLp_count (x + y))
            ((boundedSequenceMemLp_count x).add (boundedSequenceMemLp_count y))
            Filter.EventuallyEq.rfl).trans
            (MemLp.toLp_add (boundedSequenceMemLp_count x) (boundedSequenceMemLp_count y))
        map_smul' := fun c x ↦ by
          rw [boundedSequenceToCountLp]
          exact (MemLp.toLp_congr (boundedSequenceMemLp_count (c • x))
            ((boundedSequenceMemLp_count x).const_smul c) Filter.EventuallyEq.rfl).trans
            (MemLp.toLp_const_smul c (boundedSequenceMemLp_count x)) }
      1 fun x ↦ by
        simpa [one_mul] using boundedSequenceToCountLp_norm_le x)

/-- The canonical pairing map sending an `ℓ¹` sequence to the corresponding continuous linear
	functional on `ℓ^∞(ℕ, ℝ)` given by coefficientwise summation. -/
def l1BoundedSequenceDualityMap :
    lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] StrongDual ℝ (ℓ^∞(ℕ, ℝ)) :=
  ((precompL (ℓ^∞(ℕ, ℝ)) (((mul ℝ ℝ).lpPairing countℕ 1 ∞).flip)) boundedSequenceToCountLpCLM).comp
    l1SequenceToCountLpCLM

/-- Evaluating the canonical `ℓ¹`-pairing functional on a bounded sequence gives the expected
coefficientwise sum. -/
theorem l1BoundedSequenceDualityMap_apply
    (b : lp (fun _ : ℕ ↦ ℝ) 1) (x : ℓ^∞(ℕ, ℝ)) :
    l1BoundedSequenceDualityMap b x = ∑' n, x n * b n := by
  have h_integrable :
      Integrable (fun n : ℕ ↦ l1SequenceToCountLp b n * boundedSequenceToCountLp x n)
        countℕ := by
    rw [← memLp_one_iff_integrable]
    exact (mul ℝ ℝ).memLp_of_bilin 1 (Lp.memLp (l1SequenceToCountLp b))
      (Lp.memLp (boundedSequenceToCountLp x))
  rw [l1BoundedSequenceDualityMap]
  change
    (((precompL (ℓ^∞(ℕ, ℝ)) (((mul ℝ ℝ).lpPairing countℕ 1 ∞).flip)) boundedSequenceToCountLpCLM)
      (l1SequenceToCountLpCLM b)) x = ∑' n, x n * b n
  rw [ContinuousLinearMap.precompL_apply]
  rw [ContinuousLinearMap.flip_apply]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  change ∫ n : ℕ, l1SequenceToCountLp b n * boundedSequenceToCountLp x n ∂countℕ =
    ∑' n, x n * b n
  rw [integral_countable h_integrable]
  simp [l1SequenceToCountLp_apply, boundedSequenceToCountLp_apply, smul_eq_mul, mul_comm]

-- Proof sketch: extend the limit functional on the subspace of convergent bounded sequences to all
-- of `ℓ^∞(ℕ)` by Hahn--Banach, then test the extension on standard bounded sequences to show that
-- no coefficient sequence in `ℓ¹` can represent it by coordinatewise summation.
/-- Remark 7.51: there exists a continuous linear functional on `ℓ^∞(ℕ)` which agrees with the
ordinary limit on every convergent bounded sequence but does not lie in the range of the canonical
pairing map `ℓ¹(ℕ) → (ℓ^∞(ℕ))'`. Equivalently, it is not given by pairing with any `ℓ¹`
sequence. -/
theorem exists_non_l1_representable_limit_extension_on_bounded_sequences :
    ∃ F : StrongDual ℝ (ℓ^∞(ℕ, ℝ)),
      (∀ ⦃x : ℓ^∞(ℕ, ℝ)⦄ ⦃l : ℝ⦄, Tendsto (fun n ↦ x n) atTop (𝓝 l) → F x = l) ∧
      F ∉ Set.range l1BoundedSequenceDualityMap := sorry

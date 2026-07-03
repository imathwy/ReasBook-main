

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_15_42 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

open RealRandomVariableArray

section IIDStandardizedArray

variable (Y : ℕ → Ω → ℝ) (hY_meas : ∀ n, Measurable (Y n))

/- Example 15.42 is `source-facing`: it constructs the standardized triangular array attached to
an i.i.d. sequence. Its `core/canonical` owner in this chapter is `RealRandomVariableArray Ω`; the
pointwise formula below is only the bridge/view back to the textbook coordinates. -/
/-- Example 15.42: from a `0`-based Lean i.i.d. sequence `Y 0, Y 1, ...` representing the
textbook sequence `Y₁, Y₂, ...`, the `n`-th Lean row models the textbook row `n + 1` and has
entries `Y_i / √(n + 1)`. -/
def iid_standardized_array : RealRandomVariableArray Ω where
  rowLength n := n + 1
  entry n i ω := Y i.1 ω / Real.sqrt (n + 1 : ℝ)
  measurable_entry n i := by
    simpa using (hY_meas i.1).div_const (Real.sqrt (n + 1 : ℝ))

-- Proof sketch: unfold `iid_standardized_array` and read off the defining formula.
/-- The standardized array entry is the `i`-th coordinate divided by `√(n + 1)`. -/
theorem iid_standardized_array_apply (n : ℕ) (i : Fin (n + 1)) (ω : Ω) :
    iid_standardized_array Y hY_meas n i ω = Y i.1 ω / Real.sqrt (n + 1 : ℝ) := rfl

-- Proof sketch: use the measurable-entry field of the owner array.
/-- The entries of the standardized i.i.d. triangular array are measurable. -/
theorem measurable_iid_standardized_array_entry (n : ℕ) (i : Fin (n + 1)) :
    Measurable (iid_standardized_array Y hY_meas n i) :=
  (iid_standardized_array Y hY_meas).measurable_entry n i

variable {Y hY_meas}
variable {P : Measure Ω}

-- Proof sketch: each row is the finite restriction of the independent family `Y`, scaled by the
-- row-constant `√(n + 1)`.
/-- Every row of the standardized array is an independent finite family. -/
theorem iid_standardized_array_isIndependent
    (hY_indep : iIndepFun Y P) :
    IsIndependent (iid_standardized_array Y hY_meas) P := sorry

variable [IsProbabilityMeasure P]

-- Proof sketch: identical distribution transfers centeredness from `Y 0` to every coordinate, and
-- scaling by the deterministic constant `√(n + 1)` preserves mean zero.
/-- The standardized i.i.d. triangular array is centered when the common law is centered. -/
theorem iid_standardized_array_isCentered
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_centered : _root_.IsCentered (Y 0) P) :
    IsCentered (iid_standardized_array Y hY_meas) P := sorry

-- Proof sketch: identical distribution gives each row entry the variance of `Y 0` scaled by
-- `(n + 1)⁻¹`, so the row-variance sum is `1`.
/-- The standardized i.i.d. triangular array is normed when the common variance is `1`. -/
theorem iid_standardized_array_isNormed
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_var : Var[Y 0; P] = 1) :
    IsNormed (iid_standardized_array Y hY_meas) P := sorry

-- Proof sketch: the tail event for any row entry is `|Y i| > ε √(n + 1)`; by identical
-- distribution this does not depend on `i`, and the threshold tends to infinity with `n`.
/-- The standardized i.i.d. triangular array is null when the common law is centered. -/
theorem iid_standardized_array_isNull
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_centered : _root_.IsCentered (Y 0) P) :
    IsNull (iid_standardized_array Y hY_meas) P := sorry

-- Proof sketch: independence identifies `Var[Sₙ]` with the sum of the row variances, so for the
-- standardized array the owner `lindebergFunction` is the truncated second moment of `Y 0`
-- outside the threshold `ε √(n + 1)`; identical distribution then reduces the row sum to a single
-- common term, which tends to `0`.
/-- The standardized triangular array attached to an i.i.d. sequence satisfies the chapter owner's
Lindeberg condition. -/
theorem iid_standardized_array_lindeberg
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_centered : _root_.IsCentered (Y 0) P)
    (hY_var : Var[Y 0; P] = 1) :
    SatisfiesLindebergCondition (iid_standardized_array Y hY_meas) P := sorry

-- Proof sketch: independence again identifies the owner denominator through
-- `Var[(iid_standardized_array Y hY_meas).rowSum n; P]`, and identical distribution reduces the
-- numerator to `(n + 1) ^ (-δ / 2)` times the common `(2 + δ)`-moment of `Y 0`, which tends to
-- `0`.
/-- If an i.i.d. sequence has a finite common `(2 + δ)`-moment for some `δ > 0`, then its
standardized triangular array satisfies the chapter owner's Lyapunov condition. -/
theorem iid_standardized_array_lyapunov
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_centered : _root_.IsCentered (Y 0) P) {δ : ℝ} (hδ : 0 < δ)
    (hY_moment : Integrable (fun ω ↦ Real.rpow |Y 0 ω| (2 + δ)) P) :
    SatisfiesLyapunovCondition (iid_standardized_array Y hY_meas) P := sorry

end IIDStandardizedArray

end

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_38 (from Chap07) -/
noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n : ℕ} {m : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- This item lies in the chapter's finite max-absolute-inner / symmetric log-sum-exp
smoothing domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the project owner and
  its evaluation bridge for finite maxima of nonempty families;
- `absLinearLogSumExp` in `Chap07/Proposition_7_14`, the chapter owner for the symmetric
  log-sum-exp smoothing;
- `absLinearLogSumExp_apply` in `Chap07/Proposition_7_14`, the defining evaluation theorem for
  that smoothing owner.

Best owner abstraction:
- source-facing: the max-absolute-inner objective and its smooth log-sum-exp approximation;
- core/canonical: `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)` and `absLinearLogSumExp μ a`;
- bridge/view: direct recall of the positive-parameter owner surface.

Primitive data:
- a finite family `a : Fin (m : ℕ) → E`;
- a positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the canonical max-objective owner `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`;
- the canonical smoothing owner `absLinearLogSumExp μ a`.

Source/core/bridge triage:
- source-facing: the textbook formula for the max-absolute-inner objective and its smoothing;
- core/canonical: the project finite-max owner `maxTypeObjective` and the earlier Chapter 7
  smoothing owner `absLinearLogSumExp`;
- bridge/view: direct recall of the positive-parameter smoothing owner.

The previous file duplicated these owners as `maxAbsoluteInnerFunction` and
`maxAbsoluteInnerLogSumExpSmoothing`. Those wrappers carried no extra mathematics. This refined
file reuses the earlier owners directly; after fixing `Proposition_7_14` to make positivity part
of the owner itself, no extra subtype-specialization theorem is needed here.
-/

section

variable (a : Fin (m : ℕ) → E) (μ : {μ : ℝ // 0 < μ})

/- The unsmoothed objective uses the canonical finite-max owner
`maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`. -/
set_option linter.hashCommand false in
#check maxTypeObjective (fun i x ↦ |inner ℝ (a i) x|)

/- Definition 7.38: for a finite family `a : Fin (m : ℕ) → E` and a positive parameter
`μ : {μ : ℝ // 0 < μ}`, the textbook log-sum-exp smoothing
`x ↦ μ log (∑ i, [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)])`
is the Chapter 7 owner `absLinearLogSumExp μ a`. -/
#check (absLinearLogSumExp μ a : E → ℝ)

end

/-! ### Proposition_7_38 (from Chap07) -/
noncomputable section

/- Proposition 7.38 lies in Chapter 7's mixed-accuracy / scalar iteration-bound domain.

Relevant owner-style declarations sampled before refinement:
- `relativeScaleIterationBound` in `Proposition_7_40`, the sibling Chapter 7 owner for the
  logarithmic iteration budget in the same quasi-Newton complexity lane;
- `relativeScaleUniformIterationBound` in `Proposition_7_40`, the companion dimension-free
  comparison owner for that sibling bound;
- `relativeScaleIterationBound_lt_uniformBound` in `Proposition_7_40`, the matching strict
  comparison theorem, which makes the strictness hypotheses for the logarithmic estimate explicit;
- `mixedAccuracyIterationCountBound` in `Definition_7_91`, the direct downstream recall surface
  that treats the present file as the owner source.

Best owner abstraction:
- source-facing: the textbook mixed-accuracy iteration budget `N_n(ε, δ)`;
- core/canonical: the scalar owner `mixedAccuracyIterationCountBound`;
- bridge/view: the expansion theorem
  `mixedAccuracyIterationCountBound_def` and the dimension-free comparison owner
  `mixedAccuracyUniformIterationCountBound`.

Primitive data:
- the dimension `n : ℕ+`;
- the constants `L`, `R`, `ε`, and `δ`.

Derived API:
- the logarithmic expansion of `N_n(ε, δ)`;
- the dimension-free comparison quantity `N_∞(ε, δ)`;
- the strict comparison theorem between the finite-dimensional and dimension-free bounds.

The earlier version let the owner depend on `n : ℕ`, which admits the non-source case `n = 0`,
and stated the strict comparison without the nonvanishing hypothesis `L * R ≠ 0` that the strict
logarithmic inequality actually needs. This refinement keeps the same mathematical formulas while
moving the public surface to the faithful positive-dimension owner level already used by the
sibling bound file `Proposition_7_40`.
-/

/-- The iteration bound `N_n(ε, δ)` from `(7.4.20)` for the mixed-accuracy method in dimension
`n`. -/
abbrev mixedAccuracyIterationCountBound
    (n : ℕ+) (L R ε δ : ℝ) : ℝ :=
  (n : ℝ) / δ * Real.log (1 + (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * ε))

-- Proof sketch: unfold `mixedAccuracyIterationCountBound`.
/-- Expanding `mixedAccuracyIterationCountBound n L R ε δ` recovers the logarithmic formula
`(n / δ) log (1 + L² R² / (2 n ε))`. -/
theorem mixedAccuracyIterationCountBound_def
    (n : ℕ+) (L R ε δ : ℝ) :
    mixedAccuracyIterationCountBound n L R ε δ =
      (n : ℝ) / δ * Real.log (1 + (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * ε)) := rfl

/-- The dimension-free upper bound `N_∞(ε, δ) = L² R² / (2 ε δ)` for the mixed-accuracy
iteration count. -/
abbrev mixedAccuracyUniformIterationCountBound
    (L R ε δ : ℝ) : ℝ :=
  (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * ε * δ)

-- Proof sketch: unfold `mixedAccuracyUniformIterationCountBound`.
/-- Expanding `mixedAccuracyUniformIterationCountBound L R ε δ` recovers the formula
`L² R² / (2 ε δ)`. -/
theorem mixedAccuracyUniformIterationCountBound_def
    (L R ε δ : ℝ) :
    mixedAccuracyUniformIterationCountBound L R ε δ =
      (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * ε * δ) := rfl

-- Proof sketch: write `mixedAccuracyIterationCountBound n L R ε δ` as
-- `(n / δ) * log (1 + x)` with `x = L² R² / (2 n ε)`, use `Real.log_lt_sub_one_of_pos`
-- on the positive argument `1 + x`, and simplify to obtain the strict upper bound
-- `L² R² / (2 ε δ)`.
/-- Proposition 7.38: for `ε > 0` and `δ > 0`, the mixed-accuracy iteration bound
`N_n(ε, δ)` from `(7.4.20)` is strictly less than the dimension-free bound
`N_∞(ε, δ) = L² R² / (2 ε δ)` whenever `L R ≠ 0`. -/
theorem mixedAccuracyIterationCountBound_lt_uniformUpperBound
    (n : ℕ+) (L R ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hLR : L * R ≠ 0) :
    mixedAccuracyIterationCountBound n L R ε δ <
      mixedAccuracyUniformIterationCountBound L R ε δ := by
  let x : ℝ := (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * ε)
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have hx : 0 < x := by
    dsimp [x]
    have hL : L ≠ 0 := left_ne_zero_of_mul hLR
    have hR : R ≠ 0 := right_ne_zero_of_mul hLR
    have hLsq : 0 < L ^ (2 : ℕ) := by
      simpa [pow_two] using mul_self_pos.mpr hL
    have hRsq : 0 < R ^ (2 : ℕ) := by
      simpa [pow_two] using mul_self_pos.mpr hR
    have hden : 0 < 2 * (n : ℝ) * ε := by
      positivity
    exact div_pos (mul_pos hLsq hRsq) hden
  have hlog : Real.log (1 + x) < x := by
    have hpos : 0 < 1 + x := by linarith
    have hne : 1 + x ≠ (1 : ℝ) := by linarith
    simpa [sub_eq_add_neg] using Real.log_lt_sub_one_of_pos hpos hne
  have hmul :
      (n : ℝ) / δ * Real.log (1 + x) <
        (n : ℝ) / δ * x := by
    exact mul_lt_mul_of_pos_left hlog (div_pos hn hδ)
  calc
    mixedAccuracyIterationCountBound n L R ε δ
        = (n : ℝ) / δ * Real.log (1 + x) := by
          simp [mixedAccuracyIterationCountBound, x]
    _ < (n : ℝ) / δ * x := hmul
    _ = mixedAccuracyUniformIterationCountBound L R ε δ := by
          dsimp [mixedAccuracyUniformIterationCountBound, x]
          field_simp [hδ.ne', hε.ne', hn.ne']

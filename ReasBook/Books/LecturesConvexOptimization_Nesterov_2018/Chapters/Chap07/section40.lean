import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_40 (from Chap07) -/
noncomputable section

open scoped StandardSimplex

variable {n m : ℕ+}

local notation "Δₙ" => Δ[n]

/- Definition 7.40 lies in the finite simplex / simplex-saddle-point matrix-game domain.

Sampled owner-style declarations:
- `stdSimplex` and the Chapter 6 notation `Δ[n]` in `Chap06/Definition_6_11`, the canonical
  simplex owner;
- `SimplexSaddlePointProblem.primalObjective` in `Chap06/Definition_6_12`, the chapter owner for
  simplex max-type objectives of the form `x ↦ ⟪c, x⟫ + max_j {⟪a_j, x⟫ + b^(j)}`;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project
  owner for constrained optimal values.

Best owner abstraction:
- source-facing: the matrix-game payoff on the simplex `Δ[n]`;
- core/canonical: `SimplexSaddlePointProblem.primalObjective` for the zero-linear-term saddle
  problem with matrix `Aᵀ`, together with `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the specialization from a nonnegative matrix-game matrix `A` to that simplex
  saddle-point owner, and the whole-domain constrained problem on the simplex subtype.

Primitive data:
- the matrix `A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ`.

Derived API:
- the specialized simplex saddle-point problem with zero linear terms;
- the simplex payoff function;
- its textbook coordinate formula `max_i ⟪a_i, x⟫`;
- the constrained optimal value over simplex points.

The previous file overextended the source-facing matrix-game payoff to arbitrary `m : ℕ` by
inserting a synthetic `m = 0` branch, and it introduced a separate raw real-valued infimum. This
refinement moves back to the chapter's positive simplex dimension layer `n m : ℕ+`, reuses the
earlier Chapter 6 simplex saddle-point owner for the payoff, and derives the value from the
Chapter 1 constrained minimization owner instead of rebuilding a parallel value API.
-/

/-- The nonnegative matrix-game matrix determines a simplex saddle-point problem with zero primal
and dual linear terms. The row-wise primal objective of this owner is exactly the matrix-game
payoff. -/
def nonnegative_matrix_game_saddle_problem
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) :
    SimplexSaddlePointProblem n m where
  matrix := A.transpose
  primalLinearTerm := 0
  dualLinearTerm := 0

/-- Definition 7.40: for the matrix `A` in the textbook nonnegative-matrix-game setup, the
associated simplex payoff is the Chapter 6 primal objective of the zero-linear-term simplex
saddle-point problem with matrix `Aᵀ`, restricted to `Δ[n]`. -/
def nonnegative_matrix_game_payoff
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) : Δₙ → ℝ :=
  (nonnegative_matrix_game_saddle_problem A).primalObjective

/-- Evaluating `nonnegative_matrix_game_payoff A` recovers the textbook formula
`max_i ⟪a_i, x⟫`. -/
theorem nonnegative_matrix_game_payoff_apply
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) (x : Δₙ) :
    nonnegative_matrix_game_payoff A x =
      ⨆ i : Fin (m : ℕ), dotProduct (fun j ↦ A j i) x.1 := by
  simpa [nonnegative_matrix_game_payoff, nonnegative_matrix_game_saddle_problem,
    Finset.sup'_univ_eq_ciSup] using
    SimplexSaddlePointProblem.primalObjective_eq_max_rows
      (nonnegative_matrix_game_saddle_problem A) x

/-- The minimax value `f* = min_{x ∈ Δ_n} f(x)` attached to `A`, formalized as the infimum of the
payoff over the standard simplex through the Chapter 1 constrained minimization owner. -/
def nonnegative_matrix_game_value
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) : EReal :=
  (SetConstrainedMinimizationProblem.mk Set.univ (nonnegative_matrix_game_payoff A)).optimalValue

/-- Expanding `nonnegative_matrix_game_value A` gives the infimum of the simplex payoff range. -/
theorem nonnegative_matrix_game_value_eq_sInf_range
    (A : Matrix (Fin (n : ℕ)) (Fin (m : ℕ)) ℝ) :
    nonnegative_matrix_game_value A =
      sInf (Set.range fun x : Δₙ ↦ (nonnegative_matrix_game_payoff A x : EReal)) := by
  rw [nonnegative_matrix_game_value,
    SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  simp

/-! ### Proposition_7_40 (from Chap07) -/
noncomputable section

/- Proposition 7.40 lies in Chapter 7's relative-scale / scalar iteration-bound domain.

Relevant owner-style declarations sampled before refinement:
- `mixedAccuracyIterationCountBound` in `Proposition_7_38`, the sibling Chapter 7 owner for the
  logarithmic iteration budget in the same quasi-Newton complexity lane;
- `mixedAccuracyUniformIterationCountBound` in `Proposition_7_38`, the companion dimension-free
  comparison owner for that sibling bound;
- `mixedAccuracyIterationCountBound_lt_uniformUpperBound` in `Proposition_7_38`, the matching
  strict comparison theorem whose proof has the same `log (1 + x) < x` structure;
- `quasiNewton_bestPoint_relative_accuracy_of_iterationBound` in `Proposition_7_39`, the direct
  downstream theorem that uses the present logarithmic budget as a sufficient lower bound on the
  iteration index.

Best owner abstraction:
- source-facing: the textbook relative-scale iteration budget `R_n(δ)`;
- core/canonical: the scalar owner `relativeScaleIterationBound`;
- bridge/view: the expansion theorem `relativeScaleIterationBound_def` and the dimension-free
  comparison owner `relativeScaleUniformIterationBound`.

Primitive data:
- the positive dimension `n : ℕ+`;
- the constants `δ`, `L`, `R`, and `fStar`.

Derived API:
- the logarithmic expansion of `R_n(δ)`;
- the dimension-free comparison quantity `R_∞(δ)`;
- the strict comparison theorem between the finite-dimensional and dimension-free bounds.

The earlier version left the owner-level expansion theorems and strict comparison theorem as
unstructured placeholders, while the direct downstream theorem in `Proposition_7_39` repeated the
raw logarithmic formula instead of using the owner introduced here. This refinement keeps the same
mathematical semantics, proves the definitional bridge theorems directly, and makes the owner file
the canonical surface for the relative-scale budget.
-/

/-- The relative-scale iteration bound `R_n(δ)` from `(7.4.24)` in dimension `n`. -/
abbrev relativeScaleIterationBound
    (n : ℕ+) (δ L R fStar : ℝ) : ℝ :=
  ((n : ℝ) / δ) *
    Real.log
      (1 +
        ((L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
          (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ))) / (n : ℝ))

-- Proof sketch: unfold `relativeScaleIterationBound`.
/-- Expanding `relativeScaleIterationBound n δ L R fStar` recovers the logarithmic formula from
`(7.4.24)`. -/
theorem relativeScaleIterationBound_def
    (n : ℕ+) (δ L R fStar : ℝ) :
    relativeScaleIterationBound n δ L R fStar =
      ((n : ℝ) / δ) *
        Real.log
          (1 +
            ((L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
              (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ))) / (n : ℝ)) := rfl

/-- The dimension-free bound `R_∞(δ) = L² R² / (δ² (1 - 2δ) (f^*)²)` for the relative-scale
iteration complexity. -/
abbrev relativeScaleUniformIterationBound
    (δ L R fStar : ℝ) : ℝ :=
  (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
    (δ ^ (2 : ℕ) * (1 - 2 * δ) * fStar ^ (2 : ℕ))

-- Proof sketch: unfold `relativeScaleUniformIterationBound`.
/-- Expanding `relativeScaleUniformIterationBound δ L R fStar` recovers the formula
`L² R² / (δ² (1 - 2δ) (f^*)²)`. -/
theorem relativeScaleUniformIterationBound_def
    (δ L R fStar : ℝ) :
    relativeScaleUniformIterationBound δ L R fStar =
      (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
        (δ ^ (2 : ℕ) * (1 - 2 * δ) * fStar ^ (2 : ℕ)) := rfl

-- Proof sketch: write `relativeScaleIterationBound n δ L R fStar` as
-- `(1 / δ) * ((n : ℝ) * log (1 + C / n))` with
-- `C = L² R² / (δ (1 - 2δ) (f^*)²) > 0`. Then use `log (1 + x) < x` for `x > 0` to obtain
-- `(n : ℝ) * log (1 + C / n) < C`, and simplify the right-hand side to
-- `L² R² / (δ² (1 - 2δ) (f^*)²)`.
/-- Proposition 7.40: if `δ ∈ (0, 1 / 2)` and the relative-scale constants `L`, `R`, and `f^*`
are positive, then the iteration bound `R_n(δ)` from `(7.4.24)` is strictly less than the
dimension-free quantity `R_∞(δ) = L² R² / (δ² (1 - 2δ) (f^*)²)`. -/
theorem relativeScaleIterationBound_lt_uniformBound
    (n : ℕ+) (δ L R fStar : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hL : 0 < L) (hR : 0 < R) (hfStar : 0 < fStar) :
    relativeScaleIterationBound n δ L R fStar <
      relativeScaleUniformIterationBound δ L R fStar := by
  let x : ℝ :=
    ((L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
      (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ))) / (n : ℝ)
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have h_one_sub_twoδ : 0 < 1 - 2 * δ := by
    nlinarith [hδ.2]
  have hx : 0 < x := by
    dsimp [x]
    have hnum : 0 < L ^ (2 : ℕ) * R ^ (2 : ℕ) := by
      positivity
    have hden : 0 < δ * (1 - 2 * δ) * fStar ^ (2 : ℕ) := by
      have hfStar_sq : 0 < fStar ^ (2 : ℕ) := by
        positivity
      exact mul_pos (mul_pos hδ.1 h_one_sub_twoδ) hfStar_sq
    exact div_pos (div_pos hnum hden) hn
  have hlog : Real.log (1 + x) < x := by
    have hpos : 0 < 1 + x := by linarith
    have hne : 1 + x ≠ (1 : ℝ) := by linarith
    simpa [sub_eq_add_neg] using Real.log_lt_sub_one_of_pos hpos hne
  have hmul :
      (n : ℝ) / δ * Real.log (1 + x) <
        (n : ℝ) / δ * x := by
    exact mul_lt_mul_of_pos_left hlog (div_pos hn hδ.1)
  have hδ_ne : δ ≠ 0 := hδ.1.ne'
  have hn_ne : (n : ℝ) ≠ 0 := hn.ne'
  have h_one_sub_twoδ_ne : 1 - 2 * δ ≠ 0 := h_one_sub_twoδ.ne'
  have hfStar_sq_ne : fStar ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hfStar.ne'
  calc
    relativeScaleIterationBound n δ L R fStar
        = (n : ℝ) / δ * Real.log (1 + x) := by
          simp [relativeScaleIterationBound, x]
    _ < (n : ℝ) / δ * x := hmul
    _ = relativeScaleUniformIterationBound δ L R fStar := by
          dsimp [relativeScaleUniformIterationBound, x]
          field_simp [hδ_ne, hn_ne, h_one_sub_twoδ_ne, hfStar_sq_ne]

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_41 (from Chap07) -/
noncomputable section

open EuclideanSpace (nonnegativeOrthant positiveOrthant)
open scoped StandardSimplex

/- Definition 7.41 lies in the linear-packing / constrained-optimization domain.

Sampled owner-style declarations:
- `orthantHalfspacePolyhedron` and `mem_orthantHalfspacePolyhedron_iff` in `Chap07/Theorem_7_9`,
  the chapter owner and membership API for orthant-constrained halfspace polyhedra;
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the chapter owner for finite maxima over a nonempty
  family;
- `stdSimplex` and the Chapter 6 notation `Δ[n]` in `Chap06/Definition_6_11`, the canonical owner
  of the standard simplex;
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.positiveOrthant` in
  `Chap01/Definition_1_10_2`, the project owners for coordinatewise nonnegativity and positivity;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective on a fixed ambient space;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  owner optimal-value API.

Best owner abstraction:
- source-facing: `LinearPackingProblem m n`, carrying the packing data `(a_i, b, c)`;
- core/canonical: `nonnegativeOrthant`, `positiveOrthant`, `orthantHalfspacePolyhedron`, and
  `SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n))`;
- bridge/view: `problem.feasibleSet` as the chapter orthant-polyhedron owner specialized to
  `problem.a` and `problem.b`, and the negated-objective bridge to Chapter 1 minimization.

Primitive data:
- the constraint vectors `a_i`, right-hand side `b`, and objective coefficients `c`;
- the sign assumptions `a_i ∈ ℝⁿ_+`, `b ∈ ℝ₊₊ᵐ`, and `c ∈ ℝ₊₊ⁿ`.

Derived API:
- coordinatewise positivity/nonnegativity consequences of the orthant-membership hypotheses;
- the feasible packing set, via `orthantHalfspacePolyhedron`;
- the linear objective `y ↦ ⟪c, y⟫`;
- the normalized slice `{y ∈ ℝⁿ_+ | ⟪c, y⟫ = 1}` used in Proposition 7.18;
- the normalized gauge `y ↦ max_i ⟪a_i, y⟫ / b_i`;
- the simplex gauge obtained from the diagonal rescaling by `c`;
- the Chapter 1 constrained minimization bridge with objective `y ↦ -⟪c, y⟫`;
- the packed optimal value as the negated owner optimal value. -/

variable {m n : ℕ}

/-- Definition 7.41 (1): a linear packing problem consists of nonnegative constraint vectors
`a₁, …, aₘ ∈ ℝⁿ_+`, a positive right-hand side `b ∈ ℝᵐ`, and positive objective coefficients
`c ∈ ℝⁿ`. -/
structure LinearPackingProblem (m n : ℕ) where
  /-- The constraint vectors `a_i ∈ ℝⁿ_+`. -/
  a : Fin m → EuclideanSpace ℝ (Fin n)
  /-- The right-hand-side vector `b ∈ ℝᵐ`. -/
  b : EuclideanSpace ℝ (Fin m)
  /-- The objective coefficient vector `c ∈ ℝⁿ`. -/
  c : EuclideanSpace ℝ (Fin n)
  /-- Each constraint vector `a_i` lies in the nonnegative orthant `ℝⁿ_+`. -/
  a_nonneg (i : Fin m) : a i ∈ nonnegativeOrthant n
  /-- The right-hand side lies in the positive orthant `ℝ₊₊ᵐ`. -/
  b_pos : b ∈ positiveOrthant m
  /-- The objective coefficient vector lies in the positive orthant `ℝ₊₊ⁿ`. -/
  c_pos : c ∈ positiveOrthant n

namespace LinearPackingProblem

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δₙ" => Δ[n]

/-- Coordinatewise nonnegativity of each constraint vector. -/
@[simp] theorem a_nonneg_apply (problem : LinearPackingProblem m n) (i : Fin m) (j : Fin n) :
    0 ≤ problem.a i j := by
  exact (show ∀ k : Fin n, 0 ≤ problem.a i k by simpa using problem.a_nonneg i) j

/-- Coordinatewise positivity of the right-hand side vector. -/
@[simp] theorem b_pos_apply (problem : LinearPackingProblem m n) (i : Fin m) :
    0 < problem.b i := by
  exact (show ∀ k : Fin m, 0 < problem.b k by simpa using problem.b_pos) i

/-- Coordinatewise positivity of the objective coefficient vector. -/
@[simp] theorem c_pos_apply (problem : LinearPackingProblem m n) (j : Fin n) :
    0 < problem.c j := by
  exact (show ∀ k : Fin n, 0 < problem.c k by simpa using problem.c_pos) j

/-- The feasible packing polyhedron `P = {y ≥ 0 | ⟪a_i, y⟫ ≤ b_i for all i}`. -/
abbrev feasibleSet (problem : LinearPackingProblem m n) : Set E :=
  orthantHalfspacePolyhedron problem.a (fun i ↦ problem.b i)

/-- Membership in `problem.feasibleSet` is exactly the nonnegativity and packing-constraint
condition. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : LinearPackingProblem m n) {y : E} :
    y ∈ problem.feasibleSet ↔
      y ∈ nonnegativeOrthant n ∧ ∀ i : Fin m, inner ℝ (problem.a i) y ≤ problem.b i := by
  simp [feasibleSet]

/-- The packing objective `y ↦ ⟪c, y⟫`. -/
def objective (problem : LinearPackingProblem m n) : E → ℝ :=
  inner ℝ problem.c

@[simp] theorem objective_apply (problem : LinearPackingProblem m n) (y : E) :
    problem.objective y = inner ℝ problem.c y :=
  rfl

/-- The normalized nonnegative slice `{y ∈ ℝⁿ_+ | ⟪c, y⟫ = 1}` attached to a linear packing
problem. -/
def normalizedSlice (problem : LinearPackingProblem m n) : Set E :=
  {y | y ∈ nonnegativeOrthant n ∧ problem.objective y = 1}

/-- Membership in `problem.normalizedSlice` means belonging to the nonnegative orthant and
satisfying the normalization `⟪c, y⟫ = 1`. -/
@[simp] theorem mem_normalizedSlice_iff
    (problem : LinearPackingProblem m n) {y : E} :
    y ∈ problem.normalizedSlice ↔ y ∈ nonnegativeOrthant n ∧ inner ℝ problem.c y = 1 := by
  simp [normalizedSlice, objective]

/-- A linear packing problem can be used as its objective function `y ↦ ⟪c, y⟫`. -/
instance : CoeFun (LinearPackingProblem m n) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

@[simp] theorem coe_apply (problem : LinearPackingProblem m n) (y : E) :
    problem y = problem.objective y :=
  rfl

/-- The source-facing gauge `y ↦ max_i ⟪a_i, y⟫ / b_i` attached to a linear packing problem. The
positivity of `b_i` is primitive owner data, so this expression is used only in the faithful
packing regime. -/
abbrev gauge (problem : LinearPackingProblem m n) [Nonempty (Fin m)] : E → ℝ :=
  maxTypeObjective (fun i y ↦ inner ℝ (problem.a i) y / problem.b i)

@[simp] theorem gauge_apply (problem : LinearPackingProblem m n) [Nonempty (Fin m)] (y : E) :
    problem.gauge y =
      maxTypeObjective (fun i x ↦ inner ℝ (problem.a i) x / problem.b i) y :=
  rfl

/-- The simplex gauge obtained from `problem.gauge` after the diagonal change of variables
`x_j = c_j y_j`. -/
abbrev scaledGauge (problem : LinearPackingProblem m n) [Nonempty (Fin m)] : Δₙ → ℝ :=
  fun x ↦ maxTypeObjective
    (fun i y ↦ dotProduct (fun j ↦ problem.a i j / problem.c j) y / problem.b i) x.1

@[simp] theorem scaledGauge_apply
    (problem : LinearPackingProblem m n) [Nonempty (Fin m)] (x : Δₙ) :
    problem.scaledGauge x =
      maxTypeObjective
        (fun i y ↦ dotProduct (fun j ↦ problem.a i j / problem.c j) y / problem.b i) x.1 :=
  rfl

/-- The Chapter 1 constrained minimization owner attached to the packing problem, using the
negated objective so that maximization is represented canonically through minimization. -/
def toSetConstrainedMinimizationProblem
    (problem : LinearPackingProblem m n) : SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := fun y ↦ -problem.objective y

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : LinearPackingProblem m n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : LinearPackingProblem m n) (y : E) :
    problem.toSetConstrainedMinimizationProblem y = -problem.objective y :=
  rfl

/-- Definition 7.41 (2): the packing optimal value `ψ*` is the negated Chapter 1 optimal value of the
associated constrained minimization problem with objective `y ↦ -⟪c, y⟫`. This is the canonical
owner form of the textbook supremum definition. -/
def optimalValue (problem : LinearPackingProblem m n) : EReal :=
  -problem.toSetConstrainedMinimizationProblem.optimalValue

-- Proof sketch: unfold `optimalValue`, rewrite the Chapter 1 owner value as an infimum of the
-- negated objective on the feasible set, and use the order anti-isomorphism `x ↦ -x` to turn the
-- infimum of `-⟪c, y⟫` into the supremum of `⟪c, y⟫`.
/-- The canonical owner optimal value for Definition 7.41 is the supremum of the packing
objective on the feasible packing polyhedron, viewed in `EReal`. -/
theorem optimalValue_eq_sSup_image (problem : LinearPackingProblem m n) :
    problem.optimalValue =
      sSup ((fun y ↦ (problem.objective y : EReal)) '' problem.feasibleSet) := sorry

end LinearPackingProblem

end

/-! ### Proposition_7_41 (from Chap07) -/
noncomputable section

universe u

/- Proposition 7.41 lies in Chapter 7's mixed-to-absolute accuracy / scalar iteration-bound
domain.

Relevant owner-style declarations sampled before refinement:
- `mixedAccuracyIterationCountBound` in `Proposition_7_38`, the chapter owner for a logarithmic
  mixed-accuracy iteration budget with an `abbrev` owner and `rfl` expansion theorem;
- `relativeScaleIterationBound` in `Proposition_7_40`, the sibling quasi-Newton logarithmic owner
  in the same scalar-iteration-bound lane;
- `HasMixedAccuracy` in `Definition_7_89`, the later chapter owner for the scalar mixed
  absolute-relative accuracy inequality;
- `IsAbsoluteAccuracyApproximateSolutionOn` in `Definition_7_93`, the later chapter owner for the
  absolute-accuracy optimization conclusion.

Best owner abstraction:
- source-facing: the Proposition 7.41 quantity `δ(ε)`, the iteration threshold `T_n(ε)`, and the
  final absolute-accuracy theorem with its displayed gap estimate;
- core/canonical: the chapter's transparent scalar-owner pattern for such quantities, namely
  `abbrev` owners with direct definitional bridge theorems rather than opaque wrapper `def`s;
- bridge/view: the expansion theorems and the closed-form rewriting of `T_n(ε)`.

Primitive data:
- the positive dimension `n : ℕ+`;
- the iteration index `k`;
- the scalars `L`, `R`, and `ε`;
- the assumed gap estimate and the threshold lower bound on `k`.

Derived API:
- the specialization `δ(ε) = ε / (ε + 2 L R)`;
- the threshold `T_n(ε)` and its closed logarithmic form;
- the absolute-accuracy conclusion `φ x_k^* ≤ φ* + ε`.

There is no earlier project owner with exactly the Proposition 7.41 formulas, so the refinement
keeps these declarations source-facing. The cleanup is instead to align them with the chapter's
canonical scalar-owner style: transparent abbreviations for the reusable source quantities,
`rfl` bridge lemmas for those owners, and the displayed mixed-to-absolute gap estimate kept inline
in the proposition rather than exported as a one-off wrapper.
-/

/-- The parameter `δ(ε) = ε / (ε + 2 L R)` used to convert the mixed-accuracy estimate into an
absolute-accuracy estimate. -/
abbrev quasi_newton_absolute_accuracy_delta
    (ε L R : ℝ) : ℝ :=
  ε / (ε + 2 * L * R)

-- Proof sketch: unfold `quasi_newton_absolute_accuracy_delta`; the right-hand side is exactly the
-- defining formula for `δ(ε)`.
/-- Expanding `quasi_newton_absolute_accuracy_delta ε L R` recovers the formula
`ε / (ε + 2 L R)`. -/
theorem quasi_newton_absolute_accuracy_delta_def
    (ε L R : ℝ) :
    quasi_newton_absolute_accuracy_delta ε L R =
      ε / (ε + 2 * L * R) := rfl

/-- The iteration threshold
`T_n(ε) = (n / δ(ε)) * log (1 + LR / (n ε (1 - δ(ε))))` from Proposition 7.41. -/
abbrev quasi_newton_absolute_accuracy_iteration_bound
    (n : ℕ+) (ε L R : ℝ) : ℝ :=
  let δ := quasi_newton_absolute_accuracy_delta ε L R
  ((n : ℝ) / δ) * Real.log (1 + (L * R) / ((n : ℝ) * ε * (1 - δ)))

-- Proof sketch: unfold `quasi_newton_absolute_accuracy_iteration_bound`; the result is exactly the
-- definition of `T_n(ε)` written in terms of `δ(ε)`.
/-- Expanding `quasi_newton_absolute_accuracy_iteration_bound n ε L R` recovers the formula
`(n / δ(ε)) * log (1 + LR / (n ε (1 - δ(ε))))`. -/
theorem quasi_newton_absolute_accuracy_iteration_bound_def
    (n : ℕ+) (ε L R : ℝ) :
    quasi_newton_absolute_accuracy_iteration_bound n ε L R =
      let δ := quasi_newton_absolute_accuracy_delta ε L R
      ((n : ℝ) / δ) * Real.log (1 + (L * R) / ((n : ℝ) * ε * (1 - δ))) := rfl

-- Proof sketch: substitute `δ(ε) = ε / (ε + 2 L R)`, simplify
-- `1 - δ(ε) = 2 L R / (ε + 2 L R)` and
-- `(n / δ(ε)) = n * (1 + 2 L R / ε)`, then rewrite the logarithm argument accordingly. The
-- cancellation in the logarithm denominator only needs `L * R ≠ 0`, while the positivity input
-- is exactly `ε > 0` and `ε + 2 L R > 0`.
/-- Rewriting `T_n(ε)` using the explicit formula for `δ(ε)` gives the closed form
`n (1 + 2LR / ε) log (1 + (ε + 2LR) / (2 n ε))` whenever `ε > 0`,
`ε + 2LR > 0`, and `LR ≠ 0`. -/
theorem quasi_newton_absolute_accuracy_iteration_bound_eq_closed_form
    (n : ℕ+) {ε L R : ℝ} (hε : 0 < ε) (hsum : 0 < ε + 2 * L * R) (hLR : L * R ≠ 0) :
    quasi_newton_absolute_accuracy_iteration_bound n ε L R =
      (n : ℝ) * (1 + (2 * L * R) / ε) *
        Real.log (1 + (ε + 2 * L * R) / (2 * (n : ℝ) * ε)) := by
  have hε_ne : ε ≠ 0 := hε.ne'
  have hsum_ne : ε + 2 * L * R ≠ 0 := hsum.ne'
  have htwoLR_ne : 2 * L * R ≠ 0 := by
    rw [show 2 * L * R = (2 : ℝ) * (L * R) by ring]
    exact mul_ne_zero (by norm_num) hLR
  rw [quasi_newton_absolute_accuracy_iteration_bound_def]
  simp [quasi_newton_absolute_accuracy_delta]
  field_simp [hε_ne, hsum_ne]
  congr 1
  field_simp [hε_ne, htwoLR_ne]
  ring

-- Proof sketch: set `δ := δ(ε) = ε / (ε + 2 L R)`. The identity
-- `L R * δ / (1 - δ) = ε / 2` gives half of the target accuracy budget. The lower bound
-- `k ≥ T_n(ε)` implies
-- `exp (δ (k + 1) / n) - 1 ≥ LR / (n ε (1 - δ))`, so the remaining exponential term is at most
-- `ε / 2`. Adding the two contributions yields `φ xkStar - φStar ≤ ε`, hence
-- `φ xkStar ≤ φStar + ε`.
/-- Proposition 7.41: if the `k`-th iterate satisfies the mixed-accuracy gap estimate with
`δ = ε / (ε + 2LR)` and `k` is at least the threshold `T_n(ε)`, then its objective value is
within absolute accuracy `ε` of `φ*`. -/
theorem quasi_newton_absolute_accuracy_of_iteration_bound
    {X : Type u} (φ : X → ℝ) (xkStar : X) (φStar : ℝ)
    (n : ℕ+) (k : ℕ) (L R ε : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hgap :
      φ xkStar - φStar ≤
        let δ := quasi_newton_absolute_accuracy_delta ε L R
        L * R *
          (δ / (1 - δ) +
            1 /
              (2 * (n : ℝ) *
                (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1) *
                (1 - δ))))
    (hk :
      quasi_newton_absolute_accuracy_iteration_bound n ε L R ≤ (k : ℝ)) :
    φ xkStar ≤ φStar + ε := by
  let δ := quasi_newton_absolute_accuracy_delta ε L R
  let a : ℝ := (L * R) / ((n : ℝ) * ε * (1 - δ))
  let e : ℝ := Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1
  have hgap' :
      φ xkStar - φStar ≤
        L * R * (δ / (1 - δ) + 1 / (2 * (n : ℝ) * e * (1 - δ))) := by
    simpa [δ, e] using hgap
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have hδ_pos : 0 < δ := by
    dsimp [δ, quasi_newton_absolute_accuracy_delta]
    positivity
  have h_one_sub_δ_pos : 0 < 1 - δ := by
    dsimp [δ, quasi_newton_absolute_accuracy_delta]
    have hden_ne : ε + 2 * L * R ≠ 0 := by positivity
    field_simp [hden_ne]
    nlinarith [hL, hR, hε]
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hfirst_eq : L * R * (δ / (1 - δ)) = ε / 2 := by
    dsimp [δ, quasi_newton_absolute_accuracy_delta]
    field_simp [hε.ne', hL.ne', hR.ne']
    ring
  have hk_div : Real.log (1 + a) ≤ (k : ℝ) / ((n : ℝ) / δ) := by
    apply (le_div_iff₀ (div_pos hn hδ_pos)).2
    simpa [quasi_newton_absolute_accuracy_iteration_bound, δ, a, mul_comm, mul_left_comm,
      mul_assoc] using hk
  have hk_log : Real.log (1 + a) ≤ δ * (k : ℝ) / (n : ℝ) := by
    have hk_div' : Real.log (1 + a) ≤ (k : ℝ) * (δ / (n : ℝ)) := by
      simpa [div_eq_mul_inv, hδ_pos.ne', hn.ne', mul_assoc, mul_comm, mul_left_comm] using hk_div
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hk_div'
  have hk_log_succ : Real.log (1 + a) ≤ δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
    refine hk_log.trans ?_
    have hk_le : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ k
    gcongr
  have h_exp_le : 1 + a ≤ e + 1 := by
    have hlogexp : 1 + a = Real.exp (Real.log (1 + a)) := by
      rw [Real.exp_log (by linarith [ha_pos])]
    rw [hlogexp]
    simpa [e] using Real.exp_le_exp.mpr hk_log_succ
  have ha_le_e : a ≤ e := by
    linarith
  have he_pos : 0 < e := lt_of_lt_of_le ha_pos ha_le_e
  have hden_lower : (2 * L * R) / ε ≤ 2 * (n : ℝ) * e * (1 - δ) := by
    have hmul := mul_le_mul_of_nonneg_right ha_le_e (by positivity : 0 ≤ 2 * (n : ℝ) * (1 - δ))
    dsimp [a] at hmul
    simpa [div_eq_mul_inv, hε.ne', hn.ne', h_one_sub_δ_pos.ne', mul_assoc, mul_left_comm,
      mul_comm] using hmul
  have hsecond_le :
      L * R * (1 / (2 * (n : ℝ) * e * (1 - δ))) ≤ ε / 2 := by
    have hden_pos : 0 < 2 * (n : ℝ) * e * (1 - δ) := by
      positivity
    rw [mul_one_div]
    apply (div_le_iff₀ hden_pos).2
    have hmul2 := mul_le_mul_of_nonneg_left hden_lower (by positivity : 0 ≤ ε / 2)
    simpa [div_eq_mul_inv, hε.ne', mul_assoc, mul_left_comm, mul_comm] using hmul2
  have hsum_le :
      L * R * (δ / (1 - δ)) + L * R * (1 / (2 * (n : ℝ) * e * (1 - δ))) + φStar ≤
        ε / 2 + ε / 2 + φStar := by
    nlinarith [hfirst_eq, hsecond_le]
  calc
    φ xkStar = (φ xkStar - φStar) + φStar := by ring
    _ ≤ (L * R * (δ / (1 - δ) + 1 / (2 * (n : ℝ) * e * (1 - δ)))) + φStar := by
      linarith
    _ = L * R * (δ / (1 - δ)) + L * R * (1 / (2 * (n : ℝ) * e * (1 - δ))) + φStar := by
      ring
    _ ≤ ε / 2 + ε / 2 + φStar := hsum_le
    _ = φStar + ε := by ring

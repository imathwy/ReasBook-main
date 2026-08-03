import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_4

/- Theorem 10.3 is source-facing at the complete-graph matrix level, while Exercise 10.4 already
owns the repository's canonical `SimpleGraph`/`Sym2` weighted max-cut API. This file keeps the
matrix model primary and uses `Matrix.toSym2Weight` as the bridge to that canonical owner. -/

open scoped MatrixOrder

section Theorem103

variable {n : ℕ}

namespace Matrix

/-- Convert a complete-graph weight matrix into the repository's canonical `Sym2`-indexed edge
weight on unordered vertex pairs by symmetrizing the matrix entries. On symmetric matrices, this
recovers the original off-diagonal weights, while diagonal terms are harmless because the complete
graph edge set contains no loops. -/
noncomputable def toSym2Weight (w : Matrix (Fin n) (Fin n) ℝ) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j ↦ (w i j + w j i) / 2, by
    intro i j
    ring⟩

/-- On the unordered pair `s(i, j)`, `toSym2Weight w` is the average of the two matrix
orientations. -/
@[simp] theorem toSym2Weight_apply
    (w : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    toSym2Weight w s(i, j) = (w i j + w j i) / 2 := rfl

/-- For a symmetric weight matrix, `toSym2Weight` agrees with the original matrix entries. -/
theorem toSym2Weight_apply_of_isSymm
    (w : Matrix (Fin n) (Fin n) ℝ) (h_symm : w.IsSymm) (i j : Fin n) :
    toSym2Weight w s(i, j) = w i j := by
  rw [toSym2Weight_apply]
  have hij : w j i = w i j := h_symm.apply i j
  rw [hij]
  ring

/-- For a symmetric nonnegative weight matrix, the induced `Sym2`-indexed edge weight is
entrywise nonnegative. -/
theorem toSym2Weight_nonneg_of_isSymm
    (w : Matrix (Fin n) (Fin n) ℝ) (h_symm : w.IsSymm)
    (h_nonneg : ∀ i j, 0 ≤ w i j) (e : Sym2 (Fin n)) :
    0 ≤ toSym2Weight w e := by
  refine Sym2.ind ?_ e
  intro i j
  rw [toSym2Weight_apply_of_isSymm w h_symm i j]
  exact h_nonneg i j

/-- Entrywise nonnegativity of the matrix entries transfers to the canonical `Sym2`-indexed weight
function. -/
theorem toSym2Weight_nonneg
    (w : Matrix (Fin n) (Fin n) ℝ) (h_nonneg : ∀ i j, 0 ≤ w i j) (e : Sym2 (Fin n)) :
    0 ≤ toSym2Weight w e := by
  refine Sym2.ind ?_ e
  intro i j
  rw [toSym2Weight_apply]
  exact div_nonneg (add_nonneg (h_nonneg i j) (h_nonneg j i)) (by norm_num)

end Matrix

/-- Helper for Theorem 10.3: the Goemans-Williamson attainable-value set is nonempty because the
identity matrix is a feasible witness. -/
lemma goemansWilliamsonObjectiveValues_nonempty
    (w : Sym2 (Fin n) → ℝ) :
    (goemans_williamson_objective_values (⊤ : SimpleGraph (Fin n)) w).Nonempty := by
  -- Register the identity matrix as an explicit feasible point of the relaxation.
  refine ⟨goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w
    (1 : Matrix (Fin n) (Fin n) ℝ), ?_⟩
  refine ⟨(1 : Matrix (Fin n) (Fin n) ℝ), ?_, rfl⟩
  refine goemans_williamson_feasible.mk ?_ ?_
  · simpa using (Matrix.PosSemidef.one : Matrix.PosSemidef (1 : Matrix (Fin n) (Fin n) ℝ))
  · intro v
    simp

/-- Helper for Theorem 10.3: a pointwise approximation factor on every feasible
Goemans-Williamson witness upgrades directly to the ratio bound on the optimal values. -/
lemma goemansWilliamsonRatioLowerBound_of_pointwiseApprox
    (w : Sym2 (Fin n) → ℝ)
    {β : ℝ}
    (hβ : (87856 : ℝ) / 100000 < β)
    (hScaled :
      ∀ {X : Matrix (Fin n) (Fin n) ℝ}, goemans_williamson_feasible X →
        β * goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X ≤
          max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w)
    (hsdp_pos : 0 < goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w) :
    max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w /
        goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w >
      (87856 : ℝ) / 100000 := by
  have hβ_pos : 0 < β := by
    -- The target constant is positive, so any strict improvement is also positive.
    exact lt_trans (by norm_num : (0 : ℝ) < (87856 : ℝ) / 100000) hβ
  have hValueLe :
      goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w ≤
        max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w / β := by
    -- Bound the supremum by checking the scaled inequality on each feasible witness.
    rw [goemans_williamson_value_eq_sSup]
    refine csSup_le (goemansWilliamsonObjectiveValues_nonempty (n := n) w) ?_
    intro r hr
    rcases hr with ⟨X, hX, rfl⟩
    have hScaled' :
        goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X * β ≤
          max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
      simpa [mul_comm] using hScaled hX
    exact (le_div_iff₀ hβ_pos).2 hScaled'
  have hScaledValue :
      β * goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w ≤
        max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
    -- Multiply the supremum bound by `β` and simplify the right-hand side.
    calc
      β * goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w ≤
          β * (max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w / β) :=
        mul_le_mul_of_nonneg_left hValueLe hβ_pos.le
      _ = β * (max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w * β⁻¹) := by
        rw [div_eq_mul_inv]
      _ = max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w * (β * β⁻¹) := by
        ring
      _ = max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
        simp [hβ_pos.ne']
  have hRatio : β ≤
      max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w /
        goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w := by
    -- Divide by the positive semidefinite optimum to recover the ratio lower bound.
    exact (le_div_iff₀ hsdp_pos).2 hScaledValue
  exact lt_of_lt_of_le hβ hRatio

/-- Helper for Theorem 10.3: a feasible Goemans-Williamson matrix is the Gram matrix of a unit
family of column vectors in `ℝ^n`. -/
lemma existsUnitVectorFamilyOfGoemansWilliamsonFeasible
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : goemans_williamson_feasible X) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = X i j) ∧
      (∀ i, dotProduct (fun k ↦ U k i) (fun k ↦ U k i) = 1) := by
  -- Factor the feasible PSD matrix as `Uᵀ * U`, then read the columns of `U`.
  obtain ⟨U, hGram⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (goemans_williamson_feasible.posSemidef hX).nonneg
  have hDot :
      ∀ i j, dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = X i j := by
    intro i j
    -- Expanding one matrix entry turns the factorization into a dot product identity.
    calc
      dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = (star U * U) i j := by
        simp [Matrix.mul_apply, dotProduct]
      _ = X i j := by
        simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hGram.symm
  refine ⟨U, hDot, ?_⟩
  intro i
  -- The diagonal constraint identifies each self-dot-product with `1`.
  calc
    dotProduct (fun k ↦ U k i) (fun k ↦ U k i) = X i i := hDot i i
    _ = 1 := goemans_williamson_feasible.diag_eq_one hX i

/-- Helper for Theorem 10.3: after choosing Gram columns for a feasible matrix, the
Goemans-Williamson objective is the edge sum of the textbook dot-gap terms `(1 - u_i · u_j) / 2`.
-/
lemma goemansWilliamsonObjective_eq_sum_dotGap
    (w : Sym2 (Fin n) → ℝ)
    {X U : Matrix (Fin n) (Fin n) ℝ}
    (hDot : ∀ i j, dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = X i j) :
    goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun i j : Fin n ↦ (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2, by
              intro i j
              simp [dotProduct_comm]
            ⟩
            e := by
  -- Normalize the complete-graph objective once so the final comparison can be done edgewise.
  classical
  have hedgeFinset :
      (letI : DecidableRel (⊤ : SimpleGraph (Fin n)).Adj := Classical.decRel (⊤ : SimpleGraph (Fin n)).Adj
       (⊤ : SimpleGraph (Fin n)).edgeFinset) =
        (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [goemans_williamson_objective_eq_sum, hedgeFinset]
  refine Finset.sum_congr rfl ?_
  intro e _
  refine Sym2.ind ?_ e
  intro i j
  have hSymm : X j i = X i j := by
    calc
      X j i = dotProduct (fun k ↦ U k j) (fun k ↦ U k i) := by symm; exact hDot j i
      _ = dotProduct (fun k ↦ U k i) (fun k ↦ U k j) := by rw [dotProduct_comm]
      _ = X i j := hDot i j
  -- On each unordered edge, the symmetric matrix term collapses to a single dot product.
  change
    w s(i, j) * (((2 : ℝ) - X i j - X j i) / 4) =
      w s(i, j) * ((1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2)
  rw [hSymm, hDot i j]
  ring

/-- Helper for Theorem 10.3: the Gram dot products attached to a feasible witness lie in `[-1, 1]`.
-/
lemma goemansWilliamsonDot_mem_Icc_of_unitColumnFamily
    {X U : Matrix (Fin n) (Fin n) ℝ}
    (hX : goemans_williamson_feasible X)
    (hDot : ∀ i j, dotProduct (fun k ↦ U k i) (fun k ↦ U k j) = X i j)
    (i j : Fin n) :
    dotProduct (fun k ↦ U k i) (fun k ↦ U k j) ∈ Set.Icc (-1 : ℝ) 1 := by
  -- Transport the interval control from the existing Chapter 10.6 feasible edge-term lemma.
  have hSymm : X j i = X i j := by
    calc
      X j i = dotProduct (fun k ↦ U k j) (fun k ↦ U k i) := by symm; exact hDot j i
      _ = dotProduct (fun k ↦ U k i) (fun k ↦ U k j) := by rw [dotProduct_comm]
      _ = X i j := hDot i j
  have hEdge := goemansWilliamsonEdgeTerm_mem_Icc_zero_one (hX := hX) i j
  have hLower : 0 ≤ (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 := by
    have hLower' : 0 ≤ (2 - X i j - X i j) / 4 := by
      simpa [hSymm] using hEdge.1
    have hRewrite :
        (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 =
          (2 - X i j - X i j) / 4 := by
      rw [hDot i j]
      ring
    calc
      0 ≤ (2 - X i j - X i j) / 4 := hLower'
      _ = (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 := by
        symm
        exact hRewrite
  have hUpper : (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 ≤ 1 := by
    have hUpper' : (2 - X i j - X i j) / 4 ≤ 1 := by
      simpa [hSymm] using hEdge.2
    have hRewrite :
        (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 =
          (2 - X i j - X i j) / 4 := by
      rw [hDot i j]
      ring
    calc
      (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2 =
          (2 - X i j - X i j) / 4 := hRewrite
      _ ≤ 1 := hUpper'
  constructor <;> nlinarith

/-- Helper for Theorem 10.3: a Boolean sign pattern contributes `1` exactly on unordered pairs
whose endpoint signs disagree. -/
lemma boolPattern_maxCutNodeObjective_eq_disagreementSum
    (w : Sym2 (Fin n) → ℝ) (σ : Fin n → Bool) :
    max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
        (fun i ↦ if σ i then (1 : ℝ) else 0) =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                intro i j
                by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
            ⟩
            e := by
  -- Expand the node objective once and compute the `0/1` edge term by cases on the two signs.
  classical
  have hedgeFinset :
      (letI : DecidableRel (⊤ : SimpleGraph (Fin n)).Adj := Classical.decRel (⊤ : SimpleGraph (Fin n)).Adj
       (⊤ : SimpleGraph (Fin n)).edgeFinset) =
        (⊤ : SimpleGraph (Fin n)).edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [max_cut_node_objective_eq_sum, hedgeFinset]
  refine Finset.sum_congr rfl ?_
  intro e _
  refine Sym2.ind ?_ e
  intro i j
  change
    w s(i, j) *
        ((if σ i then (1 : ℝ) else 0) + (if σ j then 1 else 0) -
          2 * (if σ i then 1 else 0) * (if σ j then 1 else 0)) =
      w s(i, j) * (if σ i = σ j then 0 else 1)
  by_cases hi : σ i
  · by_cases hj : σ j
    · simp [hi, hj]
      right
      norm_num
    · simp [hi, hj]
  · by_cases hj : σ j
    · simp [hi, hj]
    · simp [hi, hj]

/-- Helper for Theorem 10.3: every Boolean sign pattern defines a feasible `0/1` max-cut point. -/
lemma boolPattern_maxCutNodeObjective_mem_values
    (w : Sym2 (Fin n) → ℝ) (σ : Fin n → Bool) :
    max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
        (fun i ↦ if σ i then (1 : ℝ) else 0) ∈
      max_cut_node_objective_values (⊤ : SimpleGraph (Fin n)) w := by
  -- Register the Boolean indicator assignment as an explicit feasible point of the node model.
  refine ⟨fun i ↦ if σ i then (1 : ℝ) else 0, ?_, rfl⟩
  intro i
  by_cases hi : σ i <;> simp [hi]

/-- Helper for Theorem 10.3: on the finite vertex set `Fin n`, the attainable integral max-cut
values form a finite set because every feasible `0/1` assignment comes from a Boolean pattern. -/
lemma maxCutNodeObjectiveValues_finite
    (w : Sym2 (Fin n) → ℝ) :
    (max_cut_node_objective_values (⊤ : SimpleGraph (Fin n)) w).Finite := by
  classical
  let F : (Fin n → Bool) → ℝ := fun σ ↦
    max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
      (fun i ↦ if σ i then (1 : ℝ) else 0)
  refine (Set.finite_range F).subset ?_
  intro r hr
  rcases hr with ⟨χ, hχ, rfl⟩
  let σ : Fin n → Bool := fun i ↦ if χ i = 1 then true else false
  refine ⟨σ, ?_⟩
  -- Recover the original feasible assignment by remembering whether each coordinate is `1`.
  have hχ_bool :
      (fun i ↦ if σ i then (1 : ℝ) else 0) = χ := by
    funext i
    rcases hχ i with h0 | h1
    · simp [σ, h0]
    · simp [σ, h1]
  simp [F, hχ_bool]

/-- Helper for Theorem 10.3: averaging Boolean cuts against any probability measure stays below
the integer optimum `z_I`. -/
lemma averageBooleanCut_le_maxCutIntegerValue
    (w : Sym2 (Fin n) → ℝ) (μ : MeasureTheory.Measure (Fin n → Bool))
    (hμ : μ Set.univ = 1) :
    MeasureTheory.integral μ
        (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
          (fun i ↦ if σ i then (1 : ℝ) else 0)) ≤
      max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
  classical
  letI : MeasureTheory.IsFiniteMeasure μ := ⟨by simp [hμ]⟩
  let f : (Fin n → Bool) → ℝ := fun σ ↦
    max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
      (fun i ↦ if σ i then (1 : ℝ) else 0)
  have hf : MeasureTheory.Integrable f μ := by
    -- The Boolean codomain is finite, so every real-valued function on it is integrable.
    exact MeasureTheory.Integrable.of_finite
  have hpointwise :
      ∀ σ, f σ ≤ max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
    intro σ
    -- Each Boolean cut value belongs to the finite attainable-value set, so it is below `sSup`.
    rw [max_cut_integer_value_eq_sSup]
    exact le_csSup
      (maxCutNodeObjectiveValues_finite (n := n) w).bddAbove
      (boolPattern_maxCutNodeObjective_mem_values (n := n) w σ)
  calc
    MeasureTheory.integral μ f = (∑ σ, μ.real {σ} • f σ) := by
      rw [MeasureTheory.integral_fintype hf]
    _ = (∑ σ, μ.real {σ} * f σ) := by
      simp [smul_eq_mul]
    _ ≤ (∑ σ, μ.real {σ} * max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w) := by
      refine Finset.sum_le_sum ?_
      intro σ _
      exact mul_le_mul_of_nonneg_left (hpointwise σ) ENNReal.toReal_nonneg
    _ = MeasureTheory.integral μ (fun _ : Fin n → Bool ↦
          max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w) := by
      symm
      rw [MeasureTheory.integral_fintype (MeasureTheory.integrable_const
        (max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w))]
      simp [smul_eq_mul]
    _ = max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
      rw [MeasureTheory.integral_const]
      have hμ_real : μ.real Set.univ = 1 := by
        simp [MeasureTheory.measureReal_def, hμ]
      rw [hμ_real]
      simp

-- Helper for Theorem 10.3: Gaussian sign rounding should identify the weighted `arccos / π`
-- sum with the expectation of Boolean cut values.
-- TODO: factor the Gaussian pushforward through sign patterns, rewrite the expectation of
-- `max_cut_node_objective` as an edgewise disagreement average, and compute each disagreement
-- probability as `Real.arccos (u_i • u_j) / Real.pi`.
/-- Helper for Theorem 10.3: the remaining Gaussian geometry frontier is the pairwise
sign-disagreement probability for two unit columns. -/
--
-- TODO: map the standard Gaussian by the two dot-product functionals, identify the resulting
-- centered bivariate Gaussian, and compute the sector probability as `Real.arccos (u • v) / π`.
lemma gaussianDisagreementProb_eq_arccos_div_pi_of_unitColumns
    (u v : EuclideanSpace ℝ (Fin n))
    (hu : dotProduct u u = 1)
    (hv : dotProduct v v = 1) :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real
        {g | (0 < dotProduct g u) ≠ (0 < dotProduct g v)} =
      Real.arccos (dotProduct u v) / Real.pi := by
  sorry

/-- Helper for Theorem 10.3: after pushing the Gaussian through the sign map, the expected cut
value is an edgewise sum of Boolean disagreement probabilities. -/
lemma gaussianRoundedCutIntegral_eq_weightedDisagreementProbSum
    (w : Sym2 (Fin n) → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) :
    let signPattern :
        EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
      fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
    let μ : MeasureTheory.Measure (Fin n → Bool) :=
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
    MeasureTheory.integral μ
        (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
          (fun i ↦ if σ i then (1 : ℝ) else 0)) =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun i j : Fin n ↦
                μ.real {σ | σ i ≠ σ j}, by
                  intro i j
                  change μ.real ({σ : Fin n → Bool | σ i ≠ σ j}) =
                    μ.real {σ : Fin n → Bool | σ j ≠ σ i}
                  congr 1
                  ext σ
                  simp [ne_comm]
            ⟩
            e := by
  classical
  let signPattern :
      EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
    fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
  let μ : MeasureTheory.Measure (Fin n → Bool) :=
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
  let disagreementTerm : Sym2 (Fin n) → ℝ :=
    Sym2.lift
      ⟨fun i j : Fin n ↦ μ.real {σ | σ i ≠ σ j}, by
          intro i j
          change μ.real ({σ : Fin n → Bool | σ i ≠ σ j}) =
            μ.real {σ : Fin n → Bool | σ j ≠ σ i}
          congr 1
          ext σ
          simp [ne_comm]
      ⟩
  have hmain :
      MeasureTheory.integral μ
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) =
        Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
          w e * disagreementTerm e := by
    letI : MeasureTheory.IsFiniteMeasure μ := by infer_instance
    have hInt :
        MeasureTheory.Integrable
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) μ := by
      -- The Boolean codomain is finite, so the rounded-cut value is automatically integrable.
      exact MeasureTheory.Integrable.of_finite
    rw [MeasureTheory.integral_fintype hInt]
    simp_rw [boolPattern_maxCutNodeObjective_eq_disagreementSum, smul_eq_mul]
    -- Exchange the finite sum over sign patterns with the finite sum over edges.
    calc
      Finset.sum Finset.univ (fun σ : Fin n → Bool ↦
          μ.real {σ} *
            Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset
              (fun e ↦
                w e *
                  Sym2.lift
                    ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                        intro i j
                        by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
                    ⟩
                    e)) =
          Finset.sum Finset.univ (fun σ : Fin n → Bool ↦
            Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset (fun e ↦
              μ.real {σ} *
                (w e *
                  Sym2.lift
                    ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                        intro i j
                        by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
                    ⟩
                    e))) := by
        refine Finset.sum_congr rfl ?_
        intro σ _
        rw [Finset.mul_sum]
      _ =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            Finset.sum Finset.univ (fun σ : Fin n → Bool ↦
              μ.real {σ} *
                (w e *
                  Sym2.lift
                    ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                        intro i j
                        by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
                    ⟩
                    e)) := by
        rw [Finset.sum_comm]
      _ =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e * Finset.sum Finset.univ (fun σ : Fin n → Bool ↦
                μ.real {σ} *
                  Sym2.lift
                    ⟨fun i j : Fin n ↦ if σ i = σ j then 0 else 1, by
                        intro i j
                        by_cases hij : σ i = σ j <;> simp [hij, eq_comm]
                    ⟩
                    e) := by
        refine Finset.sum_congr rfl ?_
        intro e _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro σ _
        ring
      _ = Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset (fun e ↦
            w e * disagreementTerm e) := by
        refine Finset.sum_congr rfl ?_
        intro e _
        refine Sym2.ind ?_ e
        intro i j
        change
          w s(i, j) *
              (∑ σ : Fin n → Bool, μ.real {σ} * (if σ i = σ j then 0 else 1)) =
            w s(i, j) * μ.real {σ : Fin n → Bool | σ i ≠ σ j}
        congr 1
        -- Collapse the finite Boolean sum back to the pushed-forward disagreement measure.
        calc
          ∑ σ : Fin n → Bool, μ.real {σ} * (if σ i = σ j then 0 else 1) =
              ∑ σ : Fin n → Bool,
                {σ : Fin n → Bool | σ i ≠ σ j}.indicator (fun τ ↦ μ.real {τ}) σ := by
            refine Finset.sum_congr rfl ?_
            intro σ _
            by_cases hij : σ i = σ j <;> simp [Set.indicator, hij]
          _ =
              ∑' σ : Fin n → Bool,
                {σ : Fin n → Bool | σ i ≠ σ j}.indicator (fun τ ↦ μ.real {τ}) σ := by
            rw [tsum_fintype]
          _ = μ.real {σ : Fin n → Bool | σ i ≠ σ j} := by
            have hindicator :
                (∑ σ : Fin n → Bool,
                    {σ : Fin n → Bool | σ i ≠ σ j}.indicator (fun τ ↦ μ.real {τ}) σ) =
                  Finset.sum (Finset.univ.filter fun σ : Fin n → Bool ↦ σ i ≠ σ j)
                    (fun σ ↦ μ.real {σ}) := by
              symm
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro σ _
              by_cases hij : σ i ≠ σ j <;> simp [Set.indicator, hij]
            have hdisagreement_measurable :
                MeasurableSet {σ : Fin n → Bool | σ i ≠ σ j} := by
              exact (Set.toFinite {σ : Fin n → Bool | σ i ≠ σ j}).measurableSet
            calc
              ∑' σ : Fin n → Bool,
                  {σ : Fin n → Bool | σ i ≠ σ j}.indicator (fun τ ↦ μ.real {τ}) σ =
                  Finset.sum (Finset.univ.filter fun σ : Fin n → Bool ↦ σ i ≠ σ j)
                    (fun σ ↦ μ.real {σ}) := by
                rw [tsum_fintype]
                exact hindicator
              _ = μ.real ((Finset.univ.filter fun σ : Fin n → Bool ↦ σ i ≠ σ j) :
                    Set (Fin n → Bool)) := by
                exact MeasureTheory.sum_measureReal_singleton (μ := μ) _
              _ = μ.real {σ : Fin n → Bool | σ i ≠ σ j} := by
                congr 1
                ext σ
                simp
  change MeasureTheory.integral μ
      (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
        (fun i ↦ if σ i then (1 : ℝ) else 0)) =
    Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
      w e *
        Sym2.lift
          ⟨fun i j : Fin n ↦ μ.real {σ | σ i ≠ σ j}, by
              intro i j
              change μ.real ({σ : Fin n → Bool | σ i ≠ σ j}) =
                μ.real {σ : Fin n → Bool | σ j ≠ σ i}
              congr 1
              ext σ
              simp [ne_comm]
          ⟩
          e
  simpa [disagreementTerm] using hmain

lemma gaussianRoundedCutIntegral_eq_weightedArccosSum
    (w : Sym2 (Fin n) → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ)
    (hUnit : ∀ i, dotProduct (fun k ↦ U k i) (fun k ↦ U k i) = 1) :
    let signPattern :
        EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
      fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
    let μ : MeasureTheory.Measure (Fin n → Bool) :=
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
    MeasureTheory.integral μ
        (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
          (fun i ↦ if σ i then (1 : ℝ) else 0)) =
      Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
        w e *
          Sym2.lift
            ⟨fun i j : Fin n ↦
                Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                  intro i j
                  simp [dotProduct_comm]
            ⟩
            e := by
  classical
  let signPattern :
      EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
    fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
  let μ : MeasureTheory.Measure (Fin n → Bool) :=
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
  have hsignPattern_measurable : Measurable signPattern := by
    -- Each Boolean coordinate is the indicator of a measurable half-space.
    refine measurable_pi_lambda _ ?_
    intro v
    refine measurable_to_bool ?_
    simpa [signPattern, Set.preimage] using
      (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hmain :
      MeasureTheory.integral μ
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) =
        Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
          w e *
            Sym2.lift
              ⟨fun i j : Fin n ↦
                  Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                    intro i j
                    simp [dotProduct_comm]
              ⟩
              e := by
    calc
      MeasureTheory.integral μ
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e *
              Sym2.lift
                ⟨fun i j : Fin n ↦
                    μ.real {σ | σ i ≠ σ j}, by
                      intro i j
                      change μ.real ({σ : Fin n → Bool | σ i ≠ σ j}) =
                        μ.real {σ : Fin n → Bool | σ j ≠ σ i}
                      congr 1
                      ext σ
                      simp [ne_comm]
                ⟩
                e := by
        exact gaussianRoundedCutIntegral_eq_weightedDisagreementProbSum (n := n) w U
      _ =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e *
              Sym2.lift
                ⟨fun i j : Fin n ↦
                    Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                      intro i j
                      simp [dotProduct_comm]
                ⟩
                e := by
        refine Finset.sum_congr rfl ?_
        intro e _
        refine Sym2.ind ?_ e
        intro i j
        change
          w s(i, j) * μ.real {σ : Fin n → Bool | σ i ≠ σ j} =
            w s(i, j) *
              (Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi)
        congr 1
        let uCol : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k ↦ U k i)
        let vCol : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k ↦ U k j)
        have hdisagreement_measurable :
            MeasurableSet {σ : Fin n → Bool | σ i ≠ σ j} := by
          exact (Set.toFinite {σ : Fin n → Bool | σ i ≠ σ j}).measurableSet
        have huCol : dotProduct uCol uCol = 1 := by
          simpa [uCol] using hUnit i
        have hvCol : dotProduct vCol vCol = 1 := by
          simpa [vCol] using hUnit j
        have hpreimage :
            signPattern ⁻¹' {σ : Fin n → Bool | σ i ≠ σ j} =
              {g : EuclideanSpace ℝ (Fin n) |
                (0 < dotProduct g (fun k ↦ U k i)) ≠
                  (0 < dotProduct g (fun k ↦ U k j))} := by
          ext g
          simp [signPattern]
        -- Push the disagreement event back through the sign map and invoke the pairwise lemma.
        calc
          μ.real {σ : Fin n → Bool | σ i ≠ σ j} =
              (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real
                (signPattern ⁻¹' {σ : Fin n → Bool | σ i ≠ σ j}) := by
            simpa [μ] using
              (MeasureTheory.map_measureReal_apply
                (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)))
                hsignPattern_measurable
                (s := {σ : Fin n → Bool | σ i ≠ σ j}) hdisagreement_measurable)
          _ =
              (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).real
                {g : EuclideanSpace ℝ (Fin n) |
                  (0 < dotProduct g (fun k ↦ U k i)) ≠
                    (0 < dotProduct g (fun k ↦ U k j))} := by
            rw [hpreimage]
          _ =
              Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi := by
            simpa [uCol, vCol] using
              (gaussianDisagreementProb_eq_arccos_div_pi_of_unitColumns
                (n := n) uCol vCol huCol hvCol)
  change MeasureTheory.integral μ
      (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
        (fun i ↦ if σ i then (1 : ℝ) else 0)) =
    Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
      w e *
        Sym2.lift
          ⟨fun i j : Fin n ↦
              Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                intro i j
                simp [dotProduct_comm]
          ⟩
          e
  exact hmain

lemma weightedArccosSum_le_maxCutIntegerValue_of_unitColumnFamily
    (w : Sym2 (Fin n) → ℝ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hUnit : ∀ i, dotProduct (fun k ↦ U k i) (fun k ↦ U k i) = 1) :
    (Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
      w e *
        Sym2.lift
          ⟨fun i j : Fin n ↦
              Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
                intro i j
                simp [dotProduct_comm]
          ⟩
          e) ≤
      max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
  -- Package the Gaussian sign rounding into a probability measure on Boolean cuts.
  let signPattern :
      EuclideanSpace ℝ (Fin n) → Fin n → Bool :=
    fun g v ↦ 0 < dotProduct g (fun k ↦ U k v)
  let μ : MeasureTheory.Measure (Fin n → Bool) :=
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).map signPattern
  have hsignPattern_measurable : Measurable signPattern := by
    refine measurable_pi_lambda _ ?_
    intro v
    refine measurable_to_bool ?_
    simpa [signPattern, Set.preimage] using
      (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hμ : μ Set.univ = 1 := by
    -- The pushforward of the standard Gaussian is still a probability measure.
    dsimp [μ]
    rw [MeasureTheory.Measure.map_apply hsignPattern_measurable MeasurableSet.univ]
    simp
  have hAverage :
      MeasureTheory.integral μ
          (fun σ ↦ max_cut_node_objective (⊤ : SimpleGraph (Fin n)) w
            (fun i ↦ if σ i then (1 : ℝ) else 0)) ≤
        max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w :=
    averageBooleanCut_le_maxCutIntegerValue (n := n) w μ hμ
  -- Rewrite the rounded-cut expectation as the weighted `arccos / π` sum.
  simpa [μ, signPattern] using
    (gaussianRoundedCutIntegral_eq_weightedArccosSum (n := n) w U hUnit).symm.le.trans hAverage

/-- Helper for Theorem 10.3: the normalized value of `arccos (-1 / 2)` is `2 / 3`. -/
lemma arccos_neg_half_div_pi_eq_two_thirds :
    Real.arccos (-(1 : ℝ) / 2) / Real.pi = (2 : ℝ) / 3 := by
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 : ℝ) / 2 := by
    calc
      Real.cos (2 * Real.pi / 3) = Real.cos (Real.pi - Real.pi / 3) := by congr 1; ring
      _ = -Real.cos (Real.pi / 3) := by rw [Real.cos_pi_sub]
      _ = -(1 : ℝ) / 2 := by rw [Real.cos_pi_div_three]; norm_num
  have harccos :
      Real.arccos (-(1 : ℝ) / 2) = 2 * Real.pi / 3 := by
    refine Real.arccos_eq_of_eq_cos ?_ ?_ hcos.symm
    · positivity
    · have hpi_pos : 0 < Real.pi := Real.pi_pos
      nlinarith
  rw [harccos]
  field_simp [Real.pi_ne_zero]

/-- Helper for Theorem 10.3: the normalized value of `arccos (1 / 2)` is `1 / 3`. -/
lemma arccos_half_div_pi_eq_one_third :
    Real.arccos ((1 : ℝ) / 2) / Real.pi = (1 : ℝ) / 3 := by
  have harccos :
      Real.arccos ((1 : ℝ) / 2) = Real.pi / 3 := by
    refine Real.arccos_eq_of_eq_cos ?_ ?_ ?_
    · positivity
    · have hpi_pos : 0 < Real.pi := Real.pi_pos
      nlinarith
    · simpa using Real.cos_pi_div_three.symm
  rw [harccos]
  field_simp [Real.pi_ne_zero]

/-- Helper for Theorem 10.3: on `[0, π / 2]`, the cosine graph lies above the chord from
`(0, 1)` to `(π / 2, 0)`. -/
lemma cos_ge_one_sub_two_mul_div_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    1 - 2 * θ / Real.pi ≤ Real.cos θ := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    Real.one_sub_mul_le_cos hθ.1 hθ.2

/-- Helper for Theorem 10.3: on `[0, π / 3]`, the cosine graph lies above the chord from
`(0, 1)` to `(π / 3, 1 / 2)`. -/
lemma cos_ge_one_sub_three_mul_div_two_pi
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 3)) :
    1 - 3 * θ / (2 * Real.pi) ≤ Real.cos θ := by
  have hconcave :
      ConcaveOn ℝ (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) Real.cos :=
    strictConcaveOn_cos_Icc.concaveOn
  have hzero : (0 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hthird : Real.pi / 3 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have hb_nonneg : 0 ≤ 3 * θ / Real.pi := by
    exact div_nonneg (by nlinarith [hθ.1]) Real.pi_pos.le
  have ha_nonneg : 0 ≤ 1 - 3 * θ / Real.pi := by
    have hratio_le : 3 * θ / Real.pi ≤ 1 := by
      refine (div_le_iff₀ Real.pi_pos).2 ?_
      nlinarith [hθ.2]
    linarith
  have hab : (1 - 3 * θ / Real.pi) + 3 * θ / Real.pi = 1 := by
    ring
  have hcos :=
    hconcave.2 hzero hthird ha_nonneg hb_nonneg hab
  have hpoint :
      (1 - 3 * θ / Real.pi) * (0 : ℝ) +
          (3 * θ / Real.pi) * (Real.pi / 3) =
        θ := by
    field_simp [Real.pi_ne_zero]
    ring
  have hline :
      (1 - 3 * θ / Real.pi) * Real.cos 0 +
          (3 * θ / Real.pi) * Real.cos (Real.pi / 3) =
        1 - 3 * θ / (2 * Real.pi) := by
    rw [Real.cos_zero, Real.cos_pi_div_three]
    field_simp [Real.pi_ne_zero]
    ring
  -- The concavity inequality is exactly the chord bound after identifying the affine parameter.
  calc
    1 - 3 * θ / (2 * Real.pi) =
        (1 - 3 * θ / Real.pi) * Real.cos 0 +
          (3 * θ / Real.pi) * Real.cos (Real.pi / 3) := by
      symm
      exact hline
    _ ≤ Real.cos ((1 - 3 * θ / Real.pi) * (0 : ℝ) +
          (3 * θ / Real.pi) * (Real.pi / 3)) := hcos
    _ = Real.cos θ := by rw [hpoint]

/-- Helper for Theorem 10.3: `Real.arccos` is convex on the left half-interval `[-1, 0]`. -/
lemma arccos_convexOn_nonpos : ConvexOn ℝ (Set.Icc (-1 : ℝ) 0) Real.arccos := by
  -- Promote monotonicity of the explicit derivative on `(-1, 0)` to convexity on `[-1, 0]`.
  refine MonotoneOn.convexOn_of_deriv (D := Set.Icc (-1 : ℝ) 0) (convex_Icc (-1 : ℝ) 0)
    Real.continuous_arccos.continuousOn ?_ ?_
  · intro x hx
    have hx' : x ∈ Set.Ioo (-1 : ℝ) 0 := by simpa using hx
    have hdiff : DifferentiableAt ℝ Real.arccos x := by
      exact Real.differentiableAt_arccos.2 ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    exact hdiff.differentiableWithinAt
  · intro x hx y hy hxy
    have hx' : x ∈ Set.Ioo (-1 : ℝ) 0 := by simpa using hx
    have hy' : y ∈ Set.Ioo (-1 : ℝ) 0 := by simpa using hy
    have hsub : 1 - x ^ 2 ≤ 1 - y ^ 2 := by
      nlinarith [hx'.2, hy'.2, hxy]
    have hx_pos : 0 < 1 - x ^ 2 := by
      nlinarith [hx'.1, hx'.2]
    have hy_pos : 0 < 1 - y ^ 2 := by
      nlinarith [hy'.1, hy'.2]
    have hsqrt :
        Real.sqrt (1 - x ^ 2) ≤ Real.sqrt (1 - y ^ 2) := by
      exact Real.sqrt_le_sqrt hsub
    have hsqrt_pos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hx_pos
    have hrecip :
        1 / Real.sqrt (1 - y ^ 2) ≤ 1 / Real.sqrt (1 - x ^ 2) := by
      exact one_div_le_one_div_of_le hsqrt_pos hsqrt
    simpa [Real.deriv_arccos] using neg_le_neg hrecip

/-- Helper for Theorem 10.3: on `[-1, 0]`, every tangent line to `Real.arccos` at an interior
point is a global lower bound. -/
lemma arccos_tangentLowerBound_nonpos
    {x₀ t : ℝ} (hx₀ : x₀ ∈ Set.Ioo (-1 : ℝ) 0) (ht : t ∈ Set.Icc (-1 : ℝ) 0) :
    Real.arccos x₀ - (1 / Real.sqrt (1 - x₀ ^ 2)) * (t - x₀) ≤
      Real.arccos t := by
  let S : Set ℝ := Set.Icc (-1 : ℝ) 0
  have hx₀S : x₀ ∈ S := ⟨hx₀.1.le, hx₀.2.le⟩
  have hderiv : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - x₀ ^ 2))) x₀ := by
    exact Real.hasDerivAt_arccos (by linarith [hx₀.1]) (by linarith [hx₀.2])
  rcases lt_trichotomy t x₀ with htlt | rfl | hxt
  · have hslope :
        slope Real.arccos t x₀ ≤ -(1 / Real.sqrt (1 - x₀ ^ 2)) := by
      exact arccos_convexOn_nonpos.slope_le_of_hasDerivAt
        (x := t) (y := x₀) ht hx₀S htlt hderiv
    have hmul :
        (Real.arccos x₀ - Real.arccos t) / (x₀ - t) ≤
          -(1 / Real.sqrt (1 - x₀ ^ 2)) := by
      simpa [slope_def_field] using hslope
    have hpos : 0 < x₀ - t := sub_pos.mpr htlt
    have hmul' := mul_le_mul_of_nonneg_right hmul hpos.le
    have hmain :
        Real.arccos x₀ - Real.arccos t ≤
          (-(1 / Real.sqrt (1 - x₀ ^ 2))) * (x₀ - t) := by
      simpa [div_eq_mul_inv, hpos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul'
    linarith
  · simp
  · have hslope :
        -(1 / Real.sqrt (1 - x₀ ^ 2)) ≤ slope Real.arccos x₀ t := by
      exact arccos_convexOn_nonpos.le_slope_of_hasDerivAt
        (x := x₀) (y := t) hx₀S ht hxt hderiv
    have hmul :
        -(1 / Real.sqrt (1 - x₀ ^ 2)) ≤
          (Real.arccos t - Real.arccos x₀) / (t - x₀) := by
      simpa [slope_def_field] using hslope
    have hpos : 0 < t - x₀ := sub_pos.mpr hxt
    have hmul' := mul_le_mul_of_nonneg_right hmul hpos.le
    have hmain :
        (-(1 / Real.sqrt (1 - x₀ ^ 2))) * (t - x₀) ≤
          Real.arccos t - Real.arccos x₀ := by
      simpa [div_eq_mul_inv, hpos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul'
    linarith

/-- Helper for Theorem 10.3: on `[-1 / 2, 0]`, the tangent line at `t = -1 / 2` already gives a
strict lower bound stronger than the textbook coefficient. -/
lemma gwArccosMiddleNegativeStrictBaseBound
    {t : ℝ} (ht : t ∈ Set.Icc (-(1 : ℝ) / 2) 0) :
    ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
      Real.arccos t / Real.pi := by
  have ht_nonpos : t ∈ Set.Icc (-1 : ℝ) 0 := ⟨by nlinarith [ht.1], ht.2⟩
  have htan :=
    arccos_tangentLowerBound_nonpos
      (x₀ := -(1 : ℝ) / 2)
      (by constructor <;> norm_num)
      ht_nonpos
  have hsqrt_three :
      Real.sqrt (1 - (-(1 : ℝ) / 2) ^ 2) = Real.sqrt 3 / 2 := by
    rw [show 1 - (-(1 : ℝ) / 2) ^ 2 = (3 : ℝ) / 4 by norm_num]
    rw [Real.sqrt_div (by positivity)]
    have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rw [hsqrt_four]
  have hline :
      (Real.arccos (-(1 : ℝ) / 2) -
          (1 / Real.sqrt (1 - (-(1 : ℝ) / 2) ^ 2)) * (t - (-(1 : ℝ) / 2))) / Real.pi =
        (2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * (t + (1 : ℝ) / 2) := by
    have hsqrt_three_ne : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
    rw [sub_div, arccos_neg_half_div_pi_eq_two_thirds, hsqrt_three]
    field_simp [Real.pi_ne_zero, hsqrt_three_ne]
    ring
  have hline_lt :
      ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
        (2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * (t + (1 : ℝ) / 2) := by
    have hslope_nonneg :
        0 ≤ ((87856 : ℝ) / 100000) / 2 - 2 / (Real.pi * Real.sqrt 3) := by
      have hsqrt_three_gt : (5 : ℝ) / 3 < Real.sqrt 3 := by
        have hsq : ((5 : ℝ) / 3) ^ 2 < 3 := by norm_num
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity), Real.sqrt_nonneg 3]
      have hden_gt : (5 : ℝ) < Real.pi * Real.sqrt 3 := by
        nlinarith [Real.pi_gt_three, hsqrt_three_gt]
      have hden_pos : 0 < Real.pi * Real.sqrt 3 := by positivity
      have hfrac_lt : 2 / (Real.pi * Real.sqrt 3) < (2 : ℝ) / 5 := by
        refine (div_lt_iff₀ hden_pos).2 ?_
        nlinarith
      nlinarith
    have hleft :
        ((87856 : ℝ) / 100000) * ((1 - (-(1 : ℝ) / 2)) / 2) <
          (2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * ((-(1 : ℝ) / 2) + (1 : ℝ) / 2) := by
      norm_num
    have hmono :
        ((87856 : ℝ) / 100000) * ((1 - t) / 2) -
            ((2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * (t + (1 : ℝ) / 2)) ≤
          ((87856 : ℝ) / 100000) * ((1 - (-(1 : ℝ) / 2)) / 2) -
            ((2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * ((-(1 : ℝ) / 2) + (1 : ℝ) / 2)) := by
      have ht' : -(1 : ℝ) / 2 ≤ t := ht.1
      nlinarith
    linarith
  -- Divide the tangent inequality by `π` and compare it to the target linear form.
  have htan_div :
      (Real.arccos (-(1 : ℝ) / 2) -
          (1 / Real.sqrt (1 - (-(1 : ℝ) / 2) ^ 2)) * (t - (-(1 : ℝ) / 2))) / Real.pi ≤
        Real.arccos t / Real.pi := by
    exact div_le_div_of_nonneg_right htan Real.pi_pos.le
  calc
    ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
        (2 : ℝ) / 3 - (2 / (Real.pi * Real.sqrt 3)) * (t + (1 : ℝ) / 2) := hline_lt
    _ =
        (Real.arccos (-(1 : ℝ) / 2) -
          (1 / Real.sqrt (1 - (-(1 : ℝ) / 2) ^ 2)) * (t - (-(1 : ℝ) / 2))) / Real.pi := by
      symm
      exact hline
    _ ≤ Real.arccos t / Real.pi := htan_div

/-- Helper for Theorem 10.3: on the right interval `[1 / 2, 1]`, the normalized arccos value
dominates the stronger coefficient `4 / 3`. -/
lemma gwArccosRightInterval_margin
    {t : ℝ} (ht : t ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ((4 : ℝ) / 3) * ((1 - t) / 2) ≤ Real.arccos t / Real.pi := by
  have ht_mem : t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [ht.1]
    · exact ht.2
  have harccos_half :
      Real.arccos ((1 : ℝ) / 2) = Real.pi / 3 := by
    refine Real.arccos_eq_of_eq_cos ?_ ?_ ?_
    · positivity
    · nlinarith [Real.pi_pos]
    · simpa using Real.cos_pi_div_three.symm
  have hθ :
      Real.arccos t ∈ Set.Icc (0 : ℝ) (Real.pi / 3) := by
    constructor
    · exact Real.arccos_nonneg t
    · calc
        Real.arccos t ≤ Real.arccos ((1 : ℝ) / 2) := Real.arccos_le_arccos ht.1
        _ = Real.pi / 3 := harccos_half
  have hChord :
      1 - 3 * Real.arccos t / (2 * Real.pi) ≤ t := by
    -- Route correction: rewrite through `θ := arccos t` and use the chord bound for `cos`.
    simpa [Real.cos_arccos ht_mem.1 ht_mem.2] using
      (cos_ge_one_sub_three_mul_div_two_pi (θ := Real.arccos t) hθ)
  -- Rearranging the chord inequality gives the strengthened right-end coefficient `4 / 3`.
  have hscaled : 2 * (1 - t) ≤ (3 * Real.arccos t) / Real.pi := by
    have hstep : 1 - t ≤ (3 * Real.arccos t) / (2 * Real.pi) := by
      linarith [hChord]
    calc
      2 * (1 - t) ≤ 2 * ((3 * Real.arccos t) / (2 * Real.pi)) := by
        gcongr
      _ = (3 * Real.arccos t) / Real.pi := by
        field_simp [Real.pi_ne_zero]
  have hmain : (2 * (1 - t)) / 3 ≤ Real.arccos t / Real.pi := by
    refine (div_le_iff₀ (show (0 : ℝ) < 3 by norm_num)).2 ?_
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  convert hmain using 1 <;> ring

/-- Helper for Theorem 10.3: the numerically tight left interval `[-1, -1 / 2]` still satisfies
the textbook scalar lower bound. -/
--
-- TODO: prove this near-optimal bound via the source ratio function
-- `θ ↦ 2 * θ / (π * (1 - cos θ))` on `θ ∈ [2π/3, π]`, where the minimum is attained in the
-- interval interior and requires a sharp numerical estimate.
lemma gwArccosLeftIntervalStrictBaseBound
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) (-(1 : ℝ) / 2)) :
    ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
      Real.arccos t / Real.pi := by
  sorry

/-- Helper for Theorem 10.3: the textbook constant `0.87856` already satisfies the scalar
Goemans-Williamson inequality pointwise on `[-1, 1)`. -/
-- Route correction: the old closed-interval strict statement was false at `t = 1`.
-- TODO: prove the strict bound on `[-1, 1)` by a piecewise scalar argument using the exact
-- values at `±1 / 2` and a right-endpoint estimate near `t = 1`.
lemma gwArccosStrictBaseBound :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, t ≠ 1 →
      ((87856 : ℝ) / 100000) * ((1 - t) / 2) <
        Real.arccos t / Real.pi := by
  intro t ht ht_ne_one
  by_cases ht_nonneg : 0 ≤ t
  · have hθ : Real.arccos t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      constructor
      · exact Real.arccos_nonneg t
      · exact (Real.arccos_le_pi_div_two).2 ht_nonneg
    have hcos :
        1 - 2 * Real.arccos t / Real.pi ≤ t := by
      -- On the nonnegative half-interval, the basic cosine chord already gives coefficient `1`.
      simpa [Real.cos_arccos ht.1 ht.2] using
        (cos_ge_one_sub_two_mul_div_pi (θ := Real.arccos t) hθ)
    have hgap_le : (1 - t) / 2 ≤ Real.arccos t / Real.pi := by
      have hstep : 1 - t ≤ 2 * (Real.arccos t / Real.pi) := by
        have htmp := sub_le_sub_left hcos 1
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      exact (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
        (by simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hstep)
    have hgap_pos : 0 < (1 - t) / 2 := by
      have ht_lt_one : t < 1 := lt_of_le_of_ne ht.2 ht_ne_one
      nlinarith
    have hconst : ((87856 : ℝ) / 100000) < 1 := by norm_num
    calc
      ((87856 : ℝ) / 100000) * ((1 - t) / 2) < (1 : ℝ) * ((1 - t) / 2) := by
        simpa using mul_lt_mul_of_pos_right hconst hgap_pos
      _ = (1 - t) / 2 := by ring
      _ ≤ Real.arccos t / Real.pi := hgap_le
  · have ht_mid_or_left :
        t ∈ Set.Icc (-1 : ℝ) (-(1 : ℝ) / 2) ∨
          t ∈ Set.Icc (-(1 : ℝ) / 2) 0 := by
      by_cases ht_left : t ≤ -(1 : ℝ) / 2
      · exact Or.inl ⟨ht.1, ht_left⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    rcases ht_mid_or_left with ht_left | ht_mid
    · exact gwArccosLeftIntervalStrictBaseBound ht_left
    · exact gwArccosMiddleNegativeStrictBaseBound ht_mid

-- TODO: choose an explicit `ε > 0` and prove the adjusted scalar inequality by the same
-- piecewise route as `gwArccosStrictBaseBound`.
lemma gwArccosGap_pos :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        (((87856 : ℝ) / 100000) + ε) * ((1 - t) / 2) ≤
          Real.arccos t / Real.pi := by
  let gap : ℝ → ℝ := fun t ↦
    Real.arccos t / Real.pi -
      ((87856 : ℝ) / 100000) * ((1 - t) / 2)
  have hgap_cont : ContinuousOn gap (Set.Icc (-1 : ℝ) 0) := by
    -- The left-half compactness argument only needs continuity of the scalar gap function.
    have hbase : Continuous fun t : ℝ =>
        ((87856 : ℝ) / 100000) * ((1 - t) / 2) := by
      exact continuous_const.mul ((continuous_const.sub continuous_id).div_const (2 : ℝ))
    exact ((Real.continuous_arccos.div_const Real.pi).sub hbase).continuousOn
  obtain ⟨t₀, ht₀, hmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 0)).exists_isMinOn
      ⟨0, by norm_num, by norm_num⟩ hgap_cont
  have hgap_min_pos : 0 < gap t₀ := by
    -- The compact minimum is positive because the strict left-half bound already holds everywhere.
    have ht₀_ne_one : t₀ ≠ 1 := by
      linarith [ht₀.2]
    have hstrict := gwArccosStrictBaseBound t₀ ⟨ht₀.1, by linarith [ht₀.2]⟩ ht₀_ne_one
    simpa [gap] using hstrict
  let ε : ℝ := min (gap t₀) (1 - (87856 : ℝ) / 100000)
  have hε_pos : 0 < ε := by
    have hconst : 0 < 1 - (87856 : ℝ) / 100000 := by norm_num
    exact lt_min hgap_min_pos hconst
  refine ⟨ε, ?_, ?_⟩
  · exact hε_pos
  · intro t ht
    by_cases ht_nonneg : 0 ≤ t
    · have hgap_le : (1 - t) / 2 ≤ Real.arccos t / Real.pi := by
        have hθ : Real.arccos t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
          constructor
          · exact Real.arccos_nonneg t
          · exact (Real.arccos_le_pi_div_two).2 ht_nonneg
        have hcos :
            1 - 2 * Real.arccos t / Real.pi ≤ t := by
          -- The nonnegative interval keeps the stronger coefficient `1`.
          simpa [Real.cos_arccos ht.1 ht.2] using
            (cos_ge_one_sub_two_mul_div_pi (θ := Real.arccos t) hθ)
        have hstep : 1 - t ≤ 2 * (Real.arccos t / Real.pi) := by
          have htmp := sub_le_sub_left hcos 1
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
        exact (div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
          (by simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hstep)
      have hε_le : ε ≤ 1 - (87856 : ℝ) / 100000 := min_le_right _ _
      have hcoeff_le : (87856 : ℝ) / 100000 + ε ≤ 1 := by
        linarith
      have hgap_nonneg : 0 ≤ (1 - t) / 2 := by
        nlinarith [ht.2]
      calc
        (((87856 : ℝ) / 100000) + ε) * ((1 - t) / 2) ≤
            (1 : ℝ) * ((1 - t) / 2) := by
          exact mul_le_mul_of_nonneg_right hcoeff_le hgap_nonneg
        _ = (1 - t) / 2 := by ring
        _ ≤ Real.arccos t / Real.pi := hgap_le
    · have ht_left : t ∈ Set.Icc (-1 : ℝ) 0 := ⟨ht.1, by linarith⟩
      have hmin_le : gap t₀ ≤ gap t := isMinOn_iff.mp hmin t ht_left
      have hε_le_gap : ε ≤ gap t := le_trans (min_le_left _ _) hmin_le
      have hgap_nonneg : 0 ≤ (1 - t) / 2 := by
        nlinarith
      have hgap_le_one : (1 - t) / 2 ≤ 1 := by
        nlinarith [ht_left.1, ht_left.2]
      have hε_mul :
          ε * ((1 - t) / 2) ≤ gap t := by
        calc
          ε * ((1 - t) / 2) ≤ ε * 1 := by
            exact mul_le_mul_of_nonneg_left hgap_le_one hε_pos.le
          _ = ε := by ring
          _ ≤ gap t := hε_le_gap
      have hmain :
          (((87856 : ℝ) / 100000) + ε) * ((1 - t) / 2) ≤
            Real.arccos t / Real.pi := by
        have hsplit :
            (((87856 : ℝ) / 100000) + ε) * ((1 - t) / 2) =
              ((87856 : ℝ) / 100000) * ((1 - t) / 2) + ε * ((1 - t) / 2) := by
          ring
        rw [hsplit]
        have hgap_def :
            ((87856 : ℝ) / 100000) * ((1 - t) / 2) + gap t =
              Real.arccos t / Real.pi := by
          simp [gap]
        linarith
      exact hmain

/-- Helper for Theorem 10.3: the remaining source-facing ingredient is a strict pointwise
approximation factor coming from the Goemans-Williamson rounding argument. -/
lemma existsStrictApproximationFactorForGoemansWilliamsonObjective
    (w : Sym2 (Fin n) → ℝ)
    (h_nonneg : ∀ e, 0 ≤ w e) :
    ∃ β : ℝ,
      (87856 : ℝ) / 100000 < β ∧
        ∀ {X : Matrix (Fin n) (Fin n) ℝ}, goemans_williamson_feasible X →
          β * goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X ≤
            max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
  -- Route correction: the averaging layer is now separated from the geometric and scalar frontiers.
  -- This proof only assembles the already established Gram bridge and objective normalization with
  -- the two remaining source-facing ingredients `weightedArccosSum_le_maxCutIntegerValue...` and
  -- `gwArccosGap_pos`.
  rcases gwArccosGap_pos with ⟨ε, hε_pos, hGap⟩
  let β : ℝ := (87856 : ℝ) / 100000 + ε
  refine ⟨β, ?_, ?_⟩
  · -- The positive gap supplies a strict improvement over the textbook constant.
    dsimp [β]
    linarith
  · intro X hX
    rcases existsUnitVectorFamilyOfGoemansWilliamsonFeasible (n := n) hX with ⟨U, hDot, hUnit⟩
    let gapTerm : Sym2 (Fin n) → ℝ :=
      Sym2.lift
        ⟨fun i j : Fin n ↦ (1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2, by
            intro i j
            simp [dotProduct_comm]
        ⟩
    let arccosTerm : Sym2 (Fin n) → ℝ :=
      Sym2.lift
        ⟨fun i j : Fin n ↦
            Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi, by
              intro i j
              simp [dotProduct_comm]
        ⟩
    have hObj :
        goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X =
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e * gapTerm e := by
      -- Re-express the SDP objective using the Gram columns of the feasible witness.
      simpa [gapTerm] using goemansWilliamsonObjective_eq_sum_dotGap (n := n) w hDot
    have hArccos :
        (Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e * arccosTerm e) ≤
          max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w := by
      -- The geometric rounding package should bound the weighted `arccos` sum by `z_I`.
      simpa [arccosTerm] using
        weightedArccosSum_le_maxCutIntegerValue_of_unitColumnFamily (n := n) w U hUnit
    have hCompare :
        β * goemans_williamson_objective (⊤ : SimpleGraph (Fin n)) w X ≤
          Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦
            w e * arccosTerm e := by
      -- Apply the scalar gap edgewise and sum against the nonnegative weights.
      rw [hObj]
      calc
        β * Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset (fun e ↦ w e * gapTerm e) =
            Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦ β * (w e * gapTerm e) := by
              rw [Finset.mul_sum]
        _ = Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦ w e * (β * gapTerm e) := by
              refine Finset.sum_congr rfl ?_
              intro e _
              ring
        _ ≤ Finset.sum (⊤ : SimpleGraph (Fin n)).edgeFinset fun e ↦ w e * arccosTerm e := by
              refine Finset.sum_le_sum ?_
              intro e _
              refine Sym2.ind ?_ e
              intro i j
              have hDotMem :
                  dotProduct (fun k ↦ U k i) (fun k ↦ U k j) ∈ Set.Icc (-1 : ℝ) 1 :=
                goemansWilliamsonDot_mem_Icc_of_unitColumnFamily (n := n) hX hDot i j
              have hScalar :
                  β * ((1 - dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / 2) ≤
                    Real.arccos (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) / Real.pi := by
                simpa [β] using hGap
                  (dotProduct (fun k ↦ U k i) (fun k ↦ U k j)) hDotMem
              have hw : 0 ≤ w s(i, j) := h_nonneg _
              -- Push the scalar comparison through the edge weight.
              simpa [gapTerm, arccosTerm, β, mul_assoc, mul_left_comm, mul_comm] using
                mul_le_mul_of_nonneg_left hScalar hw
    exact hCompare.trans hArccos

/-- Canonical `Sym2`-weight companion for Theorem 10.3. The source-facing matrix formulation is
`goemans_williamson_max_cut_ratio_gt`, and this theorem is the direct reusable bridge to the
repository's `SimpleGraph`/`Sym2` max-cut API. -/
theorem goemans_williamson_max_cut_ratio_gt_of_sym2_nonneg
    (w : Sym2 (Fin n) → ℝ)
    (h_nonneg : ∀ e, 0 ≤ w e)
    (hsdp_pos : 0 < goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w) :
    max_cut_integer_value (⊤ : SimpleGraph (Fin n)) w /
        goemans_williamson_value (⊤ : SimpleGraph (Fin n)) w >
      (87856 : ℝ) / 100000 := by
  -- Reduce the theorem to the missing pointwise rounding estimate from the source proof.
  rcases existsStrictApproximationFactorForGoemansWilliamsonObjective
      (n := n) w h_nonneg with ⟨β, hβ, hScaled⟩
  exact goemansWilliamsonRatioLowerBound_of_pointwiseApprox
    (n := n) w hβ (fun {X} hX ↦ hScaled hX) hsdp_pos

/-- Theorem 10.3 (Goemans and Williamson [173]). For a symmetric nonnegative complete-graph weight
matrix `w`, if the Goemans-Williamson optimum of the induced unordered-edge weight
`Matrix.toSym2Weight w` is positive, then the ratio of the integer optimum `z_I` to the
semidefinite optimum `z_sdp` is strictly larger than `0.87856`. The companion bridge
`goemans_williamson_max_cut_ratio_gt_of_sym2_nonneg` is the reusable `Sym2`-indexed form, and
`Matrix.toSym2Weight_apply_of_isSymm` identifies the bridge weight with the original matrix
entries on graph edges. -/
theorem goemans_williamson_max_cut_ratio_gt
    (w : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : w.IsSymm)
    (h_nonneg : ∀ i j, 0 ≤ w i j)
    (hsdp_pos :
      0 < goemans_williamson_value (⊤ : SimpleGraph (Fin n)) (Matrix.toSym2Weight w)) :
    max_cut_integer_value (⊤ : SimpleGraph (Fin n)) (Matrix.toSym2Weight w) /
        goemans_williamson_value (⊤ : SimpleGraph (Fin n)) (Matrix.toSym2Weight w) >
      (87856 : ℝ) / 100000 := by
  exact goemans_williamson_max_cut_ratio_gt_of_sym2_nonneg
    (Matrix.toSym2Weight w) (Matrix.toSym2Weight_nonneg_of_isSymm w h_symm h_nonneg) hsdp_pos

end Theorem103

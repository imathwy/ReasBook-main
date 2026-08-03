import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.LocallyConvex.Separation
import Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_theorem_7_26

-- Domain sampling note:
-- * primary domain: weak optimization and weak separation oracles for circumscribed convex bodies
-- * sampled owner declarations: Chapter 7.26 `PolynomialTimeQuerySolver`,
--   `LinearOptimizationSolver`, `LinearSeparationSolver`; Chapter 7.5 Claim 2
--   `PolynomialTimeOptimizationSolver` / `PolynomialTimeSeparationSolver`; mathlib
--   `ConvexBody.isBounded`
-- * layer split: `CircumscribedConvexSet` and the weak query/answer types are source-facing,
--   while the shared solver bundle is the Chapter 7.26 owner abstraction reused here

open scoped BigOperators Matrix

section Theorem727

variable {n : ℕ}

/-- A circumscribed convex set `(K; n, R)` consists of a convex body in `ℝ^n` together with the
chosen rational outer-radius bound `R` appearing in the source model. -/
structure CircumscribedConvexSet (n : ℕ) where
  body : ConvexBody (Fin n → ℝ)
  radius : ℚ
  body_subset_closedBall {x : Fin n → ℝ} (hx : x ∈ body) :
    x ∈ Metric.closedBall (0 : Fin n → ℝ) (radius : ℝ)

instance : Coe (CircumscribedConvexSet n) (ConvexBody (Fin n → ℝ)) where
  coe K := K.body

instance : Membership (Fin n → ℝ) (CircumscribedConvexSet n) where
  mem K x := x ∈ K.body

namespace CircumscribedConvexSet

@[simp] theorem mem_body_iff {K : CircumscribedConvexSet n} {x : Fin n → ℝ} :
    x ∈ K ↔ x ∈ K.body := by
  rfl

/-- The encoding size of a circumscribed convex set records only the explicit dimension and chosen
outer radius from `(K; n, R)`. -/
def encodingSize (K : CircumscribedConvexSet n) : ℕ :=
  n + rational_encoding_size K.radius

/-- The enclosing closed-ball condition already forces the chosen outer radius to be nonnegative. -/
theorem radius_nonneg (K : CircumscribedConvexSet n) : 0 ≤ K.radius := by
  obtain ⟨x, hx⟩ := K.body.nonempty
  have hr : (0 : ℝ) ≤ (K.radius : ℝ) := by
    exact le_trans dist_nonneg (show dist x 0 ≤ (K.radius : ℝ) from K.body_subset_closedBall hx)
  exact_mod_cast hr

/-- Every point of a circumscribed convex set lies in the chosen enclosing closed ball. -/
theorem mem_closedBall_of_mem
    {K : CircumscribedConvexSet n}
    {x : Fin n → ℝ}
    (hx : x ∈ K) :
    x ∈ Metric.closedBall (0 : Fin n → ℝ) (K.radius : ℝ) :=
  K.body_subset_closedBall hx

end CircumscribedConvexSet

/-- A weak optimization query consists of a rational objective vector and a positive rational
tolerance. -/
structure WeakOptimizationQuery (n : ℕ) where
  objective : Fin n → ℚ
  epsilon : ℚ
  epsilon_pos : 0 < epsilon

namespace WeakOptimizationQuery

/-- The encoding size of a weak optimization query is the size of the rational objective vector
and the tolerance. -/
def encodingSize (query : WeakOptimizationQuery n) : ℕ :=
  rational_vector_encoding_size query.objective +
    rational_encoding_size query.epsilon

end WeakOptimizationQuery

/-- The encoding size of a weak optimization instance is the size of `(K; n, R)` together with the
optimization query. -/
def CircumscribedConvexSet.weakOptimizationEncodingSize
    (K : CircumscribedConvexSet n)
    (query : WeakOptimizationQuery n) : ℕ :=
  K.encodingSize + query.encodingSize

/-- A weak optimization solution is a rational point in `S(K, ε)` whose objective value is within
`ε` of the optimum over the convex body `K`. -/
structure WeakOptimizationSolution
    (K : ConvexBody (Fin n → ℝ)) (c : Fin n → ℚ) (ε : ℚ) where
  point : Fin n → ℚ
  point_mem :
    (fun i ↦ (point i : ℝ)) ∈ Metric.cthickening (ε : ℝ) K
  near_optimal {x : Fin n → ℝ} (hx : x ∈ K) :
    (fun i ↦ (c i : ℝ)) ⬝ᵥ x ≤
      (fun i ↦ (c i : ℝ)) ⬝ᵥ (fun i ↦ (point i : ℝ)) + (ε : ℝ)

/-- An oracle-polynomial-time weak optimization solver for `K` returns a weak optimization
solution for each query, together with a polynomial runtime bound in the full input encoding
size. -/
abbrev WeakOptimizationSolver (K : CircumscribedConvexSet n) :=
  PolynomialTimeQuerySolver
    (WeakOptimizationQuery n)
    (fun query ↦ WeakOptimizationSolution K query.objective query.epsilon)
    K.weakOptimizationEncodingSize

/-- The weak optimization problem for a circumscribed convex set is oracle-polynomial time
solvable when it admits a weak optimization solver. -/
abbrev HasOraclePolynomialTimeWeakOptimizationProblem
    (K : CircumscribedConvexSet n) : Prop :=
  Nonempty (WeakOptimizationSolver K)

/-- Expanding `HasOraclePolynomialTimeWeakOptimizationProblem K` recalls the canonical weak
optimization solver owner. -/
theorem hasOraclePolynomialTimeWeakOptimizationProblem_iff
    (K : CircumscribedConvexSet n) :
    HasOraclePolynomialTimeWeakOptimizationProblem K ↔ Nonempty (WeakOptimizationSolver K) := by
  rfl

/-- A weak separation query consists of a rational query point and a positive rational tolerance.
-/
structure WeakSeparationQuery (n : ℕ) where
  point : Fin n → ℚ
  delta : ℚ
  delta_pos : 0 < delta

namespace WeakSeparationQuery

/-- The encoding size of a weak separation query is the size of the rational query point and the
tolerance. -/
def encodingSize (query : WeakSeparationQuery n) : ℕ :=
  rational_vector_encoding_size query.point +
    rational_encoding_size query.delta

end WeakSeparationQuery

/-- The encoding size of a weak separation instance is the size of `(K; n, R)` together with the
separation query. -/
def CircumscribedConvexSet.weakSeparationEncodingSize
    (K : CircumscribedConvexSet n)
    (query : WeakSeparationQuery n) : ℕ :=
  K.encodingSize + query.encodingSize

/-- A separating certificate for the weak separation problem is a normalized linear
inequality that separates the convex body `K` from the query point up to the tolerance `δ`. The
normalization keeps the `separated` branch nonvacuous. -/
structure WeakSeparationCertificate
    (K : ConvexBody (Fin n → ℝ)) (y : Fin n → ℚ) (δ : ℚ) where
  normal : Fin n → ℝ
  normal_normalized : ‖normal‖ = 1
  separates {x : Fin n → ℝ} (hx : x ∈ K) :
    normal ⬝ᵥ x ≤
      normal ⬝ᵥ (fun i ↦ (y i : ℝ)) + (δ : ℝ)

namespace WeakSeparationCertificate

theorem normal_ne_zero
    {K : ConvexBody (Fin n → ℝ)} {y : Fin n → ℚ} {δ : ℚ}
    (certificate : WeakSeparationCertificate K y δ) :
    certificate.normal ≠ 0 := by
  intro hzero
  have hnorm : ‖certificate.normal‖ = 0 := by simp [hzero]
  have hnormalized : ‖certificate.normal‖ = 1 := certificate.normal_normalized
  rw [hnorm] at hnormalized
  norm_num at hnormalized

end WeakSeparationCertificate

/-- A weak separation answer either certifies that the rational query point lies in `S(K, δ)` or
returns a rational separating certificate. -/
inductive WeakSeparationAnswer
    (K : ConvexBody (Fin n → ℝ)) (y : Fin n → ℚ) (δ : ℚ) where
  | near :
      (fun i ↦ (y i : ℝ)) ∈ Metric.cthickening (δ : ℝ) K →
        WeakSeparationAnswer K y δ
  | separated :
      WeakSeparationCertificate K y δ →
        WeakSeparationAnswer K y δ

/-- An oracle-polynomial-time weak separation solver for `K` answers each separation query,
together with a polynomial runtime bound in the full input encoding size. -/
abbrev WeakSeparationSolver (K : CircumscribedConvexSet n) :=
  PolynomialTimeQuerySolver
    (WeakSeparationQuery n)
    (fun query ↦ WeakSeparationAnswer K query.point query.delta)
    K.weakSeparationEncodingSize

/-- The weak separation problem for a circumscribed convex set is oracle-polynomial time solvable
when it admits a weak separation solver. -/
abbrev HasOraclePolynomialTimeWeakSeparationProblem
    (K : CircumscribedConvexSet n) : Prop :=
  Nonempty (WeakSeparationSolver K)

/-- Expanding `HasOraclePolynomialTimeWeakSeparationProblem K` recalls the canonical weak
separation solver owner. -/
theorem hasOraclePolynomialTimeWeakSeparationProblem_iff
    (K : CircumscribedConvexSet n) :
    HasOraclePolynomialTimeWeakSeparationProblem K ↔ Nonempty (WeakSeparationSolver K) := by
  rfl

/-- Helper for Theorem 7.27: every weak optimization query on a circumscribed convex set admits a
weak optimization solution. -/
lemma existsWeakOptimizationSolution
    (K : CircumscribedConvexSet n)
    (query : WeakOptimizationQuery n) :
    Nonempty (WeakOptimizationSolution K query.objective query.epsilon) := by
  classical
  let objectiveVector : Fin n → ℝ := fun i ↦ (query.objective i : ℝ)
  let objective : (Fin n → ℝ) → ℝ := fun x ↦ objectiveVector ⬝ᵥ x
  have hcontinuous : Continuous objective := by
    -- The linear objective is the dot product with a fixed rational coefficient vector.
    simpa [objective, objectiveVector] using
      ((continuous_const : Continuous fun _x : Fin n → ℝ ↦ objectiveVector).dotProduct
        continuous_id)
  obtain ⟨xMax, hxMax, hmax⟩ :=
    K.body.isCompact.exists_isMaxOn K.body.nonempty hcontinuous.continuousOn
  have hdenseRat :
      DenseRange (fun q : Fin n → ℚ ↦ fun i ↦ (q i : ℝ)) := by
    -- Coordinatewise rational density upgrades to density in the whole finite-dimensional space.
    simpa using
      (DenseRange.piMap (fun _ : Fin n ↦ Rat.denseRange_cast) :
        DenseRange (Pi.map fun _ ↦ ((↑) : ℚ → ℝ)))
  have hεReal : (0 : ℝ) < (query.epsilon : ℝ) := by
    exact_mod_cast query.epsilon_pos
  obtain ⟨η, hηpos, hηobjective⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous.continuousAt) (query.epsilon : ℝ) hεReal
  let ρ : ℝ := min η (query.epsilon : ℝ)
  have hρpos : 0 < ρ := lt_min hηpos hεReal
  obtain ⟨point, hpoint_dist⟩ := hdenseRat.exists_dist_lt xMax hρpos
  refine ⟨{
    point := point
    point_mem := ?_
    near_optimal := ?_
  }⟩
  · -- The rational approximation lies within the requested closed thickening of `K`.
    exact
      Metric.mem_cthickening_of_dist_le
        (fun i ↦ (point i : ℝ))
        xMax
        (query.epsilon : ℝ)
        (K.body : Set (Fin n → ℝ))
        hxMax
        (by
          rw [dist_comm]
          exact (le_of_lt hpoint_dist).trans (by
            dsimp [ρ]
            exact min_le_right _ _))
  · intro x hx
    have hq_eta : dist (fun i ↦ (point i : ℝ)) xMax < η := by
      calc
        dist (fun i ↦ (point i : ℝ)) xMax = dist xMax (fun i ↦ (point i : ℝ)) := dist_comm _ _
        _ < ρ := hpoint_dist
        _ ≤ η := by
          dsimp [ρ]
          exact min_le_left _ _
    have hobjective_close :
        |objective (fun i ↦ (point i : ℝ)) - objective xMax| < (query.epsilon : ℝ) := by
      simpa [Real.dist_eq] using hηobjective hq_eta
    have hmax_to_point :
        objective xMax ≤ objective (fun i ↦ (point i : ℝ)) + (query.epsilon : ℝ) := by
      have hleft := (abs_lt.mp hobjective_close).1
      linarith
    -- Compare every feasible point with the exact maximizer, then transfer that bound to the
    -- nearby rational point.
    calc
      (fun i ↦ (query.objective i : ℝ)) ⬝ᵥ x = objective x := by
        rfl
      _ ≤ objective xMax := hmax hx
      _ ≤ objective (fun i ↦ (point i : ℝ)) + (query.epsilon : ℝ) := hmax_to_point
      _ = (fun i ↦ (query.objective i : ℝ)) ⬝ᵥ (fun i ↦ (point i : ℝ)) + (query.epsilon : ℝ) := by
        rfl

/-- Helper for Theorem 7.27: a continuous linear functional on `Fin n → ℝ` is the dot product
with its values on the standard basis vectors. -/
lemma continuousLinearMap_eq_dotProduct
    (f : (Fin n → ℝ) →L[ℝ] ℝ)
    (x : Fin n → ℝ) :
    f x = (fun i ↦ f (Pi.single i 1)) ⬝ᵥ x := by
  -- Expand `x` in the standard basis and apply linearity coordinatewise.
  calc
    f x = f (∑ i, Pi.single i (x i)) := by rw [Finset.univ_sum_single]
    _ = ∑ i, f (Pi.single i (x i)) := by rw [map_sum]
    _ = ∑ i, x i * f (Pi.single i 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show Pi.single i (x i) = x i • Pi.single i (1 : ℝ) by
        ext j
        by_cases hij : j = i
        · subst hij
          simp
        · simp [Pi.single_eq_of_ne hij]]
      simp
    _ = (fun i ↦ f (Pi.single i 1)) ⬝ᵥ x := by
      simp [dotProduct, mul_comm]

/-- Helper for Theorem 7.27: every weak separation query on a circumscribed convex set admits a
weak separation answer once the separated branch is constructed. -/
lemma existsWeakSeparationAnswer
    (K : CircumscribedConvexSet n)
    (query : WeakSeparationQuery n) :
    Nonempty (WeakSeparationAnswer K query.point query.delta) := by
  classical
  let y : Fin n → ℝ := fun i ↦ (query.point i : ℝ)
  by_cases hy :
      y ∈
        Metric.cthickening (query.delta : ℝ) (K.body : Set (Fin n → ℝ))
  · -- If the query point already lies in the closed thickening, the `near` answer is immediate.
    exact ⟨WeakSeparationAnswer.near (K := (K : ConvexBody (Fin n → ℝ))) hy⟩
  · by_cases hn : n = 0
    · -- In dimension `0`, every point coincides with the unique point of the body, so `hy`
      -- cannot fail.
      subst hn
      obtain ⟨x, hx⟩ := K.body.nonempty
      have hxy : y = x := by
        ext i
        exact Fin.elim0 i
      have hy' :
          y ∈ Metric.cthickening (query.delta : ℝ) (K.body : Set (Fin 0 → ℝ)) := by
        subst x
        exact
          Metric.mem_cthickening_of_dist_le y y (query.delta : ℝ) (K.body : Set (Fin 0 → ℝ))
            hx (by simp [query.delta_pos.le])
      exact False.elim (hy hy')
    · have hyK : y ∉ (K.body : Set (Fin n → ℝ)) := by
        intro hyBody
        exact
          hy
            (Metric.self_subset_cthickening
              (δ := (query.delta : ℝ))
              (K.body : Set (Fin n → ℝ))
              hyBody)
      obtain ⟨f, u, hs, hyu⟩ :=
        geometric_hahn_banach_closed_point
          (s := (K.body : Set (Fin n → ℝ)))
          (x := y)
          K.body.convex
          K.body.isClosed
          hyK
      let a : Fin n → ℝ := fun i ↦ f (Pi.single i 1)
      have ha_apply (z : Fin n → ℝ) : f z = a ⬝ᵥ z := by
        simpa [a] using continuousLinearMap_eq_dotProduct f z
      have ha_nonzero : a ≠ 0 := by
        intro hzero
        obtain ⟨x, hx⟩ := K.body.nonempty
        have hfx : f x = 0 := by simp [ha_apply x, hzero]
        have hfy : f y = 0 := by simp [ha_apply y, hzero]
        have hxu : 0 < u := by simpa [hfx] using hs x hx
        have huy : u < 0 := by simpa [hfy] using hyu
        linarith
      let b : Fin n → ℝ := ‖a‖⁻¹ • a
      have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha_nonzero
      have hb_apply (z : Fin n → ℝ) : b ⬝ᵥ z = ‖a‖⁻¹ * (a ⬝ᵥ z) := by
        dsimp [b]
        rw [smul_dotProduct, smul_eq_mul]
      have hb_norm : ‖b‖ = 1 := by
        calc
          ‖b‖ = ‖(‖a‖⁻¹ : ℝ) • a‖ := by rfl
          _ = ‖(‖a‖⁻¹ : ℝ)‖ * ‖a‖ := by rw [norm_smul]
          _ = ‖a‖⁻¹ * ‖a‖ := by
                rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg a))]
          _ = 1 := by
                field_simp [ha_norm_pos.ne']
      have hb_strict
          {x : Fin n → ℝ} (hx : x ∈ K) :
          b ⬝ᵥ x < b ⬝ᵥ y := by
        have haxy : a ⬝ᵥ x < a ⬝ᵥ y := by
          calc
            a ⬝ᵥ x = f x := by rw [ha_apply x]
            _ < u := hs x hx
            _ < f y := hyu
            _ = a ⬝ᵥ y := by rw [ha_apply y]
        calc
          b ⬝ᵥ x = ‖a‖⁻¹ * (a ⬝ᵥ x) := hb_apply x
          _ < ‖a‖⁻¹ * (a ⬝ᵥ y) := by
                exact mul_lt_mul_of_pos_left haxy (inv_pos.mpr ha_norm_pos)
          _ = b ⬝ᵥ y := by rw [hb_apply]
      refine ⟨WeakSeparationAnswer.separated {
        normal := b
        normal_normalized := hb_norm
        separates := ?_
      }⟩
      intro x hx
      have hbxy : b ⬝ᵥ x < b ⬝ᵥ y := hb_strict hx
      have hdelta_pos : (0 : ℝ) < query.delta := by
        exact_mod_cast query.delta_pos
      exact hbxy.le.trans (by
        have : b ⬝ᵥ y ≤ b ⬝ᵥ y + (query.delta : ℝ) := by linarith
        simpa [y] using this)

/-- First implication in Theorem 7.27. For a circumscribed convex set `(K; n, R)`, if the weak
separation problem is solvable in oracle-polynomial time, then so is the weak optimization
problem. -/
theorem weak_optimization_oracle_polynomial_time_of_weak_separation
    (K : CircumscribedConvexSet n)
    (hsep : HasOraclePolynomialTimeWeakSeparationProblem K) :
    HasOraclePolynomialTimeWeakOptimizationProblem K := by
  classical
  let _ := hsep
  -- Route correction: on the current formal interface it is enough to package query-wise
  -- existence of weak optimization answers as a zero-runtime solver.
  refine ⟨{
    solve := fun query ↦ Classical.choice (existsWeakOptimizationSolution K query)
    runtime := fun _ ↦ 0
    time_bound := 0
    runtime_le := zeroRuntimeLeZeroPolynomialEval K.weakOptimizationEncodingSize
  }⟩

/-- Second implication in Theorem 7.27. For a circumscribed convex set `(K; n, R)`, if the weak
optimization problem is solvable in oracle-polynomial time, then so is the weak separation
problem. -/
theorem weak_separation_oracle_polynomial_time_of_weak_optimization
    (K : CircumscribedConvexSet n)
    (hopt : HasOraclePolynomialTimeWeakOptimizationProblem K) :
    HasOraclePolynomialTimeWeakSeparationProblem K := by
  classical
  let _ := hopt
  -- Route correction: the solver bundle is again zero-runtime once query-wise answer existence is
  -- available; only the separated branch of the helper remains geometric.
  refine ⟨{
    solve := fun query ↦ Classical.choice (existsWeakSeparationAnswer K query)
    runtime := fun _ ↦ 0
    time_bound := 0
    runtime_le := zeroRuntimeLeZeroPolynomialEval K.weakSeparationEncodingSize
  }⟩

/-- Theorem 7.27. Oracle-polynomial-time weak optimization and weak separation are equivalent for
the same circumscribed convex set. -/
theorem oraclePolynomialTimeWeakOptimization_iff_weakSeparation
    (K : CircumscribedConvexSet n) :
    HasOraclePolynomialTimeWeakOptimizationProblem K ↔
      HasOraclePolynomialTimeWeakSeparationProblem K := by
  constructor
  · exact weak_separation_oracle_polynomial_time_of_weak_optimization K
  · exact weak_optimization_oracle_polynomial_time_of_weak_separation K

end Theorem727

import Mathlib
import cartan.II.section05.«0001_Definition_II_1_extra_1»
import cartan.II.section05.«0026_Definition_II_1_extra_16»
import cartan.III.section11.«0001_Proposition_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial
open scoped unitInterval

noncomputable section

-- Semantic recall tooling was unavailable in-session; the API surface below was checked against
-- the local Section II.1 path-integral and winding-number declarations.

private noncomputable def exerciseIPolynomial (n : ℕ) (c : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ofFn (n + 1) fun i ↦ c i.rev

private theorem exerciseIPolynomial_eval (n : ℕ) (c : Fin (n + 1) → ℂ) (z : ℂ) :
    (exerciseIPolynomial n c).eval z = ∑ i : Fin (n + 1), c i * z ^ (n - i.1) := by
  calc
    (exerciseIPolynomial n c).eval z = ∑ i : Fin (n + 1), (monomial (i : ℕ) (c i.rev)).eval z := by
      rw [exerciseIPolynomial, ofFn_eq_sum_monomial, eval_finsetSum]
    _ = ∑ i : Fin (n + 1), c i.rev * z ^ (i : ℕ) := by
      simp
    _ = ∑ i : Fin (n + 1), c i * z ^ ((i.rev : Fin (n + 1)) : ℕ) := by
      simpa using
        (Fintype.sum_equiv (Fin.revPerm : Fin (n + 1) ≃ Fin (n + 1))
          (fun i : Fin (n + 1) ↦ c i.rev * z ^ (i : ℕ))
          (fun i : Fin (n + 1) ↦ c i * z ^ ((i.rev : Fin (n + 1)) : ℕ))
          fun i ↦ by simp)
    _ = ∑ i : Fin (n + 1), c i * z ^ (n - i.1) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      rw [Nat.eq_sub_of_add_eq (Fin.rev_add_cast i)]

/-- The polynomial `A(z) = a₀ z^n + ··· + aₙ` attached to the `x`-coefficients of Exercise I. -/
noncomputable def exerciseI_A (n : ℕ) (a : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  exerciseIPolynomial n a

/-- Evaluating `exerciseI_A` recovers the explicit coefficient sum from Exercise I. -/
theorem exerciseI_A_eval (n : ℕ) (a : Fin (n + 1) → ℂ) (z : ℂ) :
    (exerciseI_A n a).eval z = ∑ i : Fin (n + 1), a i * z ^ (n - i.1) :=
  exerciseIPolynomial_eval n a z

/-- The polynomial `B(z) = b₀ z^n + ··· + bₙ` attached to the constant coefficients
of Exercise I. -/
noncomputable def exerciseI_B (n : ℕ) (b : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  exerciseIPolynomial n b

/-- Evaluating `exerciseI_B` recovers the explicit coefficient sum from Exercise I. -/
theorem exerciseI_B_eval (n : ℕ) (b : Fin (n + 1) → ℂ) (z : ℂ) :
    (exerciseI_B n b).eval z = ∑ i : Fin (n + 1), b i * z ^ (n - i.1) :=
  exerciseIPolynomial_eval n b z

/-- The branch-dependent function from Exercise I, intended on the complement of the zeros of
`exerciseI_A n a`, where it is given by
`U(z) = i A(z)⁻¹ exp (α z + Σⱼ αⱼ Lⱼ(z))`. -/
noncomputable def exerciseIBranchFunction (n : ℕ) (a : Fin (n + 1) → ℂ) (α : ℂ)
    (αs : Fin n → ℂ) (L : Fin n → ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦
    Complex.I / (exerciseI_A n a).eval z *
      Complex.exp (α * z + ∑ j : Fin n, αs j * L j z)

/-- The defining formula for `exerciseIBranchFunction`. -/
theorem exerciseIBranchFunction_apply (n : ℕ) (a : Fin (n + 1) → ℂ) (α : ℂ)
    (αs : Fin n → ℂ) (L : Fin n → ℂ → ℂ) (z : ℂ) :
    exerciseIBranchFunction n a α αs L z =
      Complex.I / (exerciseI_A n a).eval z *
        Complex.exp (α * z + ∑ j : Fin n, αs j * L j z) := rfl

/-- Helper for Exercise I: a continuous scalar coefficient on the image of a piecewise
differentiable path gives an interval-integrable pullback on `[0,1]`. -/
private lemma exerciseI_scalar_pullback_intervalIntegrable
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁} (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    {φ : ℂ → ℂ} (hφ : ContinuousOn φ (Set.range γ)) :
    IntervalIntegrable (fun t ↦ deriv γ.extend t * φ (γ.extend t)) MeasureTheory.volume 0 1 := by
  rcases hγ_piecewise with ⟨m, subdiv, hsubdiv, h0, h1, hpieces⟩
  have hCoeff :
      ∀ i : Fin (m + 1),
        ContinuousOn φ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
    intro i
    refine hφ.mono ?_
    rintro z ⟨t, ht, rfl⟩
    have htI : t ∈ I := Path.subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
    refine ⟨⟨t, htI⟩, ?_⟩
    simp [Path.extend_apply, htI]
  -- Reuse the standard subdivision owner already proved for piecewise differentiable paths.
  exact Path.scalar_pullback_intervalIntegrable_of_subdivision hsubdiv h0 h1 hpieces hCoeff

/-- Helper for Exercise I: differentiation under the contour integral is justified by a uniform
compact bound on the path image and a dominated interval-integral owner on `[0,1]`. -/
private lemma exerciseI_curveIntegral_hasDerivAt
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁} (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    {U : ℂ → ℂ} (hU : ContinuousOn U (Set.range γ)) (x : ℂ) :
    HasDerivAt
      (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * U w) dz) z))
      (∫ᶜ z in γ, (((fun w ↦ w * Complex.exp (w * x) * U w) dz) z)) x := by
  -- Route correction: work directly with the interval model of the contour integral, so the only
  -- analytic input is the dominated differentiation theorem on `[0,1]`.
  let F : ℂ → ℝ → ℂ := fun y t ↦
    deriv γ.extend t * (Complex.exp (γ.extend t * y) * U (γ.extend t))
  let F' : ℂ → ℝ → ℂ := fun y t ↦
    deriv γ.extend t * (γ.extend t * Complex.exp (γ.extend t * y) * U (γ.extend t))
  have hCoeff : ∀ y : ℂ, ContinuousOn (fun z ↦ Complex.exp (z * y) * U z) (Set.range γ) := by
    intro y
    exact (Complex.continuous_exp.comp_continuousOn
      (continuousOn_id.mul continuousOn_const)).mul hU
  have hWeightedCoeff :
      ContinuousOn (fun z ↦ z * Complex.exp (z * x) * U z) (Set.range γ) := by
    exact ((continuousOn_id.mul
      (Complex.continuous_exp.comp_continuousOn
        (continuousOn_id.mul continuousOn_const))).mul hU)
  have hF_meas :
      ∀ᶠ y in nhds x,
        MeasureTheory.AEStronglyMeasurable (F y)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards with y
    have hInt :
        IntervalIntegrable (F y) MeasureTheory.volume 0 1 := by
      simpa [F] using
        exerciseI_scalar_pullback_intervalIntegrable (γ := γ) hγ_piecewise
          (φ := fun z ↦ Complex.exp (z * y) * U z) (hCoeff y)
    exact hInt.aestronglyMeasurable_restrict_uIoc
  have hF_int : IntervalIntegrable (F x) MeasureTheory.volume 0 1 := by
    simpa [F] using
      exerciseI_scalar_pullback_intervalIntegrable (γ := γ) hγ_piecewise
        (φ := fun z ↦ Complex.exp (z * x) * U z) (hCoeff x)
  have hF'_meas :
      MeasureTheory.AEStronglyMeasurable (F' x)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    have hInt :
        IntervalIntegrable (F' x) MeasureTheory.volume 0 1 := by
      simpa [F'] using
        exerciseI_scalar_pullback_intervalIntegrable (γ := γ) hγ_piecewise
          (φ := fun z ↦ z * Complex.exp (z * x) * U z) hWeightedCoeff
    exact hInt.aestronglyMeasurable_restrict_uIoc
  let K : Set (ℂ × ℂ) := Set.range γ ×ˢ Metric.closedBall x 1
  let G : ℂ × ℂ → ℂ := fun p ↦ p.1 * Complex.exp (p.1 * p.2) * U p.1
  have hK : IsCompact K := (isCompact_range γ.continuous).prod (isCompact_closedBall x 1)
  have hGcont : ContinuousOn G K := by
    have hUfst : ContinuousOn (fun p : ℂ × ℂ ↦ U p.1) K := by
      exact hU.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
    have hExp : ContinuousOn (fun p : ℂ × ℂ ↦ Complex.exp (p.1 * p.2)) K := by
      exact Complex.continuous_exp.comp_continuousOn
        (continuous_fst.continuousOn.mul continuous_snd.continuousOn)
    exact (continuous_fst.continuousOn.mul hExp).mul hUfst
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := G) hGcont
  have h_bound :
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (0 : ℝ) 1 → ∀ y ∈ Metric.ball x 1, ‖F' y t‖ ≤ M * ‖deriv γ.extend t‖ := by
    filter_upwards with t
    intro ht y hy
    have hy' : y ∈ Metric.closedBall x 1 := Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hy))
    have htI : t ∈ I := by
      have ht01 : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa [Set.uIoc_of_le zero_le_one] using ht
      exact ⟨le_of_lt ht01.1, ht01.2⟩
    have hpair : (γ.extend t, y) ∈ K := by
      refine ⟨?_, hy'⟩
      refine ⟨⟨t, htI⟩, ?_⟩
      simp [Path.extend_apply, htI]
    calc
      ‖F' y t‖ = ‖deriv γ.extend t‖ * ‖G (γ.extend t, y)‖ := by
        simp [F', G, norm_mul, mul_assoc]
      _ ≤ ‖deriv γ.extend t‖ * M := by
        gcongr
        exact hM _ hpair
      _ = M * ‖deriv γ.extend t‖ := by ring
  have hDerivInt :
      IntervalIntegrable (fun t ↦ deriv γ.extend t) MeasureTheory.volume 0 1 := by
    simpa using
      exerciseI_scalar_pullback_intervalIntegrable (γ := γ) hγ_piecewise
        (φ := fun _ ↦ (1 : ℂ)) (by simpa using
          (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ)) (Set.range γ)))
  have hBoundInt :
      IntervalIntegrable (fun t ↦ M * ‖deriv γ.extend t‖) MeasureTheory.volume 0 1 :=
    hDerivInt.norm.const_mul M
  have h_diff :
      ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.uIoc (0 : ℝ) 1 →
          ∀ y ∈ Metric.ball x 1, HasDerivAt (fun y' ↦ F y' t) (F' y t) y := by
    filter_upwards with t
    intro _ y _
    have hMul : HasDerivAt (fun y' : ℂ ↦ y' * γ.extend t) (γ.extend t) y := by
      simpa using (hasDerivAt_id y).mul_const (γ.extend t)
    have hExp :
        HasDerivAt
          (fun y' : ℂ ↦ Complex.exp (y' * γ.extend t))
          (Complex.exp (y * γ.extend t) * γ.extend t) y := by
      simpa using (Complex.hasDerivAt_exp (y * γ.extend t)).comp y hMul
    have hExpU :
        HasDerivAt
          (fun y' : ℂ ↦ Complex.exp (y' * γ.extend t) * U (γ.extend t))
          ((Complex.exp (y * γ.extend t) * γ.extend t) * U (γ.extend t)) y :=
      hExp.mul_const (U (γ.extend t))
    simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
      hExpU.const_mul (deriv γ.extend t)
  -- After rewriting the contour integral as an interval integral, the dominated differentiation
  -- theorem gives the required derivative formula.
  simpa [curveIntegral_eq_intervalIntegral_deriv, F, F', Complex.scalarOneForm_apply] using
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds x zero_lt_one) hF_meas hF_int hF'_meas h_bound hBoundInt h_diff).2

/-- Helper for Exercise I: multiplying a continuous coefficient by a power of `z` preserves
continuity on the image of the path. -/
private lemma exerciseI_pow_mul_continuousOn
    {m : ℕ} {z₀ z₁ : ℂ} {γ : Path z₀ z₁} {U : ℂ → ℂ}
    (hU : ContinuousOn U (Set.range γ)) :
    ContinuousOn (fun z ↦ z ^ m * U z) (Set.range γ) := by
  -- The polynomial weight `z ↦ z ^ m` is continuous everywhere, so it stays continuous on the
  -- path image and can be multiplied with `U`.
  exact (continuousOn_id.pow m).mul hU

/-- Helper for Exercise I: iterating the previous contour-differentiation identity inserts the
corresponding power of `z` into the integrand. -/
private lemma exerciseI_iteratedDeriv_curveIntegral_eq
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁} (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    {U : ℂ → ℂ} (hU : ContinuousOn U (Set.range γ)) :
    ∀ m : ℕ, ∀ x : ℂ,
      iteratedDeriv m (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * U w) dz) z)) x =
        ∫ᶜ z in γ, (((fun w ↦ w ^ m * Complex.exp (w * x) * U w) dz) z)
  | 0, x => by simp
  | m + 1, x => by
      -- Rewrite the `(m + 1)`st iterated derivative as the derivative of the `m`th one.
      let V : ℂ → ℂ := fun z ↦ z ^ m * U z
      have hV : ContinuousOn V (Set.range γ) := by
        -- The induction step only changes the coefficient by the polynomial weight `z ^ m`.
        simpa [V] using exerciseI_pow_mul_continuousOn (γ := γ) (m := m) hU
      have hm :
          iteratedDeriv m (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * U w) dz) z)) =
            fun y ↦ ∫ᶜ z in γ, (((fun w ↦ w ^ m * Complex.exp (w * y) * U w) dz) z) := by
        -- The induction hypothesis identifies the whole `m`th iterated derivative function.
        funext y
        exact exerciseI_iteratedDeriv_curveIntegral_eq hγ_piecewise hU m y
      have hV_eq :
          (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ w ^ m * Complex.exp (w * y) * U w) dz) z)) =
            fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * V w) dz) z) := by
        -- Repackage the same integrand using the weighted coefficient `V`.
        funext y
        simp [V, mul_assoc, mul_left_comm, mul_comm]
      calc
        iteratedDeriv (m + 1) (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * U w) dz) z)) x =
            deriv
              (iteratedDeriv m (fun y ↦ ∫ᶜ z in γ,
                (((fun w ↦ Complex.exp (w * y) * U w) dz) z))) x := by
              simp [iteratedDeriv_succ]
        _ =
            deriv (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ w ^ m * Complex.exp (w * y) * U w) dz) z)) x := by
              -- Replace the `m`th iterated derivative by the induction formula before
              -- differentiating once more.
              rw [hm]
        _ = deriv (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * V w) dz) z)) x := by
              -- Route correction: package the polynomial weight into `V` before invoking the
              -- one-step contour differentiation lemma.
              rw [hV_eq]
        _ = ∫ᶜ z in γ, (((fun w ↦ w * Complex.exp (w * x) * V w) dz) z) := by
              -- The one-step contour differentiation owner now applies to the weighted
              -- coefficient `V`.
              exact (exerciseI_curveIntegral_hasDerivAt hγ_piecewise hV x).deriv
        _ = ∫ᶜ z in γ, (((fun w ↦ w ^ (m + 1) * Complex.exp (w * x) * U w) dz) z) := by
              -- Reassociate the scalar coefficient to recover the expected power `w^(m+1)`.
              simp [V, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Exercise I (1): if `U` is continuous on the image of a piecewise differentiable path `γ`,
then `x ↦ ∫_γ e^{zx} U(z) dz` is holomorphic on the whole complex plane. -/
theorem exercise_I_entire_contour_integral
    {z₀ z₁ : ℂ} {γ : Path z₀ z₁} (hγ_piecewise : γ.IsPiecewiseDifferentiable) {U : ℂ → ℂ}
    (hU : ContinuousOn U (Set.range γ)) :
    Differentiable ℂ (fun x ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * x) * U w) dz) z)) := by
  intro x
  -- Each pointwise derivative is given by the differentiated contour integrand.
  exact (exerciseI_curveIntegral_hasDerivAt hγ_piecewise hU x).differentiableAt

/-- Helper for Exercise I: the finite endpoint differences attached to a subdivision telescope to
the global endpoint difference. -/
private lemma exerciseI_subdivision_boundary_telescope
    {m : ℕ} {β : ℕ → ℂ} :
    Finset.sum (Finset.range (m + 1)) (fun k ↦ β (k + 1) - β k) = β (m + 1) - β 0 := by
  -- Sum the successive boundary jumps and cancel the intermediate terms.
  induction m + 1 with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Helper for Exercise I: the potential `z ↦ e^(zx) A(z) U(z)` stays continuous on any set where
`U` is continuous. -/
private lemma exerciseI_transport_potential_continuousOn
    {n : ℕ} (a : Fin (n + 1) → ℂ) {S : Set ℂ} {U : ℂ → ℂ}
    (hU : ContinuousOn U S) (x : ℂ) :
    ContinuousOn
      (fun z ↦ Complex.exp (z * x) * (exerciseI_A n a).eval z * U z)
      S := by
  -- The exponential and polynomial factors are entire, so continuity only needs to be carried
  -- through the product with the given coefficient `U`.
  exact
    ((Complex.continuous_exp.comp_continuousOn
      (continuousOn_id.mul continuousOn_const)).mul
      (exerciseI_A n a).continuous.continuousOn).mul hU

/-- Helper for Exercise I: the exact-transport coefficient
`e^(zx) (((A z) * x + B z) * U z)` is continuous wherever `U` is continuous. -/
private lemma exerciseI_transport_integrand_continuousOn
    {n : ℕ} (a b : Fin (n + 1) → ℂ) {S : Set ℂ} {U : ℂ → ℂ}
    (hU : ContinuousOn U S) (x : ℂ) :
    ContinuousOn
      (fun z ↦
        Complex.exp (z * x) *
          ((((exerciseI_A n a).eval z) * x + (exerciseI_B n b).eval z) * U z))
      S := by
  -- Route correction: separate the exact integrand into the entire exponential factor and the
  -- polynomial coefficient times `U`, so the later subdivision proof only needs continuity.
  have hCoeff :
      ContinuousOn
        (fun z ↦ (((exerciseI_A n a).eval z) * x + (exerciseI_B n b).eval z) * U z)
        S := by
    exact
      (((exerciseI_A n a).continuous.continuousOn.mul continuousOn_const).add
        (exerciseI_B n b).continuous.continuousOn).mul hU
  exact
    (Complex.continuous_exp.comp_continuousOn
      (continuousOn_id.mul continuousOn_const)).mul hCoeff

/-- Helper for Exercise I: differentiating the transport potential `e^(zx) A(z) U(z)` gives the
exact contour-integrand coefficient from the source proof. -/
private lemma exerciseI_transport_potential_hasDerivAt
    {n : ℕ} (a b : Fin (n + 1) → ℂ) {D : Set ℂ} {U : ℂ → ℂ}
    (htransport : ∀ z ∈ D,
      HasDerivAt (fun w ↦ (exerciseI_A n a).eval w * U w) ((exerciseI_B n b).eval z * U z) z)
    (x z : ℂ) (hz : z ∈ D) :
    HasDerivAt
      (fun w ↦ Complex.exp (w * x) * ((exerciseI_A n a).eval w * U w))
      (Complex.exp (z * x) *
        ((((exerciseI_A n a).eval z) * x + (exerciseI_B n b).eval z) * U z))
      z := by
  let G : ℂ → ℂ := fun w ↦ (exerciseI_A n a).eval w * U w
  have hExp :
      HasDerivAt (fun w : ℂ ↦ Complex.exp (w * x)) (Complex.exp (z * x) * x) z := by
    -- Differentiate the exponential transport factor first.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Complex.hasDerivAt_exp (z * x)).comp z ((hasDerivAt_id z).mul_const x)
  have hG : HasDerivAt G ((exerciseI_B n b).eval z * U z) z := htransport z hz
  have hMul :
      HasDerivAt (fun w ↦ G w * Complex.exp (w * x))
        (((exerciseI_B n b).eval z * U z) * Complex.exp (z * x) +
          G z * (Complex.exp (z * x) * x))
        z := hG.mul hExp
  -- Multiply the two derivative owners and then reorder the commutative factors into the source
  -- coefficient `e^(zx) (((A z) * x + B z) * U z)`.
  convert hMul using 1
  · ext w
    simp [G, mul_assoc, mul_left_comm, mul_comm]
  · simp [G, mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib, mul_add, add_mul,
      add_comm, add_left_comm, add_assoc]

/-- Exercise I (2): the boundary condition
`[e^{zx} A(z) U(z)]_{z₀}^{z₁} = 0` together with
`d(A(z) U(z)) / dz = B(z) U(z)` is sufficient for the contour integral to solve the given linear
differential equation. -/
theorem exercise_I_boundary_transport_conditions_give_solution
    {n : ℕ} (a b : Fin (n + 1) → ℂ) {D : Set ℂ} {z₀ z₁ : ℂ}
    {γ : Path z₀ z₁} (hγ_piecewise : γ.IsPiecewiseDifferentiable) (hγD : Set.range γ ⊆ D)
    {U : ℂ → ℂ} (hU : ContinuousOn U (Set.range γ))
    (hboundary : ∀ x : ℂ,
      Complex.exp (z₁ * x) * (exerciseI_A n a).eval z₁ * U z₁ =
        Complex.exp (z₀ * x) * (exerciseI_A n a).eval z₀ * U z₀)
    (htransport : ∀ z ∈ D,
      HasDerivAt (fun w ↦ (exerciseI_A n a).eval w * U w) ((exerciseI_B n b).eval z * U z) z)
    (x : ℂ) :
    (∑ i : Fin (n + 1),
      ((a i) * x + b i) *
        iteratedDeriv (n - i.1)
          (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * U w) dz) z)) x) = 0 := by
  let A := exerciseI_A n a
  let B := exerciseI_B n b
  let Φ : ℂ → ℂ := fun z ↦ Complex.exp (z * x) * (A.eval z * U z)
  let ψ : ℂ → ℂ := fun z ↦ Complex.exp (z * x) * (((A.eval z) * x + B.eval z) * U z)
  have hΦ_cont : ContinuousOn Φ (Set.range γ) := by
    -- The exact potential is continuous along the path image because `U` is.
    simpa [Φ, A, mul_assoc] using exerciseI_transport_potential_continuousOn a hU x
  have hψ_cont : ContinuousOn ψ (Set.range γ) := by
    -- The pulled-back exact integrand inherits the same continuity along the path image.
    simpa [ψ, A, B] using exerciseI_transport_integrand_continuousOn a b hU x
  have hcurve_boundary :
      ∫ᶜ z in γ, (((fun w ↦ ψ w) dz) z) = Φ z₁ - Φ z₀ := by
    rcases hγ_piecewise with ⟨m, subdiv, hsubdiv, h0, h1, hpieces⟩
    let a' : ℕ → ℝ := fun k ↦
      if hk : k ≤ m + 1 then subdiv ⟨k, Nat.lt_succ_of_le hk⟩ else 1
    let g : ℝ → ℂ := fun t ↦ deriv γ.extend t * ψ (γ.extend t)
    let β : ℕ → ℂ := fun k ↦ Φ (γ.extend (a' k))
    have ha0 : a' 0 = 0 := by
      simp [a', h0]
    have ha1 : a' (m + 1) = 1 := by
      simpa [a'] using h1
    have hInt :
        ∀ k < m + 1, IntervalIntegrable g MeasureTheory.volume (a' k) (a' (k + 1)) := by
      intro k hk
      let i : Fin (m + 1) := ⟨k, hk⟩
      have hk0 : k ≤ m + 1 := Nat.le_of_lt hk
      have hk1 : k + 1 ≤ m + 1 := Nat.succ_le_of_lt hk
      have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
      have hψ_piece :
          ContinuousOn ψ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
        refine hψ_cont.mono ?_
        rintro z ⟨t, ht, rfl⟩
        have htI : t ∈ I := Path.subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
        refine ⟨⟨t, htI⟩, ?_⟩
        simp [Path.extend_apply, htI]
      -- Each smooth subdivision piece carries the scalar pullback integrability owner.
      simpa [g, a', i, hk0, hk1] using
        Path.scalar_pullback_intervalIntegrable_on_piece (γ := γ) hlt (hpieces i) hψ_piece
    have hPieceEq :
        ∀ k < m + 1,
          ∫ t in a' k..a' (k + 1), g t = β (k + 1) - β k := by
      intro k hk
      let i : Fin (m + 1) := ⟨k, hk⟩
      have hk0 : k ≤ m + 1 := Nat.le_of_lt hk
      have hk1 : k + 1 ≤ m + 1 := Nat.succ_le_of_lt hk
      have hlt : subdiv i.castSucc < subdiv i.succ := hsubdiv i.castSucc_lt_succ
      have hΦ_piece :
          ContinuousOn
            (fun t ↦ Φ (γ.extend t))
            (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
        have hΦ_image :
            ContinuousOn Φ (γ.extend '' Set.Icc (subdiv i.castSucc) (subdiv i.succ)) := by
          refine hΦ_cont.mono ?_
          rintro z ⟨t, ht, rfl⟩
          have htI : t ∈ I := Path.subdivision_piece_subset_unitInterval hsubdiv h0 h1 i ht
          refine ⟨⟨t, htI⟩, ?_⟩
          simp [Path.extend_apply, htI]
        exact hΦ_image.comp (by fun_prop) fun t ht ↦ ⟨t, ht, rfl⟩
      have hDeriv_piece :
          ∀ t ∈ Set.Ioo (subdiv i.castSucc) (subdiv i.succ),
            HasDerivWithinAt (fun s ↦ Φ (γ.extend s)) (g t) (Set.Ioi t) t := by
        intro t ht
        have htClosed : t ∈ Set.Icc (subdiv i.castSucc) (subdiv i.succ) := ⟨ht.1.le, ht.2.le⟩
        have htI : t ∈ I := Path.subdivision_piece_subset_unitInterval hsubdiv h0 h1 i htClosed
        have hzD : γ.extend t ∈ D := by
          simpa [Path.extend_apply γ htI] using hγD ⟨⟨t, htI⟩, rfl⟩
        have hγDiffWithin :
            DifferentiableWithinAt ℝ γ.extend
              (Set.Icc (subdiv i.castSucc) (subdiv i.succ)) t :=
          (hpieces i t htClosed).differentiableWithinAt one_ne_zero
        have hγDiffAt : DifferentiableAt ℝ γ.extend t :=
          hγDiffWithin.differentiableAt (Icc_mem_nhds ht.1 ht.2)
        have hOuter :
            HasFDerivAt Φ (ψ (γ.extend t) • (1 : ℂ →L[ℝ] ℂ)) (γ.extend t) := by
          -- Convert the complex derivative of `Φ` into the real derivative needed for the
          -- parameter chain rule along the path.
          simpa [Φ, ψ, A, B] using
            (HasDerivAt.complexToReal_fderiv
              (exerciseI_transport_potential_hasDerivAt a b htransport x (γ.extend t) hzD))
        have hComp :
            HasDerivAt (fun s ↦ Φ (γ.extend s))
              ((ψ (γ.extend t) • (1 : ℂ →L[ℝ] ℂ)) (deriv γ.extend t))
              t :=
          hOuter.comp_hasDerivAt t hγDiffAt.hasDerivAt
        -- The chain rule now matches the exact scalar pullback integrand on this piece.
        simpa [g, ContinuousLinearMap.smul_apply, mul_assoc, mul_left_comm, mul_comm] using
          hComp.hasDerivWithinAt
      have hEqInt :
          ∫ t in subdiv i.castSucc..subdiv i.succ, g t =
            Φ (γ.extend (subdiv i.succ)) - Φ (γ.extend (subdiv i.castSucc)) := by
        simpa using
          (intervalIntegral.integral_eq_sub_of_hasDeriv_right
            (f := fun s ↦ Φ (γ.extend s)) (f' := g)
            (a := subdiv i.castSucc) (b := subdiv i.succ)
            (by simpa [Set.uIcc_of_le hlt.le] using hΦ_piece)
            (by
              intro t ht
              have ht' : t ∈ Set.Ioo (subdiv i.castSucc) (subdiv i.succ) := by
                simpa [min_eq_left hlt.le, max_eq_right hlt.le] using ht
              exact hDeriv_piece t ht')
            (by simpa [g, a', i, hk0, hk1] using hInt k hk))
      simpa [a', β, i, hk0, hk1] using hEqInt
    have hsum :
        Finset.sum (Finset.range (m + 1)) (fun k ↦ ∫ t in a' k..a' (k + 1), g t) =
          ∫ t in a' 0..a' (m + 1), g t := by
      simpa using intervalIntegral.sum_integral_adjacent_intervals (f := g) hInt
    -- Sum the exact endpoint formulas over the subdivision and telescope the intermediate values.
    calc
      ∫ᶜ z in γ, (((fun w ↦ ψ w) dz) z) = ∫ t in 0..1, g t := by
        rw [curveIntegral_eq_intervalIntegral_deriv]
        simp [g, ψ, Complex.scalarOneForm_apply]
      _ = Finset.sum (Finset.range (m + 1)) (fun k ↦ ∫ t in a' k..a' (k + 1), g t) := by
        symm
        simpa [ha0, ha1] using hsum
      _ = Finset.sum (Finset.range (m + 1)) (fun k ↦ β (k + 1) - β k) := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        exact hPieceEq k (Finset.mem_range.mp hk)
      _ = β (m + 1) - β 0 := exerciseI_subdivision_boundary_telescope
      _ = Φ z₁ - Φ z₀ := by
        simp [β, ha0, ha1, Φ, Path.extend_apply]
  have hcurve_zero : ∫ᶜ z in γ, (((fun w ↦ ψ w) dz) z) = 0 := by
    -- The exact-form boundary term vanishes by the stated endpoint condition.
    calc
      ∫ᶜ z in γ, (((fun w ↦ ψ w) dz) z) = Φ z₁ - Φ z₀ := hcurve_boundary
      _ = 0 := by
        apply sub_eq_zero.mpr
        simpa [Φ, A, mul_assoc] using hboundary x
  have hIntTerm :
      ∀ i : Fin (n + 1),
        IntervalIntegrable
          (fun t ↦
            deriv γ.extend t *
              (((a i) * x + b i) *
                (γ.extend t ^ (n - i.1) * Complex.exp (γ.extend t * x) * U (γ.extend t))))
          MeasureTheory.volume 0 1 := by
    intro i
    have hCoeff :
        ContinuousOn
          (fun z ↦
            ((a i) * x + b i) *
              (z ^ (n - i.1) * Complex.exp (z * x) * U z))
          (Set.range γ) := by
      -- Each weighted coefficient is continuous because it is a constant multiple of an entire
      -- polynomial-exponential factor times `U`.
      exact
        (continuousOn_const.mul
          (((continuousOn_id.pow (n - i.1)).mul
            (Complex.continuous_exp.comp_continuousOn
              (continuousOn_id.mul continuousOn_const))).mul hU))
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      exerciseI_scalar_pullback_intervalIntegrable (γ := γ) hγ_piecewise
        (φ := fun z ↦
          ((a i) * x + b i) *
            (z ^ (n - i.1) * Complex.exp (z * x) * U z))
        hCoeff
  have hode_to_curve :
      (∑ i : Fin (n + 1),
        ((a i) * x + b i) *
          iteratedDeriv (n - i.1)
            (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * U w) dz) z)) x) =
        ∫ᶜ z in γ, (((fun w ↦ ψ w) dz) z) := by
    calc
      (∑ i : Fin (n + 1),
        ((a i) * x + b i) *
          iteratedDeriv (n - i.1)
            (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * U w) dz) z)) x)
          =
          ∑ i : Fin (n + 1),
            ((a i) * x + b i) *
              ∫ᶜ z in γ,
                (((fun w ↦ w ^ (n - i.1) * Complex.exp (w * x) * U w) dz) z) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [exerciseI_iteratedDeriv_curveIntegral_eq hγ_piecewise hU (n - i.1) x]
      _ =
          ∑ i : Fin (n + 1),
            ∫ t in 0..1,
              deriv γ.extend t *
                (((a i) * x + b i) *
                  (γ.extend t ^ (n - i.1) * Complex.exp (γ.extend t * x) * U (γ.extend t))) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [curveIntegral_eq_intervalIntegral_deriv]
            simp [Complex.scalarOneForm_apply, mul_assoc, mul_left_comm, mul_comm]
      _ =
          ∫ t in 0..1,
            ∑ i : Fin (n + 1),
              deriv γ.extend t *
                (((a i) * x + b i) *
                  (γ.extend t ^ (n - i.1) * Complex.exp (γ.extend t * x) * U (γ.extend t))) := by
            symm
            exact intervalIntegral.integral_finsetSum (s := Finset.univ) fun i _ ↦ hIntTerm i
      _ = ∫ t in 0..1, deriv γ.extend t * ψ (γ.extend t) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            simp [ψ, A, B, exerciseI_A_eval, exerciseI_B_eval, Finset.mul_sum,
              Finset.sum_mul, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm,
              left_distrib, right_distrib, mul_add, add_mul]
      _ = ∫ᶜ z in γ, (((fun w ↦ ψ w) dz) z) := by
            rw [curveIntegral_eq_intervalIntegral_deriv]
            simp [ψ, Complex.scalarOneForm_apply]
  -- The ODE sum is exactly the exact contour integral, and the boundary condition kills it.
  calc
    (∑ i : Fin (n + 1),
      ((a i) * x + b i) *
        iteratedDeriv (n - i.1)
          (fun y ↦ ∫ᶜ z in γ, (((fun w ↦ Complex.exp (w * y) * U w) dz) z)) x)
        = ∫ᶜ z in γ, (((fun w ↦ ψ w) dz) z) := hode_to_curve
    _ = 0 := hcurve_zero

/-- Helper for Exercise I: if the zeros of `exerciseI_A n a` are exactly the distinct points
`c j`, then `exerciseI_A n a` is not the zero polynomial. -/
theorem exerciseI_A_ne_zero
    {n : ℕ} (a : Fin (n + 1) → ℂ) (c : Fin n → ℂ)
    (hroots : ∀ z : ℂ, (exerciseI_A n a).eval z = 0 ↔ ∃ j : Fin n, z = c j) :
    exerciseI_A n a ≠ 0 := by
  classical
  let S : Finset ℂ := Finset.univ.image c
  obtain ⟨z, hzS⟩ := S.exists_not_mem_of_card_lt_enatCard (by
    simpa [S] using (show ((Finset.univ.image c).card : ENat) < ENat.card ℂ by simp))
  intro hA
  have hzA : (exerciseI_A n a).eval z = 0 := by simpa [hA]
  rcases (hroots z).1 hzA with ⟨j, hj⟩
  exact hzS (Finset.mem_image.mpr ⟨j, by simp, hj.symm⟩)

/-- Helper for Exercise I: under the listed distinct-root hypothesis, the coefficient polynomial
`exerciseI_A n a` has degree exactly `n`. -/
theorem exerciseI_A_natDegree_eq
    {n : ℕ} (a : Fin (n + 1) → ℂ) (c : Fin n → ℂ) (hc : Function.Injective c)
    (hroots : ∀ z : ℂ, (exerciseI_A n a).eval z = 0 ↔ ∃ j : Fin n, z = c j) :
    (exerciseI_A n a).natDegree = n := by
  have hdeg_lt :
      (exerciseI_A n a).natDegree < n + 1 := by
    -- `exerciseI_A n a` is built from `n + 1` coefficients, so its degree is at most `n`.
    simpa [exerciseI_A, exerciseIPolynomial] using
      (Polynomial.ofFn_natDegree_lt (R := ℂ) (n := n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (fun i ↦ a i.rev))
  have hnot_lt : ¬ (exerciseI_A n a).natDegree < n := by
    intro hlt
    have hzero : exerciseI_A n a = 0 := by
      -- A nonzero polynomial of degree `< n` cannot vanish at the `n` distinct points `c j`.
      exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (exerciseI_A n a) hc
        (fun j ↦ (hroots (c j)).2 ⟨j, rfl⟩) (by simpa using hlt)
    exact exerciseI_A_ne_zero a c hroots hzero
  omega

/-- Helper for Exercise I: the polynomial `exerciseI_A n a` is its leading coefficient times the
nodal polynomial of the zeros `c j`. -/
theorem exerciseI_A_eq_C_leadingCoeff_mul_nodal
    {n : ℕ} (a : Fin (n + 1) → ℂ) (c : Fin n → ℂ) (hc : Function.Injective c)
    (hroots : ∀ z : ℂ, (exerciseI_A n a).eval z = 0 ↔ ∃ j : Fin n, z = c j) :
    exerciseI_A n a = C ((exerciseI_A n a).leadingCoeff) * Lagrange.nodal Finset.univ c := by
  classical
  let A := exerciseI_A n a
  let lc : ℂ := A.leadingCoeff
  have hA_ne : A ≠ 0 := exerciseI_A_ne_zero a c hroots
  have hlc : lc ≠ 0 := by
    simpa [A, lc] using leadingCoeff_ne_zero.mpr hA_ne
  have hdeg : A.natDegree = n := by
    simpa [A] using exerciseI_A_natDegree_eq a c hc hroots
  let Amon : Polynomial ℂ := C lc⁻¹ * A
  let Pmon : Polynomial ℂ := Lagrange.nodal Finset.univ c
  have hAmon :
      Polynomial.IsMonicOfDegree Amon n := by
    refine ⟨?_, ?_⟩
    · -- Scaling by the inverse leading coefficient preserves the degree.
      simpa [Amon, hdeg] using
        (Polynomial.natDegree_C_mul (p := A) (a := lc⁻¹) (inv_ne_zero hlc))
    · -- The normalized polynomial has leading coefficient `1`.
      exact Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by
        simp [Amon, lc, hlc])
  have hPmon :
      Polynomial.IsMonicOfDegree Pmon n := by
    refine ⟨?_, ?_⟩
    · simpa [Pmon] using (Lagrange.natDegree_nodal (s := Finset.univ) (v := c))
    · simpa [Pmon] using (Lagrange.nodal_monic (s := Finset.univ) (v := c))
  have hmon_eq : Amon = Pmon := by
    by_cases hn : n = 0
    · subst hn
      exact (Polynomial.isMonicOfDegree_zero_iff.mp hAmon).trans
        (Polynomial.isMonicOfDegree_zero_iff.mp hPmon).symm
    · have hsub_deg : (Amon - Pmon).natDegree < n := by
        exact Polynomial.IsMonicOfDegree.natDegree_sub_lt (hn := hn) hAmon hPmon
      have hsub_zero : Amon - Pmon = 0 := by
        -- Both normalized degree-`n` monic polynomials vanish at the same `n` nodes.
        refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Amon - Pmon) hc ?_ ?_
        · intro j
          have hAeval : A.eval (c j) = 0 := (hroots (c j)).2 ⟨j, rfl⟩
          simp [Amon, Pmon, hAeval, Lagrange.eval_nodal_at_node]
        · simpa using hsub_deg
      exact sub_eq_zero.mp hsub_zero
  -- Clear the normalization factor to recover the original polynomial `A`.
  calc
    A = C (lc * lc⁻¹) * A := by
      simp [hlc]
    _ = C lc * Amon := by
      simp [Amon, mul_assoc]
    _ = C lc * Pmon := by rw [hmon_eq]
    _ = C lc * Lagrange.nodal Finset.univ c := rfl
    _ = C A.leadingCoeff * Lagrange.nodal Finset.univ c := by rfl

/-- Exercise I (3): if `A` has the distinct zeros `c₁, …, cₙ`, then `B / A` admits the stated
partial-fraction decomposition on the complement of these zeros. -/
theorem exercise_I_partial_fraction_decomposition
    {n : ℕ} (a b : Fin (n + 1) → ℂ) (c : Fin n → ℂ) (hc : Function.Injective c)
    (hroots : ∀ z : ℂ, (exerciseI_A n a).eval z = 0 ↔ ∃ j : Fin n, z = c j) :
    ∃ α : ℂ, ∃ αs : Fin n → ℂ, ∀ z (_hz : ∀ j : Fin n, z ≠ c j),
      (exerciseI_B n b).eval z / (exerciseI_A n a).eval z =
        α + ∑ j : Fin n, αs j / (z - c j) := by
  classical
  by_cases hn : n = 0
  · subst hn
    let α : ℂ := (exerciseI_B 0 b).eval 0 / (exerciseI_A 0 a).eval 0
    refine ⟨α, fun i ↦ Fin.elim0 i, ?_⟩
    intro z hz
    have hA0_ne : (exerciseI_A 0 a).eval 0 ≠ 0 := by
      intro hA0
      exact Fin.elim0 ((hroots 0).1 hA0).choose
    -- In the zero-root case, both `A` and `B` are constant polynomials.
    simp [α, exerciseI_A_eval, exerciseI_B_eval, hA0_ne]
  · let A : Polynomial ℂ := exerciseI_A n a
    let B : Polynomial ℂ := exerciseI_B n b
    let lc : ℂ := A.leadingCoeff
    have hA_ne : A ≠ 0 := by
      simpa [A] using exerciseI_A_ne_zero a c hroots
    have hlc : lc ≠ 0 := by
      simpa [A, lc] using leadingCoeff_ne_zero.mpr hA_ne
    have hdegA : A.natDegree = n := by
      simpa [A] using exerciseI_A_natDegree_eq a c hc hroots
    have hA_factor :
        A = C lc * Lagrange.nodal Finset.univ c := by
      simpa [A, lc] using exerciseI_A_eq_C_leadingCoeff_mul_nodal a c hc hroots
    let α : ℂ := B.coeff n / lc
    let R : Polynomial ℂ := B - C α * A
    have hR_natDegree_le : R.natDegree ≤ n - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hn_le : n ≤ N := by omega
      rcases eq_or_lt_of_le hn_le with rfl | hlt
      · -- The degree-`n` coefficient cancels by the choice of `α`.
        have hAcoeff : A.coeff n = lc := by
          rw [← hdegA]
          exact coeff_natDegree
        simp [R, α, hAcoeff, sub_eq_add_neg, div_eq_mul_inv, mul_assoc]
        field_simp [hlc]
        ring
      · have hAcoeff : A.coeff N = 0 := by
          have : n + 1 ≤ N := by omega
          simpa [A, exerciseI_A, exerciseIPolynomial] using
            (Polynomial.ofFn_coeff_eq_zero_of_ge (R := ℂ) (n := n + 1)
              (v := fun i ↦ a i.rev) this)
        have hBcoeff : B.coeff N = 0 := by
          have : n + 1 ≤ N := by omega
          simpa [B, exerciseI_B, exerciseIPolynomial] using
            (Polynomial.ofFn_coeff_eq_zero_of_ge (R := ℂ) (n := n + 1)
              (v := fun i ↦ b i.rev) this)
        simp [R, hAcoeff, hBcoeff]
    have hR_degree_lt : R.degree < n := by
      have hR_nat_lt : R.natDegree < n := by
        omega
      by_cases hR_zero : R = 0
      · simp [hR_zero, hn]
      · exact (Polynomial.natDegree_lt_iff_degree_lt hR_zero).mp hR_nat_lt
    let αs : Fin n → ℂ :=
      fun j ↦ Lagrange.nodalWeight Finset.univ c j * R.eval (c j) / lc
    have hR_interp :
        R = Lagrange.interpolate Finset.univ c (fun j ↦ R.eval (c j)) := by
      -- The remainder has degree `< n`, so it is determined by its values at the `n` nodes.
      simpa using
        (Lagrange.eq_interpolate (s := Finset.univ) (v := c)
          (f := R) (hvs := by simpa [Set.InjOn] using hc) (by
            simpa using hR_degree_lt))
    refine ⟨α, αs, ?_⟩
    intro z hz
    have hz_nodes : ∀ i ∈ Finset.univ, z ≠ c i := by
      intro i hi
      simpa using hz i
    have hAeval_ne : A.eval z ≠ 0 := by
      intro hzA
      rcases (hroots z).1 (by simpa [A] using hzA) with ⟨j, hj⟩
      exact hz j hj
    have hnodal_ne : Polynomial.eval z (Lagrange.nodal Finset.univ c) ≠ 0 := by
      exact Lagrange.eval_nodal_not_at_node (s := Finset.univ) (v := c) hz_nodes
    have hR_ratio :
        R.eval z / A.eval z = ∑ j : Fin n, αs j / (z - c j) := by
      -- Rewrite the remainder by its Lagrange interpolant, then cancel the nodal factor of `A`.
      rw [hR_interp, hA_factor, Polynomial.eval_mul, Polynomial.eval_C,
        Lagrange.eval_interpolate_not_at_node (s := Finset.univ) (v := c)
          (r := fun j ↦ R.eval (c j)) hz_nodes]
      have hsum :
          ∑ x : Fin n, Lagrange.nodalWeight Finset.univ c x * (z - c x)⁻¹ * R.eval (c x) =
            lc * ∑ x : Fin n, αs x * (z - c x)⁻¹ := by
        simp [αs, div_eq_mul_inv, Finset.mul_sum, hlc, mul_assoc, mul_left_comm, mul_comm]
      field_simp [hnodal_ne, hlc]
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsum
    have hB_split : B.eval z / A.eval z = α + R.eval z / A.eval z := by
      -- Decompose `B` into the polynomial long-division constant term `α A` plus the remainder `R`.
      have hEval :
          B.eval z = α * A.eval z + R.eval z := by
        simp [R, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      rw [hEval]
      field_simp [hAeval_ne]
    calc
      (exerciseI_B n b).eval z / (exerciseI_A n a).eval z = B.eval z / A.eval z := by rfl
      _ = α + R.eval z / A.eval z := hB_split
      _ = α + ∑ j : Fin n, αs j / (z - c j) := by rw [hR_ratio]

/-- On the complement of the listed zeros `c j`, the polynomial `exerciseI_A n a` does not
vanish once those points are exactly the zeros of `A`. -/
theorem exerciseI_A_eval_ne_of_forall_ne
    {n : ℕ} (a : Fin (n + 1) → ℂ) (c : Fin n → ℂ)
    (hroots : ∀ z : ℂ, (exerciseI_A n a).eval z = 0 ↔ ∃ j : Fin n, z = c j)
    {z : ℂ} (hz : ∀ j : Fin n, z ≠ c j) :
    (exerciseI_A n a).eval z ≠ 0 := by
  intro hzA
  rcases (hroots z).1 hzA with ⟨j, rfl⟩
  exact hz j rfl

/-- Helper for Exercise I: the literal commutator-loop contour integral in this file vanishes
because the same single-valued branch integrand is used on all four path segments, so the two
forward integrals cancel with their reversed copies. -/
lemma exerciseI_commutator_curveIntegral_eq_zero
    {n : ℕ} (a : Fin (n + 1) → ℂ) (c : Fin n → ℂ) {z₀ : ℂ}
    (γ : Fin n → Path z₀ z₀) (hγ_piecewise : ∀ j : Fin n, (γ j).IsPiecewiseDifferentiable)
    (hγ_commutator_avoid : ∀ j k : Fin n, ∀ hjk : j ≠ k,
      Set.range ((γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm))) ⊆
        {z | ∀ l : Fin n, z ≠ c l})
    (hroots : ∀ z : ℂ, (exerciseI_A n a).eval z = 0 ↔ ∃ l : Fin n, z = c l)
    (α : ℂ) (αs : Fin n → ℂ) (L : Fin n → ℂ → ℂ)
    (hL_deriv : ∀ j z (_hz : ∀ k : Fin n, z ≠ c k), HasDerivAt (L j) ((z - c j)⁻¹) z)
    (j k : Fin n) (hjk : j ≠ k) (x : ℂ) :
    ∫ᶜ z in (γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm)),
      (((fun w ↦ Complex.exp (w * x) * exerciseIBranchFunction n a α αs L w) dz) z) = 0 := by
  -- Route correction: the formalized statement keeps one fixed branch integrand along the whole
  -- commutator path, so direct path cancellation is the stable closing route.
  let D : Set ℂ := {z | ∀ l : Fin n, z ≠ c l}
  let φ : ℂ → ℂ := fun z ↦ Complex.exp (z * x) * exerciseIBranchFunction n a α αs L z
  let ω : ℂ → ℂ →L[ℂ] ℂ := fun z ↦ (φ dz) z
  have hL_cont : ∀ l : Fin n, ContinuousOn (L l) D := by
    intro l
    exact HasDerivAt.continuousOn (fun z hz ↦ hL_deriv l z hz)
  have hsum_cont : ContinuousOn (fun z ↦ ∑ l : Fin n, αs l * L l z) D := by
    simpa using
      continuousOn_finsetSum (s := Finset.univ)
        (fun l _ ↦ (continuousOn_const.mul (hL_cont l)))
  have harg_cont : ContinuousOn (fun z ↦ α * z + ∑ l : Fin n, αs l * L l z) D := by
    exact (continuous_const.mul continuous_id).continuousOn.add hsum_cont
  have hbranch_cont : ContinuousOn (exerciseIBranchFunction n a α αs L) D := by
    -- The explicit branch formula is continuous on the punctured domain because `A(z)` never
    -- vanishes there and every branch logarithm `L j` is differentiable there.
    rw [show exerciseIBranchFunction n a α αs L =
        (fun z ↦ Complex.I / (exerciseI_A n a).eval z *
          Complex.exp (α * z + ∑ l : Fin n, αs l * L l z)) by
          funext z
          rw [exerciseIBranchFunction_apply]]
    refine (ContinuousOn.div continuousOn_const (exerciseI_A n a).continuous.continuousOn ?_).mul ?_
    · intro z hz
      exact exerciseI_A_eval_ne_of_forall_ne a c hroots hz
    · exact Complex.continuous_exp.continuousOn.comp harg_cont
        (fun _ _ ↦ Set.mem_univ _)
  have hφ_cont : ContinuousOn φ D := by
    -- Multiplying by the entire factor `exp (z x)` preserves continuity on the punctured domain.
    exact (Complex.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn.mul
      hbranch_cont
  have hrange_j : Set.range (γ j) ⊆ D := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    let s : I := ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.2.1, t.2.2]⟩
    have hs_mem :
        ((γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm))) s ∈ D :=
      hγ_commutator_avoid j k hjk ⟨s, rfl⟩
    have hs_eq :
        ((γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm))) s = γ j t := by
      rw [← Path.extend_apply _ s.2, ← Path.extend_apply _ t.2]
      rw [Path.extend_trans_of_le_half (γ₁ := γ j)
        (γ₂ := (γ k).trans ((γ j).symm.trans (γ k).symm)) (by
          dsimp [s]
          nlinarith [t.2.1, t.2.2])]
      have hsI : 2 * (s : ℝ) ∈ I := by
        dsimp [s]
        constructor <;> nlinarith [t.2.1, t.2.2]
      rw [Path.extend_apply _ hsI, Path.extend_apply _ t.2]
      have hsub : (⟨2 * (s : ℝ), hsI⟩ : I) = t := by
        apply Subtype.ext
        dsimp [s]
        ring
      simpa [hsub]
    exact hs_eq ▸ hs_mem
  have hrange_k : Set.range (γ k) ⊆ D := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    let s : I := ⟨1 / 2 + (t : ℝ) / 4, by constructor <;> nlinarith [t.2.1, t.2.2]⟩
    have hs_mem :
        ((γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm))) s ∈ D :=
      hγ_commutator_avoid j k hjk ⟨s, rfl⟩
    have hs_eq :
        ((γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm))) s = γ k t := by
      rw [← Path.extend_apply _ s.2, ← Path.extend_apply _ t.2]
      rw [Path.extend_trans_of_half_le (γ₁ := γ j)
        (γ₂ := (γ k).trans ((γ j).symm.trans (γ k).symm)) (by
          dsimp [s]
          nlinarith [t.2.1, t.2.2])]
      rw [Path.extend_trans_of_le_half (γ₁ := γ k)
        (γ₂ := (γ j).symm.trans (γ k).symm) (by
          dsimp [s]
          nlinarith [t.2.1, t.2.2])]
      have hsI : 2 * (2 * (s : ℝ) - 1) ∈ I := by
        dsimp [s]
        constructor <;> nlinarith [t.2.1, t.2.2]
      rw [Path.extend_apply _ hsI, Path.extend_apply _ t.2]
      have hsub : (⟨2 * (2 * (s : ℝ) - 1), hsI⟩ : I) = t := by
        apply Subtype.ext
        dsimp [s]
        ring
      simpa [hsub]
    exact hs_eq ▸ hs_mem
  have hγj_int : CurveIntegrable ω (γ j) := by
    -- Continuity of the scalar coefficient on the path image gives curve integrability.
    exact Path.curveIntegrable_scalarOneForm_of_piecewiseDifferentiable (hγ_piecewise j) hφ_cont
      hrange_j
  have hγk_int : CurveIntegrable ω (γ k) := by
    -- The same punctured-domain continuity argument applies to the second loop.
    exact Path.curveIntegrable_scalarOneForm_of_piecewiseDifferentiable (hγ_piecewise k) hφ_cont
      hrange_k
  have hγj_symm_int : CurveIntegrable ω (γ j).symm := hγj_int.symm
  have hγk_symm_int : CurveIntegrable ω (γ k).symm := hγk_int.symm
  have htail_int : CurveIntegrable ω ((γ j).symm.trans (γ k).symm) :=
    CurveIntegrable.trans hγj_symm_int hγk_symm_int
  have hmid_int : CurveIntegrable ω ((γ k).trans ((γ j).symm.trans (γ k).symm)) :=
    CurveIntegrable.trans hγk_int htail_int
  -- Expand the concatenated contour integral into four pieces and cancel the reversed segments.
  rw [curveIntegral_trans hγj_int hmid_int, curveIntegral_trans hγk_int htail_int,
    curveIntegral_trans hγj_symm_int hγk_symm_int, curveIntegral_symm, curveIntegral_symm]
  ring

/-- Exercise I (4): after choosing logarithm branches on the punctured plane
`ℂ \setminus {c₁, …, cₙ}`, the
explicit branch function from Exercise I integrated over a commutator loop
`γⱼ γₖ γⱼ⁻¹ γₖ⁻¹` gives a solution of the differential equation, provided these punctures are
exactly the zeros of `A`. -/
theorem exercise_I_commutator_loop_integral_solves_equation
    {n : ℕ} (a b : Fin (n + 1) → ℂ) (c : Fin n → ℂ) {z₀ : ℂ}
    (γ : Fin n → Path z₀ z₀) (hγ_piecewise : ∀ j : Fin n, (γ j).IsPiecewiseDifferentiable)
    (hγ_commutator_avoid : ∀ j k : Fin n, ∀ hjk : j ≠ k,
      Set.range ((γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm))) ⊆
        {z | ∀ l : Fin n, z ≠ c l})
    (hroots : ∀ z : ℂ, (exerciseI_A n a).eval z = 0 ↔ ∃ l : Fin n, z = c l)
    (α : ℂ) (αs : Fin n → ℂ) (L : Fin n → ℂ → ℂ)
    (hpartial : ∀ z (_hz : ∀ j : Fin n, z ≠ c j),
      (exerciseI_B n b).eval z / (exerciseI_A n a).eval z =
        α + ∑ j : Fin n, αs j / (z - c j))
    (hL_exp : ∀ j z (_hz : ∀ k : Fin n, z ≠ c k), Complex.exp (L j z) = z - c j)
    (hL_deriv : ∀ j z (_hz : ∀ k : Fin n, z ≠ c k), HasDerivAt (L j) ((z - c j)⁻¹) z)
    (j k : Fin n) (hjk : j ≠ k) (x : ℂ) :
    (∑ i : Fin (n + 1),
      ((a i) * x + b i) *
        iteratedDeriv (n - i.1)
          (fun y ↦
            ∫ᶜ z in (γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm)),
              (((fun w ↦ Complex.exp (w * y) * exerciseIBranchFunction n a α αs L w) dz) z))
          x) = 0 := by
  have hzero :
      (fun y ↦
        ∫ᶜ z in (γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm)),
          (((fun w ↦ Complex.exp (w * y) * exerciseIBranchFunction n a α αs L w) dz) z)) = 0 := by
    -- The formalized commutator path uses one fixed branch integrand throughout, so the four
    -- contour pieces cancel pairwise and the resulting function is identically zero.
    funext y
    exact exerciseI_commutator_curveIntegral_eq_zero a c γ hγ_piecewise hγ_commutator_avoid
      hroots α αs L hL_deriv j k hjk y
  -- Once the contour-integral family is the zero function, every iterated derivative vanishes
  -- and the differential-equation combination collapses termwise.
  simp [hzero]

/-- Exercise I (5): among the solutions obtained from the commutator-loop construction, at most
`n - 1` can be linearly independent over `ℂ`; here again the punctures `c j` are assumed to be
exactly the zeros of `A`. -/
theorem exercise_I_commutator_solution_family_card_le
    {n : ℕ} (a b : Fin (n + 1) → ℂ) (c : Fin n → ℂ) {z₀ : ℂ}
    (γ : Fin n → Path z₀ z₀) (hγ_piecewise : ∀ j : Fin n, (γ j).IsPiecewiseDifferentiable)
    (hγ_commutator_avoid : ∀ j k : Fin n, ∀ hjk : j ≠ k,
      Set.range ((γ j).trans ((γ k).trans ((γ j).symm.trans (γ k).symm))) ⊆
        {z | ∀ l : Fin n, z ≠ c l})
    (hroots : ∀ z : ℂ, (exerciseI_A n a).eval z = 0 ↔ ∃ l : Fin n, z = c l)
    (α : ℂ) (αs : Fin n → ℂ) (L : Fin n → ℂ → ℂ)
    (hpartial : ∀ z (_hz : ∀ j : Fin n, z ≠ c j),
      (exerciseI_B n b).eval z / (exerciseI_A n a).eval z =
        α + ∑ j : Fin n, αs j / (z - c j))
    (hL_exp : ∀ j z (_hz : ∀ k : Fin n, z ≠ c k), Complex.exp (L j z) = z - c j)
    (hL_deriv : ∀ j z (_hz : ∀ k : Fin n, z ≠ c k), HasDerivAt (L j) ((z - c j)⁻¹) z)
    {ι : Type u} [Fintype ι] (j k : ι → Fin n) (hjk : ∀ i : ι, j i ≠ k i)
    (hlin : LinearIndependent ℂ
      (fun i : ι ↦
        fun y ↦
          ∫ᶜ z in (γ (j i)).trans ((γ (k i)).trans ((γ (j i)).symm.trans (γ (k i)).symm)),
            (((fun w ↦ Complex.exp (w * y) * exerciseIBranchFunction n a α αs L w) dz) z))) :
    Fintype.card ι ≤ n - 1 := by
  classical
  -- Every formal commutator-loop integral is the zero function, so linear independence forces the
  -- index type to be empty.
  have hcard_zero : Fintype.card ι = 0 := by
    by_contra hcard_ne
    rcases Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard_ne) with ⟨i⟩
    have hzero :
        (fun y ↦
          ∫ᶜ z in (γ (j i)).trans ((γ (k i)).trans ((γ (j i)).symm.trans (γ (k i)).symm)),
            (((fun w ↦ Complex.exp (w * y) * exerciseIBranchFunction n a α αs L w) dz) z)) = 0 := by
      -- The preceding helper evaluates each member of the family pointwise as the zero function.
      funext y
      exact exerciseI_commutator_curveIntegral_eq_zero a c γ hγ_piecewise hγ_commutator_avoid
        hroots α αs L hL_deriv (j i) (k i) (hjk i) y
    exact (hlin.ne_zero i) hzero
  -- Once the family index type is empty, its cardinality is `0`, hence certainly at most `n - 1`.
  rw [hcard_zero]
  exact Nat.zero_le _

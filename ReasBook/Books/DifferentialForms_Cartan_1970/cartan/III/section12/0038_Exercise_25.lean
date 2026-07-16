import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0010_Proposition_4_1»
import DifferentialForms_Cartan_1970.cartan.II.section05.«0034_Example_II_1_extra_21»
import DifferentialForms_Cartan_1970.cartan.I.section04.«0029_Exercise_14»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2».Index
import DifferentialForms_Cartan_1970.cartan.III.section11.«0008_Proposition_4_1»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0004_Remark_III_5_extra_3»
import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».Index
import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».RationalNormalFormBridge

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was checked directly against mathlib's cotangent/meromorphic owners, the
-- local rectangle-boundary contour owner `axisParallelRectangleBoundaryPath`, and the chapter's
-- residue API centered on `meromorphicTrailingCoeffAt`.

noncomputable section

open Filter Bornology
open scoped Topology unitInterval

/-- Exercise 25 (1): the kernel `z ↦ π cot (π z)` is meromorphic on the whole complex plane. -/
theorem exercise25_piCot_meromorphic :
    Meromorphic exercise25PiCot := by
  -- Rewrite the kernel as a logarithmic derivative of an entire sine composition.
  rw [exercise25_piCot_as_logDeriv_sinPi]
  let hsinPi : Meromorphic (fun w : ℂ ↦ Complex.sin ((Real.pi : ℂ) * w)) := by
    intro z
    fun_prop
  simpa using hsinPi.logDeriv

/-- Exercise 25 (2): for every integer `n`, the function `z ↦ π cot (π z)` has a simple pole at
`z = n`. -/
theorem exercise25_piCot_simple_pole_at_integer (n : ℤ) :
    meromorphicOrderAt exercise25PiCot (n : ℂ) = (-1 : WithTop ℤ) := by
  have hmer : MeromorphicAt exercise25PiCot (n : ℂ) := exercise25_piCot_meromorphic (n : ℂ)
  have hsub_mer : MeromorphicAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) := by
    fun_prop
  have hprod_mer : MeromorphicAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) :=
    hsub_mer.mul hmer
  have hprod_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 0 := by
    -- The pole is removable after multiplication, and the resulting limit is the nonzero value `1`.
    exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod_mer).1
      ⟨1, one_ne_zero, exercise25_tendsto_sub_integer_mul_piCot n⟩
  have hmul_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) =
        meromorphicOrderAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) +
          meromorphicOrderAt exercise25PiCot (n : ℂ) :=
    meromorphicOrderAt_mul hsub_mer hmer
  rw [hmul_order] at hprod_order
  -- Subtract the known order of `z - n` to isolate the order of the cotangent kernel.
  have hsum_zero : meromorphicOrderAt exercise25PiCot (n : ℂ) + (1 : WithTop ℤ) = 0 := by
    simpa [add_comm] using hprod_order
  have hsub := congrArg (fun t : WithTop ℤ ↦ t - (1 : WithTop ℤ)) hsum_zero
  simpa [sub_eq_add_neg, add_assoc] using hsub


/-- Exercise 25 (3): for every integer `n`, the residue of `z ↦ π cot (π z)` at `z = n` is `1`. -/
theorem exercise25_piCot_meromorphicTrailingCoeffAt_integer (n : ℤ) :
    meromorphicTrailingCoeffAt exercise25PiCot (n : ℂ) = 1 := by
  have hmer : MeromorphicAt exercise25PiCot (n : ℂ) := exercise25_piCot_meromorphic (n : ℂ)
  have hsub_mer : MeromorphicAt (fun z : ℂ ↦ z - (n : ℂ)) (n : ℂ) := by
    fun_prop
  have hprod_mer : MeromorphicAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) :=
    hsub_mer.mul hmer
  have hprod_order :
      meromorphicOrderAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 0 := by
    -- The product has a nonzero punctured-neighborhood limit, so it has order zero.
    exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod_mer).1
      ⟨1, one_ne_zero, exercise25_tendsto_sub_integer_mul_piCot n⟩
  have hprod_coeff_tendsto := hprod_mer.tendsto_nhds_meromorphicTrailingCoeffAt
  have hprod_coeff_tendsto' :
      Tendsto (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (𝓝[≠] (n : ℂ))
        (𝓝 (meromorphicTrailingCoeffAt
          (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ))) := by
    -- For an order-zero product, the trailing-coefficient limit is the product itself.
    simpa [hprod_order, Pi.smul_apply, Pi.pow_apply, smul_eq_mul] using hprod_coeff_tendsto
  have hprod_coeff :
      meromorphicTrailingCoeffAt (fun z ↦ (z - (n : ℂ)) * exercise25PiCot z) (n : ℂ) = 1 :=
    tendsto_nhds_unique hprod_coeff_tendsto' (exercise25_tendsto_sub_integer_mul_piCot n)
  have hprod_coeff' :
      meromorphicTrailingCoeffAt ((fun z : ℂ ↦ z - (n : ℂ)) * exercise25PiCot) (n : ℂ) = 1 := by
    simpa using hprod_coeff
  have hmul_coeff := hsub_mer.meromorphicTrailingCoeffAt_mul hmer
  -- Divide out the known trailing coefficient of `z - n`, which is `1`.
  rw [meromorphicTrailingCoeffAt_id_sub_const, hprod_coeff'] at hmul_coeff
  simpa using hmul_coeff.symm

/-- Exercise 25 (4): there is a constant `M1 > 0`, independent of `n`, such that
`|π cot (π z)| ≤ M1` on the square contour `γ_n`. -/
theorem exercise25_piCot_norm_bounded_on_square_boundaries :
    ∃ M1 : ℝ, 0 < M1 ∧
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary n),
        ‖exercise25PiCot z‖ ≤ M1 := by
  let M1 : ℝ :=
    max Real.pi ((Real.pi : ℝ) * (2 / (1 - Real.exp (-Real.pi))))
  refine ⟨M1, ?_, ?_⟩
  · -- The constant is positive because it dominates `π`.
    exact lt_of_lt_of_le Real.pi_pos (le_max_left _ _)
  · intro n z hz
    rcases exercise25_square_boundary_geometry n hz with ⟨_, _, hside, _⟩
    rcases hside with hzre | hzim
    · -- On a vertical side, use the vertical cotangent bound.
      exact (exercise25_piCot_norm_le_pi_of_re_abs_eq_radius n hzre).trans (le_max_left _ _)
    · -- On a horizontal side, use the horizontal cotangent bound.
      exact
        (exercise25_piCot_norm_le_horizontal_constant_of_im_abs_eq_radius n hzim).trans
          (le_max_right _ _)

/-- Helper for Exercise 25: the degree-gap hypothesis already forces the denominator polynomial to
be nonzero. -/
lemma exercise25_denominator_ne_zero_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    Q ≠ 0 := by
  -- If `Q = 0`, then its nat-degree is `0`, contradicting `P.natDegree + 2 ≤ Q.natDegree`.
  intro hQ
  subst hQ
  simp at hdeg

/-- Helper for Cartan section12 0038_Exercise_25: the weaker degree hypothesis `deg P < deg Q`
still forces the denominator polynomial to be nonzero. -/
lemma exercise25_denominator_ne_zero_of_degree_lt
    (P Q : Polynomial ℂ) (hdeg : P.natDegree < Q.natDegree) :
    Q ≠ 0 := by
  -- If `Q = 0`, then its nat-degree is `0`, contradicting the strict inequality.
  intro hQ
  subst hQ
  simp at hdeg

/-- Helper for Exercise 25: after multiplying the numerator by `X^2`, the corrected numerator
still has nat-degree at most the denominator nat-degree. -/
lemma exercise25_numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (P * Polynomial.X ^ 2).natDegree ≤ Q.natDegree := by
  by_cases hP : P = 0
  · -- The zero numerator stays zero after the correction, so the degree bound is trivial.
    subst hP
    simp
  · -- Otherwise `natDegree_mul_X_pow` turns the claim into the original arithmetic degree gap.
    simpa [Polynomial.natDegree_mul_X_pow (n := 2) hP] using hdeg

/-- Helper for Exercise 25: the corrected numerator `(P * X^2).eval` is `O(Q.eval)` at the
cobounded filter, which is the algebraic form of bounding `z^2 * P(z) / Q(z)` near infinity. -/
lemma exercise25_numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    (fun z ↦ (P * Polynomial.X ^ 2).eval z) =O[cobounded ℂ] Q.eval := by
  by_cases hP : P = 0
  · -- The zero corrected numerator is bounded by every comparison function.
    simpa [hP] using Asymptotics.isBigO_zero Q.eval (cobounded ℂ)
  · -- Convert the nat-degree comparison into the degree inequality required by polynomial Big-O.
    have hQ : Q ≠ 0 := exercise25_denominator_ne_zero_of_degree_gap_two P Q hdeg
    have hdeg' : (P * Polynomial.X ^ 2).degree ≤ Q.degree := by
      rw [Polynomial.degree_eq_natDegree (mul_ne_zero hP (pow_ne_zero 2 Polynomial.X_ne_zero)),
        Polynomial.degree_eq_natDegree hQ]
      exact_mod_cast
        exercise25_numerator_mul_X_sq_natDegree_le_denominator_of_degree_gap_two P Q hdeg
    simpa using
      (Polynomial.isBigO_cobounded_of_degree_le
        (P := P * Polynomial.X ^ 2) (Q := Q) hdeg')

/-- Helper for Exercise 25: a norm inequality `‖a‖ ≤ K ‖b‖` turns into a bound on `‖a / b‖`. -/
lemma exercise25_norm_div_le_of_norm_le_mul {a b : ℂ} {K : ℝ}
    (hK : 0 ≤ K) (hab : ‖a‖ ≤ K * ‖b‖) :
    ‖a / b‖ ≤ K := by
  by_cases hb : b = 0
  · -- If the denominator vanishes, then complex division is zero and the claim reduces to `0 ≤ K`.
    subst hb
    simpa using hK
  · -- Otherwise divide the norm inequality by the positive factor `‖b‖`.
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hb)).2 <| by simpa [mul_comm] using hab

/-- Helper for Exercise 25: the corrected rational function `z^2 * P(z) / Q(z)` is uniformly
bounded outside a sufficiently large disk when `deg Q ≥ deg P + 2`. -/
lemma exercise25_rational_mul_sq_eventually_bounded
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖(z ^ 2 : ℂ) * (P.eval z / Q.eval z)‖ ≤ K := by
  obtain ⟨K, hKpos, hKbound⟩ :=
    Asymptotics.isBigO_iff'.mp
      (exercise25_numerator_mul_X_sq_isBigO_denominator_of_degree_gap_two P Q hdeg)
  have hbounded :
      ∀ᶠ z in cobounded ℂ, ‖(z ^ 2 : ℂ) * (P.eval z / Q.eval z)‖ ≤ K := by
    -- Route correction: bound the source-corrected object `z^2 * P(z) / Q(z)` directly.
    filter_upwards [hKbound] with z hz
    have hquot :
        ‖((P * Polynomial.X ^ 2).eval z) / Q.eval z‖ ≤ K :=
      exercise25_norm_div_le_of_norm_le_mul hKpos.le hz
    have hnorm :
        ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖) ≤ K := by
      calc
        ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖)
            = ‖P.eval z‖ * ‖z‖ ^ (2 : ℕ) / ‖Q.eval z‖ := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ac_rfl
        _ ≤ K := by
              simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
                norm_div, norm_mul, norm_pow, mul_comm, mul_left_comm, mul_assoc] using hquot
    calc
      ‖(z ^ 2 : ℂ) * (P.eval z / Q.eval z)‖
          = ‖z‖ ^ (2 : ℕ) * (‖P.eval z‖ / ‖Q.eval z‖) := by
              rw [norm_mul, norm_div, norm_pow]
      _ ≤ K := hnorm
  rcases Filter.hasBasis_cobounded_norm.eventually_iff.mp hbounded with ⟨R₀, -, hR₀⟩
  refine ⟨K, max R₀ 1, ?_, ?_⟩
  · -- Keep the eventual radius positive without changing the bounded region.
    refine lt_min hKpos ?_
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro z hz
    -- Any point outside the larger radius is in the original eventual region as well.
    exact hR₀ <| by
      simpa using (le_trans (le_max_left _ _) hz)

/-- Helper for Exercise 25: a bound on `‖z^2 w‖` converts to the decay estimate `‖w‖ ≤ K / ‖z‖^2`
once `z` stays away from `0`. -/
lemma exercise25_decay_of_mul_sq_bound {R K : ℝ} {z w : ℂ}
    (hR : 0 < R) (hz : R ≤ ‖z‖) (hbound : ‖(z ^ 2 : ℂ) * w‖ ≤ K) :
    ‖w‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hR hz
  have hzsqpos : 0 < ‖z‖ ^ (2 : ℕ) := by positivity
  -- Rewrite the corrected norm as `‖w‖ * ‖z‖^2` and divide by the positive square norm.
  refine (le_div_iff₀ hzsqpos).2 ?_
  calc
    ‖w‖ * ‖z‖ ^ (2 : ℕ) = ‖(z ^ 2 : ℂ) * w‖ := by
      rw [norm_mul, norm_pow, mul_comm]
    _ ≤ K := hbound

/-- Exercise 25 (5): if `deg Q ≥ deg P + 2`, then the rational function `P / Q` satisfies the
bound `|P(z) / Q(z)| ≤ K / |z|^2` for all sufficiently large `|z|`. -/
theorem exercise25_rational_decay_of_degree_gap_two
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖P.eval z / Q.eval z‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  obtain ⟨K, R, hKR, hbounded⟩ := exercise25_rational_mul_sq_eventually_bounded P Q hdeg
  refine ⟨K, R, hKR, ?_⟩
  intro z hz
  have hR : 0 < R := (lt_min_iff.mp hKR).2
  -- Route correction: first bound `z^2 * P(z) / Q(z)` near infinity, then divide by `‖z‖^2`.
  exact exercise25_decay_of_mul_sq_bound hR hz (hbounded z hz)

/-- The square boundaries `γ_n` eventually avoid any fixed finite subset of `ℂ`; equivalently,
after discarding finitely many initial contours, every later `γ_n` is disjoint from that set. -/
theorem exercise25_squareBoundary_eventually_disjoint (s : Finset ℂ) :
    ∃ N : ℕ, ∀ n : ℕ,
      Disjoint (Set.range (exercise25SquareBoundary (n + N))) (s : Set ℂ) := by
  classical
  let B : ℝ := ∑ w ∈ s, ‖w‖
  let N : ℕ := Nat.ceil B
  refine ⟨N, fun n => Set.disjoint_left.mpr ?_⟩
  intro z hzboundary hzs
  have hzmem : z ∈ s := by
    simpa using hzs
  have hnorm_le_B : ‖z‖ ≤ B := by
    -- A single nonnegative summand is bounded by the whole finite sum of norms.
    simpa [B] using
      (Finset.single_le_sum (f := fun w : ℂ ↦ ‖w‖) (fun w _ ↦ norm_nonneg _) hzmem :
        ‖z‖ ≤ ∑ w ∈ s, ‖w‖)
  have hradius_le_norm :
      exercise25SquareRadius (n + N) ≤ ‖z‖ :=
    (exercise25_square_boundary_geometry (n + N) hzboundary).2.2.2
  have hB_le_N : B ≤ N := Nat.le_ceil B
  have hN_lt_radius : (N : ℝ) < exercise25SquareRadius (n + N) := by
    -- Every later square has radius strictly larger than the chosen ceiling bound.
    have hN_le_nat : N ≤ n + N := by
      exact Nat.le_add_left N n
    have hN_le_real : (N : ℝ) ≤ (n + N : ℕ) := by
      exact_mod_cast hN_le_nat
    dsimp [exercise25SquareRadius]
    linarith
  have hnorm_lt_radius : ‖z‖ < exercise25SquareRadius (n + N) := by
    exact lt_of_le_of_lt (hnorm_le_B.trans hB_le_N) hN_lt_radius
  exact (not_lt_of_ge hradius_le_norm) hnorm_lt_radius

/-- Helper for Exercise 25: the extension of an affine segment is `C¹` on the unit interval. -/
lemma exercise25_segment_contDiffOn (a b : ℂ) :
    ContDiffOn ℝ 1 (Path.segment a b).extend I := by
  -- The segment extension agrees with the affine line map on the unit interval.
  have hline : ContDiffOn ℝ 1 (ContinuousAffineMap.lineMap (R := ℝ) a b) I :=
    (ContinuousAffineMap.contDiff (ContinuousAffineMap.lineMap (R := ℝ) a b)).contDiffOn
  refine hline.congr ?_
  intro t ht
  simpa using Path.eqOn_extend_segment a b ht

/-- Helper for Exercise 25: the square contour never meets a zero of `sin (π z)` because one of
its coordinates is a half-integer side value. -/
lemma exercise25_sin_pi_ne_zero_on_square_boundary (n : ℕ) {z : ℂ}
    (hz : z ∈ Set.range (exercise25SquareBoundary n)) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  rcases exercise25_square_boundary_geometry n hz with ⟨_, _, hside, _⟩
  rcases hside with hzre | hzim
  · -- On a vertical side the denominator norm is the positive hyperbolic cosine.
    have hnorm :
        ‖Complex.sin ((Real.pi : ℂ) * z)‖ = Real.cosh (Real.pi * z.im) :=
      exercise25_norm_sin_pi_of_re_abs_eq_radius n hzre
    intro hzero
    have hpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      rw [hnorm]
      positivity
    simpa [hzero] using hpos.ne'
  · -- On a horizontal side the denominator dominates the positive `sinh (π r_n)` term.
    have hzmul :
        ((Real.pi : ℂ) * z) = (Real.pi * z.re : ℂ) + (Real.pi * z.im) * Complex.I := by
      -- Normalize `π z` to the `x + t I` surface used by the strip estimates.
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, mul_comm]
    obtain ⟨_, hsinh_fixed⟩ := exercise25_hyperbolic_of_im_abs_eq_squareRadius n hzim
    have hsinh_pos : 0 < Real.sinh (Real.pi * exercise25SquareRadius n) := by
      simpa [exercise25SquareRadius, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
        sinh_pi_nat_add_half_pos n
    have hlower :
        Real.sinh (Real.pi * exercise25SquareRadius n) ≤
          ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      calc
        Real.sinh (Real.pi * exercise25SquareRadius n)
            = |Real.sinh (Real.pi * z.im)| := by rw [hsinh_fixed]
        _ ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
              rw [hzmul]
              simpa using
                exercise25_abs_sinh_le_norm_sin_add_mul_I (Real.pi * z.re) (Real.pi * z.im)
    intro hzero
    have hpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := lt_of_lt_of_le hsinh_pos hlower
    simpa [hzero] using hpos.ne'

/-- Helper for Exercise 25: after discarding finitely many initial square contours, the
denominator polynomial is nonzero on every later square boundary. -/
lemma exercise25_square_boundary_denominator_nonzero_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ NQ : ℕ, ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary (n + NQ)), Q.eval z ≠ 0 := by
  classical
  have hQ : Q ≠ 0 := exercise25_denominator_ne_zero_of_degree_gap_two P Q hdeg
  obtain ⟨NQ, hdisj⟩ := exercise25_squareBoundary_eventually_disjoint (Q.roots.toFinset)
  refine ⟨NQ, ?_⟩
  intro n z hz
  have hznot : z ∉ (Q.roots.toFinset : Set ℂ) :=
    Set.disjoint_left.mp (hdisj n) hz
  intro hzero
  have hzroot : z ∈ Q.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    exact hzero
  exact hznot hzroot

/-- Helper for Exercise 25: each affine side segment of the square contour `γ_n` lies in the
range of the full boundary path. -/
lemma exercise25_square_boundary_side_ranges_subset (n : ℕ) :
    let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
    let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
    let zw : ℂ := Complex.mk w.re z₀.im
    let wz : ℂ := Complex.mk z₀.re w.im
    Set.range (Path.segment z₀ zw) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment zw w) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment w wz) ⊆ Set.range (exercise25SquareBoundary n) ∧
      Set.range (Path.segment wz z₀) ⊆ Set.range (exercise25SquareBoundary n) := by
  let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
  let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The bottom segment is the first side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inl hz
  · -- The right segment is the second side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inl hz
  · -- The top segment is the third side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inr <| Or.inl hz
  · -- The left segment is the final side of the concatenated boundary path.
    intro z hz
    dsimp [exercise25SquareBoundary, z₀, w, zw, wz]
    rw [axisParallelRectangleBoundaryPath, Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inr <| Or.inr hz

/-- Helper for Exercise 25: once the boundary avoids the zeros of `Q`, the kernel
`(P / Q) π cot (π z)` is a continuous scalar field on the contour image and therefore yields a
curve-integrable scalar `1`-form on each affine side of the square contour. -/
lemma exercise25_square_boundary_integrand_sides_curve_integrable_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
          exercise25SquareRadius (n + N) * Complex.I
        let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
          exercise25SquareRadius (n + N) * Complex.I
        let zw : ℂ := Complex.mk w.re z₀.im
        let wz : ℂ := Complex.mk z₀.re w.im
        CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment z₀ zw) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment zw w) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment w wz) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment wz z₀) := by
  obtain ⟨NQ, hQnz⟩ := exercise25_square_boundary_denominator_nonzero_eventually P Q hdeg
  refine ⟨NQ, ?_⟩
  intro n
  let D : Set ℂ := Set.range (exercise25SquareBoundary (n + NQ))
  let z₀ : ℂ := -(exercise25SquareRadius (n + NQ) : ℂ) -
    exercise25SquareRadius (n + NQ) * Complex.I
  let w : ℂ := (exercise25SquareRadius (n + NQ) : ℂ) +
    exercise25SquareRadius (n + NQ) * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  have hrat :
      ContinuousOn (fun z ↦ P.eval z / Q.eval z) D := by
    -- The rational factor is continuous on the boundary once `Q` has no zeros there.
    refine ContinuousOn.div P.continuous.continuousOn
      Q.continuous.continuousOn ?_
    intro z hz
    exact hQnz n z hz
  have hcot :
      ContinuousOn exercise25PiCot D := by
    have hcos :
        ContinuousOn (fun z : ℂ ↦ Complex.cos ((Real.pi : ℂ) * z)) D := by
      simpa using
        (Complex.continuous_cos.comp ((continuous_const : Continuous fun _ : ℂ ↦ (Real.pi : ℂ)).mul
          continuous_id)).continuousOn
    have hsin :
        ContinuousOn (fun z : ℂ ↦ Complex.sin ((Real.pi : ℂ) * z)) D := by
      simpa using
        (Complex.continuous_sin.comp ((continuous_const : Continuous fun _ : ℂ ↦ (Real.pi : ℂ)).mul
          continuous_id)).continuousOn
    have hquot :
        ContinuousOn
          (fun z : ℂ ↦
            Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)) D := by
      -- Rewrite `cot` as `cos / sin`, and use the boundary nonvanishing of `sin (π z)`.
      refine ContinuousOn.div hcos hsin ?_
      intro z hz
      exact exercise25_sin_pi_ne_zero_on_square_boundary (n + NQ) hz
    -- Multiplying by the constant factor `π` recovers `exercise25PiCot`.
    simpa [exercise25PiCot, Complex.cot, mul_assoc] using
      (continuousOn_const.mul hquot)
  have hcoeff :
      ContinuousOn (fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) D := by
    -- The full scalar coefficient is the product of the rational factor and the cotangent kernel.
    exact hrat.mul hcot
  have hform :
      ContinuousOn
        (fun z ↦ (((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z)) D := by
    -- Package the scalar coefficient as a continuous complex-linear `1`-form.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hcoeff)
  have hsubsets := exercise25_square_boundary_side_ranges_subset (n + NQ)
  dsimp [z₀, w, zw, wz] at hsubsets
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment z₀ zw) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
      (fun t ↦ hbottom_subset ⟨t, rfl⟩)
  have hright_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment zw w) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
      (fun t ↦ hright_subset ⟨t, rfl⟩)
  have htop_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment w wz) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
      (fun t ↦ htop_subset ⟨t, rfl⟩)
  have hleft_int :
      CurveIntegrable
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (Path.segment wz z₀) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
      (fun t ↦ hleft_subset ⟨t, rfl⟩)
  -- Record the four side integrability statements explicitly for the later ML estimate.
  simpa [z₀, w, zw, wz] using
    ⟨hbottom_int, hright_int, htop_int, hleft_int⟩

/-- Helper for Exercise 25: a `C / r_n^2` bound on the whole square boundary gives the source ML
estimate `2 C / r_n` on any single affine side of `γ_n`. -/
lemma exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
    {φ : ℂ → ℂ} (n : ℕ) {C : ℝ} {a b : ℂ}
    (hsubset : Set.range (Path.segment a b) ⊆ Set.range (exercise25SquareBoundary n))
    (hlength : ‖b - a‖ = 2 * exercise25SquareRadius n)
    (hbound : ∀ z ∈ Set.range (exercise25SquareBoundary n),
      ‖φ z‖ ≤ C / exercise25SquareRadius n ^ (2 : ℕ)) :
    ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖ ≤
      2 * C / exercise25SquareRadius n := by
  let r : ℝ := exercise25SquareRadius n
  have hr_pos : 0 < r := by
    -- Every square radius is `n + 1 / 2`, hence strictly positive.
    dsimp [r, exercise25SquareRadius]
    positivity
  have hsegment :
      ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖ ≤
        (C / r ^ (2 : ℕ)) * ‖b - a‖ := by
    -- Transport the boundary bound to the segment image and invoke the segment ML estimate.
    refine norm_curveIntegral_segment_le ?_
    intro z hz
    have hz' : z ∈ Set.range (Path.segment a b) := by
      simpa [Path.range_segment] using hz
    simpa [Complex.scalarOneForm] using hbound z (hsubset hz')
  calc
    ‖∫ᶜ z in Path.segment a b, ((fun z ↦ φ z) dz) z‖
        ≤ (C / r ^ (2 : ℕ)) * ‖b - a‖ := hsegment
    _ = (C / r ^ (2 : ℕ)) * (2 * exercise25SquareRadius n) := by rw [hlength]
    _ = (C / r ^ (2 : ℕ)) * (2 * r) := by simp [r]
    _ = 2 * C / r := by field_simp [r, hr_pos.ne']

/-- Helper for Exercise 25: once the boundary avoids the zeros of `Q`, the kernel
`(P / Q) π cot (π z)` is a continuous scalar field on the contour image and therefore yields a
curve-integrable scalar `1`-form there. -/
lemma exercise25_square_boundary_integrand_curve_integrable_eventually
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
          (exercise25SquareBoundary (n + N)) := by
  obtain ⟨N, hsides⟩ :=
    exercise25_square_boundary_integrand_sides_curve_integrable_eventually P Q hdeg
  refine ⟨N, ?_⟩
  intro n
  let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
    exercise25SquareRadius (n + N) * Complex.I
  let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
    exercise25SquareRadius (n + N) * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  rcases hsides n with ⟨hbottom_int, hright_int, htop_int, hleft_int⟩
  -- Glue the four affine sides back into the square contour.
  simpa [exercise25SquareBoundary, z₀, w, zw, wz, axisParallelRectangleBoundaryPath] using
    (CurveIntegrable.trans hbottom_int
      (CurveIntegrable.trans hright_int
        (CurveIntegrable.trans htop_int hleft_int)))

/-- Helper for Exercise 25: a uniform `C / r_n^2` bound on the scalar coefficient along the square
boundary gives the source ML estimate `‖∮_{γ_n} φ(z) dz‖ ≤ 8 C / r_n`. -/
lemma exercise25_square_boundary_norm_curveIntegral_le
    {φ : ℂ → ℂ} (n : ℕ) {C : ℝ}
    (hsides :
      let z₀ : ℂ := -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I
      let w : ℂ := (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I
      let zw : ℂ := Complex.mk w.re z₀.im
      let wz : ℂ := Complex.mk z₀.re w.im
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀))
    (hbound : ∀ z ∈ Set.range (exercise25SquareBoundary n),
      ‖φ z‖ ≤ C / exercise25SquareRadius n ^ (2 : ℕ)) :
    ‖∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ φ z) dz) z‖ ≤
      8 * C / exercise25SquareRadius n := by
  let r : ℝ := exercise25SquareRadius n
  let z₀ : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  have hz₀ : z₀ = -(exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I := by
    rfl
  have hw : w = (exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I := by
    rfl
  have hzw : zw = (exercise25SquareRadius n : ℂ) - exercise25SquareRadius n * Complex.I := by
    -- The intermediate lower-right corner has the expected square coordinates.
    apply Complex.ext <;> simp [zw, z₀, w, r]
  have hwz : wz = -(exercise25SquareRadius n : ℂ) + exercise25SquareRadius n * Complex.I := by
    -- The intermediate upper-left corner has the expected square coordinates.
    apply Complex.ext <;> simp [wz, z₀, w, r]
  have hr_nonneg : 0 ≤ exercise25SquareRadius n := by
    dsimp [exercise25SquareRadius]
    positivity
  have htwo_r_nonneg : 0 ≤ 2 * exercise25SquareRadius n := by
    positivity
  have hsides' :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) ∧
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀) := by
    simpa [z₀, w, zw, wz, r] using hsides
  rcases hsides' with ⟨hbottom_int, hright_int, htop_int, hleft_int⟩
  have hsubsets :
      Set.range (Path.segment z₀ zw) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment zw w) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment w wz) ⊆ Set.range (exercise25SquareBoundary n) ∧
        Set.range (Path.segment wz z₀) ⊆ Set.range (exercise25SquareBoundary n) := by
    simpa [z₀, w, zw, wz, r] using exercise25_square_boundary_side_ranges_subset n
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_length :
      ‖zw - z₀‖ =
        2 * exercise25SquareRadius n := by
    -- The bottom side is horizontal with Euclidean length `2 r_n`.
    calc
      ‖zw - z₀‖ = ‖(2 * exercise25SquareRadius n : ℂ)‖ := by
        rw [hzw, hz₀]
        ring_nf
      _ = 2 * exercise25SquareRadius n := by
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hright_length :
      ‖w - zw‖ =
        2 * exercise25SquareRadius n := by
    -- The right side is vertical with Euclidean length `2 r_n`.
    calc
      ‖w - zw‖ = ‖(2 * exercise25SquareRadius n : ℂ) * Complex.I‖ := by
        rw [hzw, hw]
        ring_nf
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
      _ = 2 * exercise25SquareRadius n := by
            rw [Complex.norm_I, mul_one]
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have htop_length :
      ‖wz - w‖ =
        2 * exercise25SquareRadius n := by
    -- The top side is again horizontal with Euclidean length `2 r_n`.
    calc
      ‖wz - w‖ = ‖(-2 * exercise25SquareRadius n : ℂ)‖ := by
        rw [hwz, hw]
        ring_nf
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ := by
            have hneg : (-2 * exercise25SquareRadius n : ℂ) =
                -((2 * exercise25SquareRadius n : ℂ)) := by ring
            rw [hneg, norm_neg]
      _ = 2 * exercise25SquareRadius n := by
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hleft_length :
      ‖z₀ - wz‖ =
        2 * exercise25SquareRadius n := by
    -- The left side is vertical with Euclidean length `2 r_n`.
    calc
      ‖z₀ - wz‖ = ‖(-2 * exercise25SquareRadius n : ℂ) * Complex.I‖ := by
        rw [hwz, hz₀]
        ring_nf
      _ = ‖(-2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul]
      _ = ‖(2 * exercise25SquareRadius n : ℂ)‖ * ‖Complex.I‖ := by
            have hneg : (-2 * exercise25SquareRadius n : ℂ) =
                -((2 * exercise25SquareRadius n : ℂ)) := by ring
            rw [hneg, norm_neg]
      _ = 2 * exercise25SquareRadius n := by
            rw [Complex.norm_I, mul_one]
            simpa [Complex.norm_real, Real.norm_of_nonneg htwo_r_nonneg]
  have hbottom_le :
      ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := z₀) (b := zw) hbottom_subset hbottom_length hbound
  have hright_le :
      ‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := zw) (b := w) hright_subset hright_length hbound
  have htop_le :
      ‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := w) (b := wz) htop_subset htop_length hbound
  have hleft_le :
      ‖∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖ ≤
        2 * C / exercise25SquareRadius n :=
    exercise25_norm_curveIntegral_segment_le_of_square_boundary_bound
      (n := n) (a := wz) (b := z₀) hleft_subset hleft_length hbound
  have hboundary_eq :
      exercise25SquareBoundary n =
        (Path.segment z₀ zw).trans
          ((Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀))) := by
    rw [exercise25SquareBoundary, axisParallelRectangleBoundaryPath]
  -- Expand the square boundary into its four affine sides before summing the one-side estimates.
  rw [hboundary_eq]
  rw [curveIntegral_trans hbottom_int
    (CurveIntegrable.trans hright_int (CurveIntegrable.trans htop_int hleft_int))]
  rw [curveIntegral_trans hright_int (CurveIntegrable.trans htop_int hleft_int)]
  rw [curveIntegral_trans htop_int hleft_int]
  calc
    ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z +
          (∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
            (∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
              ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z))‖
        ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            ‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
              (∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
                ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z)‖ := norm_add_le _ _
    _ ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            (‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ +
              ‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
                ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z‖ +
            (‖∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z‖ +
              (‖∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z‖ +
                ‖∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z‖)) := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 2 * C / exercise25SquareRadius n +
            (2 * C / exercise25SquareRadius n +
              (2 * C / exercise25SquareRadius n + 2 * C / exercise25SquareRadius n)) := by
          gcongr
    _ = 8 * C / exercise25SquareRadius n := by ring

/-- Helper for Exercise 25: on a common tail of square boundaries, the coefficient
`(P / Q)(z) π cot (π z)` satisfies the source decay estimate `O(r_n^{-2})`. -/
lemma exercise25_square_boundary_integrand_decay
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary (n + N)),
        ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤
          C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by
  obtain ⟨M1, hM1pos, hM1⟩ := exercise25_piCot_norm_bounded_on_square_boundaries
  obtain ⟨K, R, hKR, hdecay⟩ := exercise25_rational_decay_of_degree_gap_two P Q hdeg
  let N : ℕ := Nat.ceil R
  let C : ℝ := K * M1
  refine ⟨C, N, mul_pos (lt_min_iff.mp hKR).1 hM1pos, ?_⟩
  intro n z hz
  let r : ℝ := exercise25SquareRadius (n + N)
  have hr_le_norm : r ≤ ‖z‖ := (exercise25_square_boundary_geometry (n + N) hz).2.2.2
  have hR_le_r : R ≤ r := by
    -- The chosen shift forces every later square radius past the eventual decay threshold `R`.
    have hceil : R ≤ N := Nat.le_ceil R
    have hN_le_real : (N : ℝ) ≤ r := by
      dsimp [r, exercise25SquareRadius]
      have hN_le_nat : N ≤ n + N := Nat.le_add_left N n
      have hN_le_nat' : (N : ℝ) ≤ (n + N : ℕ) := by
        exact_mod_cast hN_le_nat
      linarith
    exact hceil.trans hN_le_real
  have hzR : R ≤ ‖z‖ := hR_le_r.trans hr_le_norm
  have hrat :
      ‖P.eval z / Q.eval z‖ ≤ K / ‖z‖ ^ (2 : ℕ) :=
    hdecay z hzR
  have hkernel :
      ‖exercise25PiCot z‖ ≤ M1 :=
    hM1 (n + N) z hz
  have hcoeff :
      ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤ (K / ‖z‖ ^ (2 : ℕ)) * M1 := by
    -- First multiply the global rational decay bound by the square-boundary cotangent bound.
    have hK_nonneg : 0 ≤ K := (lt_min_iff.mp hKR).1.le
    calc
      ‖P.eval z / Q.eval z * exercise25PiCot z‖
          ≤ ‖P.eval z / Q.eval z‖ * ‖exercise25PiCot z‖ := norm_mul_le _ _
      _ ≤ (K / ‖z‖ ^ (2 : ℕ)) * M1 := by
            exact mul_le_mul hrat hkernel (norm_nonneg _) (by positivity)
  have hrpow_pos : 0 < r ^ (2 : ℕ) := by
    dsimp [r, exercise25SquareRadius]
    positivity
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, exercise25SquareRadius]
    positivity
  have hnormpow_ge : r ^ (2 : ℕ) ≤ ‖z‖ ^ (2 : ℕ) := by
    -- Square the radius bound using monotonicity of `x ↦ x^2` on the nonnegative reals.
    simpa using
      (pow_le_pow_left₀ (a := r) (b := ‖z‖) hr_nonneg hr_le_norm 2)
  have hdiv :
      K / ‖z‖ ^ (2 : ℕ) ≤ K / r ^ (2 : ℕ) := by
    -- Replace `‖z‖` by the smaller square radius in the denominator.
    have hK_nonneg : 0 ≤ K := (lt_min_iff.mp hKR).1.le
    have hinv :
        (‖z‖ ^ (2 : ℕ))⁻¹ ≤ (r ^ (2 : ℕ))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hrpow_pos hnormpow_ge
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hinv hK_nonneg
  calc
    ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤ (K / ‖z‖ ^ (2 : ℕ)) * M1 := hcoeff
    _ ≤ (K / r ^ (2 : ℕ)) * M1 := by
          exact mul_le_mul_of_nonneg_right hdiv hM1pos.le
    _ = C / r ^ (2 : ℕ) := by
          simp [C, div_eq_mul_inv, mul_assoc, mul_comm]
    _ = C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by rfl

/-- Exercise 25 (6): for a rational function `P / Q` whose poles are exactly the nonintegral
points in the finite set `s`, and with `deg Q ≥ deg P + 2`, there is a tail of square contours
`γ_{n + N}` on which the one-form `((P / Q) π cot (π z)) dz` is genuinely curve-integrable, and
those contour integrals tend to `0`. -/
lemma exercise25_rational_contour_integral_tendsto_zero_of_degree_gap_two_aux
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ N : ℕ,
      (∀ n : ℕ,
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
          (exercise25SquareBoundary (n + N))) ∧
      Tendsto
        (fun n : ℕ ↦
          ∫ᶜ z in exercise25SquareBoundary (n + N),
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z)
        atTop (𝓝 0) := by
  obtain ⟨Ncontour, hcontour⟩ :=
    exercise25_square_boundary_integrand_curve_integrable_eventually P Q hdeg
  obtain ⟨Nsides, hsides⟩ :=
    exercise25_square_boundary_integrand_sides_curve_integrable_eventually P Q hdeg
  obtain ⟨C, Ndecay, hCpos, hdecay⟩ := exercise25_square_boundary_integrand_decay P Q hdeg
  let N : ℕ := max Ncontour (max Nsides Ndecay)
  refine ⟨N, (fun n ↦ ?_), ?_⟩
  · let m : ℕ := n + (N - Ncontour)
    have hidx : m + Ncontour = n + N := by
      dsimp [m, N]
      omega
    -- Rewrite the eventual contour-integrability tail to the common square `γ_{n + N}`.
    rw [← hidx]
    exact hcontour m
  · have hbound :
        ∀ n : ℕ,
          ‖∫ᶜ z in exercise25SquareBoundary (n + N),
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z‖ ≤
            8 * C / exercise25SquareRadius (n + N) := by
      intro n
      let ms : ℕ := n + (N - Nsides)
      let md : ℕ := n + (N - Ndecay)
      have hidxs : ms + Nsides = n + N := by
        dsimp [ms, N]
        omega
      have hidxd : md + Ndecay = n + N := by
        dsimp [md, N]
        omega
      have hsidesN :
          let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
            exercise25SquareRadius (n + N) * Complex.I
          let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
            exercise25SquareRadius (n + N) * Complex.I
          let zw : ℂ := Complex.mk w.re z₀.im
          let wz : ℂ := Complex.mk z₀.re w.im
          CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
              (Path.segment z₀ zw) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
              (Path.segment zw w) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
              (Path.segment w wz) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
              (Path.segment wz z₀) := by
        -- The four side-integrability statements are the same after rewriting the index.
        rw [← hidxs]
        exact hsides ms
      have hdecayN :
          ∀ z ∈ Set.range (exercise25SquareBoundary (n + N)),
            ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤
              C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by
        intro z hz
        -- The coefficient bound is likewise the same after rewriting the index.
        rw [← hidxd] at hz ⊢
        exact hdecay md z hz
      exact exercise25_square_boundary_norm_curveIntegral_le (n := n + N) hsidesN hdecayN
    have htail :
        Tendsto (fun n : ℕ ↦ (8 * C) / exercise25SquareRadius (n + N)) atTop (𝓝 0) := by
      have hradius :
          Tendsto (fun n : ℕ ↦ exercise25SquareRadius (n + N)) atTop atTop := by
        -- The square radius is the linear function `n ↦ n + N + 1 / 2`.
        simpa [exercise25SquareRadius, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          (tendsto_atTop_add_const_right atTop ((N : ℝ) + (1 / 2 : ℝ))
            tendsto_natCast_atTop_atTop)
      have hinv :
          Tendsto (fun n : ℕ ↦ (exercise25SquareRadius (n + N))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hradius
      simpa [div_eq_mul_inv, mul_assoc] using
        (tendsto_const_nhds.mul hinv :
          Tendsto
            (fun n : ℕ ↦ (8 * C) * (exercise25SquareRadius (n + N))⁻¹)
            atTop (𝓝 ((8 * C) * 0)))
    -- Squeeze the contour integrals between their norm bound and the vanishing reciprocal tail.
    exact squeeze_zero_norm hbound htail

/-- Exercise 25 (6): for a rational function `P / Q` whose poles are exactly the nonintegral
points in the finite set `s`, and with `deg Q ≥ deg P + 2`, there is a tail of square contours
`γ_{n + N}` on which the one-form `((P / Q) π cot (π z)) dz` is genuinely curve-integrable, and
those contour integrals tend to `0`. -/
theorem exercise25_rational_contour_integral_tendsto_zero
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree)
    {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    ∃ N : ℕ,
      (∀ n : ℕ,
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz)
          (exercise25SquareBoundary (n + N))) ∧
      Tendsto
        (fun n : ℕ ↦
          ∫ᶜ z in exercise25SquareBoundary (n + N),
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z)
        atTop (𝓝 0) := by
  let _ := hpoles
  let _ := hnonint
  exact exercise25_rational_contour_integral_tendsto_zero_of_degree_gap_two_aux P Q hdeg

/-- Source-faithful residue data for Exercise 25: `residue z` is the contour residue of the
rational function `P / Q` at each listed nonintegral pole `z`, with the local residue circle chosen
away from the other listed poles. The summation formula below uses these ordinary residues under
the explicit simple-pole hypothesis. -/
def exercise25RationalResidueData
    (P Q : Polynomial ℂ) (s : Finset ℂ) (residue : ℂ → ℂ) : Prop :=
  ∀ z ∈ s,
    IsolatedLocalResidueCircle (Set.univ : Set ℂ) Set.univ s
      (fun w ↦ P.eval w / Q.eval w) z (residue z)

/-- Helper for Cartan section12 0038_Exercise_25: the oscillatory exponential factor on the square
contours has norm `exp (-α Im z)`, so only the imaginary coordinate matters in the bounds. -/
lemma exercise25_exp_phase_norm (alpha : ℝ) (z : ℂ) :
    ‖Complex.exp (Complex.I * (alpha : ℂ) * z)‖ = Real.exp (-alpha * z.im) := by
  -- Expand the real part of `I * (α z)` in coordinates and then apply `‖exp w‖ = exp (Re w)`.
  rcases z with ⟨x, y⟩
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, mul_comm, mul_left_comm]

/-- Helper for Cartan section12 0038_Exercise_25: once `u ≥ π / 2`, the quotient
`exp u / sinh u` is bounded by the same uniform horizontal-side constant used for the cotangent
kernel. -/
lemma exercise25_exp_div_sinh_le_uniform {u : ℝ} (hu : Real.pi / 2 ≤ u) :
    Real.exp u / Real.sinh u ≤ 2 / (1 - Real.exp (-Real.pi)) := by
  have hu_pos : 0 < u := by
    linarith [Real.pi_pos]
  have hsinh_pos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu_pos
  have hexp_lt_one : Real.exp (-Real.pi) < 1 := by
    simpa using (Real.exp_lt_exp.mpr (by linarith [Real.pi_pos] : -Real.pi < 0))
  have hcoef_nonneg : 0 ≤ 1 - Real.exp (-Real.pi) := sub_nonneg.mpr hexp_lt_one.le
  have hcoef_pos : 0 < 1 - Real.exp (-Real.pi) := sub_pos.mpr hexp_lt_one
  have hExpTail :
      Real.exp (-u) ≤ Real.exp (-Real.pi) * Real.exp u := by
    calc
      Real.exp (-u) ≤ Real.exp (u - Real.pi) := by
        exact Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-Real.pi) * Real.exp u := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
  have hsinh_lower :
      (1 - Real.exp (-Real.pi)) * Real.exp u ≤ 2 * Real.sinh u := by
    -- Rewrite `sinh` via exponentials and use the tail estimate `exp (-u) ≤ exp (-π) exp u`.
    rw [Real.sinh_eq]
    nlinarith
  -- Cross-multiplying through the positive denominators isolates the claimed uniform quotient
  -- bound.
  exact (div_le_div_iff₀ hsinh_pos hcoef_pos).2 <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsinh_lower

/-- Helper for Cartan section12 0038_Exercise_25: away from the integers, the cotangent kernel is
the explicit cosine-over-sine quotient `π cos (π z) / sin (π z)`. -/
lemma exercise25_piCot_eq_cos_div_sin (z : ℂ) :
    exercise25PiCot z =
      (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z) := by
  -- Expand `cot` into `cos / sin` and reassociate the scalar factor `π`.
  simp [exercise25PiCot, Complex.cot_eq_cos_div_sin, div_eq_mul_inv, mul_assoc]

/-- Helper for Cartan section12 0038_Exercise_25: if `z` is not an integer, then the denominator
`sin (π z)` of the cotangent kernel does not vanish at `z`. -/
lemma exercise25_sin_pi_ne_zero_of_not_integer {z : ℂ}
    (hz : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  -- Convert the vanishing of `sin (π z)` into the integer-zero description from Exercise 14.
  intro hsin
  rcases (sin_real_mul_eq_zero_iff Real.pi Real.pi_ne_zero z).1 hsin with ⟨p, hp⟩
  apply hz
  refine ⟨p, ?_⟩
  simpa [div_eq_mul_inv, Real.pi_ne_zero] using hp.symm

/-- Helper for Cartan section12 0038_Exercise_25: the cotangent kernel is holomorphic away from
the integer lattice. -/
lemma exercise25_piCot_differentiableAt_of_not_integer {z : ℂ}
    (hz : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    DifferentiableAt ℂ exercise25PiCot z := by
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    exercise25_sin_pi_ne_zero_of_not_integer hz
  have hnum :
      DifferentiableAt ℂ
        (fun w : ℂ ↦ (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * w)) z := by
    fun_prop
  have hden :
      DifferentiableAt ℂ (fun w : ℂ ↦ Complex.sin ((Real.pi : ℂ) * w)) z := by
    fun_prop
  have hrepr :
      exercise25PiCot =
        (fun w ↦
          (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * w) /
            Complex.sin ((Real.pi : ℂ) * w)) := by
    funext w
    exact exercise25_piCot_eq_cos_div_sin w
  -- Once the sine denominator is nonzero, the explicit quotient formula differentiates directly.
  rw [hrepr]
  exact hnum.div hden hsin

/-- Helper for Cartan section12 0038_Exercise_25: differentiability already gives continuity of
the cotangent kernel at every noninteger point. -/
lemma exercise25_piCot_continuousAt_of_not_integer {z : ℂ}
    (hz : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    ContinuousAt exercise25PiCot z :=
  (exercise25_piCot_differentiableAt_of_not_integer hz).continuousAt

/-- Helper for Cartan section12 0038_Exercise_25: at each simple noninteger pole, the source
circle-integral residue datum agrees with the meromorphic trailing coefficient of `P / Q`. -/
lemma exercise25_rational_trailingCoeff_eq_residue
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue)
    {z : ℂ} (hz : z ∈ s) :
    meromorphicTrailingCoeffAt (fun w ↦ P.eval w / Q.eval w) z = residue z := by
  -- Route correction: the plain quotient `P.eval / Q.eval` can have removable singularities at
  -- common roots of `P` and `Q`, so the bridge runs through the meromorphic normal form, which is
  -- holomorphic away from the actual pole finset `s`.
  let f : ℂ → ℂ := fun w ↦ P.eval w / Q.eval w
  let gNF : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  have hmeromorphic : MeromorphicOn f Set.univ := by
    simpa [f] using exercise25_rationalEval_meromorphicOn_univ P Q
  have hEqNF : gNF =ᶠ[𝓝[≠] z] f := by
    simpa [gNF, f] using hmeromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE (by simp : z ∈ Set.univ)
  have hholNF : DifferentiableOn ℂ gNF (↑s : Set ℂ)ᶜ := by
    simpa [gNF, f] using
      exercise25_rationalNormalForm_differentiableOn_compl_poleFinset P Q s hpoles
  have horderNF : meromorphicOrderAt gNF z = (-1 : WithTop ℤ) := by
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hmeromorphic (by simp)]
    simpa [f] using hsimple z hz
  have hmerNF : MeromorphicAt gNF z := by
    apply meromorphicAt_of_meromorphicOrderAt_ne_zero
    simpa [horderNF]
  -- Write the normal form in the canonical simple-pole shape `G(w) / (w - z)`.
  obtain ⟨G, hG_an, hG_ne, hG_eq⟩ := (meromorphicOrderAt_eq_int_iff hmerNF).1 horderNF
  have hcoeffNF : meromorphicTrailingCoeffAt gNF z = G z := by
    exact
      hG_an.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (f := gNF) (x := z) (n := (-1 : ℤ)) hG_ne hG_eq
  obtain ⟨ρG, hρG_pos, hG_ball⟩ := hG_an.exists_ball_analyticOnNhd
  have hEqNF' : ∀ᶠ w in 𝓝[≠] z, gNF w = f w := by
    simpa [Filter.EventuallyEq] using hEqNF
  have hG_eq' : ∀ᶠ w in 𝓝[≠] z, gNF w = (w - z) ^ (-1 : ℤ) • G w := by
    simpa [Filter.EventuallyEq] using hG_eq
  rw [eventually_nhdsWithin_iff] at hEqNF' hG_eq'
  rcases Metric.mem_nhds_iff.1 hEqNF' with ⟨δNF, hδNF_pos, hδNF⟩
  rcases Metric.mem_nhds_iff.1 hG_eq' with ⟨δG, hδG_pos, hδG⟩
  rcases hresidue z hz with ⟨R, hR, hRK, hRD, hsep, hdiffR, hcircleR⟩
  let r : ℝ := min (R / 2) (min (ρG / 2) (min (δNF / 2) (δG / 2)))
  have hr : 0 < r := by
    dsimp [r]
    refine lt_min (half_pos hR) ?_
    refine lt_min (half_pos hρG_pos) ?_
    exact lt_min (half_pos hδNF_pos) (half_pos hδG_pos)
  have hr_le_R : r ≤ R := by
    dsimp [r]
    calc
      r ≤ R / 2 := min_le_left _ _
      _ ≤ R := by linarith
  have hr_lt_ρG : r < ρG := by
    dsimp [r]
    calc
      r ≤ ρG / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
      _ < ρG := by linarith
  have hr_lt_δNF : r < δNF := by
    dsimp [r]
    calc
      r ≤ δNF / 2 := le_trans (min_le_right _ _) <|
          le_trans (min_le_right _ _) (min_le_left _ _)
      _ < δNF := by linarith
  have hr_lt_δG : r < δG := by
    dsimp [r]
    calc
      r ≤ δG / 2 := le_trans (min_le_right _ _) <|
          le_trans (min_le_right _ _) (min_le_right _ _)
      _ < δG := by linarith
  have hG_diff : DifferentiableOn ℂ G (Metric.closedBall z r) := by
    -- The analytic numerator `G` is holomorphic on a small ball around `z`, so it remains
    -- differentiable on the closed ball supporting the comparison circle.
    refine hG_ball.differentiableOn.mono ?_
    intro w hw
    exact Metric.mem_ball.2 (lt_of_le_of_lt hw hr_lt_ρG)
  have hcircleR_nf :
      ∮ w in C(z, R), gNF w = (2 * Real.pi * Complex.I : ℂ) * residue z := by
    have hEqCircle :
        (fun w ↦ gNF w) =ᶠ[Filter.codiscreteWithin (Metric.sphere z |R|)] f := by
      exact
        (toMeromorphicNFOn_eqOn_codiscrete (U := Set.univ) hmeromorphic).symm.filter_mono
          (Filter.codiscreteWithin_mono (by
            intro w hw
            simp))
    -- The source residue circle transfers unchanged to the meromorphic normal form on the same
    -- boundary because the two functions differ only on a codiscrete subset of that sphere.
    calc
      ∮ w in C(z, R), gNF w = ∮ w in C(z, R), f w := by
        exact circleIntegral.circleIntegral_congr_codiscreteWithin hEqCircle hR.ne'
      _ = (2 * Real.pi * Complex.I : ℂ) * residue z := hcircleR
  have hClosedAnnulusSubset :
      Metric.closedBall z R \ Metric.ball z r ⊆ (↑s : Set ℂ)ᶜ := by
    intro w hw hwS
    by_cases hwz : w = z
    · subst hwz
      exact hw.2 (Metric.mem_ball_self hr)
    · exact hsep w (by simpa using hwS) hwz hw.1
  have hOpenAnnulusSubset :
      Metric.ball z R \ Metric.closedBall z r ⊆ (↑s : Set ℂ)ᶜ := by
    intro w hw hwS
    by_cases hwz : w = z
    · subst hwz
      exact hw.2 (Metric.mem_closedBall_self hr.le)
    · exact hsep w (by simpa using hwS) hwz (Metric.ball_subset_closedBall hw.1)
  have hcontAnnulus :
      ContinuousOn gNF (Metric.closedBall z R \ Metric.ball z r) :=
    hholNF.continuousOn.mono hClosedAnnulusSubset
  have hdiffAnnulus :
      DifferentiableOn ℂ gNF (Metric.ball z R \ Metric.closedBall z r) :=
    hholNF.mono hOpenAnnulusSubset
  have hshrink :
      (∮ w in C(z, R), gNF w) = ∮ w in C(z, r), gNF w :=
    circleIntegral_eq_of_punctured_ball_shrink hr hr_le_R hcontAnnulus hdiffAnnulus
  have hkernelSphere :
      ∀ w ∈ Metric.sphere z r, gNF w = G w / (w - z) := by
    intro w hw
    have hw_norm : ‖w - z‖ = r := by
      simpa [Metric.mem_sphere] using hw
    have hw_ball_NF : w ∈ Metric.ball z δNF := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hw_norm.trans_lt hr_lt_δNF
    have hw_ball_G : w ∈ Metric.ball z δG := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hw_norm.trans_lt hr_lt_δG
    have hw_ne : w ≠ z := Metric.ne_of_mem_sphere hw hr.ne'
    have hGw : gNF w = (w - z) ^ (-1 : ℤ) • G w := by
      exact hδG hw_ball_G (by simpa using hw_ne)
    -- On the small circle, both the normal form and the raw quotient coincide with the same
    -- Cauchy kernel model.
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hGw
  have hcircleSmall :
      ∮ w in C(z, r), gNF w = (2 * Real.pi * Complex.I : ℂ) * G z := by
    have hcongr :
        (∮ w in C(z, r), gNF w) = ∮ w in C(z, r), G w / (w - z) := by
      -- Replace the inner-circle integrand by the explicit simple-pole kernel model.
      refine circleIntegral.integral_congr hr.le ?_
      intro w hw
      exact hkernelSphere w hw
    have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
    have hkernel :
        (∮ w in C(z, r), G w / (w - z)) = (2 * Real.pi * Complex.I : ℂ) * G z := by
      -- Cauchy's circle integral formula evaluates the kernel model at the center.
      simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        hG_diff.circleIntegral_sub_inv_smul hz_ball
    calc
      (∮ w in C(z, r), gNF w) = ∮ w in C(z, r), G w / (w - z) := hcongr
      _ = (2 * Real.pi * Complex.I : ℂ) * G z := hkernel
  have hResidue_eq_G : residue z = G z := by
    have hconst :
        (2 * Real.pi * Complex.I : ℂ) * residue z =
          (2 * Real.pi * Complex.I : ℂ) * G z := by
      calc
        (2 * Real.pi * Complex.I : ℂ) * residue z = ∮ w in C(z, R), gNF w := by
          simpa using hcircleR_nf.symm
        _ = ∮ w in C(z, r), gNF w := hshrink
        _ = (2 * Real.pi * Complex.I : ℂ) * G z := hcircleSmall
    have htwoPiI_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      refine mul_ne_zero ?_ ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    exact mul_left_cancel₀ htwoPiI_ne hconst
  -- Identify the trailing coefficient through the normal form, then replace the circle residue by
  -- the center value `G z` computed above.
  calc
    meromorphicTrailingCoeffAt f z = meromorphicTrailingCoeffAt gNF z := by
      simpa [f, gNF] using (meromorphicTrailingCoeffAt_congr_nhdsNE hEqNF).symm
    _ = G z := hcoeffNF
    _ = residue z := hResidue_eq_G.symm

/-- Helper for Cartan section12 0038_Exercise_25: the cotangent kernel is odd, so negating the
argument flips its sign. -/
lemma exercise25_piCot_neg (z : ℂ) :
    exercise25PiCot (-z) = -exercise25PiCot z := by
  -- Rewrite the cotangent kernel through `cos / sin` and use the parity of `cos` and `sin`.
  rw [exercise25_piCot_eq_cos_div_sin, exercise25_piCot_eq_cos_div_sin]
  simp [Complex.cos_neg, Complex.sin_neg, div_eq_mul_inv, mul_assoc]

/-- Helper for Cartan section12 0038_Exercise_25: dividing the odd cotangent kernel by `z`
produces an even function. -/
lemma exercise25_piCot_div_z_even (z : ℂ) :
    exercise25PiCot (-z) / (-z) = exercise25PiCot z / z := by
  -- The numerator and denominator both pick up the same sign under `z ↦ -z`.
  simpa [div_eq_mul_inv, exercise25_piCot_neg, mul_assoc]

/-- Helper for Cartan section12 0038_Exercise_25: the correction integral from the degree-gap-one
split vanishes because opposite sides of the square contour contribute opposite values to the even
integrand `π cot (π z) / z`. -/
lemma exercise25_piCotDivZ_squareCurveIntegrable (n : ℕ) :
    CurveIntegrable ((fun z ↦ exercise25PiCot z / z) dz) (exercise25SquareBoundary n) := by
  let φ : ℂ → ℂ := fun z ↦ exercise25PiCot z / z
  let r : ℝ := exercise25SquareRadius n
  let z₀ : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  let D : Set ℂ := Set.range (exercise25SquareBoundary n)
  have hcoeff : ContinuousOn φ D := by
    intro z hz
    have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
      exercise25_sin_pi_ne_zero_on_square_boundary n hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      subst hz0
      simpa using hsin
    have hz_notint : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)) := by
      intro hzint
      rcases hzint with ⟨p, rfl⟩
      exact hsin <| by simpa [mul_comm] using Complex.sin_int_mul_pi p
    -- The cotangent kernel and the extra divisor are both regular on the square boundary.
    have hcont : ContinuousAt φ z := by
      simpa [φ] using
        (exercise25_piCot_continuousAt_of_not_integer hz_notint).div continuousAt_id hz_ne
    exact hcont.continuousWithinAt
  have hform :
      ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z)) D := by
    -- Package the scalar coefficient as a continuous complex-linear one-form on the contour.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hcoeff)
  have hsubsets := exercise25_square_boundary_side_ranges_subset n
  dsimp [z₀, w, zw, wz] at hsubsets
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
      (fun t ↦ hbottom_subset ⟨t, rfl⟩)
  have hright_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
      (fun t ↦ hright_subset ⟨t, rfl⟩)
  have htop_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
      (fun t ↦ htop_subset ⟨t, rfl⟩)
  have hleft_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
      (fun t ↦ hleft_subset ⟨t, rfl⟩)
  have hboundary_eq :
      exercise25SquareBoundary n =
        (Path.segment z₀ zw).trans
          ((Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀))) := by
    rw [exercise25SquareBoundary, axisParallelRectangleBoundaryPath]
  -- The square boundary is the concatenation of its four affine sides, so side integrability
  -- yields whole-boundary integrability.
  rw [hboundary_eq]
  exact CurveIntegrable.trans hbottom_int
    (CurveIntegrable.trans hright_int (CurveIntegrable.trans htop_int hleft_int))

/-- Helper for Cartan section12 0038_Exercise_25: the correction integral from the degree-gap-one
split vanishes because opposite sides of the square contour contribute opposite values to the even
integrand `π cot (π z) / z`. -/
lemma exercise25_piCotDivZ_squareIntegral_eq_zero (n : ℕ) :
    ∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ exercise25PiCot z / z) dz) z = 0 := by
  let φ : ℂ → ℂ := fun z ↦ exercise25PiCot z / z
  let r : ℝ := exercise25SquareRadius n
  let z₀ : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  let D : Set ℂ := Set.range (exercise25SquareBoundary n)
  have hcoeff : ContinuousOn φ D := by
    intro z hz
    have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
      exercise25_sin_pi_ne_zero_on_square_boundary n hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      subst hz0
      simpa using hsin
    have hz_notint : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)) := by
      intro hzint
      rcases hzint with ⟨p, rfl⟩
      exact hsin <| by simpa [mul_comm] using Complex.sin_int_mul_pi p
    -- On the boundary, the cotangent factor and the extra divisor `z` are both regular.
    have hcont : ContinuousAt φ z := by
      simpa [φ] using
        (exercise25_piCot_continuousAt_of_not_integer hz_notint).div continuousAt_id hz_ne
    exact hcont.continuousWithinAt
  have hform :
      ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z)) D := by
    -- Package the scalar coefficient as a continuous complex-linear one-form on the contour.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hcoeff)
  have hsubsets := exercise25_square_boundary_side_ranges_subset n
  dsimp [z₀, w, zw, wz] at hsubsets
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
      (fun t ↦ hbottom_subset ⟨t, rfl⟩)
  have hright_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
      (fun t ↦ hright_subset ⟨t, rfl⟩)
  have htop_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
      (fun t ↦ htop_subset ⟨t, rfl⟩)
  have hleft_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
      (fun t ↦ hleft_subset ⟨t, rfl⟩)
  have htop_line :
      ∀ t : ℝ, AffineMap.lineMap w wz t = -AffineMap.lineMap z₀ zw t := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, z₀, w, zw, wz, r] <;> ring
  have hleft_line :
      ∀ t : ℝ, AffineMap.lineMap wz z₀ t = -AffineMap.lineMap zw w t := by
    intro t
    apply Complex.ext <;> simp [AffineMap.lineMap_apply, z₀, w, zw, wz, r] <;> ring
  have htop_diff : wz - w = -(zw - z₀) := by
    apply Complex.ext <;> simp [z₀, w, zw, wz, r]
  have hleft_diff : z₀ - wz = -(w - zw) := by
    apply Complex.ext <;> simp [z₀, w, zw, wz, r]
  have htop_eq :
      ∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z =
        -∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z := by
    rw [curveIntegral_segment, curveIntegral_segment]
    calc
      ∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap w wz t)) (wz - w) =
          ∫ t in (0 : ℝ)..1, -((((fun z ↦ φ z) dz) (AffineMap.lineMap z₀ zw t)) (zw - z₀)) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            simp only [Complex.scalarOneForm_apply, φ]
            rw [htop_line t, htop_diff, exercise25_piCot_div_z_even]
            ring
      _ = -∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap z₀ zw t)) (zw - z₀) := by
            rw [intervalIntegral.integral_neg]
  have hleft_eq :
      ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z =
        -∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z := by
    rw [curveIntegral_segment, curveIntegral_segment]
    calc
      ∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap wz z₀ t)) (z₀ - wz) =
          ∫ t in (0 : ℝ)..1, -((((fun z ↦ φ z) dz) (AffineMap.lineMap zw w t)) (w - zw)) := by
            refine intervalIntegral.integral_congr ?_
            intro t ht
            simp only [Complex.scalarOneForm_apply, φ]
            rw [hleft_line t, hleft_diff, exercise25_piCot_div_z_even]
            ring
      _ = -∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap zw w t)) (w - zw) := by
            rw [intervalIntegral.integral_neg]
  have hboundary_eq :
      exercise25SquareBoundary n =
        (Path.segment z₀ zw).trans
          ((Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀))) := by
    rw [exercise25SquareBoundary, axisParallelRectangleBoundaryPath]
  -- Expand the contour into its four affine sides and cancel the opposite pairs using evenness.
  rw [hboundary_eq]
  rw [curveIntegral_trans hbottom_int
    (CurveIntegrable.trans hright_int (CurveIntegrable.trans htop_int hleft_int))]
  rw [curveIntegral_trans hright_int (CurveIntegrable.trans htop_int hleft_int)]
  rw [curveIntegral_trans htop_int hleft_int]
  rw [htop_eq, hleft_eq]
  ring

/-- Helper for Cartan section12 0038_Exercise_25: an integer whose absolute value lies inside the
quarter-thickened square strip already belongs to the index interval attached to that square. -/
lemma exercise25_int_mem_Icc_of_abs_lt_squareRadius_add_quarter {m : ℕ} {p : ℤ}
    (hp : |(p : ℝ)| < exercise25SquareRadius m + 1 / 4) :
    p ∈ Finset.Icc (-((m : ℤ))) (m : ℤ) := by
  -- Normalize the radius bound to `|p| < m + 1`, then convert the strict real inequalities back
  -- to integer bounds.
  have hp' : |(p : ℝ)| < (m : ℝ) + 1 := by
    dsimp [exercise25SquareRadius] at hp
    linarith
  have hsplit := abs_lt.mp hp'
  have hlow1 : Int.negSucc m < p := by
    exact_mod_cast hsplit.1
  have hlow : -((m : ℤ)) ≤ p := by
    omega
  have hupp1 : p < (m : ℤ) + 1 := by
    exact_mod_cast hsplit.2
  have hupp : p ≤ (m : ℤ) := by
    omega
  exact Finset.mem_Icc.mpr ⟨hlow, hupp⟩

/-- Helper for Cartan section12 0038_Exercise_25: an integer point inside the quarter-thickened
square neighborhood is one of the lattice points already listed in the square residue finset. -/
lemma exercise25_intCast_mem_squareIndexSet {m : ℕ} {p : ℤ}
    (hp : |(p : ℝ)| < exercise25SquareRadius m + 1 / 4) :
    (p : ℂ) ∈
      (Finset.image (fun q : ℤ ↦ (q : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ)) : Set ℂ) := by
  -- Package the integer directly as a point of the image finset after checking the index bounds.
  show (p : ℂ) ∈ Finset.image (fun q : ℤ ↦ (q : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  exact Finset.mem_image.mpr ⟨p, exercise25_int_mem_Icc_of_abs_lt_squareRadius_add_quarter hp, rfl⟩

/-- Helper for Cartan section12 0038_Exercise_25: on the quarter-thickened neighborhood of the
`m`-th square, the cotangent kernel is holomorphic away from the integer lattice points enclosed by
that square. -/
lemma exercise25_piCot_differentiableAt_away_from_squareIntegers {m : ℕ} {z : ℂ}
    (hzD :
      |z.re| < exercise25SquareRadius m + 1 / 4 ∧
        |z.im| < exercise25SquareRadius m + 1 / 4)
    (hzI :
      z ∉
        (Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ)) : Set ℂ)) :
    DifferentiableAt ℂ exercise25PiCot z := by
  -- Any integer in this neighborhood would already lie in the listed square index set.
  apply exercise25_piCot_differentiableAt_of_not_integer
  intro hzInt
  rcases hzInt with ⟨p, rfl⟩
  apply hzI
  exact exercise25_intCast_mem_squareIndexSet (m := m) (by simpa using hzD.1)

/-- Helper for Cartan section12 0038_Exercise_25: on the quarter-thickened square neighborhood,
away from the mixed pole finset consisting of the noninteger poles of `P / Q` together with the
enclosed integers, the product integrand built from the meromorphic normal form of `P / Q` is
holomorphic. -/
lemma exercise25_squareNeighborhood_piCotProduct_differentiableOn
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (m : ℕ) :
    let D : Set ℂ :=
      {z : ℂ |
        |z.re| < exercise25SquareRadius m + 1 / 4 ∧
          |z.im| < exercise25SquareRadius m + 1 / 4}
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let integerSet : Finset ℂ :=
      Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    DifferentiableOn ℂ
      (fun w ↦ gNF w * exercise25PiCot w)
      (D \ (↑residueSet : Set ℂ)) := by
  -- Route correction: the square-neighborhood owner must be the normal form `gNF`; the remaining
  -- work is to restrict its holomorphy from `sᶜ` to the mixed residue complement.
  dsimp
  intro z hz
  have hz_not_s : z ∉ (↑s : Set ℂ) := by
    intro hzS
    exact hz.2 (show z ∈ (↑(s ∪ Finset.image (fun p : ℤ ↦ (p : ℂ))
      (Finset.Icc (-((m : ℤ))) (m : ℤ))) : Set ℂ) from Finset.mem_union.mpr (Or.inl hzS))
  have hz_not_int :
      z ∉
        (Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ)) : Set ℂ) := by
    intro hzI
    exact hz.2 (show z ∈ (↑(s ∪ Finset.image (fun p : ℤ ↦ (p : ℂ))
      (Finset.Icc (-((m : ℤ))) (m : ℤ))) : Set ℂ) from Finset.mem_union.mpr (Or.inr hzI))
  have hnf :
      DifferentiableWithinAt ℂ
        (toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ)
        ((↑s : Set ℂ)ᶜ) z :=
    exercise25_rationalNormalForm_differentiableOn_compl_poleFinset P Q s hpoles z hz_not_s
  have hnf' :
      DifferentiableWithinAt ℂ
        (toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ)
        ({w : ℂ |
          |w.re| < exercise25SquareRadius m + 1 / 4 ∧
            |w.im| < exercise25SquareRadius m + 1 / 4} \
          (↑(s ∪ Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))) :
            Set ℂ)) z := by
    refine hnf.mono ?_
    intro w hw
    exact fun hwS ↦ hw.2 (by simp [hwS])
  have hcot :
      DifferentiableAt ℂ exercise25PiCot z :=
    exercise25_piCot_differentiableAt_away_from_squareIntegers hz.1 hz_not_int
  exact hnf'.mul hcot.differentiableWithinAt

/-- Helper for Cartan section12 0038_Exercise_25: the mixed residue finset on the `m`-th square
splits as the disjoint union of the listed noninteger poles and the enclosed integer lattice
points, so the residue sum separates into the textbook integer sum plus the noninteger residue
sum. -/
lemma exercise25_squareResidueSet_sum_split
    (P Q : Polynomial ℂ) {s : Finset ℂ} (m : ℕ)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (residue : ℂ → ℂ) :
    let integerSet : Finset ℂ :=
      Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    let residueValue : ℂ → ℂ := fun z ↦
      if hz : z ∈ s then residue z * exercise25PiCot z
      else if hzInt : z ∈ integerSet then P.eval z / Q.eval z
      else 0
    Finset.sum residueSet residueValue =
      Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ)) (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)) +
        s.sum (fun z ↦ residue z * exercise25PiCot z) := by
  -- Split the mixed residue finset into the disjoint noninteger-pole part `s` and the enclosed
  -- integer image, then simplify the piecewise residue value on each summand.
  classical
  dsimp
  let integerSet : Finset ℂ :=
    Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueValue : ℂ → ℂ := fun z ↦
    if hz : z ∈ s then residue z * exercise25PiCot z
    else if hzInt : z ∈ integerSet then P.eval z / Q.eval z
    else 0
  have hdisj : Disjoint s integerSet := by
    rw [Finset.disjoint_left]
    intro z hzS hzI
    apply hnonint z hzS
    rcases Finset.mem_image.mp hzI with ⟨p, hp, rfl⟩
    exact ⟨p, rfl⟩
  have hs_sum :
      Finset.sum s residueValue = s.sum (fun z ↦ residue z * exercise25PiCot z) := by
    -- On `s`, the first branch of the piecewise residue value is the only surviving one.
    refine Finset.sum_congr rfl ?_
    intro z hz
    simp [residueValue, hz]
  have hi_sum :
      Finset.sum integerSet residueValue =
        Finset.sum integerSet (fun z ↦ P.eval z / Q.eval z) := by
    -- On the integer image, disjointness forces the `s`-branch off, so only the integer value
    -- remains.
    refine Finset.sum_congr rfl ?_
    intro z hz
    have hz_not_s : z ∉ s := by
      intro hzS
      exact (Finset.disjoint_left.mp hdisj) hzS hz
    have hz_int : z ∈ integerSet := hz
    simp [residueValue, hz_not_s, hz_int]
  have himage :
      Finset.sum integerSet (fun z ↦ P.eval z / Q.eval z) =
        Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ))
          (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)) := by
    -- Reindex the integer-image sum back to the original interval of integers.
    dsimp [integerSet]
    refine Finset.sum_image (f := fun z ↦ P.eval z / Q.eval z) (g := fun p : ℤ ↦ (p : ℂ))
      (s := Finset.Icc (-((m : ℤ))) (m : ℤ)) ?_
    intro a ha b hb hab
    exact Int.cast_injective hab
  calc
    Finset.sum (s ∪ integerSet) residueValue =
        Finset.sum s residueValue + Finset.sum integerSet residueValue := by
      simpa [integerSet] using Finset.sum_union hdisj
    _ = s.sum (fun z ↦ residue z * exercise25PiCot z) +
          Finset.sum integerSet (fun z ↦ P.eval z / Q.eval z) := by
      rw [hs_sum, hi_sum]
    _ = s.sum (fun z ↦ residue z * exercise25PiCot z) +
          Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ))
            (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)) := by
      rw [himage]
    _ = Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ))
          (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)) +
          s.sum (fun z ↦ residue z * exercise25PiCot z) := by
      ring

/-- Helper for Cartan section12 0038_Exercise_25: an explicit `G(w) / (w - z)` model on one
isolated closed ball already gives the exact `IsolatedLocalResidueCircle` payload required by the
oriented-boundary residue theorem. -/
lemma exercise25_isolatedLocalResidueCircle_of_circle_kernel_model_closedBall
    {K D : Set ℂ} {s : Finset ℂ} {φ G : ℂ → ℂ} {z c : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall z r ⊆ interior K)
    (hD : Metric.closedBall z r ⊆ D)
    (havoid : ∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z r)
    (hdiff : DifferentiableOn ℂ φ (Metric.ball z r \ ({z} : Set ℂ)))
    (hG : DifferentiableOn ℂ G (Metric.closedBall z r))
    (hGc : G z = c)
    (hφ : ∀ w ∈ Metric.sphere z r, φ w = G w / (w - z)) :
    IsolatedLocalResidueCircle K D s φ z c := by
  have hcongr :
      (∮ w in C(z, r), φ w) = ∮ w in C(z, r), G w / (w - z) := by
    -- Replace the boundary integrand by the explicit Cauchy-kernel model on the chosen circle.
    refine circleIntegral.integral_congr hr.le ?_
    intro w hw
    exact hφ w hw
  have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hkernel :
      (∮ w in C(z, r), G w / (w - z)) = (2 * Real.pi * Complex.I : ℂ) * G z := by
    -- Cauchy's circle formula computes the kernel integral once the numerator is holomorphic on
    -- the closed ball.
    simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hG.circleIntegral_sub_inv_smul hz_ball
  -- The kernel-model integral plus the already assembled isolation data give the residue circle.
  refine ⟨r, hr, hK, hD, havoid, hdiff, ?_⟩
  calc
    (∮ w in C(z, r), φ w) = ∮ w in C(z, r), G w / (w - z) := hcongr
    _ = (2 * Real.pi * Complex.I : ℂ) * G z := hkernel
    _ = (2 * Real.pi * Complex.I : ℂ) * c := by rw [hGc]

/-- Helper for Cartan section12 0038_Exercise_25: every point of a finite residue set admits a
positive closed-ball radius avoiding all other points of that finite set. -/
lemma exercise25_exists_separating_radius_closedBall
    {s : Finset ℂ} {z : ℂ} (hz : z ∈ s) :
    ∃ r > 0, ∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z r := by
  let t : Set ℂ := (↑s : Set ℂ) \ ({z} : Set ℂ)
  have htfinite : t.Finite := s.finite_toSet.subset (by
    intro w hw
    exact hw.1)
  have htclosed : IsClosed t := htfinite.isClosed
  have hz_not_closure_t : z ∉ closure t := by
    simp [t, htclosed.closure_eq]
  obtain ⟨ε, hε, hεlt⟩ := Metric.exists_real_pos_lt_infEDist_of_notMem_closure hz_not_closure_t
  refine ⟨ε, hε, ?_⟩
  intro w hw hwz hwball
  have hwt : w ∈ t := by
    refine ⟨by simpa using hw, ?_⟩
    simpa [Set.mem_singleton_iff] using hwz
  have hInf : Metric.infEDist z t ≤ edist z w := Metric.infEDist_le_edist_of_mem hwt
  have hedist : edist z w ≤ ENNReal.ofReal ε := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (by simpa [Metric.mem_closedBall, dist_comm] using hwball)
  exact (not_lt_of_ge hedist) (lt_of_lt_of_le hεlt hInf)

/-- Helper for Cartan section12 0038_Exercise_25: after shifting the square index far enough, every
point of the finite noninteger pole set lies strictly inside the square in both coordinates. -/
lemma exercise25_polesEventuallyInSquareInterior
    (s : Finset ℂ) :
    ∃ N : ℕ,
      ∀ n : ℕ, ∀ z ∈ s,
        |z.re| < exercise25SquareRadius (n + N) ∧
          |z.im| < exercise25SquareRadius (n + N) := by
  -- Dominate both coordinates by the norm of `z`, then choose one eventual square radius larger
  -- than the finite sum of those norms.
  classical
  let B : ℝ := ∑ w ∈ s, ‖w‖
  let N : ℕ := Nat.ceil B
  refine ⟨N, ?_⟩
  intro n z hz
  have hnorm_le_B : ‖z‖ ≤ B := by
    simpa [B] using
      (Finset.single_le_sum (f := fun w : ℂ ↦ ‖w‖) (fun w _ ↦ norm_nonneg _) hz :
        ‖z‖ ≤ ∑ w ∈ s, ‖w‖)
  have hB_le_N : B ≤ N := Nat.le_ceil B
  have hN_lt_radius : (N : ℝ) < exercise25SquareRadius (n + N) := by
    have hN_le_nat : N ≤ n + N := Nat.le_add_left N n
    have hN_le_real : (N : ℝ) ≤ (n + N : ℕ) := by
      exact_mod_cast hN_le_nat
    dsimp [exercise25SquareRadius]
    linarith
  have hnorm_lt_radius : ‖z‖ < exercise25SquareRadius (n + N) :=
    lt_of_le_of_lt (hnorm_le_B.trans hB_le_N) hN_lt_radius
  constructor
  · exact lt_of_le_of_lt (Complex.abs_re_le_norm z) hnorm_lt_radius
  · exact lt_of_le_of_lt (Complex.abs_im_le_norm z) hnorm_lt_radius

/-- Helper for Cartan section12 0038_Exercise_25: the square `K` with radius
`exercise25SquareRadius m` sits inside the quarter-thickened neighborhood `D` used for the local
holomorphy arguments. -/
lemma exercise25_squareRectangle_subset_thickenedNeighborhood (m : ℕ) :
    Complex.Rectangle
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I) ⊆
      {z : ℂ |
        |z.re| < exercise25SquareRadius m + 1 / 4 ∧
          |z.im| < exercise25SquareRadius m + 1 / 4} := by
  intro z hz
  have hr_nonneg : 0 ≤ exercise25SquareRadius m := by
    dsimp [exercise25SquareRadius]
    positivity
  rw [Complex.Rectangle, Complex.mem_reProdIm] at hz
  rcases hz with ⟨hzre, hzim⟩
  have hzre_bounds : -(exercise25SquareRadius m) ≤ z.re ∧ z.re ≤ exercise25SquareRadius m := by
    simpa [Set.uIcc, hr_nonneg] using hzre
  have hzim_bounds : -(exercise25SquareRadius m) ≤ z.im ∧ z.im ≤ exercise25SquareRadius m := by
    simpa [Set.uIcc, hr_nonneg] using hzim
  have hzre_abs : |z.re| ≤ exercise25SquareRadius m := abs_le.2 hzre_bounds
  have hzim_abs : |z.im| ≤ exercise25SquareRadius m := abs_le.2 hzim_bounds
  constructor
  · exact lt_of_le_of_lt hzre_abs (by linarith)
  · exact lt_of_le_of_lt hzim_abs (by linarith)

/-- Helper for Cartan section12 0038_Exercise_25: multiplying a local simple-pole kernel model by
an analytic factor preserves the same `G(w) / (w - z)` shape, with the center value multiplied by
that regular factor. -/
lemma exercise25_closedBallSimplePoleMulRegularFactor
    {z c : ℂ} {r : ℝ} {φ G ψ : ℂ → ℂ}
    (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (Metric.closedBall z r))
    (hGc : G z = c)
    (hφ : ∀ w ∈ Metric.sphere z r, φ w = G w / (w - z))
    (hψ : DifferentiableOn ℂ ψ (Metric.closedBall z r)) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (Metric.closedBall z r) ∧
        H z = c * ψ z ∧
          ∀ w ∈ Metric.sphere z r, φ w * ψ w = H w / (w - z) := by
  refine ⟨fun w ↦ G w * ψ w, ?_, ?_, ?_⟩
  · intro w hw
    -- The new numerator is a product of the old analytic numerator and the regular factor.
    exact (hG w hw).mul (hψ w hw)
  · -- At the pole center, only the numerator value changes, by multiplication with the regular
    -- factor.
    simp [hGc]
  · intro w hw
    have hw_ne : w ≠ z := Metric.ne_of_mem_sphere hw hr.ne'
    -- Rewrite the pole term by factoring the analytic multiplier into the numerator.
    calc
      φ w * ψ w = (G w / (w - z)) * ψ w := by rw [hφ w hw]
      _ = (G w * ψ w) / (w - z) := by
        field_simp [sub_ne_zero.mpr hw_ne]

/-- Helper for Cartan section12 0038_Exercise_25: at a noninteger pole of `P / Q` inside the
square, the mixed integrand built from the meromorphic normal form of `P / Q` admits an explicit
local kernel model on a closed ball adapted to the square residue set. -/
lemma exercise25_nonintegerPiCotProduct_circleKernelModelOnSquare
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue)
    {m : ℕ} {K D : Set ℂ}
    (hK :
      K = Complex.Rectangle
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I))
    (hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4})
    {z : ℂ} (hz : z ∈ s) (hzK : z ∈ interior K) :
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let integerSet : Finset ℂ :=
      Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    ∃ r > 0, ∃ G : ℂ → ℂ,
      Metric.closedBall z r ⊆ interior K ∧
        Metric.closedBall z r ⊆ D ∧
          (∀ w ∈ residueSet, w ≠ z → w ∉ Metric.closedBall z r) ∧
            DifferentiableOn ℂ
              (fun w ↦ gNF w * exercise25PiCot w)
              (Metric.ball z r \ ({z} : Set ℂ)) ∧
              DifferentiableOn ℂ G (Metric.closedBall z r) ∧
                G z = residue z * exercise25PiCot z ∧
                  (∀ w ∈ Metric.sphere z r,
                    gNF w * exercise25PiCot w = G w / (w - z)) := by
  -- Route correction: first build the simple-pole `gNF = H / (w - z)` model on a small closed
  -- ball, then multiply it by the regular cotangent factor.
  dsimp
  let f : ℂ → ℂ := fun w ↦ P.eval w / Q.eval w
  let gNF : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  let integerSet : Finset ℂ :=
    Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  have hzResidue : z ∈ residueSet := Finset.mem_union.mpr <| Or.inl hz
  have hmeromorphic : MeromorphicOn f Set.univ := by
    simpa [f] using exercise25_rationalEval_meromorphicOn_univ P Q
  have hEqNF : gNF =ᶠ[𝓝[≠] z] f := by
    simpa [f, gNF] using
      hmeromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE (by simp : z ∈ Set.univ)
  have horderNF : meromorphicOrderAt gNF z = (-1 : WithTop ℤ) := by
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hmeromorphic (by simp)]
    simpa [f] using hsimple z hz
  have hmerNF : MeromorphicAt gNF z := by
    exact meromorphicAt_of_meromorphicOrderAt_ne_zero (by simpa [horderNF])
  obtain ⟨H, hH_an, hH_ne, hH_eq⟩ := (meromorphicOrderAt_eq_int_iff hmerNF).1 horderNF
  have hH_coeff : meromorphicTrailingCoeffAt gNF z = H z := by
    exact
      hH_an.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (f := gNF) (x := z) (n := (-1 : ℤ)) hH_ne hH_eq
  have hHz : H z = residue z := by
    calc
      H z = meromorphicTrailingCoeffAt gNF z := hH_coeff.symm
      _ = meromorphicTrailingCoeffAt f z := by
        simpa [f, gNF] using meromorphicTrailingCoeffAt_congr_nhdsNE hEqNF
      _ = residue z := exercise25_rational_trailingCoeff_eq_residue
        P Q hpoles hsimple residue hresidue hz
  obtain ⟨ρK, hρK_pos, hρK_ball⟩ :=
    Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hzK)
  obtain ⟨ρsep, hρsep_pos, hsepρ⟩ :=
    exercise25_exists_separating_radius_closedBall (s := residueSet) hzResidue
  obtain ⟨ρH, hρH_pos, hH_ball⟩ := hH_an.exists_ball_analyticOnNhd
  have hH_eq' : ∀ᶠ w in 𝓝[≠] z, gNF w = (w - z) ^ (-1 : ℤ) • H w := by
    simpa [Filter.EventuallyEq] using hH_eq
  rw [eventually_nhdsWithin_iff] at hH_eq'
  rcases Metric.mem_nhds_iff.1 hH_eq' with ⟨δH, hδH_pos, hδH⟩
  let r : ℝ := min (ρK / 2) (min (ρsep / 2) (min (ρH / 2) (δH / 2)))
  have hr : 0 < r := by
    dsimp [r]
    refine lt_min (half_pos hρK_pos) ?_
    refine lt_min (half_pos hρsep_pos) ?_
    exact lt_min (half_pos hρH_pos) (half_pos hδH_pos)
  have hr_lt_K : r < ρK := by
    dsimp [r]
    have : r ≤ ρK / 2 := min_le_left _ _
    linarith
  have hr_le_sep : r ≤ ρsep / 2 := by
    dsimp [r]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_lt_H : r < ρH := by
    dsimp [r]
    have : r ≤ ρH / 2 := le_trans (min_le_right _ _) <|
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hr_lt_δH : r < δH := by
    dsimp [r]
    have : r ≤ δH / 2 := le_trans (min_le_right _ _) <|
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hclosedK : Metric.closedBall z r ⊆ interior K := by
    exact (Metric.closedBall_subset_ball hr_lt_K).trans hρK_ball
  have hKD :
      K ⊆
        {w : ℂ |
          |w.re| < exercise25SquareRadius m + 1 / 4 ∧
            |w.im| < exercise25SquareRadius m + 1 / 4} := by
    rw [hK]
    exact exercise25_squareRectangle_subset_thickenedNeighborhood m
  have hclosedD : Metric.closedBall z r ⊆ D := by
    intro w hw
    have hwD' :
        w ∈
          {w : ℂ |
            |w.re| < exercise25SquareRadius m + 1 / 4 ∧
              |w.im| < exercise25SquareRadius m + 1 / 4} :=
      hKD (interior_subset (hclosedK hw))
    simpa [hD] using hwD'
  have havoid :
      ∀ w ∈ residueSet, w ≠ z → w ∉ Metric.closedBall z r := by
    intro w hw hwz hwball
    exact hsepρ w hw hwz <|
      Metric.closedBall_subset_closedBall (by linarith : r ≤ ρsep) hwball
  have hH_diff : DifferentiableOn ℂ H (Metric.closedBall z r) := by
    -- The analytic numerator for the normal-form principal part stays holomorphic after the ball
    -- is shrunk below its analytic radius.
    refine hH_ball.differentiableOn.mono ?_
    intro w hw
    exact Metric.mem_ball.2 (lt_of_le_of_lt hw hr_lt_H)
  have hkernelNF :
      ∀ w ∈ Metric.sphere z r, gNF w = H w / (w - z) := by
    intro w hw
    have hw_norm : ‖w - z‖ = r := by
      simpa [Metric.mem_sphere] using hw
    have hw_ball : w ∈ Metric.ball z δH := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hw_norm.trans_lt hr_lt_δH
    have hw_ne : w ≠ z := Metric.ne_of_mem_sphere hw hr.ne'
    have hHw : gNF w = (w - z) ^ (-1 : ℤ) • H w := by
      exact hδH hw_ball (by simpa using hw_ne)
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hHw
  have hprodDiffGlobal :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25PiCot w)
        (D \ (↑residueSet : Set ℂ)) := by
    simpa [hD, gNF, integerSet, residueSet] using
      exercise25_squareNeighborhood_piCotProduct_differentiableOn P Q hpoles m
  have hprodDiff :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25PiCot w)
        (Metric.ball z r \ ({z} : Set ℂ)) := by
    exact
      differentiableOn_punctured_ball_of_finite_support_separation
        hclosedD havoid hprodDiffGlobal
  have hPiCotDiff : DifferentiableOn ℂ exercise25PiCot (Metric.closedBall z r) := by
    intro w hw
    have hwD :
        |w.re| < exercise25SquareRadius m + 1 / 4 ∧
          |w.im| < exercise25SquareRadius m + 1 / 4 := by
      simpa [hD] using hclosedD hw
    have hw_not_int : w ∉ (integerSet : Set ℂ) := by
      intro hwInt
      by_cases hwz : w = z
      · have hzInt : z ∈ (integerSet : Set ℂ) := by simpa [hwz] using hwInt
        apply hnonint z hz
        rcases Finset.mem_image.mp hzInt with ⟨p, hp, rfl⟩
        exact ⟨p, rfl⟩
      · exact havoid w (Finset.mem_union.mpr <| Or.inr hwInt) hwz hw
    exact
      (exercise25_piCot_differentiableAt_away_from_squareIntegers
        (m := m) hwD hw_not_int).differentiableWithinAt
  obtain ⟨G, hG_diff, hG_center, hkernel⟩ :=
    exercise25_closedBallSimplePoleMulRegularFactor
      (z := z) (c := residue z) (r := r) (φ := gNF) (G := H) (ψ := exercise25PiCot)
      hr hH_diff hHz hkernelNF hPiCotDiff
  refine ⟨r, hr, G, hclosedK, hclosedD, havoid, hprodDiff, hG_diff, hG_center, ?_⟩
  intro w hw
  exact hkernel w hw

/-- Helper for Cartan section12 0038_Exercise_25: at an integer pole of `π cot (π w)` inside the
square, the mixed integrand built from the meromorphic normal form of `P / Q` admits an explicit
local kernel model on a closed ball adapted to the square residue set. -/
lemma exercise25_normalForm_eq_rationalEval_at_regularInteger
    (P Q : Polynomial ℂ) {p : ℤ} (hQp : Q.eval (p : ℂ) ≠ 0) :
    toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ (p : ℂ) =
      P.eval (p : ℂ) / Q.eval (p : ℂ) := by
  let f : ℂ → ℂ := fun w ↦ P.eval w / Q.eval w
  have hmeromorphic : MeromorphicOn f Set.univ := by
    simpa [f] using exercise25_rationalEval_meromorphicOn_univ P Q
  have hrat : AnalyticAt ℂ f (p : ℂ) := by
    -- Away from the denominator roots, the literal quotient is already holomorphic.
    have hPanalytic : AnalyticAt ℂ (fun w : ℂ ↦ P.eval w) (p : ℂ) := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) P (p : ℂ) (by simp))
    have hQanalytic : AnalyticAt ℂ (fun w : ℂ ↦ Q.eval w) (p : ℂ) := by
      simpa [Polynomial.coe_aeval_eq_eval] using
        (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (A := ℂ) Q (p : ℂ) (by simp))
    simpa [f] using hPanalytic.div hQanalytic hQp
  -- The global normal form agrees pointwise with the honest quotient at every regular integer.
  calc
    toMeromorphicNFOn f Set.univ (p : ℂ) = toMeromorphicNFAt f (p : ℂ) (p : ℂ) := by
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hmeromorphic (by simp)]
    _ = f (p : ℂ) := by
      exact congrFun (toMeromorphicNFAt_eq_self.2 hrat.meromorphicNFAt) (p : ℂ)

/-- Helper for Cartan section12 0038_Exercise_25: around each integer enclosed by the `m`-th
square, the cotangent kernel itself admits a `H(w) / (w - p)` model on a separated closed ball,
with center value `H(p) = 1`. -/
lemma exercise25_integerPiCot_circleKernelModelOnSeparatedBall
    {s : Finset ℂ} {m : ℕ} {K D : Set ℂ}
    (hK :
      K = Complex.Rectangle
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I))
    (hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4})
    {p : ℤ} (hp : p ∈ Finset.Icc (-((m : ℤ))) (m : ℤ)) :
    let integerSet : Finset ℂ :=
      Finset.image (fun q : ℤ ↦ (q : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    ∃ r > 0, r ≤ (1 / 4 : ℝ) ∧ ∃ H : ℂ → ℂ,
      Metric.closedBall (p : ℂ) r ⊆ interior K ∧
        Metric.closedBall (p : ℂ) r ⊆ D ∧
          (∀ w ∈ residueSet, w ≠ (p : ℂ) → w ∉ Metric.closedBall (p : ℂ) r) ∧
            DifferentiableOn ℂ H (Metric.closedBall (p : ℂ) r) ∧
              H (p : ℂ) = 1 ∧
                (∀ w ∈ Metric.sphere (p : ℂ) r,
                  exercise25PiCot w = H w / (w - (p : ℂ))) := by
  -- Route correction: isolate the pure `π cot (π z)` simple-pole model first, before multiplying
  -- it by the regular rational normal form.
  dsimp
  let integerSet : Finset ℂ :=
    Finset.image (fun q : ℤ ↦ (q : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  have hpResidue : (p : ℂ) ∈ residueSet := by
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have horder : meromorphicOrderAt exercise25PiCot (p : ℂ) = (-1 : WithTop ℤ) := by
    simpa using exercise25_piCot_simple_pole_at_integer p
  have hmer : MeromorphicAt exercise25PiCot (p : ℂ) := by
    exact meromorphicAt_of_meromorphicOrderAt_ne_zero (by simpa [horder])
  obtain ⟨H, hH_an, hH_ne, hH_eq⟩ := (meromorphicOrderAt_eq_int_iff hmer).1 horder
  have hH_coeff : meromorphicTrailingCoeffAt exercise25PiCot (p : ℂ) = H (p : ℂ) := by
    exact
      hH_an.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (f := exercise25PiCot) (x := (p : ℂ)) (n := (-1 : ℤ)) hH_ne hH_eq
  have hHp : H (p : ℂ) = 1 := by
    calc
      H (p : ℂ) = meromorphicTrailingCoeffAt exercise25PiCot (p : ℂ) := hH_coeff.symm
      _ = 1 := exercise25_piCot_meromorphicTrailingCoeffAt_integer p
  obtain ⟨ρsep, hρsep_pos, hsepρ⟩ :=
    exercise25_exists_separating_radius_closedBall (s := residueSet) hpResidue
  obtain ⟨ρH, hρH_pos, hH_ball⟩ := hH_an.exists_ball_analyticOnNhd
  have hH_eq' :
      ∀ᶠ w in 𝓝[≠] (p : ℂ), exercise25PiCot w = (w - (p : ℂ)) ^ (-1 : ℤ) • H w := by
    simpa [Filter.EventuallyEq] using hH_eq
  rw [eventually_nhdsWithin_iff] at hH_eq'
  rcases Metric.mem_nhds_iff.1 hH_eq' with ⟨δH, hδH_pos, hδH⟩
  let r : ℝ := min (1 / 4 : ℝ) (min (ρsep / 2) (min (ρH / 2) (δH / 2)))
  have hr : 0 < r := by
    dsimp [r]
    refine lt_min (by positivity) ?_
    refine lt_min (half_pos hρsep_pos) ?_
    exact lt_min (half_pos hρH_pos) (half_pos hδH_pos)
  have hr_le_quarter : r ≤ (1 / 4 : ℝ) := by
    dsimp [r]
    exact min_le_left _ _
  have hr_lt_H : r < ρH := by
    dsimp [r]
    have : r ≤ ρH / 2 := by
      exact le_trans (min_le_right _ _) <| le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hr_lt_δH : r < δH := by
    dsimp [r]
    have : r ≤ δH / 2 := by
      exact le_trans (min_le_right _ _) <| le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hp_abs_le : |(p : ℝ)| ≤ m := by
    rcases Finset.mem_Icc.mp hp with ⟨hpL, hpU⟩
    have hpL' : -((m : ℤ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpL
    have hpU' : (p : ℝ) ≤ m := by exact_mod_cast hpU
    exact abs_le.2 ⟨by simpa using hpL', by simpa using hpU'⟩
  have hclosedK : Metric.closedBall (p : ℂ) r ⊆ interior K := by
    intro w hw
    have hw_norm : ‖w - (p : ℂ)‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hwre_center : |w.re - (p : ℝ)| ≤ r := by
      calc
        |w.re - (p : ℝ)| = |(w - (p : ℂ)).re| := by simp
        _ ≤ ‖w - (p : ℂ)‖ := Complex.abs_re_le_norm _
        _ ≤ r := hw_norm
    have hwim : |w.im| ≤ r := by
      calc
        |w.im| = |(w - (p : ℂ)).im| := by simp
        _ ≤ ‖w - (p : ℂ)‖ := Complex.abs_im_le_norm _
        _ ≤ r := hw_norm
    have hwre : |w.re| < exercise25SquareRadius m := by
      have hwre_le : |w.re| ≤ |w.re - (p : ℝ)| + |(p : ℝ)| := by
        calc
          |w.re| = |(w.re - (p : ℝ)) + (p : ℝ)| := by ring_nf
          _ ≤ |w.re - (p : ℝ)| + |(p : ℝ)| := by
              simpa [Real.norm_eq_abs] using norm_add_le (w.re - (p : ℝ)) (p : ℝ)
      dsimp [exercise25SquareRadius]
      linarith
    have hwim_lt : |w.im| < exercise25SquareRadius m := by
      dsimp [exercise25SquareRadius]
      linarith
    have hr_nonneg : 0 ≤ exercise25SquareRadius m := by
      dsimp [exercise25SquareRadius]
      positivity
    rw [hK, Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
    simpa [Set.uIcc_of_le (by linarith : -(exercise25SquareRadius m) ≤ exercise25SquareRadius m),
      interior_Icc] using
      (show w.re ∈ Set.Ioo (-(exercise25SquareRadius m)) (exercise25SquareRadius m) ∧
          w.im ∈ Set.Ioo (-(exercise25SquareRadius m)) (exercise25SquareRadius m) from by
        exact ⟨abs_lt.mp hwre, abs_lt.mp hwim_lt⟩)
  have hclosedD : Metric.closedBall (p : ℂ) r ⊆ D := by
    intro w hw
    have hw_norm : ‖w - (p : ℂ)‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hwre_center : |w.re - (p : ℝ)| ≤ r := by
      calc
        |w.re - (p : ℝ)| = |(w - (p : ℂ)).re| := by simp
        _ ≤ ‖w - (p : ℂ)‖ := Complex.abs_re_le_norm _
        _ ≤ r := hw_norm
    have hwim : |w.im| ≤ r := by
      calc
        |w.im| = |(w - (p : ℂ)).im| := by simp
        _ ≤ ‖w - (p : ℂ)‖ := Complex.abs_im_le_norm _
        _ ≤ r := hw_norm
    have hwre : |w.re| < exercise25SquareRadius m + (1 / 4 : ℝ) := by
      have hwre_le : |w.re| ≤ |w.re - (p : ℝ)| + |(p : ℝ)| := by
        calc
          |w.re| = |(w.re - (p : ℝ)) + (p : ℝ)| := by ring_nf
          _ ≤ |w.re - (p : ℝ)| + |(p : ℝ)| := by
              simpa [Real.norm_eq_abs] using norm_add_le (w.re - (p : ℝ)) (p : ℝ)
      dsimp [exercise25SquareRadius]
      linarith
    have hwim_lt : |w.im| < exercise25SquareRadius m + (1 / 4 : ℝ) := by
      dsimp [exercise25SquareRadius]
      linarith
    rw [hD]
    exact ⟨hwre, hwim_lt⟩
  have havoid :
      ∀ w ∈ residueSet, w ≠ (p : ℂ) → w ∉ Metric.closedBall (p : ℂ) r := by
    intro w hw hwp hwball
    exact hsepρ w hw hwp <|
      Metric.closedBall_subset_closedBall (by
        have : r ≤ ρsep / 2 := by
          dsimp [r]
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        linarith) hwball
  have hH_diff : DifferentiableOn ℂ H (Metric.closedBall (p : ℂ) r) := by
    -- Shrinking below the analytic radius keeps the numerator holomorphic on the comparison ball.
    refine hH_ball.differentiableOn.mono ?_
    intro w hw
    exact Metric.mem_ball.2 (lt_of_le_of_lt hw hr_lt_H)
  refine ⟨r, hr, hr_le_quarter, H, hclosedK, hclosedD, havoid, hH_diff, hHp, ?_⟩
  intro w hw
  have hw_norm : ‖w - (p : ℂ)‖ = r := by
    simpa [Metric.mem_sphere] using hw
  have hw_ball : w ∈ Metric.ball (p : ℂ) δH := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hw_norm.trans_lt hr_lt_δH
  have hw_ne : w ≠ (p : ℂ) := Metric.ne_of_mem_sphere hw hr.ne'
  have hHw : exercise25PiCot w = (w - (p : ℂ)) ^ (-1 : ℤ) • H w := by
    exact hδH hw_ball (by simpa using hw_ne)
  -- On the sphere, the cotangent kernel is exactly the Cauchy kernel determined by `H`.
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hHw

/-- Helper for Cartan section12 0038_Exercise_25: at an integer pole of `π cot (π w)` inside the
square, the mixed integrand built from the meromorphic normal form of `P / Q` admits an explicit
local kernel model on a closed ball adapted to the square residue set. -/
lemma exercise25_integerPiCotProduct_circleKernelModelOnSquare
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun q : ℤ ↦ (q : ℂ)))
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    {m : ℕ} {K D : Set ℂ}
    (hK :
      K = Complex.Rectangle
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I))
    (hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4})
    {p : ℤ} (hp : p ∈ Finset.Icc (-((m : ℤ))) (m : ℤ)) :
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let integerSet : Finset ℂ :=
      Finset.image (fun q : ℤ ↦ (q : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    ∃ r > 0, ∃ G : ℂ → ℂ,
      Metric.closedBall (p : ℂ) r ⊆ interior K ∧
        Metric.closedBall (p : ℂ) r ⊆ D ∧
          (∀ w ∈ residueSet, w ≠ (p : ℂ) → w ∉ Metric.closedBall (p : ℂ) r) ∧
            DifferentiableOn ℂ
              (fun w ↦ gNF w * exercise25PiCot w)
              (Metric.ball (p : ℂ) r \ ({(p : ℂ)} : Set ℂ)) ∧
              DifferentiableOn ℂ G (Metric.closedBall (p : ℂ) r) ∧
                G (p : ℂ) = P.eval (p : ℂ) / Q.eval (p : ℂ) ∧
                  (∀ w ∈ Metric.sphere (p : ℂ) r,
                    gNF w * exercise25PiCot w = G w / (w - (p : ℂ))) := by
  -- Route correction: first isolate the pure cotangent simple-pole model at `p`, then multiply it
  -- by the regular rational normal form on the same separated closed ball.
  dsimp
  let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
  let integerSet : Finset ℂ :=
    Finset.image (fun q : ℤ ↦ (q : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  have hpInt : (p : ℂ) ∈ integerSet := by
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hp_not_s : (p : ℂ) ∉ s := by
    intro hpS
    exact hnonint (p : ℂ) hpS ⟨p, rfl⟩
  obtain ⟨r, hr, _, H, hclosedK, hclosedD, havoid, hH_diff, hHp, hkernelPiCot⟩ :=
    exercise25_integerPiCot_circleKernelModelOnSeparatedBall
      (s := s) (m := m) (K := K) (D := D) hK hD hp
  have hholNF : DifferentiableOn ℂ gNF (↑s : Set ℂ)ᶜ := by
    simpa [gNF] using
      exercise25_rationalNormalForm_differentiableOn_compl_poleFinset P Q s hpoles
  have hclosedNoS : Metric.closedBall (p : ℂ) r ⊆ (↑s : Set ℂ)ᶜ := by
    intro w hw hwS
    by_cases hwp : w = (p : ℂ)
    · subst hwp
      exact hp_not_s hwS
    · exact havoid w (Finset.mem_union.mpr <| Or.inl hwS) hwp hw
  have hgNF_diff : DifferentiableOn ℂ gNF (Metric.closedBall (p : ℂ) r) := by
    -- The rational normal form is holomorphic on the whole comparison ball because that ball
    -- avoids the actual pole set `s`.
    exact hholNF.mono hclosedNoS
  have hprodDiffGlobal :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25PiCot w)
        (D \ (↑residueSet : Set ℂ)) := by
    simpa [hD, gNF, integerSet, residueSet] using
      exercise25_squareNeighborhood_piCotProduct_differentiableOn P Q hpoles m
  have hprodDiff :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25PiCot w)
        (Metric.ball (p : ℂ) r \ ({(p : ℂ)} : Set ℂ)) := by
    exact
      differentiableOn_punctured_ball_of_finite_support_separation
        hclosedD havoid hprodDiffGlobal
  obtain ⟨G, hG_diff, hG_center_raw, hkernel⟩ :=
    exercise25_closedBallSimplePoleMulRegularFactor
      (z := (p : ℂ)) (c := (1 : ℂ)) (r := r) (φ := exercise25PiCot) (G := H) (ψ := gNF)
      hr hH_diff hHp hkernelPiCot hgNF_diff
  have hG_center : G (p : ℂ) = P.eval (p : ℂ) / Q.eval (p : ℂ) := by
    calc
      G (p : ℂ) = (1 : ℂ) * gNF (p : ℂ) := hG_center_raw
      _ = gNF (p : ℂ) := by simp
      _ = P.eval (p : ℂ) / Q.eval (p : ℂ) :=
        exercise25_normalForm_eq_rationalEval_at_regularInteger P Q (p := p) (hdenom_int p)
  refine ⟨r, hr, G, hclosedK, hclosedD, havoid, hprodDiff, hG_diff, hG_center, ?_⟩
  intro w hw
  -- The multiplier helper produces the same kernel model up to the commutativity of multiplication.
  simpa [mul_comm] using hkernel w hw

/-- Helper for Cartan section12 0038_Exercise_25: once the two local kernel models are available,
the mixed residue data on the square residue finset are obtained by a direct case split between the
noninteger poles of `P / Q` and the integer poles of `π cot (π z)`. -/
lemma exercise25_squarePiCotProduct_isolatedResidueData
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue)
    {m : ℕ} {K D : Set ℂ}
    (hK :
      K = Complex.Rectangle
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I))
    (hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4})
    (hsK : (↑s : Set ℂ) ⊆ interior K) :
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let integerSet : Finset ℂ :=
      Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    let residueValue : ℂ → ℂ := fun z ↦
      if hz : z ∈ s then residue z * exercise25PiCot z
      else if hzInt : z ∈ integerSet then P.eval z / Q.eval z
      else 0
    ∀ z ∈ residueSet,
      IsolatedLocalResidueCircle K D residueSet
        (fun w ↦ gNF w * exercise25PiCot w) z (residueValue z) := by
  -- Dispatch between the noninteger poles of `P / Q` and the integer poles of the cotangent
  -- kernel, then feed the corresponding local kernel model into the generic residue-circle wrapper.
  let integerSet : Finset ℂ :=
    Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  let residueValue : ℂ → ℂ := fun z ↦
    if hz : z ∈ s then residue z * exercise25PiCot z
    else if hzInt : z ∈ integerSet then P.eval z / Q.eval z
    else 0
  dsimp [integerSet, residueSet, residueValue]
  intro z hz
  by_cases hzS : z ∈ s
  · have hzK : z ∈ interior K := hsK hzS
    obtain ⟨r, hr, G, hclosedK, hclosedD, havoid, hdiff, hG_diff, hG_center, hkernel⟩ :=
      exercise25_nonintegerPiCotProduct_circleKernelModelOnSquare
        P Q hpoles hnonint hsimple residue hresidue hK hD hzS hzK
    refine
      exercise25_isolatedLocalResidueCircle_of_circle_kernel_model_closedBall
        hr hclosedK hclosedD havoid hdiff hG_diff ?_ hkernel
    -- On the noninteger branch, the residue value is exactly the prescribed `residue z * π cot(π z)`.
    simpa [hzS] using hG_center
  · have hzInt : z ∈ integerSet := (Finset.mem_union.mp hz).resolve_left hzS
    rcases Finset.mem_image.mp hzInt with ⟨p, hp, rfl⟩
    obtain ⟨r, hr, G, hclosedK, hclosedD, havoid, hdiff, hG_diff, hG_center, hkernel⟩ :=
      exercise25_integerPiCotProduct_circleKernelModelOnSquare
        P Q hpoles hnonint hdenom_int hK hD hp
    have hp_not_s : (p : ℂ) ∉ s := by
      intro hpS
      exact hnonint (p : ℂ) hpS ⟨p, rfl⟩
    refine
      exercise25_isolatedLocalResidueCircle_of_circle_kernel_model_closedBall
        hr hclosedK hclosedD havoid hdiff hG_diff ?_ hkernel
    -- On the integer branch, only the quotient value survives in the piecewise residue function.
    calc
      G (p : ℂ) = P.eval (p : ℂ) / Q.eval (p : ℂ) := hG_center
      _ =
        (if hz : (p : ℂ) ∈ s then residue (p : ℂ) * exercise25PiCot (p : ℂ)
          else if hzInt : (p : ℂ) ∈ integerSet then P.eval (p : ℂ) / Q.eval (p : ℂ) else 0) := by
            simp [hp_not_s, hzInt]

/-- Helper for Cartan section12 0038_Exercise_25: the singleton closed-path family attached to the
square contour carries the same boundary integral as the raw square path, and the meromorphic
normal form may be used on that boundary because it agrees codiscretely with the rational owner on
`Set.univ`. -/
lemma exercise25_squareBoundary_normalForm_boundaryTransfer
    (P Q : Polynomial ℂ) (m : ℕ) (κ : ℂ → ℂ) :
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let Γ : Unit → ClosedPath ℂ := fun _ ↦ (exercise25SquareBoundary m).toClosedPath
    (∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun z ↦ gNF z * κ z) dz) z) =
      ∫ᶜ z in exercise25SquareBoundary m, ((fun z ↦ P.eval z / Q.eval z * κ z) dz) z := by
  let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (exercise25SquareBoundary m).toClosedPath
  let z₀ : ℂ := -(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I
  let w : ℂ := (exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I
  have hmeromorphic :
      MeromorphicOn (fun w : ℂ ↦ P.eval w / Q.eval w) Set.univ :=
    exercise25_rationalEval_meromorphicOn_univ P Q
  have hr_pos : 0 < exercise25SquareRadius m := by
    dsimp [exercise25SquareRadius]
    positivity
  have hRe : z₀.re < w.re := by
    -- The square has positive half-side length, so the left vertex lies strictly to the left of
    -- the right vertex.
    have hz₀re : z₀.re = -exercise25SquareRadius m := by
      simp [z₀]
    have hwre : w.re = exercise25SquareRadius m := by
      simp [w]
    rw [hz₀re, hwre]
    linarith
  have hIm : z₀.im < w.im := by
    -- The same positivity gives the strict inequality between the lower and upper vertices.
    have hz₀im : z₀.im = -exercise25SquareRadius m := by
      simp [z₀]
    have hwim : w.im = exercise25SquareRadius m := by
      simp [w]
    rw [hz₀im, hwim]
    linarith
  have hΓ :
      IsOrientedBoundaryOf (Complex.Rectangle z₀ w) Γ := by
    -- Package the explicit square contour as the singleton oriented-boundary family required by
    -- the residue theorem API.
    simpa [Γ, z₀, w, exercise25SquareBoundary] using
      axisParallelRectangleBoundary_isOrientedBoundaryOf z₀ w hRe hIm
  have hEqNF :
      gNF =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] (fun w ↦ P.eval w / Q.eval w) := by
    simpa [gNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (U := Set.univ) hmeromorphic).symm
  have hEqProd :
      (fun z ↦ gNF z * κ z) =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)]
        (fun z ↦ P.eval z / Q.eval z * κ z) := by
    -- Multiply the codiscrete owner equality by the fixed kernel `κ`.
    filter_upwards [hEqNF] with z hz
    simp [hz]
  have hclosed_transfer :
      ∫ᶜ z in ((exercise25SquareBoundary m).toClosedPath.toPath), ((fun z ↦ gNF z * κ z) dz) z =
        ∫ᶜ z in ((exercise25SquareBoundary m).toClosedPath.toPath),
          ((fun z ↦ P.eval z / Q.eval z * κ z) dz) z := by
    -- Replace the normal-form owner by the raw rational owner on the singleton boundary family.
    simpa [Γ] using
      (curveIntegral_eq_of_codiscrete_boundary_component
        (K := Complex.Rectangle z₀ w) (U := Set.univ) (Γ := Γ) hΓ ()
        (φ := fun z ↦ gNF z * κ z)
        (ψ := fun z ↦ P.eval z / Q.eval z * κ z)
        hEqProd
        (by
          intro z hz
          simp))
  calc
    ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun z ↦ gNF z * κ z) dz) z =
        ∫ᶜ z in ((exercise25SquareBoundary m).toClosedPath.toPath),
          ((fun z ↦ gNF z * κ z) dz) z := by
      -- Collapse the singleton boundary family back to the unique square loop.
      simp [Γ]
    _ =
        ∫ᶜ z in ((exercise25SquareBoundary m).toClosedPath.toPath),
          ((fun z ↦ P.eval z / Q.eval z * κ z) dz) z := hclosed_transfer
    _ = ∫ᶜ z in exercise25SquareBoundary m, ((fun z ↦ P.eval z / Q.eval z * κ z) dz) z := by
      -- Unpack the closed-path wrapper back to the original square contour.
      rw [loop_toClosedPath_toPath_eq_cast (γ := exercise25SquareBoundary m)]
      simp [curveIntegral_cast]

/-- Helper for Cartan section12 0038_Exercise_25: on a sufficiently large square boundary, the
residue theorem for `(P / Q)(z) π cot (π z)` splits into the integer residues inside the square and
the prescribed noninteger pole residues coming from `s`. -/
lemma exercise25_squareBoundary_piCot_product_curveIntegral_eq_two_pi_I_mul_sum
    (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue) :
    ∃ N : ℕ,
    ∀ n : ℕ,
        ∫ᶜ z in exercise25SquareBoundary (n + N),
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z =
          (2 * Real.pi * Complex.I : ℂ) *
            (Finset.sum
                (Finset.Icc (-(((n + N : ℕ) : ℤ))) (((n + N : ℕ) : ℤ)))
                (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)) +
              s.sum (fun z ↦ residue z * exercise25PiCot z)) := by
  -- Route correction: theorem (7) should run the residue theorem on the normal-form owner
  -- `gNF * exercise25PiCot` and then transfer the outer square-boundary integral back to the raw
  -- quotient by codiscrete equality.
  obtain ⟨N, hinside⟩ := exercise25_polesEventuallyInSquareInterior s
  refine ⟨N, ?_⟩
  intro n
  let m : ℕ := n + N
  let K : Set ℂ :=
    Complex.Rectangle
      (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
      ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I)
  let D : Set ℂ :=
    {z : ℂ |
      |z.re| < exercise25SquareRadius m + 1 / 4 ∧
        |z.im| < exercise25SquareRadius m + 1 / 4}
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (exercise25SquareBoundary m).toClosedPath
  let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
  let integerSet : Finset ℂ :=
    Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  let residueValue : ℂ → ℂ := fun z ↦
    if hz : z ∈ s then residue z * exercise25PiCot z
    else if hzInt : z ∈ integerSet then P.eval z / Q.eval z
    else 0
  have hK :
      K =
        Complex.Rectangle
          (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
          ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I) := rfl
  have hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4} := rfl
  have hΓ :
      IsOrientedBoundaryOf K Γ := by
    have hr_pos : 0 < exercise25SquareRadius m := by
      dsimp [exercise25SquareRadius]
      positivity
    have hRe :
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I).re <
          ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I).re := by
      -- The left endpoint of the square lies strictly to the left of the right endpoint.
      simp
      linarith
    have hIm :
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I).im <
          ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I).im := by
      -- Likewise, the lower endpoint lies strictly below the upper endpoint.
      simp
      linarith
    simpa [K, Γ, exercise25SquareBoundary] using
      axisParallelRectangleBoundary_isOrientedBoundaryOf
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I)
        hRe hIm
  have hKD : K ⊆ D := by
    -- The closed square is contained in the quarter-thickened open neighborhood used for the
    -- holomorphy owner.
    simpa [K, D] using exercise25_squareRectangle_subset_thickenedNeighborhood m
  have hDopen : IsOpen D := by
    -- Both coordinate inequalities are open conditions.
    refine
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hsK : (↑s : Set ℂ) ⊆ interior K := by
    intro z hz
    have hzBounds : |z.re| < exercise25SquareRadius m ∧ |z.im| < exercise25SquareRadius m :=
      hinside n z hz
    rw [hK, Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
    simpa
      [Set.uIcc_of_le (by
        dsimp [exercise25SquareRadius]
        linarith : -(exercise25SquareRadius m) ≤ exercise25SquareRadius m), interior_Icc] using
      (show z.re ∈ Set.Ioo (-(exercise25SquareRadius m)) (exercise25SquareRadius m) ∧
          z.im ∈ Set.Ioo (-(exercise25SquareRadius m)) (exercise25SquareRadius m) from
        ⟨abs_lt.mp hzBounds.1, abs_lt.mp hzBounds.2⟩)
  have hhol :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25PiCot w)
        (D \ (↑residueSet : Set ℂ)) := by
    -- The mixed integrand is holomorphic on the thickened square away from the noninteger poles
    -- and the enclosed integers.
    simpa [D, gNF, integerSet, residueSet, m] using
      exercise25_squareNeighborhood_piCotProduct_differentiableOn P Q hpoles m
  have hres :
      ∀ z ∈ residueSet,
        IsolatedLocalResidueCircle K D residueSet
          (fun w ↦ gNF w * exercise25PiCot w) z (residueValue z) := by
    -- The local residue circles were already packaged on the square by separating the noninteger
    -- poles of `P / Q` from the integer poles of `π cot (π z)`.
    simpa [K, D, gNF, integerSet, residueSet, residueValue, m] using
      exercise25_squarePiCotProduct_isolatedResidueData
        P Q hpoles hnonint hsimple hdenom_int residue hresidue hK hD hsK
  have hboundary_nf :
      ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ gNF w * exercise25PiCot w) dz) z =
        (2 * Real.pi * Complex.I : ℂ) * Finset.sum residueSet residueValue := by
    -- Apply the residue theorem to the singleton square boundary family on the normal-form owner.
    have hboundary_disjoint :
        ∀ i : Unit, Disjoint (Set.range (Γ i).toPath) (↑residueSet : Set ℂ) := by
      intro i
      refine Set.disjoint_left.mpr ?_
      intro z hzΓ hzRes
      rcases Finset.mem_union.mp hzRes with hzS | hzInt
      · have hzInterior : z ∈ interior K := hsK hzS
        exact
          (mem_interior_iff_notMem_frontier (interior_subset hzInterior)).1 hzInterior
            (hΓ.range_toPath_subset_frontier i hzΓ)
      · rcases Finset.mem_image.mp hzInt with ⟨p, hp, rfl⟩
        exact
          exercise25_sin_pi_ne_zero_on_square_boundary m (by simpa [Γ] using hzΓ) <| by
            simpa [mul_comm] using Complex.sin_int_mul_pi p
    exact
      orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
        (Γ := Γ) (K := K) (D := D)
        (f := fun w ↦ gNF w * exercise25PiCot w)
        (s := residueSet) (residue := residueValue)
        hΓ hKD hDopen hboundary_disjoint hhol hres
  have hsum_split :
      Finset.sum residueSet residueValue =
        Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ))
          (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)) +
          s.sum (fun z ↦ residue z * exercise25PiCot z) := by
    -- The mixed residue sum separates into the enclosed integer values and the prescribed
    -- noninteger residues.
    simpa [integerSet, residueSet, residueValue, m] using
      exercise25_squareResidueSet_sum_split P Q (s := s) m hnonint residue
  calc
    ∫ᶜ z in exercise25SquareBoundary m, ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z =
        ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ gNF w * exercise25PiCot w) dz) z := by
      -- Transfer the normal-form boundary integral back to the raw square contour once.
      simpa [m] using
        (exercise25_squareBoundary_normalForm_boundaryTransfer P Q m exercise25PiCot).symm
    _ = (2 * Real.pi * Complex.I : ℂ) * Finset.sum residueSet residueValue := hboundary_nf
    _ =
        (2 * Real.pi * Complex.I : ℂ) *
          (Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ))
              (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)) +
            s.sum (fun z ↦ residue z * exercise25PiCot z)) := by
      rw [hsum_split]
    _ =
        (2 * Real.pi * Complex.I : ℂ) *
          (Finset.sum (Finset.Icc (-(((n + N : ℕ) : ℤ))) (((n + N : ℕ) : ℤ)))
              (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)) +
            s.sum (fun z ↦ residue z * exercise25PiCot z)) := by
      simp [m]

/-- Exercise 25 (7): under the same hypotheses as in part (6), the symmetric sums of the values of
`P / Q` at the integers converge to minus the sum of the nonintegral residues weighted by
`π cot (π z)`. -/
theorem exercise25_rational_integer_sum_tendsto
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue) :
    Tendsto
      (fun n : ℕ ↦
        Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)))
      atTop
      (𝓝 (-s.sum fun z ↦ residue z * exercise25PiCot z)) := by
  -- Combine the repaired square-boundary residue identity with the already proved vanishing of the
  -- contour integral tail, then divide by `2 π i`.
  obtain ⟨Nres, hresEq⟩ :=
    exercise25_squareBoundary_piCot_product_curveIntegral_eq_two_pi_I_mul_sum
      P Q hpoles hnonint hsimple hdenom_int residue hresidue
  obtain ⟨Ntail, _, htail₀⟩ :=
    exercise25_rational_contour_integral_tendsto_zero P Q hdeg hpoles hnonint
  let N : ℕ := max Nres Ntail
  let integralSeq : ℕ → ℂ := fun n ↦
    ∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z
  let sumSeq : ℕ → ℂ := fun n ↦
    Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ))
  let residueSum : ℂ := s.sum (fun z ↦ residue z * exercise25PiCot z)
  have htail :
      Tendsto (fun n : ℕ ↦ integralSeq (n + N)) atTop (𝓝 0) := by
    -- Reindex the vanishing contour tail to the common shift `N`.
    have hshift :
        Tendsto (fun n : ℕ ↦ integralSeq ((n + (N - Ntail)) + Ntail)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat (N - Ntail)).2 htail₀
    refine Tendsto.congr' ?_ hshift
    refine Filter.Eventually.of_forall ?_
    intro n
    have hidx : (n + (N - Ntail)) + Ntail = n + N := by
      dsimp [N]
      omega
    simp [integralSeq, hidx]
  have hshifted :
      Tendsto (fun n : ℕ ↦ sumSeq (n + N)) atTop (𝓝 (-residueSum)) := by
    let scaledIntegral : ℕ → ℂ := fun n ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N)
    have hformula :
        ∀ n : ℕ, sumSeq (n + N) = scaledIntegral n - residueSum := by
      intro n
      have hEq : integralSeq (n + N) =
          (2 * Real.pi * Complex.I : ℂ) * (sumSeq (n + N) + residueSum) := by
        have hshift :
            integralSeq ((n + (N - Nres)) + Nres) =
              (2 * Real.pi * Complex.I : ℂ) *
                (sumSeq ((n + (N - Nres)) + Nres) + residueSum) := by
          simpa [integralSeq, sumSeq, residueSum] using hresEq (n + (N - Nres))
        have hidx : (n + (N - Nres)) + Nres = n + N := by
          dsimp [N]
          omega
        simpa [integralSeq, sumSeq, residueSum, hidx] using hshift
      have hscaled :
          scaledIntegral n = sumSeq (n + N) + residueSum := by
        -- Multiply back by `2πi` so the inverse scalar disappears, then cancel the nonzero
        -- factor using the contour identity.
        apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
        dsimp [scaledIntegral]
        field_simp [Complex.two_pi_I_ne_zero]
        simpa [mul_assoc] using hEq
      -- Subtract the constant residue contribution from both sides.
      have hsub := congrArg (fun z : ℂ ↦ z - residueSum) hscaled
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, scaledIntegral] using hsub.symm
    have hscaled :
        Tendsto (fun n : ℕ ↦ scaledIntegral n) atTop (𝓝 0) := by
      change Tendsto (fun n : ℕ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N))
        atTop (𝓝 0)
      simpa [mul_zero] using
        (tendsto_const_nhds.mul htail :
          Tendsto (fun n : ℕ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N))
            atTop (𝓝 (((2 * Real.pi * Complex.I : ℂ)⁻¹) * 0)))
    have hshiftedScaled :
        Tendsto (fun n : ℕ ↦ scaledIntegral n - residueSum) atTop (𝓝 (-residueSum)) := by
      simpa [sub_eq_add_neg] using hscaled.sub tendsto_const_nhds
    -- Replace the shifted sums by the scaled contour expression minus the constant residue sum.
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hformula n).symm) hshiftedScaled
  -- Dropping a finite initial shift does not change the limit of the symmetric sums.
  have hshifted' :
      Tendsto (fun n : ℕ ↦ sumSeq (n + N)) atTop (𝓝 (-residueSum)) := hshifted
  exact (tendsto_add_atTop_iff_nat N).1 hshifted'

/-- Helper for Cartan section12 0038_Exercise_25: passing a loop through `toClosedPath.toPath`
does not change its curve integral. -/
lemma exercise25_curveIntegral_loop_toClosedPath_toPath
    {x : ℂ} (ω : ℂ → ℂ →L[ℂ] ℂ) (γ : Path x x) :
    ∫ᶜ z in γ.toClosedPath.toPath, ω z = ∫ᶜ z in γ, ω z := by
  -- Transport along the endpoint equalities introduced by `toClosedPath`, then erase the cast.
  rw [loop_toClosedPath_toPath_eq_cast (γ := γ)]
  simp [curveIntegral_cast]

/-- Helper for Cartan section12 0038_Exercise_25: in the exact-gap-one case, the rational
function `P / Q` splits into a gap-two remainder over `X * Q` plus the elementary term `c / z`,
and the identity is only used where both denominators are regular. -/
lemma exercise25_degreeGapOneSplitAtInfinity
    (P Q : Polynomial ℂ) (hdeg : P.natDegree < Q.natDegree)
    (hgap1 : ¬ P.natDegree + 2 ≤ Q.natDegree) :
    ∃ c : ℂ, ∃ R : Polynomial ℂ,
      R.natDegree + 2 ≤ (Polynomial.X * Q).natDegree ∧
      ∀ z : ℂ, z ≠ 0 → Q.eval z ≠ 0 →
        P.eval z / Q.eval z =
          R.eval z / ((Polynomial.X * Q).eval z) + c / z := by
  by_cases hP : P = 0
  · refine ⟨0, 0, ?_, ?_⟩
    · have hQ : Q ≠ 0 := exercise25_denominator_ne_zero_of_degree_lt P Q hdeg
      have hQlc : Q.leadingCoeff ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.1 hQ
      have hXQdeg : (Polynomial.X * Q).natDegree = Q.natDegree + 1 := by
        have hmul :
            Polynomial.leadingCoeff (Polynomial.X : Polynomial ℂ) * Q.leadingCoeff ≠ 0 := by
          simpa [Polynomial.leadingCoeff_X] using hQlc
        simpa [Polynomial.natDegree_X, Nat.add_comm] using
          (Polynomial.natDegree_mul' (p := (Polynomial.X : Polynomial ℂ)) (q := Q) hmul)
      subst hP
      rw [Polynomial.natDegree_zero, hXQdeg]
      have hQpos : 1 ≤ Q.natDegree := Nat.succ_le_of_lt hdeg
      omega
    · intro z hz hQz
      simp [hP, hz, hQz]
  · have hQ : Q ≠ 0 := exercise25_denominator_ne_zero_of_degree_lt P Q hdeg
    have hdegEq : P.natDegree + 1 = Q.natDegree := by
      omega
    let c : ℂ := P.leadingCoeff / Q.leadingCoeff
    let R : Polynomial ℂ := Polynomial.X * P - Polynomial.C c * Q
    have hPlc : P.leadingCoeff ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.1 hP
    have hQlc : Q.leadingCoeff ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.1 hQ
    have hc : c ≠ 0 := by
      dsimp [c]
      exact div_ne_zero hPlc hQlc
    have hXP_ne : Polynomial.X * P ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hP
    have hCQ_ne : Polynomial.C c * Q ≠ 0 := by
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hQ
    have hXP_deg_nat : (Polynomial.X * P).natDegree = Q.natDegree := by
      have hmul :
          Polynomial.leadingCoeff (Polynomial.X : Polynomial ℂ) * P.leadingCoeff ≠ 0 := by
        simpa [Polynomial.leadingCoeff_X] using hPlc
      calc
        (Polynomial.X * P).natDegree = 1 + P.natDegree := by
          simpa [Polynomial.natDegree_X] using
            (Polynomial.natDegree_mul' (p := (Polynomial.X : Polynomial ℂ)) (q := P) hmul)
        _ = Q.natDegree := by
          omega
    have hCQ_deg_nat : (Polynomial.C c * Q).natDegree = Q.natDegree := by
      simpa [c] using (Polynomial.natDegree_C_mul (p := Q) hc)
    have hXP_deg : (Polynomial.X * P).degree = Q.degree := by
      rw [Polynomial.degree_eq_natDegree hXP_ne, Polynomial.degree_eq_natDegree hQ]
      exact_mod_cast hXP_deg_nat
    have hCQ_deg : (Polynomial.C c * Q).degree = Q.degree := by
      rw [Polynomial.degree_eq_natDegree hCQ_ne, Polynomial.degree_eq_natDegree hQ]
      exact_mod_cast hCQ_deg_nat
    have hXP_lc :
        (Polynomial.X * P).leadingCoeff = P.leadingCoeff := by
      have hmul :
          Polynomial.leadingCoeff (Polynomial.X : Polynomial ℂ) * P.leadingCoeff ≠ 0 := by
        simpa [Polynomial.leadingCoeff_X] using hPlc
      simpa [Polynomial.leadingCoeff_X] using
        (Polynomial.leadingCoeff_mul' (p := (Polynomial.X : Polynomial ℂ)) (q := P) hmul)
    have hCQ_lc :
        (Polynomial.C c * Q).leadingCoeff = c * Q.leadingCoeff := by
      have hmul :
          Polynomial.leadingCoeff (Polynomial.C c : Polynomial ℂ) * Q.leadingCoeff ≠ 0 := by
        simp [hc, hQlc]
      simpa [hc] using
        (Polynomial.leadingCoeff_mul' (p := Polynomial.C c) (q := Q) hmul)
    have hlead :
        (Polynomial.X * P).leadingCoeff = (Polynomial.C c * Q).leadingCoeff := by
      calc
        (Polynomial.X * P).leadingCoeff = P.leadingCoeff := hXP_lc
        _ = c * Q.leadingCoeff := by
          dsimp [c]
          symm
          exact div_mul_cancel₀ _ hQlc
        _ = (Polynomial.C c * Q).leadingCoeff := hCQ_lc.symm
    have hR_deg_lt :
        R.degree < Q.degree := by
      have hsub :
          R.degree < (Polynomial.X * P).degree := by
        simpa [R] using
          (Polynomial.degree_sub_lt (p := Polynomial.X * P) (q := Polynomial.C c * Q)
            (hXP_deg.trans hCQ_deg.symm) hXP_ne hlead)
      simpa [hXP_deg] using hsub
    have hR_nat_lt : R.natDegree < Q.natDegree := by
      by_cases hR : R = 0
      · rw [hR, Polynomial.natDegree_zero]
        have hQpos : 0 < Q.natDegree := by
          omega
        exact hQpos
      · exact Polynomial.natDegree_lt_natDegree hR hR_deg_lt
    have hXQ_deg : (Polynomial.X * Q).natDegree = Q.natDegree + 1 := by
      have hmul :
          Polynomial.leadingCoeff (Polynomial.X : Polynomial ℂ) * Q.leadingCoeff ≠ 0 := by
        simpa [Polynomial.leadingCoeff_X] using hQlc
      simpa [Polynomial.natDegree_X, Nat.add_comm] using
        (Polynomial.natDegree_mul' (p := (Polynomial.X : Polynomial ℂ)) (q := Q) hmul)
    refine ⟨c, R, ?_, ?_⟩
    · rw [hXQ_deg]
      omega
    · intro z hz hQz
      have hsplit :
          P.eval z / Q.eval z =
            (z * P.eval z - c * Q.eval z) / (z * Q.eval z) + c / z := by
        field_simp [hz, hQz]
        ring
      -- Evaluate the polynomial split on the regular locus and simplify the common denominator.
      simpa [R, c, add_mul, Polynomial.eval_sub, Polynomial.eval_mul, mul_assoc, mul_left_comm,
        mul_comm] using hsplit

/-- Helper for Cartan section12 0038_Exercise_25: when `deg P < deg Q`, the square-boundary
integrals of `(P / Q) π cot (π z)` still tend to zero. In the exact-gap-one case, only the contour
tail is replaced by the split-at-infinity argument; the residue identity is left untouched. -/
lemma exercise25_rational_piCot_contour_tendsto_zero_of_degree_lt
    (P Q : Polynomial ℂ) (hdeg : P.natDegree < Q.natDegree)
    {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    ∃ N : ℕ,
      Tendsto
        (fun n : ℕ ↦
          ∫ᶜ z in exercise25SquareBoundary (n + N),
            ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z)
        atTop (𝓝 0) := by
  by_cases hgap2 : P.natDegree + 2 ≤ Q.natDegree
  · obtain ⟨N, _, htail⟩ :=
      exercise25_rational_contour_integral_tendsto_zero P Q hgap2 hpoles hnonint
    exact ⟨N, htail⟩
  · obtain ⟨c, R, hRdeg, hsplit⟩ :=
      exercise25_degreeGapOneSplitAtInfinity P Q hdeg hgap2
    obtain ⟨Nrem, hcontRem, htailRem⟩ :=
      exercise25_rational_contour_integral_tendsto_zero_of_degree_gap_two_aux
        R (Polynomial.X * Q) hRdeg
    let originalSeq : ℕ → ℂ := fun n ↦
      ∫ᶜ z in exercise25SquareBoundary (n + Nrem),
        ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z
    let remainderSeq : ℕ → ℂ := fun n ↦
      ∫ᶜ z in exercise25SquareBoundary (n + Nrem),
        ((fun z ↦ R.eval z / (z * Q.eval z) * exercise25PiCot z) dz) z
    let correctionSeq : ℕ → ℂ := fun n ↦
      ∫ᶜ z in exercise25SquareBoundary (n + Nrem),
        ((fun z ↦ exercise25PiCot z / z) dz) z
    have hcontRem' :
        ∀ n : ℕ,
          CurveIntegrable
            ((fun z ↦ R.eval z / (z * Q.eval z) * exercise25PiCot z) dz)
            (exercise25SquareBoundary (n + Nrem)) := by
      intro n
      simpa [Polynomial.eval_mul, mul_assoc, mul_left_comm, mul_comm] using hcontRem n
    have htailRem' :
        Tendsto (fun n : ℕ ↦ remainderSeq n) atTop (𝓝 0) := by
      simpa [remainderSeq, Polynomial.eval_mul, mul_assoc, mul_left_comm, mul_comm] using htailRem
    have hformula :
        ∀ n : ℕ, originalSeq n = remainderSeq n + c * correctionSeq n := by
      intro n
      let m : ℕ := n + Nrem
      let z₀ : ℂ := -(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I
      let w : ℂ := (exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I
      let Γ : Unit → ClosedPath ℂ := fun _ ↦ (exercise25SquareBoundary m).toClosedPath
      let splitIntegrand : ℂ → ℂ := fun z ↦
        R.eval z / (z * Q.eval z) * exercise25PiCot z +
          c * (exercise25PiCot z / z)
      have hRe : z₀.re < w.re := by
        simp [z₀, w, exercise25SquareRadius]
        linarith
      have hIm : z₀.im < w.im := by
        simp [z₀, w, exercise25SquareRadius]
        linarith
      have hΓ :
          IsOrientedBoundaryOf (Complex.Rectangle z₀ w) Γ := by
        -- Package the explicit square contour as a singleton oriented-boundary family.
        simpa [Γ, z₀, w, exercise25SquareBoundary] using
          axisParallelRectangleBoundary_isOrientedBoundaryOf z₀ w hRe hIm
      have hEq :
          (fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) =ᶠ[
              Filter.codiscreteWithin (Set.univ : Set ℂ)]
            splitIntegrand := by
        let bad : Set ℂ := insert 0 (Q.roots.toFinset : Set ℂ)
        have hbad :
            badᶜ ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
          exact compl_finite_mem_codiscreteWithin
            ((Q.roots.toFinset).finite_toSet.insert 0)
        refine Filter.eventuallyEq_of_mem hbad ?_
        intro z hz
        have hz0 : z ≠ 0 := by
          intro hz'
          exact hz (by simp [bad, hz'])
        have hQz : Q.eval z ≠ 0 := by
          intro hQzero
          have hzroot : z ∈ (Q.roots.toFinset : Set ℂ) := by
            simpa using
              (Polynomial.mem_roots
                (exercise25_denominator_ne_zero_of_degree_lt P Q hdeg)).2 hQzero
          exact hz (by simp [bad, hzroot])
        calc
          P.eval z / Q.eval z * exercise25PiCot z
              = (P.eval z / Q.eval z) * exercise25PiCot z := by ring
          _ = (R.eval z / ((Polynomial.X * Q).eval z) + c / z) * exercise25PiCot z := by
                rw [hsplit z hz0 hQz]
          _ = splitIntegrand z := by
                dsimp [splitIntegrand]
                rw [Polynomial.eval_mul, Polynomial.eval_X, add_mul]
                field_simp [hz0, hQz]
      have htransfer :
          originalSeq n =
            ∫ᶜ z in exercise25SquareBoundary m,
              ((fun z ↦ splitIntegrand z) dz) z := by
        -- Replace the original integrand by its split-at-infinity form on the square boundary.
        have htransfer' :
            ∫ᶜ z in (Γ ()).toPath, ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z =
              ∫ᶜ z in (Γ ()).toPath, ((fun z ↦ splitIntegrand z) dz) z := by
          exact
            curveIntegral_eq_of_codiscrete_boundary_component
              (K := Complex.Rectangle z₀ w) (U := Set.univ) (Γ := Γ) hΓ ()
              (φ := fun z ↦ P.eval z / Q.eval z * exercise25PiCot z)
              (ψ := fun z ↦ splitIntegrand z) hEq (by intro z hz; simp)
        have hloop_left :
            ∫ᶜ z in (Γ ()).toPath, ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z =
              ∫ᶜ z in exercise25SquareBoundary m,
                ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z := by
          simpa [Γ] using
            exercise25_curveIntegral_loop_toClosedPath_toPath
              ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) (exercise25SquareBoundary m)
        have hloop_right :
            ∫ᶜ z in (Γ ()).toPath, ((fun z ↦ splitIntegrand z) dz) z =
              ∫ᶜ z in exercise25SquareBoundary m, ((fun z ↦ splitIntegrand z) dz) z := by
          simpa [Γ] using
            exercise25_curveIntegral_loop_toClosedPath_toPath
              ((fun z ↦ splitIntegrand z) dz) (exercise25SquareBoundary m)
        simpa [originalSeq, m] using hloop_left.symm.trans (htransfer'.trans hloop_right)
      have hcorrInt :
          CurveIntegrable ((fun z ↦ exercise25PiCot z / z) dz) (exercise25SquareBoundary m) :=
        exercise25_piCotDivZ_squareCurveIntegrable m
      have hsum :
          ∫ᶜ z in exercise25SquareBoundary m,
              ((fun z ↦ splitIntegrand z) dz) z =
            remainderSeq n + c * correctionSeq n := by
        -- Split the contour integral into the gap-two remainder term and the elementary correction.
        have hsplitForm :
            (fun z ↦ ((fun z ↦ splitIntegrand z) dz) z) =
              (fun z ↦
                (((fun z ↦ R.eval z / (z * Q.eval z) * exercise25PiCot z) dz) z) +
                  c • (((fun z ↦ exercise25PiCot z / z) dz) z)) := by
          funext z
          ext v
          simp [splitIntegrand, Complex.scalarOneForm, add_mul, smul_eq_mul, mul_assoc,
            mul_left_comm, mul_comm]
        calc
          ∫ᶜ z in exercise25SquareBoundary m,
              ((fun z ↦ splitIntegrand z) dz) z
              =
              ∫ᶜ z in exercise25SquareBoundary m,
                ((((fun z ↦ R.eval z / (z * Q.eval z) * exercise25PiCot z) dz) z) +
                  c • (((fun z ↦ exercise25PiCot z / z) dz) z)) := by
                rw [hsplitForm]
          _ =
              ∫ᶜ z in exercise25SquareBoundary m,
                ((fun z ↦ R.eval z / (z * Q.eval z) * exercise25PiCot z) dz) z +
              ∫ᶜ z in exercise25SquareBoundary m,
                c • (((fun z ↦ exercise25PiCot z / z) dz) z) := by
                exact curveIntegral_fun_add (hcontRem' n) (hcorrInt.smul (c := c))
          _ = remainderSeq n + c * correctionSeq n := by
                simp [remainderSeq, correctionSeq, m, curveIntegral_fun_smul]
      exact htransfer.trans hsum
    have hcorr_zero : ∀ n : ℕ, correctionSeq n = 0 := by
      intro n
      simp [correctionSeq, exercise25_piCotDivZ_squareIntegral_eq_zero]
    have hcorr :
        Tendsto (fun n : ℕ ↦ c * correctionSeq n) atTop (𝓝 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      refine Filter.Eventually.of_forall ?_
      intro n
      simpa [hcorr_zero n]
    have hsum :
        Tendsto (fun n : ℕ ↦ remainderSeq n + c * correctionSeq n) atTop (𝓝 0) := by
      simpa using htailRem'.add hcorr
    exact ⟨Nrem, Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hformula n).symm) hsum⟩

/-- Exercise 25 (8): the symmetric integer-sum formula remains valid under the weaker degree
assumption `deg P < deg Q`. -/
theorem exercise25_rational_integer_sum_tendsto_of_degree_gap_one
    (P Q : Polynomial ℂ) (hdeg : P.natDegree < Q.natDegree) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue) :
    Tendsto
      (fun n : ℕ ↦
        Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ)))
      atTop
      (𝓝 (-s.sum fun z ↦ residue z * exercise25PiCot z)) := by
  -- Reuse the repaired residue identity from theorem (7); only the contour-tail argument changes.
  obtain ⟨Nres, hresEq⟩ :=
    exercise25_squareBoundary_piCot_product_curveIntegral_eq_two_pi_I_mul_sum
      P Q hpoles hnonint hsimple hdenom_int residue hresidue
  obtain ⟨Ntail, htail₀⟩ :=
    exercise25_rational_piCot_contour_tendsto_zero_of_degree_lt P Q hdeg hpoles hnonint
  let N : ℕ := max Nres Ntail
  let integralSeq : ℕ → ℂ := fun n ↦
    ∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ P.eval z / Q.eval z * exercise25PiCot z) dz) z
  let sumSeq : ℕ → ℂ := fun n ↦
    Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦ P.eval (p : ℂ) / Q.eval (p : ℂ))
  let residueSum : ℂ := s.sum (fun z ↦ residue z * exercise25PiCot z)
  have htail :
      Tendsto (fun n : ℕ ↦ integralSeq (n + N)) atTop (𝓝 0) := by
    -- Reindex the vanishing contour tail to the common shift `N`.
    have hshift :
        Tendsto (fun n : ℕ ↦ integralSeq ((n + (N - Ntail)) + Ntail)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat (N - Ntail)).2 htail₀
    refine Tendsto.congr' ?_ hshift
    refine Filter.Eventually.of_forall ?_
    intro n
    have hidx : (n + (N - Ntail)) + Ntail = n + N := by
      dsimp [N]
      omega
    simp [integralSeq, hidx]
  have hshifted :
      Tendsto (fun n : ℕ ↦ sumSeq (n + N)) atTop (𝓝 (-residueSum)) := by
    let scaledIntegral : ℕ → ℂ := fun n ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N)
    have hformula :
        ∀ n : ℕ, sumSeq (n + N) = scaledIntegral n - residueSum := by
      intro n
      have hEq : integralSeq (n + N) =
          (2 * Real.pi * Complex.I : ℂ) * (sumSeq (n + N) + residueSum) := by
        have hshift :
            integralSeq ((n + (N - Nres)) + Nres) =
              (2 * Real.pi * Complex.I : ℂ) *
                (sumSeq ((n + (N - Nres)) + Nres) + residueSum) := by
          simpa [integralSeq, sumSeq, residueSum] using hresEq (n + (N - Nres))
        have hidx : (n + (N - Nres)) + Nres = n + N := by
          dsimp [N]
          omega
        simpa [integralSeq, sumSeq, residueSum, hidx] using hshift
      have hscaled :
          scaledIntegral n = sumSeq (n + N) + residueSum := by
        -- Multiply back by `2πi` so the inverse scalar disappears, then cancel the nonzero
        -- factor using the contour identity.
        apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
        dsimp [scaledIntegral]
        field_simp [Complex.two_pi_I_ne_zero]
        simpa [mul_assoc] using hEq
      -- Subtract the constant residue contribution from both sides.
      have hsub := congrArg (fun z : ℂ ↦ z - residueSum) hscaled
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, scaledIntegral] using hsub.symm
    have hscaled :
        Tendsto (fun n : ℕ ↦ scaledIntegral n) atTop (𝓝 0) := by
      change Tendsto (fun n : ℕ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N))
        atTop (𝓝 0)
      simpa [mul_zero] using
        (tendsto_const_nhds.mul htail :
          Tendsto (fun n : ℕ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N))
            atTop (𝓝 (((2 * Real.pi * Complex.I : ℂ)⁻¹) * 0)))
    have hshiftedScaled :
        Tendsto (fun n : ℕ ↦ scaledIntegral n - residueSum) atTop (𝓝 (-residueSum)) := by
      simpa [sub_eq_add_neg] using hscaled.sub tendsto_const_nhds
    -- Replace the shifted sums by the scaled contour expression minus the constant residue sum.
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hformula n).symm) hshiftedScaled
  -- Dropping a finite initial shift does not change the limit of the symmetric sums.
  have hshifted' :
      Tendsto (fun n : ℕ ↦ sumSeq (n + N)) atTop (𝓝 (-residueSum)) := hshifted
  exact (tendsto_add_atTop_iff_nat N).1 hshifted'

/-- Exercise 25 (9): if `-π < α < π`, then there is a constant `M2 > 0`, independent of `n`,
such that `|exp(i α z) / sin(π z)| ≤ M2` on the square contour `γ_n`. -/
theorem exercise25_exp_div_sin_norm_bounded_on_square_boundaries
    (alpha : ℝ) (halpha_left : -Real.pi < alpha) (halpha_right : alpha < Real.pi) :
    ∃ M2 : ℝ, 0 < M2 ∧
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary n),
        ‖Complex.exp (Complex.I * (alpha : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z)‖ ≤ M2 := by
  let Mvert : ℝ := 2
  let Mhor : ℝ := 2 / (1 - Real.exp (-Real.pi))
  let M2 : ℝ := max Mvert Mhor
  have habs_lt_pi : |alpha| < Real.pi := by
    rw [abs_lt]
    constructor <;> linarith
  refine ⟨M2, ?_, ?_⟩
  · -- The chosen bound is positive because it dominates the positive vertical-side constant `2`.
    dsimp [M2, Mvert]
    positivity
  · intro n z hz
    rcases exercise25_square_boundary_geometry n hz with ⟨_, _, hside, _⟩
    rcases hside with hzre | hzim
    · have hnum :
        ‖Complex.exp (Complex.I * (alpha : ℂ) * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
        -- Route correction: on the vertical sides, bound the oscillatory factor only through
        -- `|α| < π` and the explicit norm formula for `exp (i α z)`.
        rw [exercise25_exp_phase_norm]
        refine Real.exp_le_exp.mpr <| (le_abs_self _).trans ?_
        calc
          |(-alpha) * z.im| = |alpha| * |z.im| := by rw [abs_mul, abs_neg]
          _ ≤ Real.pi * |z.im| := by
            exact mul_le_mul_of_nonneg_right habs_lt_pi.le (abs_nonneg _)
      have hden :
          ‖Complex.sin ((Real.pi : ℂ) * z)‖ = Real.cosh (Real.pi * z.im) :=
        exercise25_norm_sin_pi_of_re_abs_eq_radius n hzre
      have hcosh_bound :
          Real.exp (Real.pi * |z.im|) ≤ 2 * Real.cosh (Real.pi * z.im) := by
        have haux :
            Real.exp (Real.pi * |z.im|) ≤ 2 * Real.cosh (Real.pi * |z.im|) := by
          rw [Real.cosh_eq]
          have hexp_nonneg : 0 ≤ Real.exp (-(Real.pi * |z.im|)) := by positivity
          nlinarith
        calc
          Real.exp (Real.pi * |z.im|) ≤ 2 * Real.cosh (Real.pi * |z.im|) := haux
          _ = 2 * Real.cosh (Real.pi * z.im) := by
                rw [← Real.cosh_abs (Real.pi * z.im), abs_mul, abs_of_pos Real.pi_pos]
      have hbound :
          ‖Complex.exp (Complex.I * (alpha : ℂ) * z) /
              Complex.sin ((Real.pi : ℂ) * z)‖ ≤ 2 := by
        rw [norm_div, hden]
        exact (div_le_iff₀ (Real.cosh_pos _)).2 (hnum.trans hcosh_bound)
      exact hbound.trans (le_max_left _ _)
    · have hzmul :
          ((Real.pi : ℂ) * z) = (Real.pi * z.re : ℂ) + (Real.pi * z.im) * Complex.I := by
        -- Normalize `π z` to the `x + t I` form used by the half-integer strip estimates.
        apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, mul_comm]
      obtain ⟨_, hsinh_fixed⟩ := exercise25_hyperbolic_of_im_abs_eq_squareRadius n hzim
      have hsinh_pos : 0 < Real.sinh (Real.pi * exercise25SquareRadius n) := by
        simpa [exercise25SquareRadius, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using
          sinh_pi_nat_add_half_pos n
      have hden :
          Real.sinh (Real.pi * exercise25SquareRadius n) ≤
            ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
        calc
          Real.sinh (Real.pi * exercise25SquareRadius n)
              = |Real.sinh (Real.pi * z.im)| := by rw [hsinh_fixed]
          _ ≤ ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
                rw [hzmul]
                simpa using
                  exercise25_abs_sinh_le_norm_sin_add_mul_I (Real.pi * z.re) (Real.pi * z.im)
      have hnum :
          ‖Complex.exp (Complex.I * (alpha : ℂ) * z)‖ ≤
            Real.exp (Real.pi * exercise25SquareRadius n) := by
        -- On the horizontal sides, `|Im z| = r_n`; the strict inequality `|α| < π` upgrades the
        -- exponential growth to the universal `exp (π r_n)` majorant.
        have hr_nonneg : 0 ≤ exercise25SquareRadius n := by
          dsimp [exercise25SquareRadius]
          positivity
        rw [exercise25_exp_phase_norm]
        refine Real.exp_le_exp.mpr <| (le_abs_self _).trans ?_
        calc
          |(-alpha) * z.im| = |alpha| * |z.im| := by rw [abs_mul, abs_neg]
          _ ≤ Real.pi * exercise25SquareRadius n := by
            rw [hzim]
            exact mul_le_mul_of_nonneg_right habs_lt_pi.le hr_nonneg
      have hinv :
          ‖Complex.sin ((Real.pi : ℂ) * z)‖⁻¹ ≤
            (Real.sinh (Real.pi * exercise25SquareRadius n))⁻¹ := by
        -- Inverting the horizontal denominator lower bound turns it into a quotient upper bound.
        simpa [one_div] using one_div_le_one_div_of_le hsinh_pos hden
      have hquot :
          ‖Complex.exp (Complex.I * (alpha : ℂ) * z) /
              Complex.sin ((Real.pi : ℂ) * z)‖ ≤
            Real.exp (Real.pi * exercise25SquareRadius n) /
              Real.sinh (Real.pi * exercise25SquareRadius n) := by
        rw [norm_div]
        calc
          ‖Complex.exp (Complex.I * (alpha : ℂ) * z)‖ / ‖Complex.sin ((Real.pi : ℂ) * z)‖
              = ‖Complex.exp (Complex.I * (alpha : ℂ) * z)‖ *
                  ‖Complex.sin ((Real.pi : ℂ) * z)‖⁻¹ := by
                    rw [div_eq_mul_inv]
          _ ≤ Real.exp (Real.pi * exercise25SquareRadius n) *
                (Real.sinh (Real.pi * exercise25SquareRadius n))⁻¹ := by
                  exact mul_le_mul hnum hinv
                    (inv_nonneg.mpr (norm_nonneg _))
                    (Real.exp_pos _).le
          _ = Real.exp (Real.pi * exercise25SquareRadius n) /
                Real.sinh (Real.pi * exercise25SquareRadius n) := by
                  rw [div_eq_mul_inv]
      have hu : Real.pi / 2 ≤ Real.pi * exercise25SquareRadius n := by
        dsimp [exercise25SquareRadius]
        nlinarith [Real.pi_pos]
      exact
        hquot.trans <|
          (exercise25_exp_div_sinh_le_uniform hu).trans (le_max_right _ _)

/-- Helper for Cartan section12 0038_Exercise_25: the weighted kernel used in the alternating
residue formula is `π * exp (i α z) / sin (π z)`. -/
def exercise25WeightedKernel (alpha : ℝ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * Complex.exp (Complex.I * (alpha : ℂ) * z) /
    Complex.sin ((Real.pi : ℂ) * z)

/-- Helper for Cartan section12 0038_Exercise_25: away from the integers, the weighted kernel is
holomorphic because its sine denominator stays nonzero. -/
lemma exercise25_weightedKernel_differentiableAt_of_not_integer
    (alpha : ℝ) {z : ℂ}
    (hz : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    DifferentiableAt ℂ (exercise25WeightedKernel alpha) z := by
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    exercise25_sin_pi_ne_zero_of_not_integer hz
  have hnum :
      DifferentiableAt ℂ
        (fun w : ℂ ↦
          (Real.pi : ℂ) * Complex.exp (Complex.I * (alpha : ℂ) * w)) z := by
    fun_prop
  have hden :
      DifferentiableAt ℂ (fun w : ℂ ↦ Complex.sin ((Real.pi : ℂ) * w)) z := by
    fun_prop
  -- The numerator is entire, so only the sine denominator matters.
  simpa [exercise25WeightedKernel] using hnum.div hden hsin

/-- Helper for Cartan section12 0038_Exercise_25: differentiability of the weighted kernel away
from the integers immediately gives continuity there. -/
lemma exercise25_weightedKernel_continuousAt_of_not_integer
    (alpha : ℝ) {z : ℂ}
    (hz : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    ContinuousAt (exercise25WeightedKernel alpha) z :=
  (exercise25_weightedKernel_differentiableAt_of_not_integer alpha hz).continuousAt

/-- Helper for Cartan section12 0038_Exercise_25: on the quarter-thickened square neighborhood,
away from the enclosed integer lattice points, the weighted kernel is holomorphic. -/
lemma exercise25_weightedKernel_differentiableAt_away_from_squareIntegers
    (alpha : ℝ) {m : ℕ} {z : ℂ}
    (hzD :
      |z.re| < exercise25SquareRadius m + 1 / 4 ∧
        |z.im| < exercise25SquareRadius m + 1 / 4)
    (hzI :
      z ∉
        (Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ)) : Set ℂ)) :
    DifferentiableAt ℂ (exercise25WeightedKernel alpha) z := by
  -- Any integer in this neighborhood already belongs to the square index set, so the weighted
  -- kernel is holomorphic once those lattice points are excluded.
  apply exercise25_weightedKernel_differentiableAt_of_not_integer alpha
  intro hzInt
  rcases hzInt with ⟨p, rfl⟩
  apply hzI
  exact exercise25_intCast_mem_squareIndexSet (m := m) (by simpa using hzD.1)

/-- Helper for Cartan section12 0038_Exercise_25: on the quarter-thickened square neighborhood,
away from the mixed pole finset consisting of the noninteger poles of `P / Q` together with the
enclosed integers, the weighted product built from the meromorphic normal form of `P / Q` is
holomorphic. -/
lemma exercise25_squareNeighborhood_weightedKernelProduct_differentiableOn
    (alpha : ℝ) (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (m : ℕ) :
    let D : Set ℂ :=
      {z : ℂ |
        |z.re| < exercise25SquareRadius m + 1 / 4 ∧
          |z.im| < exercise25SquareRadius m + 1 / 4}
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let integerSet : Finset ℂ :=
      Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    DifferentiableOn ℂ
      (fun w ↦ gNF w * exercise25WeightedKernel alpha w)
      (D \ (↑residueSet : Set ℂ)) := by
  -- This is the weighted analogue of the `π cot` neighborhood holomorphy theorem; the normal-form
  -- owner is unchanged and only the kernel input is swapped.
  dsimp
  intro z hz
  have hz_not_s : z ∉ (↑s : Set ℂ) := by
    intro hzS
    exact hz.2 (show z ∈ (↑(s ∪ Finset.image (fun p : ℤ ↦ (p : ℂ))
      (Finset.Icc (-((m : ℤ))) (m : ℤ))) : Set ℂ) from Finset.mem_union.mpr (Or.inl hzS))
  have hz_not_int :
      z ∉
        (Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ)) : Set ℂ) := by
    intro hzI
    exact hz.2 (show z ∈ (↑(s ∪ Finset.image (fun p : ℤ ↦ (p : ℂ))
      (Finset.Icc (-((m : ℤ))) (m : ℤ))) : Set ℂ) from Finset.mem_union.mpr (Or.inr hzI))
  have hnf :
      DifferentiableWithinAt ℂ
        (toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ)
        ((↑s : Set ℂ)ᶜ) z :=
    exercise25_rationalNormalForm_differentiableOn_compl_poleFinset P Q s hpoles z hz_not_s
  have hnf' :
      DifferentiableWithinAt ℂ
        (toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ)
        ({w : ℂ |
          |w.re| < exercise25SquareRadius m + 1 / 4 ∧
            |w.im| < exercise25SquareRadius m + 1 / 4} \
          (↑(s ∪ Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))) :
            Set ℂ)) z := by
    refine hnf.mono ?_
    intro w hw
    exact fun hwS ↦ hw.2 (by simp [hwS])
  have hweighted :
      DifferentiableAt ℂ (exercise25WeightedKernel alpha) z :=
    exercise25_weightedKernel_differentiableAt_away_from_squareIntegers alpha hz.1 hz_not_int
  exact hnf'.mul hweighted.differentiableWithinAt

/-- Helper for Cartan section12 0038_Exercise_25: at a noninteger pole of `P / Q` inside the
square, the weighted integrand built from the meromorphic normal form of `P / Q` admits an
explicit local kernel model on a closed ball adapted to the square residue set. -/
lemma exercise25_nonintegerWeightedProduct_circleKernelModelOnSquare
    (alpha : ℝ) (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue)
    {m : ℕ} {K D : Set ℂ}
    (hK :
      K = Complex.Rectangle
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I))
    (hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4})
    {z : ℂ} (hz : z ∈ s) (hzK : z ∈ interior K) :
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let integerSet : Finset ℂ :=
      Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    ∃ r > 0, ∃ G : ℂ → ℂ,
      Metric.closedBall z r ⊆ interior K ∧
        Metric.closedBall z r ⊆ D ∧
          (∀ w ∈ residueSet, w ≠ z → w ∉ Metric.closedBall z r) ∧
            DifferentiableOn ℂ
              (fun w ↦ gNF w * exercise25WeightedKernel alpha w)
              (Metric.ball z r \ ({z} : Set ℂ)) ∧
              DifferentiableOn ℂ G (Metric.closedBall z r) ∧
                G z = residue z * exercise25WeightedKernel alpha z ∧
                  (∀ w ∈ Metric.sphere z r,
                    gNF w * exercise25WeightedKernel alpha w = G w / (w - z)) := by
  -- The noninteger branch keeps the same rational normal-form numerator as before; only the
  -- analytic multiplier changes from `π cot` to the weighted kernel itself.
  dsimp
  let f : ℂ → ℂ := fun w ↦ P.eval w / Q.eval w
  let gNF : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  let integerSet : Finset ℂ :=
    Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  have hzResidue : z ∈ residueSet := Finset.mem_union.mpr <| Or.inl hz
  have hmeromorphic : MeromorphicOn f Set.univ := by
    simpa [f] using exercise25_rationalEval_meromorphicOn_univ P Q
  have hEqNF : gNF =ᶠ[𝓝[≠] z] f := by
    simpa [f, gNF] using
      hmeromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE (by simp : z ∈ Set.univ)
  have horderNF : meromorphicOrderAt gNF z = (-1 : WithTop ℤ) := by
    rw [meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := Set.univ) hmeromorphic (by simp)]
    simpa [f] using hsimple z hz
  have hmerNF : MeromorphicAt gNF z := by
    exact meromorphicAt_of_meromorphicOrderAt_ne_zero (by simpa [horderNF])
  obtain ⟨H, hH_an, hH_ne, hH_eq⟩ := (meromorphicOrderAt_eq_int_iff hmerNF).1 horderNF
  have hH_coeff : meromorphicTrailingCoeffAt gNF z = H z := by
    exact
      hH_an.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
        (f := gNF) (x := z) (n := (-1 : ℤ)) hH_ne hH_eq
  have hHz : H z = residue z := by
    calc
      H z = meromorphicTrailingCoeffAt gNF z := hH_coeff.symm
      _ = meromorphicTrailingCoeffAt f z := by
        simpa [f, gNF] using meromorphicTrailingCoeffAt_congr_nhdsNE hEqNF
      _ = residue z := exercise25_rational_trailingCoeff_eq_residue
        P Q hpoles hsimple residue hresidue hz
  obtain ⟨ρK, hρK_pos, hρK_ball⟩ :=
    Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hzK)
  obtain ⟨ρsep, hρsep_pos, hsepρ⟩ :=
    exercise25_exists_separating_radius_closedBall (s := residueSet) hzResidue
  obtain ⟨ρH, hρH_pos, hH_ball⟩ := hH_an.exists_ball_analyticOnNhd
  have hH_eq' : ∀ᶠ w in 𝓝[≠] z, gNF w = (w - z) ^ (-1 : ℤ) • H w := by
    simpa [Filter.EventuallyEq] using hH_eq
  rw [eventually_nhdsWithin_iff] at hH_eq'
  rcases Metric.mem_nhds_iff.1 hH_eq' with ⟨δH, hδH_pos, hδH⟩
  let r : ℝ := min (ρK / 2) (min (ρsep / 2) (min (ρH / 2) (δH / 2)))
  have hr : 0 < r := by
    dsimp [r]
    refine lt_min (half_pos hρK_pos) ?_
    refine lt_min (half_pos hρsep_pos) ?_
    exact lt_min (half_pos hρH_pos) (half_pos hδH_pos)
  have hr_lt_K : r < ρK := by
    dsimp [r]
    have : r ≤ ρK / 2 := min_le_left _ _
    linarith
  have hr_lt_H : r < ρH := by
    dsimp [r]
    have : r ≤ ρH / 2 := le_trans (min_le_right _ _) <|
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hr_lt_δH : r < δH := by
    dsimp [r]
    have : r ≤ δH / 2 := le_trans (min_le_right _ _) <|
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hclosedK : Metric.closedBall z r ⊆ interior K := by
    exact (Metric.closedBall_subset_ball hr_lt_K).trans hρK_ball
  have hKD :
      K ⊆
        {w : ℂ |
          |w.re| < exercise25SquareRadius m + 1 / 4 ∧
            |w.im| < exercise25SquareRadius m + 1 / 4} := by
    rw [hK]
    exact exercise25_squareRectangle_subset_thickenedNeighborhood m
  have hclosedD : Metric.closedBall z r ⊆ D := by
    intro w hw
    have hwD' :
        w ∈
          {w : ℂ |
            |w.re| < exercise25SquareRadius m + 1 / 4 ∧
              |w.im| < exercise25SquareRadius m + 1 / 4} :=
      hKD (interior_subset (hclosedK hw))
    simpa [hD] using hwD'
  have havoid :
      ∀ w ∈ residueSet, w ≠ z → w ∉ Metric.closedBall z r := by
    intro w hw hwz hwball
    exact hsepρ w hw hwz <|
      Metric.closedBall_subset_closedBall (by
        have : r ≤ ρsep / 2 := by
          dsimp [r]
          exact le_trans (min_le_right _ _) (min_le_left _ _)
        linarith) hwball
  have hH_diff : DifferentiableOn ℂ H (Metric.closedBall z r) := by
    -- Shrinking below the analytic radius keeps the numerator holomorphic on the comparison ball.
    refine hH_ball.differentiableOn.mono ?_
    intro w hw
    exact Metric.mem_ball.2 (lt_of_le_of_lt hw hr_lt_H)
  have hkernelNF :
      ∀ w ∈ Metric.sphere z r, gNF w = H w / (w - z) := by
    intro w hw
    have hw_norm : ‖w - z‖ = r := by
      simpa [Metric.mem_sphere] using hw
    have hw_ball : w ∈ Metric.ball z δH := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hw_norm.trans_lt hr_lt_δH
    have hw_ne : w ≠ z := Metric.ne_of_mem_sphere hw hr.ne'
    have hHw : gNF w = (w - z) ^ (-1 : ℤ) • H w := by
      exact hδH hw_ball (by simpa using hw_ne)
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hHw
  have hprodDiffGlobal :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25WeightedKernel alpha w)
        (D \ (↑residueSet : Set ℂ)) := by
    simpa [hD, gNF, integerSet, residueSet] using
      exercise25_squareNeighborhood_weightedKernelProduct_differentiableOn
        alpha P Q hpoles m
  have hprodDiff :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25WeightedKernel alpha w)
        (Metric.ball z r \ ({z} : Set ℂ)) := by
    exact
      differentiableOn_punctured_ball_of_finite_support_separation
        hclosedD havoid hprodDiffGlobal
  have hweightedDiff : DifferentiableOn ℂ (exercise25WeightedKernel alpha) (Metric.closedBall z r) := by
    intro w hw
    have hwD :
        |w.re| < exercise25SquareRadius m + 1 / 4 ∧
          |w.im| < exercise25SquareRadius m + 1 / 4 := by
      simpa [hD] using hclosedD hw
    have hw_not_int : w ∉ (integerSet : Set ℂ) := by
      intro hwInt
      by_cases hwz : w = z
      · subst hwz
        apply hnonint w hz
        rcases Finset.mem_image.mp hwInt with ⟨p, hp, rfl⟩
        exact ⟨p, rfl⟩
      · exact havoid w (Finset.mem_union.mpr <| Or.inr hwInt) hwz hw
    exact
      (exercise25_weightedKernel_differentiableAt_away_from_squareIntegers
        alpha (m := m) hwD hw_not_int).differentiableWithinAt
  obtain ⟨G, hG_diff, hG_center, hkernel⟩ :=
    exercise25_closedBallSimplePoleMulRegularFactor
      (z := z) (c := residue z) (r := r) (φ := gNF) (G := H)
      (ψ := exercise25WeightedKernel alpha)
      hr hH_diff hHz hkernelNF hweightedDiff
  refine ⟨r, hr, G, hclosedK, hclosedD, havoid, hprodDiff, hG_diff, hG_center, ?_⟩
  intro w hw
  exact hkernel w hw

/-- Helper for Cartan section12 0038_Exercise_25: every real half-integer stays at least `1 / 2`
away from the integer lattice. -/
lemma exercise25_intCast_add_half_abs_ge_half (m : ℤ) :
    (1 / 2 : ℝ) ≤ |(m : ℝ) + 1 / 2| := by
  by_cases hm : 0 ≤ m
  · have hm' : (0 : ℝ) ≤ m := by
      exact_mod_cast hm
    have hnonneg : 0 ≤ (m : ℝ) + 1 / 2 := by
      nlinarith
    rw [abs_of_nonneg hnonneg]
    nlinarith
  · have hm' : m ≤ -1 := by
      omega
    have hm'' : (m : ℝ) ≤ -1 := by
      exact_mod_cast hm'
    have hnonpos : (m : ℝ) + 1 / 2 ≤ 0 := by
      nlinarith
    rw [abs_of_nonpos hnonpos]
    nlinarith

/-- Helper for Cartan section12 0038_Exercise_25: if a point stays within distance `1 / 4` of an
integer `p`, then `cos (π z)` cannot vanish there, because the nearest half-integer zeros are at
distance at least `1 / 2` from `p`. -/
lemma exercise25_cos_pi_ne_zero_on_closedBall_of_int
    {p : ℤ} {r : ℝ} (hr : r ≤ 1 / 4) {w : ℂ}
    (hw : w ∈ Metric.closedBall (p : ℂ) r) :
    Complex.cos ((Real.pi : ℂ) * w) ≠ 0 := by
  intro hcos
  rcases Complex.cos_eq_zero_iff.mp hcos with ⟨k, hk⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hw_eq : w = (k : ℂ) + (1 / 2 : ℂ) := by
    apply (mul_left_cancel₀ hpi)
    calc
      (Real.pi : ℂ) * w = (2 * k + 1) * (Real.pi : ℂ) / 2 := hk
      _ = (Real.pi : ℂ) * ((k : ℂ) + (1 / 2 : ℂ)) := by
        norm_num
        ring
  have hw_norm : ‖w - (p : ℂ)‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hreal :
      |((k - p : ℤ) : ℝ) + 1 / 2| ≤ r := by
    have hRe :
        |w.re - (p : ℝ)| ≤ ‖w - (p : ℂ)‖ := by
      calc
        |w.re - (p : ℝ)| = |(w - (p : ℂ)).re| := by simp
        _ ≤ ‖w - (p : ℂ)‖ := Complex.abs_re_le_norm _
    have hrew :
        |((k - p : ℤ) : ℝ) + 1 / 2| = |w.re - (p : ℝ)| := by
      rw [hw_eq]
      norm_num
      ring_nf
    exact hrew.symm ▸ (hRe.trans hw_norm)
  have hhalf :
      (1 / 2 : ℝ) ≤ |((k - p : ℤ) : ℝ) + 1 / 2| :=
    exercise25_intCast_add_half_abs_ge_half (k - p)
  linarith

/-- Helper for Cartan section12 0038_Exercise_25: away from the zeros of `cos (π z)`, the weighted
kernel is the cotangent kernel multiplied by the regular factor `exp (i α z) / cos (π z)`. -/
lemma exercise25_weightedKernel_eq_piCot_mul_exp_div_cos
    (alpha : ℝ) {z : ℂ}
    (hcos : Complex.cos ((Real.pi : ℂ) * z) ≠ 0) :
    exercise25WeightedKernel alpha z =
      exercise25PiCot z *
        (Complex.exp (Complex.I * (alpha : ℂ) * z) /
          Complex.cos ((Real.pi : ℂ) * z)) := by
  -- Rewrite `π cot (π z)` as `π cos (π z) / sin (π z)` and cancel the nonvanishing cosine factor.
  rw [exercise25WeightedKernel, exercise25_piCot_eq_cos_div_sin]
  field_simp [hcos]

/-- Helper for Cartan section12 0038_Exercise_25: at an integer pole of the weighted kernel inside
the square, the mixed integrand built from the meromorphic normal form of `P / Q` admits an
explicit local kernel model on a closed ball adapted to the square residue set. -/
lemma exercise25_integerWeightedProduct_circleKernelModelOnSquare
    (alpha : ℝ) (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun q : ℤ ↦ (q : ℂ)))
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    {m : ℕ} {K D : Set ℂ}
    (hK :
      K = Complex.Rectangle
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I))
    (hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4})
    {p : ℤ} (hp : p ∈ Finset.Icc (-((m : ℤ))) (m : ℤ)) :
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let integerSet : Finset ℂ :=
      Finset.image (fun q : ℤ ↦ (q : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    ∃ r > 0, ∃ G : ℂ → ℂ,
      Metric.closedBall (p : ℂ) r ⊆ interior K ∧
        Metric.closedBall (p : ℂ) r ⊆ D ∧
          (∀ w ∈ residueSet, w ≠ (p : ℂ) → w ∉ Metric.closedBall (p : ℂ) r) ∧
            DifferentiableOn ℂ
              (fun w ↦ gNF w * exercise25WeightedKernel alpha w)
              (Metric.ball (p : ℂ) r \ ({(p : ℂ)} : Set ℂ)) ∧
              DifferentiableOn ℂ G (Metric.closedBall (p : ℂ) r) ∧
                G (p : ℂ) =
                  (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                    Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                    (P.eval (p : ℂ) / Q.eval (p : ℂ)) ∧
                  (∀ w ∈ Metric.sphere (p : ℂ) r,
                    gNF w * exercise25WeightedKernel alpha w = G w / (w - (p : ℂ))) := by
  -- Route correction: start from the pure `π cot` simple-pole model and multiply by the regular
  -- factor `gNF(w) * exp (i α w) / cos (π w)` on the same separated ball.
  dsimp
  let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
  let integerSet : Finset ℂ :=
    Finset.image (fun q : ℤ ↦ (q : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  have hp_not_s : (p : ℂ) ∉ s := by
    intro hpS
    exact hnonint (p : ℂ) hpS ⟨p, rfl⟩
  obtain ⟨r, hr, hr_quarter, H, hclosedK, hclosedD, havoid, hH_diff, hHp, hkernelPiCot⟩ :=
    exercise25_integerPiCot_circleKernelModelOnSeparatedBall
      (s := s) (m := m) (K := K) (D := D) hK hD hp
  have hholNF : DifferentiableOn ℂ gNF (↑s : Set ℂ)ᶜ := by
    simpa [gNF] using
      exercise25_rationalNormalForm_differentiableOn_compl_poleFinset P Q s hpoles
  have hclosedNoS : Metric.closedBall (p : ℂ) r ⊆ (↑s : Set ℂ)ᶜ := by
    intro w hw hwS
    by_cases hwp : w = (p : ℂ)
    · subst hwp
      exact hp_not_s hwS
    · exact havoid w (Finset.mem_union.mpr <| Or.inl hwS) hwp hw
  have hgNF_diff : DifferentiableOn ℂ gNF (Metric.closedBall (p : ℂ) r) := by
    -- The normal form is holomorphic on the whole comparison ball because that ball avoids `s`.
    exact hholNF.mono hclosedNoS
  have hprodDiffGlobal :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25WeightedKernel alpha w)
        (D \ (↑residueSet : Set ℂ)) := by
    simpa [hD, gNF, integerSet, residueSet] using
      exercise25_squareNeighborhood_weightedKernelProduct_differentiableOn
        alpha P Q hpoles m
  have hprodDiff :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25WeightedKernel alpha w)
        (Metric.ball (p : ℂ) r \ ({(p : ℂ)} : Set ℂ)) := by
    exact
      differentiableOn_punctured_ball_of_finite_support_separation
        hclosedD havoid hprodDiffGlobal
  let ψ : ℂ → ℂ := fun w ↦
    gNF w * (Complex.exp (Complex.I * (alpha : ℂ) * w) /
      Complex.cos ((Real.pi : ℂ) * w))
  have hψ_diff : DifferentiableOn ℂ ψ (Metric.closedBall (p : ℂ) r) := by
    intro w hw
    have hcos : Complex.cos ((Real.pi : ℂ) * w) ≠ 0 :=
      exercise25_cos_pi_ne_zero_on_closedBall_of_int hr_quarter hw
    have hexp_diff :
        DifferentiableAt ℂ (fun z : ℂ ↦ Complex.exp (Complex.I * (alpha : ℂ) * z)) w := by
      fun_prop
    have hcos_diff :
        DifferentiableAt ℂ (fun z : ℂ ↦ Complex.cos ((Real.pi : ℂ) * z)) w := by
      fun_prop
    -- The rational normal form and the cosine denominator are both regular on the chosen ball.
    exact (hgNF_diff w hw).mul (hexp_diff.div hcos_diff hcos).differentiableWithinAt
  obtain ⟨G, hG_diff, hG_center_raw, hkernel⟩ :=
    exercise25_closedBallSimplePoleMulRegularFactor
      (z := (p : ℂ)) (c := (1 : ℂ)) (r := r) (φ := exercise25PiCot) (G := H) (ψ := ψ)
      hr hH_diff hHp hkernelPiCot hψ_diff
  have hG_center :
      G (p : ℂ) =
        (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
          Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
          (P.eval (p : ℂ) / Q.eval (p : ℂ)) := by
    -- Evaluate the regular factor at the center integer and rewrite `cos (π p)` as `(-1)^p`.
    have hnormal :
        gNF (p : ℂ) = P.eval (p : ℂ) / Q.eval (p : ℂ) := by
      simpa [gNF] using
        exercise25_normalForm_eq_rationalEval_at_regularInteger P Q (p := p) (hdenom_int p)
    calc
      G (p : ℂ) = ψ (p : ℂ) := by simpa [hHp] using hG_center_raw
      _ =
          gNF (p : ℂ) *
            (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
              Complex.cos ((Real.pi : ℂ) * (p : ℂ))) := by
                simp [ψ]
      _ =
          (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
            Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
            gNF (p : ℂ) := by ring
      _ =
          (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
            Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
            (P.eval (p : ℂ) / Q.eval (p : ℂ)) := by
              rw [hnormal]
  refine ⟨r, hr, G, hclosedK, hclosedD, havoid, hprodDiff, hG_diff, hG_center, ?_⟩
  intro w hw
  have hw_closed : w ∈ Metric.closedBall (p : ℂ) r := by
    rw [Metric.mem_closedBall, Metric.mem_sphere] at *
    exact le_of_eq hw
  have hcos : Complex.cos ((Real.pi : ℂ) * w) ≠ 0 :=
    exercise25_cos_pi_ne_zero_on_closedBall_of_int hr_quarter hw_closed
  calc
    gNF w * exercise25WeightedKernel alpha w =
        exercise25PiCot w * ψ w := by
          rw [exercise25_weightedKernel_eq_piCot_mul_exp_div_cos alpha hcos]
          simp [ψ]
          ring
    _ = G w / (w - (p : ℂ)) := hkernel w hw

/-- Helper for Cartan section12 0038_Exercise_25: once the two weighted local kernel models are
available, the mixed residue data on the square residue finset are obtained by the same case split
between the noninteger poles of `P / Q` and the integer poles of the weighted kernel. -/
lemma exercise25_squareWeightedProduct_isolatedResidueData
    (alpha : ℝ) (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue)
    {m : ℕ} {K D : Set ℂ}
    (hK :
      K = Complex.Rectangle
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I))
    (hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4})
    (hsK : (↑s : Set ℂ) ⊆ interior K) :
    let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
    let integerSet : Finset ℂ :=
      Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    let residueValue : ℂ → ℂ := fun z ↦
      if hz : z ∈ s then residue z * exercise25WeightedKernel alpha z
      else if hzInt : z ∈ integerSet then
        (Complex.exp (Complex.I * (alpha : ℂ) * z) /
          Complex.cos ((Real.pi : ℂ) * z)) *
          (P.eval z / Q.eval z)
      else 0
    ∀ z ∈ residueSet,
      IsolatedLocalResidueCircle K D residueSet
        (fun w ↦ gNF w * exercise25WeightedKernel alpha w) z (residueValue z) := by
  -- Dispatch between the weighted noninteger branch and the weighted integer branch, then feed
  -- the corresponding local kernel model into the generic residue-circle wrapper.
  let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
  let integerSet : Finset ℂ :=
    Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  let residueValue : ℂ → ℂ := fun z ↦
    if hz : z ∈ s then residue z * exercise25WeightedKernel alpha z
    else if hzInt : z ∈ integerSet then
      (Complex.exp (Complex.I * (alpha : ℂ) * z) /
        Complex.cos ((Real.pi : ℂ) * z)) *
        (P.eval z / Q.eval z)
    else 0
  dsimp [gNF, integerSet, residueSet, residueValue]
  intro z hz
  by_cases hzS : z ∈ s
  · have hzK : z ∈ interior K := hsK hzS
    obtain ⟨r, hr, G, hclosedK, hclosedD, havoid, hdiff, hG_diff, hG_center, hkernel⟩ :=
      exercise25_nonintegerWeightedProduct_circleKernelModelOnSquare
        alpha P Q hpoles hnonint hsimple residue hresidue hK hD hzS hzK
    refine
      exercise25_isolatedLocalResidueCircle_of_circle_kernel_model_closedBall
        hr hclosedK hclosedD havoid hdiff hG_diff ?_ hkernel
    -- On the noninteger branch, the residue is exactly the prescribed `residue z * κα(z)`.
    simpa [hzS] using hG_center
  · have hzInt : z ∈ integerSet := (Finset.mem_union.mp hz).resolve_left hzS
    rcases Finset.mem_image.mp hzInt with ⟨p, hp, rfl⟩
    obtain ⟨r, hr, G, hclosedK, hclosedD, havoid, hdiff, hG_diff, hG_center, hkernel⟩ :=
      exercise25_integerWeightedProduct_circleKernelModelOnSquare
        alpha P Q hpoles hnonint hdenom_int hK hD hp
    have hp_not_s : (p : ℂ) ∉ s := by
      intro hpS
      exact hnonint (p : ℂ) hpS ⟨p, rfl⟩
    refine
      exercise25_isolatedLocalResidueCircle_of_circle_kernel_model_closedBall
        hr hclosedK hclosedD havoid hdiff hG_diff ?_ hkernel
    -- On the integer branch, only the weighted integer value survives in the piecewise residue
    -- function.
    calc
      G (p : ℂ) =
          (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
            Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
            (P.eval (p : ℂ) / Q.eval (p : ℂ)) := hG_center
      _ =
          (if hz : (p : ℂ) ∈ s then residue (p : ℂ) * exercise25WeightedKernel alpha (p : ℂ)
            else if hzInt : (p : ℂ) ∈ integerSet then
              (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                (P.eval (p : ℂ) / Q.eval (p : ℂ))
            else 0) := by
              simp [hp_not_s, hzInt]

/-- Helper for Cartan section12 0038_Exercise_25: the mixed weighted residue finset on the `m`-th
square splits as the disjoint union of the listed noninteger poles and the enclosed integer lattice
points, so the weighted residue sum separates into the textbook alternating exponential sum plus
the noninteger weighted residue sum. -/
lemma exercise25_squareWeightedResidueSet_sum_split
    (alpha : ℝ) (P Q : Polynomial ℂ) {s : Finset ℂ} (m : ℕ)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (residue : ℂ → ℂ) :
    let integerSet : Finset ℂ :=
      Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
    let residueSet : Finset ℂ := s ∪ integerSet
    let residueValue : ℂ → ℂ := fun z ↦
      if hz : z ∈ s then residue z * exercise25WeightedKernel alpha z
      else if hzInt : z ∈ integerSet then
        (Complex.exp (Complex.I * (alpha : ℂ) * z) /
          Complex.cos ((Real.pi : ℂ) * z)) *
          (P.eval z / Q.eval z)
      else 0
    Finset.sum residueSet residueValue =
      Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ)) (fun p ↦
        (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
          Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
            (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
        s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z) := by
  -- Split the mixed weighted residue finset into the disjoint noninteger-pole part `s` and the
  -- enclosed integer image, then simplify the piecewise residue value on each summand.
  classical
  dsimp
  let integerSet : Finset ℂ :=
    Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueValue : ℂ → ℂ := fun z ↦
    if hz : z ∈ s then residue z * exercise25WeightedKernel alpha z
    else if hzInt : z ∈ integerSet then
      (Complex.exp (Complex.I * (alpha : ℂ) * z) /
        Complex.cos ((Real.pi : ℂ) * z)) *
        (P.eval z / Q.eval z)
    else 0
  have hdisj : Disjoint s integerSet := by
    rw [Finset.disjoint_left]
    intro z hzS hzI
    apply hnonint z hzS
    rcases Finset.mem_image.mp hzI with ⟨p, hp, rfl⟩
    exact ⟨p, rfl⟩
  have hs_sum :
      Finset.sum s residueValue = s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z) := by
    -- On `s`, the first branch of the weighted residue value is the only surviving one.
    refine Finset.sum_congr rfl ?_
    intro z hz
    simp [residueValue, hz]
  have hi_sum :
      Finset.sum integerSet residueValue =
        Finset.sum integerSet (fun z ↦
          (Complex.exp (Complex.I * (alpha : ℂ) * z) /
            Complex.cos ((Real.pi : ℂ) * z)) *
            (P.eval z / Q.eval z)) := by
    -- On the integer image, disjointness turns off the noninteger residue branch.
    refine Finset.sum_congr rfl ?_
    intro z hz
    have hz_not_s : z ∉ s := by
      intro hzS
      exact (Finset.disjoint_left.mp hdisj) hzS hz
    simp [residueValue, hz_not_s, hz]
  have himage :
      Finset.sum integerSet (fun z ↦
        (Complex.exp (Complex.I * (alpha : ℂ) * z) /
          Complex.cos ((Real.pi : ℂ) * z)) *
          (P.eval z / Q.eval z)) =
        Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ)) (fun p ↦
          (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
            Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
              (P.eval (p : ℂ) / Q.eval (p : ℂ))) := by
    -- Reindex the weighted integer-image sum back to the original interval of integers.
    dsimp [integerSet]
    refine Finset.sum_image (f := fun p ↦
      (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
        Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
        (P.eval (p : ℂ) / Q.eval (p : ℂ)))
      (g := fun p : ℤ ↦ (p : ℂ))
      (s := Finset.Icc (-((m : ℤ))) (m : ℤ)) ?_
    intro a ha b hb hab
    exact Int.cast_injective hab
  calc
    Finset.sum (s ∪ integerSet) residueValue =
        Finset.sum s residueValue + Finset.sum integerSet residueValue := by
      simpa [integerSet] using Finset.sum_union hdisj
    _ = s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z) +
          Finset.sum integerSet (fun z ↦
            (Complex.exp (Complex.I * (alpha : ℂ) * z) /
              Complex.cos ((Real.pi : ℂ) * z)) *
              (P.eval z / Q.eval z)) := by
      rw [hs_sum, hi_sum]
    _ = s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z) +
          Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ)) (fun p ↦
            (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
              Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                (P.eval (p : ℂ) / Q.eval (p : ℂ))) := by
      rw [himage]
    _ =
        Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ)) (fun p ↦
          (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
            Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
              (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
          s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z) := by
      simpa [add_comm, add_left_comm, add_assoc]

/-- Helper for Cartan section12 0038_Exercise_25: on a sufficiently large square boundary, the
residue theorem for `(P / Q)(z) κα(z)` splits into the weighted integer residues inside the square
and the prescribed noninteger residues coming from `s`. -/
lemma exercise25_weightedSquareBoundary_curveIntegral_eq_two_pi_I_mul_sum
    (alpha : ℝ) (P Q : Polynomial ℂ) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        ∫ᶜ z in exercise25SquareBoundary (n + N),
            ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z =
          (2 * Real.pi * Complex.I : ℂ) *
            (Finset.sum
                (Finset.Icc (-(((n + N : ℕ) : ℤ))) (((n + N : ℕ) : ℤ)))
                (fun p ↦
                  (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                    Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                      (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
              s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z)) := by
  -- Run the same square-boundary residue theorem as in the unweighted case, but swap in the
  -- weighted kernel and the corresponding mixed local residue data.
  obtain ⟨N, hinside⟩ := exercise25_polesEventuallyInSquareInterior s
  refine ⟨N, ?_⟩
  intro n
  let m : ℕ := n + N
  let K : Set ℂ :=
    Complex.Rectangle
      (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
      ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I)
  let D : Set ℂ :=
    {z : ℂ |
      |z.re| < exercise25SquareRadius m + 1 / 4 ∧
        |z.im| < exercise25SquareRadius m + 1 / 4}
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (exercise25SquareBoundary m).toClosedPath
  let gNF : ℂ → ℂ := toMeromorphicNFOn (fun w ↦ P.eval w / Q.eval w) Set.univ
  let integerSet : Finset ℂ :=
    Finset.image (fun p : ℤ ↦ (p : ℂ)) (Finset.Icc (-((m : ℤ))) (m : ℤ))
  let residueSet : Finset ℂ := s ∪ integerSet
  let residueValue : ℂ → ℂ := fun z ↦
    if hz : z ∈ s then residue z * exercise25WeightedKernel alpha z
    else if hzInt : z ∈ integerSet then
      (Complex.exp (Complex.I * (alpha : ℂ) * z) /
        Complex.cos ((Real.pi : ℂ) * z)) *
        (P.eval z / Q.eval z)
    else 0
  have hK :
      K =
        Complex.Rectangle
          (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
          ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I) := rfl
  have hD :
      D =
        {z : ℂ |
          |z.re| < exercise25SquareRadius m + 1 / 4 ∧
            |z.im| < exercise25SquareRadius m + 1 / 4} := rfl
  have hΓ :
      IsOrientedBoundaryOf K Γ := by
    have hr_pos : 0 < exercise25SquareRadius m := by
      dsimp [exercise25SquareRadius]
      positivity
    have hRe :
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I).re <
          ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I).re := by
      simp
      linarith
    have hIm :
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I).im <
          ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I).im := by
      simp
      linarith
    simpa [K, Γ, exercise25SquareBoundary] using
      axisParallelRectangleBoundary_isOrientedBoundaryOf
        (-(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I)
        ((exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I)
        hRe hIm
  have hKD : K ⊆ D := by
    simpa [K, D] using exercise25_squareRectangle_subset_thickenedNeighborhood m
  have hDopen : IsOpen D := by
    refine
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hsK : (↑s : Set ℂ) ⊆ interior K := by
    intro z hz
    have hzBounds : |z.re| < exercise25SquareRadius m ∧ |z.im| < exercise25SquareRadius m :=
      hinside n z hz
    rw [hK, Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
    simpa
      [Set.uIcc_of_le (by
        dsimp [exercise25SquareRadius]
        linarith : -(exercise25SquareRadius m) ≤ exercise25SquareRadius m), interior_Icc] using
      (show z.re ∈ Set.Ioo (-(exercise25SquareRadius m)) (exercise25SquareRadius m) ∧
          z.im ∈ Set.Ioo (-(exercise25SquareRadius m)) (exercise25SquareRadius m) from
        ⟨abs_lt.mp hzBounds.1, abs_lt.mp hzBounds.2⟩)
  have hhol :
      DifferentiableOn ℂ
        (fun w ↦ gNF w * exercise25WeightedKernel alpha w)
        (D \ (↑residueSet : Set ℂ)) := by
    simpa [D, gNF, integerSet, residueSet, m] using
      exercise25_squareNeighborhood_weightedKernelProduct_differentiableOn
        alpha P Q hpoles m
  have hres :
      ∀ z ∈ residueSet,
        IsolatedLocalResidueCircle K D residueSet
          (fun w ↦ gNF w * exercise25WeightedKernel alpha w) z (residueValue z) := by
    simpa [K, D, gNF, integerSet, residueSet, residueValue, m] using
      exercise25_squareWeightedProduct_isolatedResidueData
        alpha P Q hpoles hnonint hsimple hdenom_int residue hresidue hK hD hsK
  have hboundary_nf :
      ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ gNF w * exercise25WeightedKernel alpha w) dz) z =
        (2 * Real.pi * Complex.I : ℂ) * Finset.sum residueSet residueValue := by
    have hboundary_disjoint :
        ∀ i : Unit, Disjoint (Set.range (Γ i).toPath) (↑residueSet : Set ℂ) := by
      intro i
      refine Set.disjoint_left.mpr ?_
      intro z hzΓ hzRes
      rcases Finset.mem_union.mp hzRes with hzS | hzInt
      · have hzInterior : z ∈ interior K := hsK hzS
        exact
          (mem_interior_iff_notMem_frontier (interior_subset hzInterior)).1 hzInterior
            (hΓ.range_toPath_subset_frontier i hzΓ)
      · rcases Finset.mem_image.mp hzInt with ⟨p, hp, rfl⟩
        exact
          exercise25_sin_pi_ne_zero_on_square_boundary m (by simpa [Γ] using hzΓ) <| by
            simpa [mul_comm] using Complex.sin_int_mul_pi p
    exact
      orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
        (Γ := Γ) (K := K) (D := D)
        (f := fun w ↦ gNF w * exercise25WeightedKernel alpha w)
        (s := residueSet) (residue := residueValue)
        hΓ hKD hDopen hboundary_disjoint hhol hres
  have hsum_split :
      Finset.sum residueSet residueValue =
        Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ)) (fun p ↦
          (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
            Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
              (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
          s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z) := by
    simpa [integerSet, residueSet, residueValue, m] using
      exercise25_squareWeightedResidueSet_sum_split alpha P Q (s := s) m hnonint residue
  calc
    ∫ᶜ z in exercise25SquareBoundary m,
        ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z =
      ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ gNF w * exercise25WeightedKernel alpha w) dz) z := by
        simpa [m] using
          (exercise25_squareBoundary_normalForm_boundaryTransfer
            P Q m (exercise25WeightedKernel alpha)).symm
    _ = (2 * Real.pi * Complex.I : ℂ) * Finset.sum residueSet residueValue := hboundary_nf
    _ =
        (2 * Real.pi * Complex.I : ℂ) *
          (Finset.sum (Finset.Icc (-((m : ℤ))) (m : ℤ)) (fun p ↦
            (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
              Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
            s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z)) := by
      rw [hsum_split]
    _ =
        (2 * Real.pi * Complex.I : ℂ) *
          (Finset.sum (Finset.Icc (-(((n + N : ℕ) : ℤ))) (((n + N : ℕ) : ℤ))) (fun p ↦
            (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
              Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
            s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z)) := by
      simp [m]

/-- Helper for Cartan section12 0038_Exercise_25: when `deg Q ≥ deg P + 2`, the weighted square
contour integrals with kernel `κα(z) = π exp(i α z) / sin(π z)` are curve-integrable on a common
tail and tend to `0`. -/
lemma exercise25_rational_weighted_contour_integral_tendsto_zero_of_degree_gap_two_aux
    (alpha : ℝ) (halpha_left : -Real.pi < alpha) (halpha_right : alpha < Real.pi)
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ N : ℕ,
      (∀ n : ℕ,
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
          (exercise25SquareBoundary (n + N))) ∧
      Tendsto
        (fun n : ℕ ↦
          ∫ᶜ z in exercise25SquareBoundary (n + N),
            ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z)
        atTop (𝓝 0) := by
  obtain ⟨NQ, hQnz⟩ := exercise25_square_boundary_denominator_nonzero_eventually P Q hdeg
  obtain ⟨M2, hM2pos, hM2⟩ :=
    exercise25_exp_div_sin_norm_bounded_on_square_boundaries alpha halpha_left halpha_right
  obtain ⟨K, R, hKR, hdecayRat⟩ := exercise25_rational_decay_of_degree_gap_two P Q hdeg
  let Ndecay : ℕ := Nat.ceil R
  let N : ℕ := max NQ Ndecay
  let C : ℝ := K * ((Real.pi : ℝ) * M2)
  have hsides :
      ∀ n : ℕ,
        let z₀ : ℂ := -(exercise25SquareRadius (n + NQ) : ℂ) -
          exercise25SquareRadius (n + NQ) * Complex.I
        let w : ℂ := (exercise25SquareRadius (n + NQ) : ℂ) +
          exercise25SquareRadius (n + NQ) * Complex.I
        let zw : ℂ := Complex.mk w.re z₀.im
        let wz : ℂ := Complex.mk z₀.re w.im
        CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
            (Path.segment z₀ zw) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
            (Path.segment zw w) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
            (Path.segment w wz) ∧
          CurveIntegrable
            ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
            (Path.segment wz z₀) := by
    intro n
    let D : Set ℂ := Set.range (exercise25SquareBoundary (n + NQ))
    let z₀ : ℂ := -(exercise25SquareRadius (n + NQ) : ℂ) -
      exercise25SquareRadius (n + NQ) * Complex.I
    let w : ℂ := (exercise25SquareRadius (n + NQ) : ℂ) +
      exercise25SquareRadius (n + NQ) * Complex.I
    let zw : ℂ := Complex.mk w.re z₀.im
    let wz : ℂ := Complex.mk z₀.re w.im
    have hrat :
        ContinuousOn (fun z ↦ P.eval z / Q.eval z) D := by
      -- The rational factor is continuous once the denominator has no boundary zeros.
      refine ContinuousOn.div P.continuous.continuousOn Q.continuous.continuousOn ?_
      intro z hz
      exact hQnz n z hz
    have hweighted : ContinuousOn (exercise25WeightedKernel alpha) D := by
      intro z hz
      have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
        exercise25_sin_pi_ne_zero_on_square_boundary (n + NQ) hz
      have hz_notint : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)) := by
        intro hzInt
        rcases hzInt with ⟨p, rfl⟩
        exact hsin <| by simpa [mul_comm] using Complex.sin_int_mul_pi p
      exact (exercise25_weightedKernel_continuousAt_of_not_integer alpha hz_notint).continuousWithinAt
    have hcoeff :
        ContinuousOn (fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) D := by
      -- Multiply the regular rational factor by the weighted kernel.
      exact hrat.mul hweighted
    have hform :
        ContinuousOn
          (fun z ↦
            (((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z)) D := by
      -- Package the scalar coefficient as a continuous complex-linear one-form.
      simpa [Complex.scalarOneForm] using
        (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
          ((continuousOn_const :
            ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hcoeff)
    have hsubsets := exercise25_square_boundary_side_ranges_subset (n + NQ)
    dsimp [z₀, w, zw, wz] at hsubsets
    rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
    have hbottom_int :
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
          (Path.segment z₀ zw) :=
      hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
        (fun t ↦ hbottom_subset ⟨t, rfl⟩)
    have hright_int :
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
          (Path.segment zw w) :=
      hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
        (fun t ↦ hright_subset ⟨t, rfl⟩)
    have htop_int :
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
          (Path.segment w wz) :=
      hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
        (fun t ↦ htop_subset ⟨t, rfl⟩)
    have hleft_int :
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
          (Path.segment wz z₀) :=
      hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
        (fun t ↦ hleft_subset ⟨t, rfl⟩)
    -- Record the four side integrability statements for the later ML estimate.
    simpa [z₀, w, zw, wz] using ⟨hbottom_int, hright_int, htop_int, hleft_int⟩
  have hcontour :
      ∀ n : ℕ,
        CurveIntegrable
          ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
          (exercise25SquareBoundary (n + NQ)) := by
    intro n
    let z₀ : ℂ := -(exercise25SquareRadius (n + NQ) : ℂ) -
      exercise25SquareRadius (n + NQ) * Complex.I
    let w : ℂ := (exercise25SquareRadius (n + NQ) : ℂ) +
      exercise25SquareRadius (n + NQ) * Complex.I
    let zw : ℂ := Complex.mk w.re z₀.im
    let wz : ℂ := Complex.mk z₀.re w.im
    rcases hsides n with ⟨hbottom_int, hright_int, htop_int, hleft_int⟩
    -- Glue the four affine sides back into the square contour.
    simpa [exercise25SquareBoundary, z₀, w, zw, wz, axisParallelRectangleBoundaryPath] using
      (CurveIntegrable.trans hbottom_int
        (CurveIntegrable.trans hright_int
          (CurveIntegrable.trans htop_int hleft_int)))
  have hdecay :
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary (n + Ndecay)),
        ‖P.eval z / Q.eval z * exercise25WeightedKernel alpha z‖ ≤
          C / exercise25SquareRadius (n + Ndecay) ^ (2 : ℕ) := by
    intro n z hz
    let r : ℝ := exercise25SquareRadius (n + Ndecay)
    have hr_le_norm : r ≤ ‖z‖ := (exercise25_square_boundary_geometry (n + Ndecay) hz).2.2.2
    have hR_le_r : R ≤ r := by
      -- The chosen shift `Ndecay` moves every later square past the global decay radius `R`.
      have hceil : R ≤ Ndecay := Nat.le_ceil R
      have hN_le_nat : Ndecay ≤ n + Ndecay := Nat.le_add_left Ndecay n
      have hN_le_real : (Ndecay : ℝ) ≤ (n + Ndecay : ℕ) := by
        exact_mod_cast hN_le_nat
      dsimp [r, exercise25SquareRadius]
      linarith
    have hzR : R ≤ ‖z‖ := hR_le_r.trans hr_le_norm
    have hrat :
        ‖P.eval z / Q.eval z‖ ≤ K / ‖z‖ ^ (2 : ℕ) := hdecayRat z hzR
    have hkernel :
        ‖exercise25WeightedKernel alpha z‖ ≤ (Real.pi : ℝ) * M2 := by
      have hM2z :=
        hM2 (n + Ndecay) z hz
      calc
        ‖exercise25WeightedKernel alpha z‖
            = ‖(Real.pi : ℂ)‖ *
                ‖Complex.exp (Complex.I * (alpha : ℂ) * z) /
                  Complex.sin ((Real.pi : ℂ) * z)‖ := by
                simpa [exercise25WeightedKernel, div_eq_mul_inv, mul_assoc] using
                  (norm_mul (Real.pi : ℂ)
                    (Complex.exp (Complex.I * (alpha : ℂ) * z) /
                      Complex.sin ((Real.pi : ℂ) * z)))
        _ ≤ (Real.pi : ℝ) * M2 := by
              simpa [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] using
                mul_le_mul_of_nonneg_left hM2z Real.pi_pos.le
    have hcoeff :
        ‖P.eval z / Q.eval z * exercise25WeightedKernel alpha z‖ ≤
          (K / ‖z‖ ^ (2 : ℕ)) * ((Real.pi : ℝ) * M2) := by
      calc
        ‖P.eval z / Q.eval z * exercise25WeightedKernel alpha z‖
            ≤ ‖P.eval z / Q.eval z‖ * ‖exercise25WeightedKernel alpha z‖ := norm_mul_le _ _
        _ ≤ (K / ‖z‖ ^ (2 : ℕ)) * ((Real.pi : ℝ) * M2) := by
              nlinarith [hrat, hkernel, norm_nonneg (P.eval z / Q.eval z),
                norm_nonneg (exercise25WeightedKernel alpha z)]
    have hrpow_pos : 0 < r ^ (2 : ℕ) := by
      dsimp [r, exercise25SquareRadius]
      positivity
    have hr_nonneg : 0 ≤ r := by
      dsimp [r, exercise25SquareRadius]
      positivity
    have hnormpow_ge : r ^ (2 : ℕ) ≤ ‖z‖ ^ (2 : ℕ) := by
      simpa using
        (pow_le_pow_left₀ (a := r) (b := ‖z‖) hr_nonneg hr_le_norm 2)
    have hdiv :
        K / ‖z‖ ^ (2 : ℕ) ≤ K / r ^ (2 : ℕ) := by
      have hK_nonneg : 0 ≤ K := (lt_min_iff.mp hKR).1.le
      have hinv :
          (‖z‖ ^ (2 : ℕ))⁻¹ ≤ (r ^ (2 : ℕ))⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hrpow_pos hnormpow_ge
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hinv hK_nonneg
    calc
      ‖P.eval z / Q.eval z * exercise25WeightedKernel alpha z‖
          ≤ (K / ‖z‖ ^ (2 : ℕ)) * ((Real.pi : ℝ) * M2) := hcoeff
      _ ≤ (K / r ^ (2 : ℕ)) * ((Real.pi : ℝ) * M2) := by
            exact mul_le_mul_of_nonneg_right hdiv (by positivity)
      _ = C / r ^ (2 : ℕ) := by
            dsimp [C]
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring
      _ = C / exercise25SquareRadius (n + Ndecay) ^ (2 : ℕ) := by rfl
  refine ⟨N, (fun n ↦ ?_), ?_⟩
  · let m : ℕ := n + (N - NQ)
    have hidx : m + NQ = n + N := by
      dsimp [m, N]
      omega
    -- Rewrite the contour-integrability tail to the common shift `N`.
    rw [← hidx]
    exact hcontour m
  · have hbound :
        ∀ n : ℕ,
          ‖∫ᶜ z in exercise25SquareBoundary (n + N),
              ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z‖ ≤
            8 * C / exercise25SquareRadius (n + N) := by
      intro n
      let ms : ℕ := n + (N - NQ)
      let md : ℕ := n + (N - Ndecay)
      have hidxs : ms + NQ = n + N := by
        dsimp [ms, N]
        omega
      have hidxd : md + Ndecay = n + N := by
        dsimp [md, N]
        omega
      have hsidesN :
          let z₀ : ℂ := -(exercise25SquareRadius (n + N) : ℂ) -
            exercise25SquareRadius (n + N) * Complex.I
          let w : ℂ := (exercise25SquareRadius (n + N) : ℂ) +
            exercise25SquareRadius (n + N) * Complex.I
          let zw : ℂ := Complex.mk w.re z₀.im
          let wz : ℂ := Complex.mk z₀.re w.im
          CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
              (Path.segment z₀ zw) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
              (Path.segment zw w) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
              (Path.segment w wz) ∧
            CurveIntegrable
              ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
              (Path.segment wz z₀) := by
        -- The four side integrability statements are unchanged after rewriting the index.
        rw [← hidxs]
        exact hsides ms
      have hdecayN :
          ∀ z ∈ Set.range (exercise25SquareBoundary (n + N)),
            ‖P.eval z / Q.eval z * exercise25WeightedKernel alpha z‖ ≤
              C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by
        intro z hz
        -- Transport the pointwise weighted decay estimate to the common contour.
        rw [← hidxd] at hz ⊢
        exact hdecay md z hz
      exact exercise25_square_boundary_norm_curveIntegral_le
        (n := n + N) (C := C) hsidesN hdecayN
    have hradius :
        Tendsto (fun n : ℕ ↦ exercise25SquareRadius (n + N)) atTop atTop := by
      -- The square radius is linear in `n`, so its reciprocal vanishes.
      simpa [exercise25SquareRadius, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
        (tendsto_atTop_add_const_right atTop ((N : ℝ) + (1 / 2 : ℝ))
          tendsto_natCast_atTop_atTop)
    have htail :
        Tendsto (fun n : ℕ ↦ 8 * C / exercise25SquareRadius (n + N)) atTop (𝓝 0) := by
      have hinv :
          Tendsto (fun n : ℕ ↦ (exercise25SquareRadius (n + N))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hradius
      simpa [div_eq_mul_inv, mul_assoc] using
        (tendsto_const_nhds.mul hinv :
          Tendsto
            (fun n : ℕ ↦ (8 * C) * (exercise25SquareRadius (n + N))⁻¹)
            atTop (𝓝 ((8 * C) * 0)))
    -- Squeeze the weighted contour integrals between the ML bound and the vanishing reciprocal.
    exact squeeze_zero_norm hbound htail

/-- Helper for Cartan section12 0038_Exercise_25: the weighted correction integrand
`κα(z) / z = π exp(i α z) / (z sin(π z))` is regular on every square boundary `γ_n`. -/
lemma exercise25_weightedKernelDivZ_continuousOn_squareBoundary
    (alpha : ℝ) (n : ℕ) :
    ContinuousOn (fun z ↦ exercise25WeightedKernel alpha z / z)
      (Set.range (exercise25SquareBoundary n)) := by
  intro z hz
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    exercise25_sin_pi_ne_zero_on_square_boundary n hz
  have hz_ne : z ≠ 0 := by
    intro hz0
    subst hz0
    simpa using hsin
  have hz_notint : z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)) := by
    intro hzint
    rcases hzint with ⟨p, rfl⟩
    exact hsin <| by simpa [mul_comm] using Complex.sin_int_mul_pi p
  -- On the square boundary, both the weighted kernel and the extra divisor `z` stay regular.
  have hcont :
      ContinuousAt (fun z ↦ exercise25WeightedKernel alpha z / z) z := by
    simpa using
      (exercise25_weightedKernel_continuousAt_of_not_integer alpha hz_notint).div
        continuousAt_id hz_ne
  exact hcont.continuousWithinAt

/-- Helper for Cartan section12 0038_Exercise_25: the scalar one-form attached to the weighted
correction integrand is continuous along every square boundary. -/
lemma exercise25_weightedKernelDivZ_oneForm_continuousOn_squareBoundary
    (alpha : ℝ) (n : ℕ) :
    ContinuousOn
      (fun z ↦ (((fun z ↦ exercise25WeightedKernel alpha z / z) dz) z))
      (Set.range (exercise25SquareBoundary n)) := by
  simpa [Complex.scalarOneForm] using
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
      ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) _).prodMk
        (exercise25_weightedKernelDivZ_continuousOn_squareBoundary alpha n))

/-- Helper for Cartan section12 0038_Exercise_25: the weighted correction integrand
`κα(z) / z = π exp(i α z) / (z sin(π z))` is regular on every square boundary `γ_n`. -/
lemma exercise25_weightedKernelDivZ_squareCurveIntegrable
    (alpha : ℝ) (n : ℕ) :
    CurveIntegrable ((fun z ↦ exercise25WeightedKernel alpha z / z) dz) (exercise25SquareBoundary n) := by
  let φ : ℂ → ℂ := fun z ↦ exercise25WeightedKernel alpha z / z
  let r : ℝ := exercise25SquareRadius n
  let z₀ : ℂ := -(r : ℂ) - r * Complex.I
  let w : ℂ := (r : ℂ) + r * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  let D : Set ℂ := Set.range (exercise25SquareBoundary n)
  have hcoeff : ContinuousOn φ D := by
    simpa [D, φ] using exercise25_weightedKernelDivZ_continuousOn_squareBoundary alpha n
  have hform :
      ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z)) D := by
    -- Package the scalar coefficient as a continuous complex-linear one-form on the contour.
    simpa [Complex.scalarOneForm] using
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
        ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hcoeff)
  have hsubsets := exercise25_square_boundary_side_ranges_subset n
  dsimp [z₀, w, zw, wz] at hsubsets
  rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
  have hbottom_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
      (fun t ↦ hbottom_subset ⟨t, rfl⟩)
  have hright_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
      (fun t ↦ hright_subset ⟨t, rfl⟩)
  have htop_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
      (fun t ↦ htop_subset ⟨t, rfl⟩)
  have hleft_int :
      CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀) :=
    hform.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
      (fun t ↦ hleft_subset ⟨t, rfl⟩)
  have hboundary_eq :
      exercise25SquareBoundary n =
        (Path.segment z₀ zw).trans
          ((Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀))) := by
    rw [exercise25SquareBoundary, axisParallelRectangleBoundaryPath]
  rw [hboundary_eq]
  exact CurveIntegrable.trans hbottom_int
    (CurveIntegrable.trans hright_int (CurveIntegrable.trans htop_int hleft_int))

/-- Helper for Cartan section12 0038_Exercise_25: pairing opposite sides of the weighted
correction integrand replaces `exp(i α z)` by the odd numerator `2 i sin(α z)`. -/
lemma exercise25_weightedKernelDivZ_sub_neg
    (alpha : ℝ) (z : ℂ) :
    exercise25WeightedKernel alpha z / z - exercise25WeightedKernel alpha (-z) / (-z) =
      (2 * Real.pi * Complex.I : ℂ) *
        (Complex.sin ((alpha : ℂ) * z) / (z * Complex.sin ((Real.pi : ℂ) * z))) := by
  have hnegExp :
      Complex.exp (-(((alpha : ℂ) * z) * Complex.I)) =
        Complex.cos (-((alpha : ℂ) * z)) + Complex.sin (-((alpha : ℂ) * z)) * Complex.I := by
    simpa using (Complex.exp_mul_I (-((alpha : ℂ) * z)))
  have hexp :
      Complex.exp (Complex.I * (alpha : ℂ) * z) -
          Complex.exp (-Complex.I * (alpha : ℂ) * z) =
        2 * Complex.sin ((alpha : ℂ) * z) * Complex.I := by
    calc
      Complex.exp (Complex.I * (alpha : ℂ) * z) -
          Complex.exp (-Complex.I * (alpha : ℂ) * z)
          =
          Complex.exp (((alpha : ℂ) * z) * Complex.I) -
            Complex.exp (-(((alpha : ℂ) * z) * Complex.I)) := by
              ring_nf
      _ =
          (Complex.cos ((alpha : ℂ) * z) + Complex.sin ((alpha : ℂ) * z) * Complex.I) -
            (Complex.cos (-((alpha : ℂ) * z)) +
              Complex.sin (-((alpha : ℂ) * z)) * Complex.I) := by
              rw [Complex.exp_mul_I, hnegExp]
      _ = 2 * Complex.sin ((alpha : ℂ) * z) * Complex.I := by
            simp [Complex.cos_neg, Complex.sin_neg]
            ring
  calc
    exercise25WeightedKernel alpha z / z - exercise25WeightedKernel alpha (-z) / (-z)
        =
        (Real.pi : ℂ) *
          (Complex.exp (Complex.I * (alpha : ℂ) * z) -
            Complex.exp (-Complex.I * (alpha : ℂ) * z)) /
          (z * Complex.sin ((Real.pi : ℂ) * z)) := by
            simp [exercise25WeightedKernel, div_eq_mul_inv, Complex.sin_neg, mul_assoc,
              mul_left_comm, mul_comm]
            ring
    _ =
        (2 * Real.pi * Complex.I : ℂ) *
          (Complex.sin ((alpha : ℂ) * z) / (z * Complex.sin ((Real.pi : ℂ) * z))) := by
            rw [hexp]
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Cartan section12 0038_Exercise_25: the symmetric exponential weight
`exp (-k |2 t - 1|)` has interval integral at most `1 / k` on `[0, 1]`. -/
lemma exercise25_intervalIntegral_exp_abs_affine_le_inv
    {k : ℝ} (hk : 0 < k) :
    ∫ t in (0 : ℝ)..1, Real.exp (-k * |2 * t - 1|) ≤ 1 / k := by
  let f : ℝ → ℝ := fun x ↦ Real.exp (-k * x)
  have hzero_half : (0 : ℝ) ≤ (1 / 2 : ℝ) := by
    norm_num
  have hhalf_one : (1 / 2 : ℝ) ≤ (1 : ℝ) := by
    norm_num
  have hleft :
      ∫ t in (0 : ℝ)..(1 / 2 : ℝ), Real.exp (-k * |2 * t - 1|) =
        (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
    have habs :
        ∫ t in (0 : ℝ)..(1 / 2 : ℝ), Real.exp (-k * |2 * t - 1|) =
          ∫ t in (0 : ℝ)..(1 / 2 : ℝ), f ((-2 : ℝ) * t + 1) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht_mem : t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := by
        simpa [Set.uIcc_of_le hzero_half] using ht
      have hneg : 2 * t - 1 ≤ 0 := by
        nlinarith [ht_mem.2]
      have habs' : |2 * t - 1| = (-2 : ℝ) * t + 1 := by
        rw [abs_of_nonpos hneg]
        ring
      simpa [f, habs']
    have hsub :
        (-2 : ℝ) * ∫ t in (0 : ℝ)..(1 / 2 : ℝ), f ((-2 : ℝ) * t + 1) =
          ∫ x in (1 : ℝ)..0, f x := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
        mul_comm] using
        (intervalIntegral.smul_integral_comp_mul_add (f := f)
          (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (c := (-2 : ℝ)) (d := (1 : ℝ)))
    have hsub' :
        (2 : ℝ) * ∫ t in (0 : ℝ)..(1 / 2 : ℝ), f ((-2 : ℝ) * t + 1) =
          ∫ x in (0 : ℝ)..1, f x := by
      have hnegmul := congrArg (fun y : ℝ ↦ -y) hsub
      have hsymm : ∫ x in (1 : ℝ)..0, f x = -∫ x in (0 : ℝ)..1, f x := by
        rw [intervalIntegral.integral_symm]
      calc
        (2 : ℝ) * ∫ t in (0 : ℝ)..(1 / 2 : ℝ), f ((-2 : ℝ) * t + 1) =
            -((-2 : ℝ) * ∫ t in (0 : ℝ)..(1 / 2 : ℝ), f ((-2 : ℝ) * t + 1)) := by
              ring
        _ = -(∫ x in (1 : ℝ)..0, f x) := hnegmul
        _ = ∫ x in (0 : ℝ)..1, f x := by
              nlinarith [hsymm]
    have hhalf :
        ∫ t in (0 : ℝ)..(1 / 2 : ℝ), f ((-2 : ℝ) * t + 1) =
          (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
      nlinarith [hsub']
    exact habs.trans hhalf
  have hright :
      ∫ t in (1 / 2 : ℝ)..1, Real.exp (-k * |2 * t - 1|) =
        (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
    have habs :
        ∫ t in (1 / 2 : ℝ)..1, Real.exp (-k * |2 * t - 1|) =
          ∫ t in (1 / 2 : ℝ)..1, f ((2 : ℝ) * t - 1) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have ht_mem : t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
        have ht' := ht
        rw [Set.uIcc_of_le hhalf_one] at ht'
        exact ht'
      have hnonneg : 0 ≤ 2 * t - 1 := by
        nlinarith [ht_mem.1]
      simpa [f, abs_of_nonneg hnonneg]
    have hsub :
        (2 : ℝ) * ∫ t in (1 / 2 : ℝ)..1, f ((2 : ℝ) * t - 1) =
          ∫ x in (0 : ℝ)..1, f x := by
      have hcomp :
          (2 : ℝ) * ∫ t in (1 / 2 : ℝ)..1, f ((2 : ℝ) * t + (-1 : ℝ)) =
            ∫ x in ((2 : ℝ) * (1 / 2 : ℝ) + (-1 : ℝ))..((2 : ℝ) * (1 : ℝ) + (-1 : ℝ)), f x := by
        simpa using
          (intervalIntegral.smul_integral_comp_mul_add (f := f)
            (a := (1 / 2 : ℝ)) (b := (1 : ℝ)) (c := (2 : ℝ)) (d := (-1 : ℝ)))
      have hintegrand :
          ∫ t in (1 / 2 : ℝ)..1, f ((2 : ℝ) * t - 1) =
            ∫ t in (1 / 2 : ℝ)..1, f ((2 : ℝ) * t + (-1 : ℝ)) := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        simp [sub_eq_add_neg]
      calc
        (2 : ℝ) * ∫ t in (1 / 2 : ℝ)..1, f ((2 : ℝ) * t - 1) =
            (2 : ℝ) * ∫ t in (1 / 2 : ℝ)..1, f ((2 : ℝ) * t + (-1 : ℝ)) := by
              rw [hintegrand]
        _ = ∫ x in ((2 : ℝ) * (1 / 2 : ℝ) + (-1 : ℝ))..((2 : ℝ) * (1 : ℝ) + (-1 : ℝ)), f x :=
              hcomp
        _ = ∫ x in (0 : ℝ)..1, f x := by
              norm_num
    have hhalf :
        ∫ t in (1 / 2 : ℝ)..1, f ((2 : ℝ) * t - 1) =
          (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
      nlinarith [hsub]
    exact habs.trans hhalf
  have hcont : Continuous (fun t : ℝ ↦ Real.exp (-k * |2 * t - 1|)) := by
    fun_prop
  have hsplit :
      ∫ x in (0 : ℝ)..1, Real.exp (-k * |2 * x - 1|) =
        ∫ x in (0 : ℝ)..(1 / 2 : ℝ), Real.exp (-k * |2 * x - 1|) +
          ∫ x in (1 / 2 : ℝ)..1, Real.exp (-k * |2 * x - 1|) := by
    have hsplit' :=
      intervalIntegral.integral_add_adjacent_intervals
        (μ := MeasureTheory.volume)
        (f := fun x : ℝ ↦ Real.exp (-k * |2 * x - 1|))
        (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (c := (1 : ℝ))
        (hcont.intervalIntegrable (0 : ℝ) (1 / 2 : ℝ))
        (hcont.intervalIntegrable (1 / 2 : ℝ) 1)
    simpa [add_assoc] using hsplit'.symm
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hmain :
      ∫ x in (0 : ℝ)..1, f x = (1 - Real.exp (-k)) / k := by
    have hsub :
        (-k : ℝ) * ∫ x in (0 : ℝ)..1, Real.exp (-k * x) =
          ∫ y in (0 : ℝ)..(-k), Real.exp y := by
      simpa [f] using
        (intervalIntegral.smul_integral_comp_mul_add
          (f := fun y : ℝ ↦ Real.exp y) (a := (0 : ℝ)) (b := (1 : ℝ))
          (c := (-k : ℝ)) (d := (0 : ℝ)))
    rw [integral_exp] at hsub
    have hsub' : (∫ x in (0 : ℝ)..1, f x) * k = 1 - Real.exp (-k) := by
      have hsub'' : -(k * ∫ x in (0 : ℝ)..1, f x) = Real.exp (-k) - 1 := by
        simpa [f, mul_comm, mul_left_comm, mul_assoc] using hsub
      nlinarith [hsub'']
    exact (eq_div_iff hk0).2 hsub'
  calc
    ∫ t in (0 : ℝ)..1, Real.exp (-k * |2 * t - 1|)
        = ∫ t in (0 : ℝ)..(1 / 2 : ℝ), Real.exp (-k * |2 * t - 1|) +
            ∫ t in (1 / 2 : ℝ)..1, Real.exp (-k * |2 * t - 1|) := by
              simpa using hsplit
    _ = (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, f x +
          (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
          simpa [hleft, hright]
    _ = ∫ x in (0 : ℝ)..1, f x := by
          let I : ℝ := ∫ x in (0 : ℝ)..1, f x
          change (1 / 2 : ℝ) * I + (1 / 2 : ℝ) * I = I
          ring
    _ = (1 - Real.exp (-k)) / k := hmain
    _ ≤ 1 / k := by
          have hnum_le : 1 - Real.exp (-k) ≤ 1 := by
            have hexp_nonneg : 0 ≤ Real.exp (-k) := Real.exp_nonneg (-k)
            linarith
          exact (div_le_div_of_nonneg_right hnum_le hk.le)

/-- Helper for Cartan section12 0038_Exercise_25: the correction contour integrals
`∮_{γ_n} π exp(i α z) / (z sin(π z)) dz` tend to `0` for `-π < α < π`. -/
lemma exercise25_weightedKernelDivZ_squareIntegral_tendsto_zero
    (alpha : ℝ) (halpha_left : -Real.pi < alpha) (halpha_right : alpha < Real.pi) :
    Tendsto
      (fun n : ℕ ↦
        ∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ exercise25WeightedKernel alpha z / z) dz) z)
      atTop (𝓝 0) := by
  let φ : ℂ → ℂ := fun z ↦ exercise25WeightedKernel alpha z / z
  let c : ℝ := Real.pi - |alpha|
  have hc : 0 < c := by
    rw [sub_pos]
    rw [abs_lt]
    exact ⟨by linarith, halpha_right⟩
  have hbound :
      ∀ n : ℕ,
        ‖∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ φ z) dz) z‖ ≤
          8 * Real.pi / (c * exercise25SquareRadius n) +
            (8 * Real.pi / (1 - Real.exp (-Real.pi))) *
              Real.exp (-(c * exercise25SquareRadius n)) := by
    intro n
    let r : ℝ := exercise25SquareRadius n
    let z₀ : ℂ := -(r : ℂ) - r * Complex.I
    let w : ℂ := (r : ℂ) + r * Complex.I
    let zw : ℂ := Complex.mk w.re z₀.im
    let wz : ℂ := Complex.mk z₀.re w.im
    have hphi_int := exercise25_weightedKernelDivZ_squareCurveIntegrable alpha n
    have hsubsets := exercise25_square_boundary_side_ranges_subset n
    dsimp [z₀, w, zw, wz] at hsubsets
    rcases hsubsets with ⟨hbottom_subset, hright_subset, htop_subset, hleft_subset⟩
    have hform :
        ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z))
          (Set.range (exercise25SquareBoundary n)) := by
      simpa [φ] using exercise25_weightedKernelDivZ_oneForm_continuousOn_squareBoundary alpha n
    have hform_bottom :
        ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z)) (Set.range (Path.segment z₀ zw)) := by
      exact hform.mono hbottom_subset
    have hform_right :
        ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z)) (Set.range (Path.segment zw w)) := by
      exact hform.mono hright_subset
    have hform_top :
        ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z)) (Set.range (Path.segment w wz)) := by
      exact hform.mono htop_subset
    have hform_left :
        ContinuousOn (fun z ↦ (((fun z ↦ φ z) dz) z)) (Set.range (Path.segment wz z₀)) := by
      exact hform.mono hleft_subset
    have hbottom_curve :
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment z₀ zw) := by
      exact hform_bottom.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn z₀ zw)
        (fun t ↦ ⟨t, rfl⟩)
    have hright_curve :
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment zw w) := by
      exact hform_right.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn zw w)
        (fun t ↦ ⟨t, rfl⟩)
    have htop_curve :
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment w wz) := by
      exact hform_top.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn w wz)
        (fun t ↦ ⟨t, rfl⟩)
    have hleft_curve :
        CurveIntegrable ((fun z ↦ φ z) dz) (Path.segment wz z₀) := by
      exact hform_left.curveIntegrable_of_contDiffOn (exercise25_segment_contDiffOn wz z₀)
        (fun t ↦ ⟨t, rfl⟩)
    have hbottom_int :
        IntervalIntegrable
          (fun t : ℝ ↦ (((fun z ↦ φ z) dz) (AffineMap.lineMap z₀ zw t)) (zw - z₀))
          MeasureTheory.volume 0 1 := by
      exact (curveIntegrable_segment.mp hbottom_curve)
    have hright_int :
        IntervalIntegrable
          (fun t : ℝ ↦ (((fun z ↦ φ z) dz) (AffineMap.lineMap zw w t)) (w - zw))
          MeasureTheory.volume 0 1 := by
      exact (curveIntegrable_segment.mp hright_curve)
    have htop_int :
        IntervalIntegrable
          (fun t : ℝ ↦ (((fun z ↦ φ z) dz) (AffineMap.lineMap w wz t)) (wz - w))
          MeasureTheory.volume 0 1 := by
      exact (curveIntegrable_segment.mp htop_curve)
    have hleft_int :
        IntervalIntegrable
          (fun t : ℝ ↦ (((fun z ↦ φ z) dz) (AffineMap.lineMap wz z₀ t)) (z₀ - wz))
          MeasureTheory.volume 0 1 := by
      exact (curveIntegrable_segment.mp hleft_curve)
    let ψ : ℂ → ℂ := fun z ↦
      (2 * Real.pi * Complex.I : ℂ) *
        (Complex.sin ((alpha : ℂ) * z) / (z * Complex.sin ((Real.pi : ℂ) * z)))
    have htop_line :
        ∀ t : ℝ, AffineMap.lineMap w wz t = -AffineMap.lineMap z₀ zw t := by
      intro t
      apply Complex.ext <;> simp [AffineMap.lineMap_apply, z₀, w, zw, wz, r] <;> ring
    have hleft_line :
        ∀ t : ℝ, AffineMap.lineMap wz z₀ t = -AffineMap.lineMap zw w t := by
      intro t
      apply Complex.ext <;> simp [AffineMap.lineMap_apply, z₀, w, zw, wz, r] <;> ring
    have htop_diff : wz - w = -(zw - z₀) := by
      apply Complex.ext <;> simp [z₀, w, zw, wz, r]
    have hleft_diff : z₀ - wz = -(w - zw) := by
      apply Complex.ext <;> simp [z₀, w, zw, wz, r]
    have htop_pair :
        ∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z +
            ∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z =
          ∫ᶜ z in Path.segment w wz, ((fun z ↦ ψ z) dz) z := by
      rw [curveIntegral_segment, curveIntegral_segment, curveIntegral_segment]
      have hbottom_eq :
          ∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap z₀ zw t)) (zw - z₀) =
            ∫ t in (0 : ℝ)..1, -((((fun z ↦ φ (-z)) dz) (AffineMap.lineMap w wz t)) (wz - w)) := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        have hline : -(AffineMap.lineMap w wz t) = AffineMap.lineMap z₀ zw t := by
          simpa [htop_line t]
        have hdir : zw - z₀ = -(wz - w) := by
          simpa [htop_diff]
        simp only [Complex.scalarOneForm_apply, φ]
        rw [hline, hdir]
        ring
      have hneg_int :
          IntervalIntegrable
            (fun t : ℝ ↦ -((((fun z ↦ φ (-z)) dz) (AffineMap.lineMap w wz t)) (wz - w)))
            MeasureTheory.volume 0 1 := by
        refine hbottom_int.congr ?_
        intro t ht
        have hline : -(AffineMap.lineMap w wz t) = AffineMap.lineMap z₀ zw t := by
          simpa [htop_line t]
        have hdir : zw - z₀ = -(wz - w) := by
          simpa [htop_diff]
        simp only [Complex.scalarOneForm_apply, φ]
        rw [hline, hdir]
        ring
      rw [hbottom_eq, ← intervalIntegral.integral_add hneg_int htop_int]
      refine intervalIntegral.integral_congr ?_
      intro t ht
      simp only [Complex.scalarOneForm_apply, φ, ψ]
      rw [← exercise25_weightedKernelDivZ_sub_neg alpha (AffineMap.lineMap w wz t)]
      ring
    have hright_pair :
        ∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
            ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z =
          ∫ᶜ z in Path.segment zw w, ((fun z ↦ ψ z) dz) z := by
      rw [curveIntegral_segment, curveIntegral_segment, curveIntegral_segment]
      have hleft_eq :
          ∫ t in (0 : ℝ)..1, (((fun z ↦ φ z) dz) (AffineMap.lineMap wz z₀ t)) (z₀ - wz) =
            ∫ t in (0 : ℝ)..1, -((((fun z ↦ φ (-z)) dz) (AffineMap.lineMap zw w t)) (w - zw)) := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        have hline : -(AffineMap.lineMap zw w t) = AffineMap.lineMap wz z₀ t := by
          simpa [hleft_line t]
        have hdir : z₀ - wz = -(w - zw) := by
          simpa [hleft_diff]
        simp only [Complex.scalarOneForm_apply, φ]
        rw [hline, hdir]
        ring
      have hneg_int :
          IntervalIntegrable
            (fun t : ℝ ↦ -((((fun z ↦ φ (-z)) dz) (AffineMap.lineMap zw w t)) (w - zw)))
            MeasureTheory.volume 0 1 := by
        refine hleft_int.congr ?_
        intro t ht
        have hline : -(AffineMap.lineMap zw w t) = AffineMap.lineMap wz z₀ t := by
          simpa [hleft_line t]
        have hdir : z₀ - wz = -(w - zw) := by
          simpa [hleft_diff]
        simp only [Complex.scalarOneForm_apply, φ]
        rw [hline, hdir]
        ring
      rw [hleft_eq, add_comm, ← intervalIntegral.integral_add hneg_int hright_int]
      refine intervalIntegral.integral_congr ?_
      intro t ht
      simp only [Complex.scalarOneForm_apply, φ, ψ]
      rw [← exercise25_weightedKernelDivZ_sub_neg alpha (AffineMap.lineMap zw w t)]
      ring
    have hboundary_eq :
        exercise25SquareBoundary n =
          (Path.segment z₀ zw).trans
            ((Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀))) := by
      rw [exercise25SquareBoundary, axisParallelRectangleBoundaryPath]
    have htop_bound :
        ‖∫ᶜ z in Path.segment w wz, ((fun z ↦ ψ z) dz) z‖ ≤
          (8 * Real.pi / (1 - Real.exp (-Real.pi))) * Real.exp (-(c * r)) := by
      rw [curveIntegral_segment]
      refine
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun t : ℝ ↦ (((fun z ↦ ψ z) dz) (AffineMap.lineMap w wz t)) (wz - w))
          (C := (8 * Real.pi / (1 - Real.exp (-Real.pi))) * Real.exp (-(c * r))) ?_).trans ?_
      · intro t ht
        have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
          refine ⟨?_, ?_⟩
          · exact le_of_lt <| by simpa [min_eq_left zero_le_one] using ht.1
          · simpa [max_eq_right zero_le_one] using ht.2
        have hz : AffineMap.lineMap w wz t ∈ Set.range (Path.segment w wz) := by
          exact ⟨⟨t, ht_mem⟩, rfl⟩
        have hzim :
            |(AffineMap.lineMap w wz t).im| = exercise25SquareRadius n := by
          have hr_nonneg : 0 ≤ r := by
            dsimp [r, exercise25SquareRadius]
            positivity
          simp [AffineMap.lineMap_apply, w, wz, r, abs_of_nonneg hr_nonneg]
        have hr_le_norm :
            r ≤ ‖AffineMap.lineMap w wz t‖ := by
          have hz' : AffineMap.lineMap w wz t ∈ Set.range (exercise25SquareBoundary n) :=
            htop_subset hz
          exact (exercise25_square_boundary_geometry n hz').2.2.2
        have hratio :
            ‖Complex.sin ((alpha : ℂ) * AffineMap.lineMap w wz t) /
                Complex.sin ((Real.pi : ℂ) * AffineMap.lineMap w wz t)‖ ≤
              Real.cosh (alpha * r) / Real.sinh (Real.pi * r) := by
          have hline :
              AffineMap.lineMap w wz t =
                (r * (1 - 2 * t) : ℂ) + (((n : ℂ) + (1 / 2 : ℂ)) * Complex.I) := by
            apply Complex.ext <;> simp [AffineMap.lineMap_apply, z₀, w, wz, r, exercise25SquareRadius] <;> ring
          simpa [hline, r, exercise25SquareRadius, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc] using
            norm_sin_real_mul_div_sin_pi_le_cosh_ratio_horizontal_half_integer alpha
              (r * (1 - 2 * t)) n
        have hratio' :
            ‖Complex.sin ((alpha : ℂ) * AffineMap.lineMap w wz t) /
                Complex.sin ((Real.pi : ℂ) * AffineMap.lineMap w wz t)‖ ≤
              Real.exp (|alpha| * r) / Real.sinh (Real.pi * r) := by
          have hr_nonneg : 0 ≤ r := by
            dsimp [r, exercise25SquareRadius]
            positivity
          have hcosh_le :
              Real.cosh (alpha * r) ≤ Real.exp (|alpha| * r) := by
            rw [← Real.cosh_abs (alpha * r)]
            have habs : |alpha * r| = |alpha| * r := by
              rw [abs_mul, abs_of_nonneg hr_nonneg]
            rw [habs]
            have hsum_nonneg : 0 ≤ |alpha| * r := by positivity
            rw [Real.cosh_eq]
            have hneg_le : Real.exp (-(|alpha| * r)) ≤ Real.exp (|alpha| * r) :=
              Real.exp_le_exp.mpr (by linarith)
            nlinarith [Real.exp_nonneg (|alpha| * r), Real.exp_nonneg (-(|alpha| * r)), hneg_le]
          have hsinh_pos : 0 < Real.sinh (Real.pi * r) := by
            refine Real.sinh_pos_iff.mpr ?_
            dsimp [r, exercise25SquareRadius]
            positivity
          exact hratio.trans (div_le_div_of_nonneg_right hcosh_le hsinh_pos.le)
        have hu : Real.pi / 2 ≤ Real.pi * r := by
          dsimp [r, exercise25SquareRadius]
          nlinarith [Real.pi_pos]
        have hsinh_ratio :
            Real.exp (|alpha| * r) / Real.sinh (Real.pi * r) ≤
              (2 / (1 - Real.exp (-Real.pi))) * Real.exp (-(c * r)) := by
          have hsplit :
              Real.exp (|alpha| * r) / Real.sinh (Real.pi * r) =
                (Real.exp (Real.pi * r) / Real.sinh (Real.pi * r)) *
                  Real.exp (-(c * r)) := by
            have hc_eq : |alpha| * r = Real.pi * r + -(c * r) := by
              dsimp [c]
              ring
            rw [hc_eq, Real.exp_add, div_eq_mul_inv]
            ring
          rw [hsplit]
          exact mul_le_mul_of_nonneg_right
            (exercise25_exp_div_sinh_le_uniform hu) (Real.exp_nonneg _)
        calc
          ‖(((fun z ↦ ψ z) dz) (AffineMap.lineMap w wz t)) (wz - w)‖
              = ‖ψ (AffineMap.lineMap w wz t)‖ * ‖wz - w‖ := by
                  simp [Complex.scalarOneForm, mul_comm]
          _ =
              (2 * Real.pi) *
                ‖Complex.sin ((alpha : ℂ) * AffineMap.lineMap w wz t) /
                  Complex.sin ((Real.pi : ℂ) * AffineMap.lineMap w wz t)‖ *
                (‖wz - w‖ / ‖AffineMap.lineMap w wz t‖) := by
                dsimp [ψ]
                rw [norm_mul, norm_div, norm_mul, Complex.norm_I]
                simp [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ 2 * Real.pi by positivity),
                  div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          _ ≤
              (2 * Real.pi) *
                (Real.exp (|alpha| * r) / Real.sinh (Real.pi * r)) * 2 := by
                  have hr_pos : 0 < r := by
                    dsimp [r, exercise25SquareRadius]
                    positivity
                  have hwzw : ‖wz - w‖ = 2 * r := by
                    rw [show wz - w = (-2 * r : ℂ) by
                      apply Complex.ext <;> simp [z₀, w, wz, r] <;> ring]
                    simp [Complex.norm_real, Real.norm_of_nonneg (by nlinarith [hr_pos])]
                  have hdivnorm : ‖wz - w‖ / ‖AffineMap.lineMap w wz t‖ ≤ 2 := by
                    rw [hwzw]
                    exact (div_le_iff₀ (lt_of_lt_of_le hr_pos hr_le_norm)).2 <| by
                      nlinarith
                  gcongr
                  · exact hratio'.trans hsinh_ratio.le
                  · exact hdivnorm
          _ = (8 * Real.pi / (1 - Real.exp (-Real.pi))) * Real.exp (-(c * r)) := by
                ring
      · have hcont :
            Continuous (fun _ : ℝ ↦
              (8 * Real.pi / (1 - Real.exp (-Real.pi))) * Real.exp (-(c * r))) := by
          fun_prop
        simpa using hcont.intervalIntegrable (0 : ℝ) 1
    have hright_bound :
        ‖∫ᶜ z in Path.segment zw w, ((fun z ↦ ψ z) dz) z‖ ≤ 8 * Real.pi / (c * r) := by
      rw [curveIntegral_segment]
      refine
        (intervalIntegral.norm_integral_le_of_norm_le
          (μ := MeasureTheory.volume)
          (f := fun t : ℝ ↦ (((fun z ↦ ψ z) dz) (AffineMap.lineMap zw w t)) (w - zw))
          (g := fun t : ℝ ↦ 8 * Real.pi * Real.exp (-(c * |r * (2 * t - 1)|)))
          zero_le_one ?_ ?_).trans ?_
      · refine Filter.Eventually.of_forall ?_
        intro t
        intro ht
        have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
        have hratio :
            ‖Complex.sin ((alpha : ℂ) * AffineMap.lineMap zw w t) /
                Complex.sin ((Real.pi : ℂ) * AffineMap.lineMap zw w t)‖ ≤
              2 * Real.exp (-(c * |r * (2 * t - 1)|)) := by
          have hline :
              AffineMap.lineMap zw w t =
                (n : ℂ) + (1 / 2 : ℂ) + (r * (2 * t - 1)) * Complex.I := by
            apply Complex.ext <;> simp [AffineMap.lineMap_apply, z₀, zw, w, r] <;> ring
          have hbase :
              ‖Complex.sin ((alpha : ℂ) * AffineMap.lineMap zw w t) /
                  Complex.sin ((Real.pi : ℂ) * AffineMap.lineMap zw w t)‖ ≤
                Real.cosh (alpha * (r * (2 * t - 1))) / Real.cosh (Real.pi * (r * (2 * t - 1))) := by
            simpa [hline, add_comm, add_left_comm, add_assoc,
              mul_comm, mul_left_comm, mul_assoc] using
              norm_sin_real_mul_div_sin_pi_le_cosh_ratio_vertical_half_integer alpha
                (r * (2 * t - 1)) n
          have hnum :
              Real.cosh (alpha * (r * (2 * t - 1))) ≤
                Real.exp (|alpha| * |r * (2 * t - 1)|) := by
            rw [← Real.cosh_abs (alpha * (r * (2 * t - 1)))]
            have habs :
                |alpha * (r * (2 * t - 1))| = |alpha| * |r * (2 * t - 1)| := by
              rw [abs_mul]
            rw [habs]
            rw [Real.cosh_eq]
            have hnonneg : 0 ≤ |alpha| * |r * (2 * t - 1)| := by positivity
            have hneg_le :
                Real.exp (-(|alpha| * |r * (2 * t - 1)|)) ≤
                  Real.exp (|alpha| * |r * (2 * t - 1)|) :=
              Real.exp_le_exp.mpr (by linarith)
            nlinarith [Real.exp_nonneg (|alpha| * |r * (2 * t - 1)|),
              Real.exp_nonneg (-(|alpha| * |r * (2 * t - 1)|)), hneg_le]
          have hden :
              Real.exp (Real.pi * |r * (2 * t - 1)|) ≤
                2 * Real.cosh (Real.pi * (r * (2 * t - 1))) := by
            rw [← Real.cosh_abs (Real.pi * (r * (2 * t - 1)))]
            have habs :
                |Real.pi * (r * (2 * t - 1))| = Real.pi * |r * (2 * t - 1)| := by
              rw [abs_mul, abs_of_pos Real.pi_pos]
            rw [habs, Real.cosh_eq]
            nlinarith [Real.exp_nonneg (Real.pi * |r * (2 * t - 1)|),
              Real.exp_nonneg (-(Real.pi * |r * (2 * t - 1)|))]
          have hden_pos : 0 < Real.cosh (Real.pi * (r * (2 * t - 1))) := Real.cosh_pos _
          have hdecay :
              Real.exp (|alpha| * |r * (2 * t - 1)|) /
                  Real.cosh (Real.pi * (r * (2 * t - 1))) ≤
                2 * Real.exp (-(c * |r * (2 * t - 1)|)) := by
            have haux :
                Real.exp (|alpha| * |r * (2 * t - 1)|) /
                    Real.cosh (Real.pi * (r * (2 * t - 1))) ≤
                  2 * (Real.exp (|alpha| * |r * (2 * t - 1)|) /
                    Real.exp (Real.pi * |r * (2 * t - 1)|)) := by
              have := (div_le_iff₀ hden_pos).2 hden
              have hnonneg : 0 ≤ Real.exp (|alpha| * |r * (2 * t - 1)|) := Real.exp_nonneg _
              have hmul := mul_le_mul_of_nonneg_left this hnonneg
              simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
            have hexp :
                Real.exp (|alpha| * |r * (2 * t - 1)|) /
                    Real.exp (Real.pi * |r * (2 * t - 1)|) =
                  Real.exp (-(c * |r * (2 * t - 1)|)) := by
              rw [div_eq_mul_inv, ← Real.exp_add]
              congr 1
              ring_nf
              simp [c]
            calc
              Real.exp (|alpha| * |r * (2 * t - 1)|) /
                  Real.cosh (Real.pi * (r * (2 * t - 1)))
                  ≤
                    2 * (Real.exp (|alpha| * |r * (2 * t - 1)|) /
                      Real.exp (Real.pi * |r * (2 * t - 1)|)) := haux
              _ = 2 * Real.exp (-(c * |r * (2 * t - 1)|)) := by rw [hexp]
          exact hbase.trans <| by
            exact (div_le_div_of_nonneg_right hnum hden_pos.le).trans hdecay
        have hr_le_norm :
            r ≤ ‖AffineMap.lineMap zw w t‖ := by
          have hz : AffineMap.lineMap zw w t ∈ Set.range (Path.segment zw w) := by
            exact ⟨⟨t, ht_mem⟩, rfl⟩
          have hz' : AffineMap.lineMap zw w t ∈ Set.range (exercise25SquareBoundary n) :=
            hright_subset hz
          exact (exercise25_square_boundary_geometry n hz').2.2.2
        calc
          ‖(((fun z ↦ ψ z) dz) (AffineMap.lineMap zw w t)) (w - zw)‖
              = ‖ψ (AffineMap.lineMap zw w t)‖ * ‖w - zw‖ := by
                  simp [Complex.scalarOneForm]
          _ ≤ (4 * Real.pi) *
              (2 * Real.exp (-(c * |r * (2 * t - 1)|))) := by
                have hr_pos : 0 < r := by
                  dsimp [r, exercise25SquareRadius]
                  positivity
                have hwzw : ‖w - zw‖ = 2 * r := by
                  rw [show w - zw = (2 * r : ℂ) * Complex.I by
                    apply Complex.ext <;> simp [z₀, zw, w, r] <;> ring]
                  rw [norm_mul, Complex.norm_I, mul_one]
                  simp [Complex.norm_real, Real.norm_of_nonneg (by nlinarith [hr_pos])]
                have hdivnorm : ‖w - zw‖ / ‖AffineMap.lineMap zw w t‖ ≤ 2 := by
                  rw [hwzw]
                  exact (div_le_iff₀ (lt_of_lt_of_le hr_pos hr_le_norm)).2 <| by
                    nlinarith
                have hnorm_psi :
                    ‖ψ (AffineMap.lineMap zw w t)‖ * ‖w - zw‖ =
                      (2 * Real.pi) *
                        ‖Complex.sin ((alpha : ℂ) * AffineMap.lineMap zw w t) /
                          Complex.sin ((Real.pi : ℂ) * AffineMap.lineMap zw w t)‖ *
                        (‖w - zw‖ / ‖AffineMap.lineMap zw w t‖) := by
                  simp [ψ, norm_mul, norm_div, Complex.norm_I, div_eq_mul_inv,
                    Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ 2 * Real.pi by positivity),
                    mul_assoc,
                    mul_left_comm, mul_comm]
                calc
                  ‖ψ (AffineMap.lineMap zw w t)‖ * ‖w - zw‖
                      = (2 * Real.pi) *
                          ‖Complex.sin ((alpha : ℂ) * AffineMap.lineMap zw w t) /
                            Complex.sin ((Real.pi : ℂ) * AffineMap.lineMap zw w t)‖ *
                          (‖w - zw‖ / ‖AffineMap.lineMap zw w t‖) := hnorm_psi
                  _ ≤ (2 * Real.pi) * (2 * Real.exp (-(c * |r * (2 * t - 1)|))) * 2 := by
                      gcongr
                  _ = (4 * Real.pi) * (2 * Real.exp (-(c * |r * (2 * t - 1)|))) := by ring
          _ = 8 * Real.pi * Real.exp (-(c * |r * (2 * t - 1)|)) := by ring
      ·
        have hcont :
            Continuous (fun t : ℝ ↦ 8 * Real.pi * Real.exp (-(c * |r * (2 * t - 1)|))) := by
          fun_prop
        exact hcont.intervalIntegrable _ _
      ·
        calc
          ∫ t in (0 : ℝ)..1, 8 * Real.pi * Real.exp (-(c * |r * (2 * t - 1)|))
              = 8 * Real.pi * ∫ t in (0 : ℝ)..1, Real.exp (-(c * |r * (2 * t - 1)|)) := by
                  rw [intervalIntegral.integral_const_mul]
          _ ≤ 8 * Real.pi * (1 / (c * r)) := by
                gcongr
                have hr_pos : 0 < r := by
                  dsimp [r, exercise25SquareRadius]
                  positivity
                have habs :
                    ∫ t in (0 : ℝ)..1, Real.exp (-(c * |r|) * |2 * t - 1|) ≤ 1 / (c * |r|) :=
                  exercise25_intervalIntegral_exp_abs_affine_le_inv (by
                    simpa [abs_of_nonneg hr_pos.le] using mul_pos hc hr_pos)
                simpa [abs_mul, abs_of_nonneg hr_pos.le, mul_assoc, mul_left_comm, mul_comm]
                  using habs
          _ = 8 * Real.pi / (c * r) := by ring
    have hbound_r :
        ‖∫ᶜ z in exercise25SquareBoundary n, ((fun z ↦ φ z) dz) z‖ ≤
          8 * Real.pi / (c * r) +
            (8 * Real.pi / (1 - Real.exp (-Real.pi))) * Real.exp (-(c * r)) := by
      rw [hboundary_eq]
      rw [curveIntegral_trans hbottom_curve
        (CurveIntegrable.trans hright_curve (CurveIntegrable.trans htop_curve hleft_curve))]
      rw [curveIntegral_trans hright_curve (CurveIntegrable.trans htop_curve hleft_curve)]
      rw [curveIntegral_trans htop_curve hleft_curve]
      calc
        ‖∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z +
            (∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
              (∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z +
                ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z))‖
            =
              ‖(∫ᶜ z in Path.segment z₀ zw, ((fun z ↦ φ z) dz) z +
                  ∫ᶜ z in Path.segment w wz, ((fun z ↦ φ z) dz) z) +
                (∫ᶜ z in Path.segment zw w, ((fun z ↦ φ z) dz) z +
                  ∫ᶜ z in Path.segment wz z₀, ((fun z ↦ φ z) dz) z)‖ := by
                  congr 1
                  ring
        _ 
          ≤ ‖∫ᶜ z in Path.segment w wz, ((fun z ↦ ψ z) dz) z‖ +
              ‖∫ᶜ z in Path.segment zw w, ((fun z ↦ ψ z) dz) z‖ := by
                rw [htop_pair, hright_pair]
                exact norm_add_le _ _
        _ ≤ 8 * Real.pi / (c * r) +
              (8 * Real.pi / (1 - Real.exp (-Real.pi))) * Real.exp (-(c * r)) := by
                simpa [add_assoc, add_left_comm, add_comm] using add_le_add htop_bound hright_bound
    simpa [r] using hbound_r
  have hradius :
      Tendsto (fun n : ℕ ↦ exercise25SquareRadius n) atTop atTop := by
    simpa [exercise25SquareRadius] using
      (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) tendsto_natCast_atTop_atTop)
  have hvertical :
      Tendsto (fun n : ℕ ↦ 8 * Real.pi / (c * exercise25SquareRadius n)) atTop (𝓝 0) := by
    have hcradius :
        Tendsto (fun n : ℕ ↦ c * exercise25SquareRadius n) atTop atTop :=
      (Filter.Tendsto.const_mul_atTop hc hradius)
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hcradius) :
        Tendsto
          (fun n : ℕ ↦ (8 * Real.pi) * (c * exercise25SquareRadius n)⁻¹)
          atTop (𝓝 ((8 * Real.pi) * 0)))
  have hhorizontal :
      Tendsto
        (fun n : ℕ ↦
          (8 * Real.pi / (1 - Real.exp (-Real.pi))) *
            Real.exp (-(c * exercise25SquareRadius n)))
        atTop (𝓝 0) := by
    have hneg :
        Tendsto (fun n : ℕ ↦ -(c * exercise25SquareRadius n)) atTop atBot :=
      tendsto_neg_atBot_iff.mpr (Filter.Tendsto.const_mul_atTop hc hradius)
    simpa [mul_zero] using
      (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hneg) :
        Tendsto
          (fun n : ℕ ↦
            (8 * Real.pi / (1 - Real.exp (-Real.pi))) *
              Real.exp (-(c * exercise25SquareRadius n)))
          atTop (𝓝 ((8 * Real.pi / (1 - Real.exp (-Real.pi))) * 0)))
  have htail :
      Tendsto
        (fun n : ℕ ↦
          8 * Real.pi / (c * exercise25SquareRadius n) +
            (8 * Real.pi / (1 - Real.exp (-Real.pi))) *
              Real.exp (-(c * exercise25SquareRadius n)))
        atTop (𝓝 0) := by
    simpa using hvertical.add hhorizontal
  simpa [φ] using squeeze_zero_norm hbound htail

/-- Helper for Cartan section12 0038_Exercise_25: on integral arguments, the cosine factor
`cos (π p)` matches the alternating-sign convention `(-1)^(natAbs p)` used in the weighted sums. -/
lemma exercise25_complex_cos_int_mul_pi_natAbs (p : ℤ) :
    Complex.cos ((Real.pi : ℂ) * (p : ℂ)) = ((-1 : ℂ) ^ Int.natAbs p) := by
  calc
    Complex.cos ((Real.pi : ℂ) * (p : ℂ)) = ((-1 : ℂ) ^ p) := by
      simpa [mul_comm] using congrArg (fun x : ℝ ↦ (x : ℂ)) (Real.cos_int_mul_pi p)
    _ = (((p.negOnePow : ℤˣ) : ℂ)) := by
      symm
      exact Int.cast_negOnePow ℂ p
    _ = (((((Int.natAbs p : ℤ)).negOnePow : ℤˣ) : ℂ)) := by
      simpa using congrArg (fun u : ℤˣ ↦ (u : ℂ)) (Int.negOnePow_abs p).symm
    _ = ((-1 : ℂ) ^ Int.natAbs p) := by
      simpa using (Int.cast_negOnePow_natCast ℂ (Int.natAbs p)).symm

/-- Helper for Cartan section12 0038_Exercise_25: the alternating-sign factor
`(-1)^(natAbs p)` is self-inverse. -/
lemma exercise25_negOnePow_natAbs_inv (p : ℤ) :
    (((-1 : ℂ) ^ Int.natAbs p) : ℂ)⁻¹ = ((-1 : ℂ) ^ Int.natAbs p) := by
  apply inv_eq_of_mul_eq_one_left
  rw [← pow_add]
  have htwo : Int.natAbs p + Int.natAbs p = 2 * Int.natAbs p := by
    ring
  rw [htwo, pow_mul]
  norm_num

/-- Helper for Cartan section12 0038_Exercise_25: when `deg P < deg Q`, the weighted square-boundary
contour integrals still tend to `0`; in the exact-gap-one case only the split-at-infinity
correction contour changes. -/
lemma exercise25_rational_weighted_contour_integral_tendsto_zero_of_degree_lt
    (alpha : ℝ) (halpha_left : -Real.pi < alpha) (halpha_right : alpha < Real.pi)
    (P Q : Polynomial ℂ) (hdeg : P.natDegree < Q.natDegree)
    {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ))) :
    ∃ N : ℕ,
      Tendsto
        (fun n : ℕ ↦
          ∫ᶜ z in exercise25SquareBoundary (n + N),
            ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z)
        atTop (𝓝 0) := by
  by_cases hgap2 : P.natDegree + 2 ≤ Q.natDegree
  · obtain ⟨N, _, htail⟩ :=
      exercise25_rational_weighted_contour_integral_tendsto_zero_of_degree_gap_two_aux
        alpha halpha_left halpha_right P Q hgap2
    exact ⟨N, htail⟩
  · obtain ⟨c, R, hRdeg, hsplit⟩ :=
      exercise25_degreeGapOneSplitAtInfinity P Q hdeg hgap2
    obtain ⟨Nrem, hcontRem, htailRem⟩ :=
      exercise25_rational_weighted_contour_integral_tendsto_zero_of_degree_gap_two_aux
        alpha halpha_left halpha_right R (Polynomial.X * Q) hRdeg
    let originalSeq : ℕ → ℂ := fun n ↦
      ∫ᶜ z in exercise25SquareBoundary (n + Nrem),
        ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z
    let remainderSeq : ℕ → ℂ := fun n ↦
      ∫ᶜ z in exercise25SquareBoundary (n + Nrem),
        ((fun z ↦ R.eval z / (z * Q.eval z) * exercise25WeightedKernel alpha z) dz) z
    let correctionSeq : ℕ → ℂ := fun n ↦
      ∫ᶜ z in exercise25SquareBoundary (n + Nrem),
        ((fun z ↦ exercise25WeightedKernel alpha z / z) dz) z
    have hcontRem' :
        ∀ n : ℕ,
          CurveIntegrable
            ((fun z ↦ R.eval z / (z * Q.eval z) * exercise25WeightedKernel alpha z) dz)
            (exercise25SquareBoundary (n + Nrem)) := by
      intro n
      simpa [Polynomial.eval_mul, mul_assoc, mul_left_comm, mul_comm] using hcontRem n
    have htailRem' :
        Tendsto (fun n : ℕ ↦ remainderSeq n) atTop (𝓝 0) := by
      simpa [remainderSeq, Polynomial.eval_mul, mul_assoc, mul_left_comm, mul_comm] using htailRem
    have hformula :
        ∀ n : ℕ, originalSeq n = remainderSeq n + c * correctionSeq n := by
      intro n
      let m : ℕ := n + Nrem
      let z₀ : ℂ := -(exercise25SquareRadius m : ℂ) - exercise25SquareRadius m * Complex.I
      let w : ℂ := (exercise25SquareRadius m : ℂ) + exercise25SquareRadius m * Complex.I
      let Γ : Unit → ClosedPath ℂ := fun _ ↦ (exercise25SquareBoundary m).toClosedPath
      let splitIntegrand : ℂ → ℂ := fun z ↦
        R.eval z / (z * Q.eval z) * exercise25WeightedKernel alpha z +
          c * (exercise25WeightedKernel alpha z / z)
      have hRe : z₀.re < w.re := by
        simp [z₀, w, exercise25SquareRadius]
        linarith
      have hIm : z₀.im < w.im := by
        simp [z₀, w, exercise25SquareRadius]
        linarith
      have hΓ :
          IsOrientedBoundaryOf (Complex.Rectangle z₀ w) Γ := by
        simpa [Γ, z₀, w, exercise25SquareBoundary] using
          axisParallelRectangleBoundary_isOrientedBoundaryOf z₀ w hRe hIm
      have hEq :
          (fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) =ᶠ[
              Filter.codiscreteWithin (Set.univ : Set ℂ)]
            splitIntegrand := by
        let bad : Set ℂ := insert 0 (Q.roots.toFinset : Set ℂ)
        have hbad :
            badᶜ ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
          exact compl_finite_mem_codiscreteWithin ((Q.roots.toFinset).finite_toSet.insert 0)
        refine Filter.eventuallyEq_of_mem hbad ?_
        intro z hz
        have hz0 : z ≠ 0 := by
          intro hz'
          exact hz (by simp [bad, hz'])
        have hQz : Q.eval z ≠ 0 := by
          intro hQzero
          have hzroot : z ∈ (Q.roots.toFinset : Set ℂ) := by
            simpa using
              (Polynomial.mem_roots
                (exercise25_denominator_ne_zero_of_degree_lt P Q hdeg)).2 hQzero
          exact hz (by simp [bad, hzroot])
        calc
          P.eval z / Q.eval z * exercise25WeightedKernel alpha z
              = (P.eval z / Q.eval z) * exercise25WeightedKernel alpha z := by ring
          _ =
              (R.eval z / ((Polynomial.X * Q).eval z) + c / z) *
                exercise25WeightedKernel alpha z := by
                  rw [hsplit z hz0 hQz]
          _ = splitIntegrand z := by
                dsimp [splitIntegrand]
                rw [Polynomial.eval_mul, Polynomial.eval_X, add_mul]
                field_simp [hz0, hQz]
      have htransfer :
          originalSeq n =
            ∫ᶜ z in exercise25SquareBoundary m,
              ((fun z ↦ splitIntegrand z) dz) z := by
        have htransfer' :
            ∫ᶜ z in (Γ ()).toPath,
                ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z =
              ∫ᶜ z in (Γ ()).toPath, ((fun z ↦ splitIntegrand z) dz) z := by
          exact
            curveIntegral_eq_of_codiscrete_boundary_component
              (K := Complex.Rectangle z₀ w) (U := Set.univ) (Γ := Γ) hΓ ()
              (φ := fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z)
              (ψ := fun z ↦ splitIntegrand z) hEq (by intro z hz; simp)
        have hloop_left :
            ∫ᶜ z in (Γ ()).toPath,
                ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z =
              ∫ᶜ z in exercise25SquareBoundary m,
                ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z := by
          simpa [Γ] using
            exercise25_curveIntegral_loop_toClosedPath_toPath
              ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz)
              (exercise25SquareBoundary m)
        have hloop_right :
            ∫ᶜ z in (Γ ()).toPath, ((fun z ↦ splitIntegrand z) dz) z =
              ∫ᶜ z in exercise25SquareBoundary m, ((fun z ↦ splitIntegrand z) dz) z := by
          simpa [Γ] using
            exercise25_curveIntegral_loop_toClosedPath_toPath
              ((fun z ↦ splitIntegrand z) dz) (exercise25SquareBoundary m)
        simpa [originalSeq, m] using hloop_left.symm.trans (htransfer'.trans hloop_right)
      have hcorrInt :
          CurveIntegrable ((fun z ↦ exercise25WeightedKernel alpha z / z) dz)
            (exercise25SquareBoundary m) :=
        exercise25_weightedKernelDivZ_squareCurveIntegrable alpha m
      have hsum :
          ∫ᶜ z in exercise25SquareBoundary m, ((fun z ↦ splitIntegrand z) dz) z =
            remainderSeq n + c * correctionSeq n := by
        have hsplitForm :
            (fun z ↦ ((fun z ↦ splitIntegrand z) dz) z) =
              (fun z ↦
                (((fun z ↦ R.eval z / (z * Q.eval z) * exercise25WeightedKernel alpha z) dz) z) +
                  c • (((fun z ↦ exercise25WeightedKernel alpha z / z) dz) z)) := by
          funext z
          ext v
          simp [splitIntegrand, Complex.scalarOneForm, add_mul, smul_eq_mul, mul_assoc,
            mul_left_comm, mul_comm]
        calc
          ∫ᶜ z in exercise25SquareBoundary m, ((fun z ↦ splitIntegrand z) dz) z =
              ∫ᶜ z in exercise25SquareBoundary m,
                ((((fun z ↦ R.eval z / (z * Q.eval z) * exercise25WeightedKernel alpha z) dz) z) +
                  c • (((fun z ↦ exercise25WeightedKernel alpha z / z) dz) z)) := by
                    rw [hsplitForm]
          _ =
              ∫ᶜ z in exercise25SquareBoundary m,
                ((fun z ↦ R.eval z / (z * Q.eval z) * exercise25WeightedKernel alpha z) dz) z +
              ∫ᶜ z in exercise25SquareBoundary m,
                c • (((fun z ↦ exercise25WeightedKernel alpha z / z) dz) z) := by
                exact curveIntegral_fun_add (hcontRem' n) (hcorrInt.smul (c := c))
          _ = remainderSeq n + c * correctionSeq n := by
                simp [remainderSeq, correctionSeq, m, curveIntegral_fun_smul]
      exact htransfer.trans hsum
    have hcorr :
        Tendsto (fun n : ℕ ↦ c * correctionSeq n) atTop (𝓝 0) := by
      have hcorrBase :
          Tendsto (fun n : ℕ ↦ correctionSeq n) atTop (𝓝 0) := by
        simpa [correctionSeq] using
          (exercise25_weightedKernelDivZ_squareIntegral_tendsto_zero
            alpha halpha_left halpha_right).comp (tendsto_add_atTop_nat Nrem)
      simpa [mul_zero] using tendsto_const_nhds.mul hcorrBase
    have hsum :
        Tendsto (fun n : ℕ ↦ remainderSeq n + c * correctionSeq n) atTop (𝓝 0) := by
      simpa using htailRem'.add hcorr
    exact ⟨Nrem, Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hformula n).symm) hsum⟩

/-- Exercise 25 (10): if `-π < α < π`, then the weighted symmetric sums
`∑_{-n ≤ p ≤ n} (-1)^p f(p) exp(i α p)` of a rational function `P / Q` with `deg P < deg Q`
converge to the residue sum weighted by `exp(i α z) / sin(π z)`. -/
theorem exercise25_rational_alternating_exponential_sum_tendsto
    (alpha : ℝ) (halpha : -Real.pi < alpha ∧ alpha < Real.pi)
    (P Q : Polynomial ℂ) (hdeg : P.natDegree < Q.natDegree) {s : Finset ℂ}
    (hpoles : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z < 0 ↔ z ∈ s)
    (hnonint : ∀ z ∈ s, z ∉ Set.range (fun p : ℤ ↦ (p : ℂ)))
    (hsimple : ∀ z ∈ s, meromorphicOrderAt (fun w ↦ P.eval w / Q.eval w) z = -1)
    (hdenom_int : ∀ p : ℤ, Q.eval (p : ℂ) ≠ 0)
    (residue : ℂ → ℂ) (hresidue : exercise25RationalResidueData P Q s residue) :
    Tendsto
      (fun n : ℕ ↦
        Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦
          ((-1 : ℂ) ^ Int.natAbs p) *
            Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) *
              (P.eval (p : ℂ) / Q.eval (p : ℂ))))
      atTop
      (𝓝 (-(Real.pi : ℂ) *
        s.sum fun z ↦
          residue z *
            Complex.exp (Complex.I * (alpha : ℂ) * z) /
            Complex.sin ((Real.pi : ℂ) * z))) := by
  by_cases hgap2 : P.natDegree + 2 ≤ Q.natDegree
  · -- In the gap-two regime, the weighted residue identity combines directly with the weighted
    -- contour-tail theorem; no split-at-infinity correction term is needed.
    obtain ⟨Nres, hresEq⟩ :=
      exercise25_weightedSquareBoundary_curveIntegral_eq_two_pi_I_mul_sum
        alpha P Q hpoles hnonint hsimple hdenom_int residue hresidue
    obtain ⟨Ntail, _, htail₀⟩ :=
      exercise25_rational_weighted_contour_integral_tendsto_zero_of_degree_gap_two_aux
        alpha halpha.1 halpha.2 P Q hgap2
    let N : ℕ := max Nres Ntail
    let integralSeq : ℕ → ℂ := fun n ↦
      ∫ᶜ z in exercise25SquareBoundary n,
        ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z
    let sumSeq : ℕ → ℂ := fun n ↦
      Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦
        ((-1 : ℂ) ^ Int.natAbs p) *
          Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) *
            (P.eval (p : ℂ) / Q.eval (p : ℂ)))
    let residueSum : ℂ := s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z)
    have htail :
        Tendsto (fun n : ℕ ↦ integralSeq (n + N)) atTop (𝓝 0) := by
      -- Reindex the vanishing weighted contour tail to the common shift `N`.
      have hshift :
          Tendsto (fun n : ℕ ↦ integralSeq ((n + (N - Ntail)) + Ntail)) atTop (𝓝 0) :=
        (tendsto_add_atTop_iff_nat (N - Ntail)).2 htail₀
      refine Tendsto.congr' ?_ hshift
      refine Filter.Eventually.of_forall ?_
      intro n
      have hidx : (n + (N - Ntail)) + Ntail = n + N := by
        dsimp [N]
        omega
      simp [integralSeq, hidx]
    have hshifted :
        Tendsto (fun n : ℕ ↦ sumSeq (n + N)) atTop (𝓝 (-residueSum)) := by
      let scaledIntegral : ℕ → ℂ := fun n ↦
        (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N)
      have hformula :
          ∀ n : ℕ, sumSeq (n + N) = scaledIntegral n - residueSum := by
        intro n
        have hsumRewrite :
            Finset.sum
                (Finset.Icc (-(((n + N : ℕ) : ℤ))) (((n + N : ℕ) : ℤ)))
                (fun p ↦
                  (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                    Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                      (P.eval (p : ℂ) / Q.eval (p : ℂ))) =
              sumSeq (n + N) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            have hcos_int :
                Complex.cos ((Real.pi : ℂ) * (p : ℂ)) = ((-1 : ℂ) ^ p) := by
              simpa [mul_comm] using
                congrArg (fun x : ℝ ↦ (x : ℂ)) (Real.cos_int_mul_pi p)
            have hcos :
                Complex.cos ((Real.pi : ℂ) * (p : ℂ)) = ((-1 : ℂ) ^ Int.natAbs p) := by
              exact exercise25_complex_cos_int_mul_pi_natAbs p
            have hinv :
                (((-1 : ℂ) ^ Int.natAbs p) : ℂ)⁻¹ = ((-1 : ℂ) ^ Int.natAbs p) := by
              exact exercise25_negOnePow_natAbs_inv p
            calc
              (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                  Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                    (P.eval (p : ℂ) / Q.eval (p : ℂ))
                  =
                  (((-1 : ℂ) ^ Int.natAbs p) *
                      Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ))) *
                    (P.eval (p : ℂ) / Q.eval (p : ℂ)) := by
                      rw [div_eq_mul_inv, hcos, hinv]
                      ring
              _ =
                  ((-1 : ℂ) ^ Int.natAbs p) *
                    Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) *
                      (P.eval (p : ℂ) / Q.eval (p : ℂ)) := by
                        ring
        have hEq :
            integralSeq (n + N) =
              (2 * Real.pi * Complex.I : ℂ) * (sumSeq (n + N) + residueSum) := by
          have hshift :
              integralSeq ((n + (N - Nres)) + Nres) =
                (2 * Real.pi * Complex.I : ℂ) *
                  (Finset.sum
                      (Finset.Icc (-((((n + (N - Nres)) + Nres : ℕ) : ℤ)))
                        ((((n + (N - Nres)) + Nres : ℕ) : ℤ)))
                      (fun p ↦
                        (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                          Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                            (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
                    residueSum) := by
            simpa [integralSeq, residueSum] using hresEq (n + (N - Nres))
          have hidx : (n + (N - Nres)) + Nres = n + N := by
            dsimp [N]
            omega
          calc
            integralSeq (n + N) = integralSeq ((n + (N - Nres)) + Nres) := by simp [hidx]
            _ =
                (2 * Real.pi * Complex.I : ℂ) *
                  (Finset.sum
                      (Finset.Icc (-(((n + N : ℕ) : ℤ))) (((n + N : ℕ) : ℤ)))
                      (fun p ↦
                        (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                          Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                            (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
                    residueSum) := by
                      simpa [hidx] using hshift
            _ = (2 * Real.pi * Complex.I : ℂ) * (sumSeq (n + N) + residueSum) := by
                  rw [hsumRewrite]
        have hscaled :
            scaledIntegral n = sumSeq (n + N) + residueSum := by
          -- Multiply back by `2πi` to cancel the inverse scalar.
          apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
          dsimp [scaledIntegral]
          field_simp [Complex.two_pi_I_ne_zero]
          simpa [mul_assoc] using hEq
        -- Subtract the constant residue term after scaling the contour identity.
        have hsub := congrArg (fun z : ℂ ↦ z - residueSum) hscaled
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, scaledIntegral] using hsub.symm
      have hscaled :
          Tendsto (fun n : ℕ ↦ scaledIntegral n) atTop (𝓝 0) := by
        change Tendsto
          (fun n : ℕ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N))
          atTop (𝓝 0)
        simpa [mul_zero] using
          (tendsto_const_nhds.mul htail :
            Tendsto
              (fun n : ℕ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N))
              atTop (𝓝 (((2 * Real.pi * Complex.I : ℂ)⁻¹) * 0)))
      have hshiftedScaled :
          Tendsto (fun n : ℕ ↦ scaledIntegral n - residueSum) atTop (𝓝 (-residueSum)) := by
        simpa [sub_eq_add_neg] using hscaled.sub tendsto_const_nhds
      exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hformula n).symm) hshiftedScaled
    have hshifted' :
        Tendsto (fun n : ℕ ↦ sumSeq (n + N)) atTop (𝓝 (-residueSum)) := hshifted
    have hfinal := (tendsto_add_atTop_iff_nat N).1 hshifted'
    -- Unfold the weighted residue term only at the end to recover the textbook statement.
    simpa [sumSeq, residueSum, exercise25WeightedKernel, Finset.mul_sum, mul_assoc, mul_left_comm,
      mul_comm, div_eq_mul_inv, sub_eq_add_neg] using hfinal
  · -- In the exact-gap-one regime, only the contour-tail argument changes; the weighted residue
    -- identity itself is unchanged.
    obtain ⟨Nres, hresEq⟩ :=
      exercise25_weightedSquareBoundary_curveIntegral_eq_two_pi_I_mul_sum
        alpha P Q hpoles hnonint hsimple hdenom_int residue hresidue
    obtain ⟨Ntail, htail₀⟩ :=
      exercise25_rational_weighted_contour_integral_tendsto_zero_of_degree_lt
        alpha halpha.1 halpha.2 P Q hdeg hpoles hnonint
    let N : ℕ := max Nres Ntail
    let integralSeq : ℕ → ℂ := fun n ↦
      ∫ᶜ z in exercise25SquareBoundary n,
        ((fun z ↦ P.eval z / Q.eval z * exercise25WeightedKernel alpha z) dz) z
    let sumSeq : ℕ → ℂ := fun n ↦
      Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun p ↦
        ((-1 : ℂ) ^ Int.natAbs p) *
          Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) *
            (P.eval (p : ℂ) / Q.eval (p : ℂ)))
    let residueSum : ℂ := s.sum (fun z ↦ residue z * exercise25WeightedKernel alpha z)
    have htail :
        Tendsto (fun n : ℕ ↦ integralSeq (n + N)) atTop (𝓝 0) := by
      have hshift :
          Tendsto (fun n : ℕ ↦ integralSeq ((n + (N - Ntail)) + Ntail)) atTop (𝓝 0) :=
        (tendsto_add_atTop_iff_nat (N - Ntail)).2 htail₀
      refine Tendsto.congr' ?_ hshift
      refine Filter.Eventually.of_forall ?_
      intro n
      have hidx : (n + (N - Ntail)) + Ntail = n + N := by
        dsimp [N]
        omega
      simp [integralSeq, hidx]
    have hshifted :
        Tendsto (fun n : ℕ ↦ sumSeq (n + N)) atTop (𝓝 (-residueSum)) := by
      let scaledIntegral : ℕ → ℂ := fun n ↦
        (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N)
      have hformula :
          ∀ n : ℕ, sumSeq (n + N) = scaledIntegral n - residueSum := by
        intro n
        have hsumRewrite :
            Finset.sum
                (Finset.Icc (-(((n + N : ℕ) : ℤ))) (((n + N : ℕ) : ℤ)))
                (fun p ↦
                  (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                    Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                      (P.eval (p : ℂ) / Q.eval (p : ℂ))) =
              sumSeq (n + N) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            have hcos_int :
                Complex.cos ((Real.pi : ℂ) * (p : ℂ)) = ((-1 : ℂ) ^ p) := by
              simpa [mul_comm] using
                congrArg (fun x : ℝ ↦ (x : ℂ)) (Real.cos_int_mul_pi p)
            have hcos :
                Complex.cos ((Real.pi : ℂ) * (p : ℂ)) = ((-1 : ℂ) ^ Int.natAbs p) := by
              exact exercise25_complex_cos_int_mul_pi_natAbs p
            have hinv :
                (((-1 : ℂ) ^ Int.natAbs p) : ℂ)⁻¹ = ((-1 : ℂ) ^ Int.natAbs p) := by
              exact exercise25_negOnePow_natAbs_inv p
            calc
              (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                  Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                    (P.eval (p : ℂ) / Q.eval (p : ℂ))
                  =
                  (((-1 : ℂ) ^ Int.natAbs p) *
                      Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ))) *
                    (P.eval (p : ℂ) / Q.eval (p : ℂ)) := by
                      rw [div_eq_mul_inv, hcos, hinv]
                      ring
              _ =
                  ((-1 : ℂ) ^ Int.natAbs p) *
                    Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) *
                      (P.eval (p : ℂ) / Q.eval (p : ℂ)) := by
                        ring
        have hEq :
            integralSeq (n + N) =
              (2 * Real.pi * Complex.I : ℂ) * (sumSeq (n + N) + residueSum) := by
          have hshift :
              integralSeq ((n + (N - Nres)) + Nres) =
                (2 * Real.pi * Complex.I : ℂ) *
                  (Finset.sum
                      (Finset.Icc (-((((n + (N - Nres)) + Nres : ℕ) : ℤ)))
                        ((((n + (N - Nres)) + Nres : ℕ) : ℤ)))
                      (fun p ↦
                        (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                          Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                            (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
                    residueSum) := by
            simpa [integralSeq, residueSum] using hresEq (n + (N - Nres))
          have hidx : (n + (N - Nres)) + Nres = n + N := by
            dsimp [N]
            omega
          calc
            integralSeq (n + N) = integralSeq ((n + (N - Nres)) + Nres) := by simp [hidx]
            _ =
                (2 * Real.pi * Complex.I : ℂ) *
                  (Finset.sum
                      (Finset.Icc (-(((n + N : ℕ) : ℤ))) (((n + N : ℕ) : ℤ)))
                      (fun p ↦
                        (Complex.exp (Complex.I * (alpha : ℂ) * (p : ℂ)) /
                          Complex.cos ((Real.pi : ℂ) * (p : ℂ))) *
                            (P.eval (p : ℂ) / Q.eval (p : ℂ))) +
                    residueSum) := by
                      simpa [hidx] using hshift
            _ = (2 * Real.pi * Complex.I : ℂ) * (sumSeq (n + N) + residueSum) := by
                  rw [hsumRewrite]
        have hscaled :
            scaledIntegral n = sumSeq (n + N) + residueSum := by
          apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
          dsimp [scaledIntegral]
          field_simp [Complex.two_pi_I_ne_zero]
          simpa [mul_assoc] using hEq
        have hsub := congrArg (fun z : ℂ ↦ z - residueSum) hscaled
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, scaledIntegral] using hsub.symm
      have hscaled :
          Tendsto (fun n : ℕ ↦ scaledIntegral n) atTop (𝓝 0) := by
        change Tendsto
          (fun n : ℕ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N))
          atTop (𝓝 0)
        simpa [mul_zero] using
          (tendsto_const_nhds.mul htail :
            Tendsto
              (fun n : ℕ ↦ (2 * Real.pi * Complex.I : ℂ)⁻¹ * integralSeq (n + N))
              atTop (𝓝 (((2 * Real.pi * Complex.I : ℂ)⁻¹) * 0)))
      have hshiftedScaled :
          Tendsto (fun n : ℕ ↦ scaledIntegral n - residueSum) atTop (𝓝 (-residueSum)) := by
        simpa [sub_eq_add_neg] using hscaled.sub tendsto_const_nhds
      exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hformula n).symm) hshiftedScaled
    have hshifted' :
        Tendsto (fun n : ℕ ↦ sumSeq (n + N)) atTop (𝓝 (-residueSum)) := hshifted
    have hfinal := (tendsto_add_atTop_iff_nat N).1 hshifted'
    simpa [sumSeq, residueSum, exercise25WeightedKernel, Finset.mul_sum, mul_assoc, mul_left_comm,
      mul_comm, div_eq_mul_inv, sub_eq_add_neg] using hfinal

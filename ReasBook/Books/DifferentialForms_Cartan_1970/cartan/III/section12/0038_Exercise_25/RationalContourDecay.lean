import DifferentialForms_Cartan_1970.cartan.III.section11.«0003_Theorem_III_5_extra_2».Index
import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».RationalDecay
import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».SquareBoundaryPiCotBounds
import DifferentialForms_Cartan_1970.cartan.III.section12.«0038_Exercise_25».SquareBoundaryIntegrability

noncomputable section

open Filter Bornology
open scoped Topology unitInterval

/-- Helper for Cartan section12 0038_Exercise_25: the cotangent kernel is uniformly bounded on
all square contours `γ_n`. -/
theorem exercise25_piCot_square_boundary_uniform_bound :
    ∃ M1 : ℝ, 0 < M1 ∧
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary n),
        ‖exercise25PiCot z‖ ≤ M1 := by
  let M1 : ℝ :=
    max Real.pi ((Real.pi : ℝ) * (2 / (1 - Real.exp (-Real.pi))))
  refine ⟨M1, ?_, ?_⟩
  · exact lt_of_lt_of_le Real.pi_pos (le_max_left _ _)
  · intro n z hz
    rcases exercise25_square_boundary_geometry n hz with ⟨_, _, hside, _⟩
    rcases hside with hzre | hzim
    · exact (exercise25_piCot_norm_le_pi_of_re_abs_eq_radius n hzre).trans (le_max_left _ _)
    · exact
        (exercise25_piCot_norm_le_horizontal_constant_of_im_abs_eq_radius n hzim).trans
          (le_max_right _ _)

/-- Helper for Cartan section12 0038_Exercise_25: a degree gap of at least two forces the rational
function `P / Q` to decay like `O(|z|⁻²)`. -/
theorem exercise25_rational_degree_gap_two_decay
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ K R : ℝ, 0 < min K R ∧
      ∀ z : ℂ, R ≤ ‖z‖ → ‖P.eval z / Q.eval z‖ ≤ K / ‖z‖ ^ (2 : ℕ) := by
  obtain ⟨K, R, hKR, hbounded⟩ := exercise25_rational_mul_sq_eventually_bounded P Q hdeg
  refine ⟨K, R, hKR, ?_⟩
  intro z hz
  have hR : 0 < R := (lt_min_iff.mp hKR).2
  exact exercise25_decay_of_mul_sq_bound hR hz (hbounded z hz)

/-- Helper for Cartan section12 0038_Exercise_25: on a common tail of square boundaries, the
coefficient `(P / Q)(z) π cot (π z)` satisfies the source decay estimate `O(r_n^{-2})`. -/
lemma exercise25_square_boundary_integrand_decay
    (P Q : Polynomial ℂ) (hdeg : P.natDegree + 2 ≤ Q.natDegree) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
      ∀ n : ℕ, ∀ z ∈ Set.range (exercise25SquareBoundary (n + N)),
        ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤
          C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by
  obtain ⟨M1, hM1pos, hM1⟩ := exercise25_piCot_square_boundary_uniform_bound
  obtain ⟨K, R, hKR, hdecay⟩ := exercise25_rational_degree_gap_two_decay P Q hdeg
  let N : ℕ := Nat.ceil R
  let C : ℝ := K * M1
  refine ⟨C, N, mul_pos (lt_min_iff.mp hKR).1 hM1pos, ?_⟩
  intro n z hz
  let r : ℝ := exercise25SquareRadius (n + N)
  have hr_le_norm : r ≤ ‖z‖ := (exercise25_square_boundary_geometry (n + N) hz).2.2.2
  have hR_le_r : R ≤ r := by
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
    ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤ (K / ‖z‖ ^ (2 : ℕ)) * M1 := hcoeff
    _ ≤ (K / r ^ (2 : ℕ)) * M1 := by
          exact mul_le_mul_of_nonneg_right hdiv hM1pos.le
    _ = C / r ^ (2 : ℕ) := by
          simp [C, div_eq_mul_inv, mul_assoc, mul_comm]
    _ = C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by rfl

/-- Helper for Cartan section12 0038_Exercise_25: if `deg Q ≥ deg P + 2`, then the contour
integrals of `((P / Q) π cot (π z)) dz` over a tail of square boundaries are integrable and tend
to `0`. -/
theorem exercise25_rational_contour_integral_vanishes
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
  obtain ⟨Ncontour, hcontour⟩ :=
    exercise25_square_boundary_integrand_curve_integrable_eventually P Q hdeg
  obtain ⟨Nsides, hsides⟩ :=
    exercise25_square_boundary_integrand_sides_curve_integrable_eventually P Q hdeg
  obtain ⟨C, Ndecay, hCpos, hdecay⟩ := exercise25_square_boundary_integrand_decay P Q hdeg
  let N : ℕ := max Ncontour (max Nsides Ndecay)
  refine ⟨N, (fun n ↦ ?_), ?_⟩
  · let m : ℕ := n + (N - Ncontour)
    have hidx : m + Ncontour = n + N := by
      dsimp [m]
      omega
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
        dsimp [ms]
        omega
      have hidxd : md + Ndecay = n + N := by
        dsimp [md]
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
        rw [← hidxs]
        exact hsides ms
      have hdecayN :
          ∀ z ∈ Set.range (exercise25SquareBoundary (n + N)),
            ‖P.eval z / Q.eval z * exercise25PiCot z‖ ≤
              C / exercise25SquareRadius (n + N) ^ (2 : ℕ) := by
        intro z hz
        rw [← hidxd] at hz ⊢
        exact hdecay md z hz
      exact exercise25_square_boundary_norm_curveIntegral_le
        (n := n + N) (C := C) hsidesN hdecayN
    have hradius :
        Tendsto (fun n : ℕ ↦ exercise25SquareRadius (n + N)) atTop atTop := by
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
    exact squeeze_zero_norm hbound htail

/-- Helper for Cartan section12 0038_Exercise_25: `residue z` records the ordinary contour residue
of the rational function `P / Q` at each listed nonintegral pole `z`. -/
def exercise25RationalResidueData
    (P Q : Polynomial ℂ) (s : Finset ℂ) (residue : ℂ → ℂ) : Prop :=
  ∀ z ∈ s,
    IsolatedLocalResidueCircle (Set.univ : Set ℂ) Set.univ s
      (fun w ↦ P.eval w / Q.eval w) z (residue z)

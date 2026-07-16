import Mathlib
import DifferentialForms_Cartan_1970.cartan.I.section04.«0013_Proposition_4_1»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0008_Proposition_4_1»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2»

-- Semantic Lean search tool `lean_leansearch` was unavailable in this session; the statement shape
-- below was chosen from local mathlib and repository inspection.

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology
open MeromorphicOn

noncomputable section

/-- The Jacobi parameter `q = exp (π I τ)` attached to `τ`. -/
def jacobi_q (τ : ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * τ)

/-- Expansion of `jacobi_q`. -/
theorem jacobi_q_eq_exp (τ : ℂ) :
    jacobi_q τ = Complex.exp (Real.pi * Complex.I * τ) := rfl

-- Domain sampling: the core/canonical owner in this domain is mathlib's two-variable Jacobi theta
-- function `jacobiTheta₂`; the source-facing functions `θ₀` and `θ₁` are the standard
-- shifted/twisted views of that owner.

/-- The symmetric partial sums of the theta series `θ₀`. -/
def jacobi_theta_zero_partial (τ : ℂ) (N : ℕ) : ℂ → ℂ :=
  fun u ↦
    Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n ↦
      jacobiTheta₂_term n (u + (1 / 2 : ℂ)) τ

/-- Evaluation formula for `jacobi_theta_zero_partial`. -/
theorem jacobi_theta_zero_partial_apply (τ : ℂ) (N : ℕ) (u : ℂ) :
    jacobi_theta_zero_partial τ N u =
      Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n ↦
        jacobiTheta₂_term n (u + (1 / 2 : ℂ)) τ := rfl

/-- The symmetric partial sums of the theta series `θ₁`. -/
def jacobi_theta_one_partial (τ : ℂ) (N : ℕ) : ℂ → ℂ :=
  fun u ↦
    -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
      Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n ↦
        jacobiTheta₂_term n (u + (τ + 1) / 2) τ

/-- Evaluation formula for `jacobi_theta_one_partial`. -/
theorem jacobi_theta_one_partial_apply (τ : ℂ) (N : ℕ) (u : ℂ) :
    jacobi_theta_one_partial τ N u =
      -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
        Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n ↦
          jacobiTheta₂_term n (u + (τ + 1) / 2) τ := rfl

/-- The Jacobi theta function `θ₀` attached to `τ`. -/
def jacobi_theta_zero (τ : ℂ) : ℂ → ℂ :=
  fun u ↦ jacobiTheta₂ (u + (1 / 2 : ℂ)) τ

/-- The Jacobi theta function `θ₁` attached to `τ`. -/
def jacobi_theta_one (τ : ℂ) : ℂ → ℂ :=
  fun u ↦
    -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
      jacobiTheta₂ (u + (τ + 1) / 2) τ

scoped[JacobiTheta] notation "θ₀[" τ "]" => jacobi_theta_zero τ
scoped[JacobiTheta] notation "θ₁[" τ "]" => jacobi_theta_one τ

open scoped JacobiTheta

/-- Bridge formula identifying `θ₀` with the shifted two-variable Jacobi theta function. -/
theorem jacobi_theta_zero_apply (τ : ℂ) (u : ℂ) :
    (θ₀[τ]) u = jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := rfl

/-- Bridge formula identifying `θ₁` with the shifted/twisted two-variable Jacobi theta function. -/
theorem jacobi_theta_one_apply (τ : ℂ) (u : ℂ) :
    (θ₁[τ]) u =
      -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
        jacobiTheta₂ (u + (τ + 1) / 2) τ := rfl

/-- Helper for Exercise 3: the symmetric truncations `[-N, N]` exhaust `ℤ` as finite subsets. -/
theorem symmetric_truncations_tendsto_atTop :
    Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) Filter.atTop
      (Filter.atTop : Filter (Finset ℤ)) :=
by
  -- The symmetric intervals enlarge monotonically with `N`.
  have hmono : Monotone (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro a b hab
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    have hcast : (a : ℤ) ≤ b := by
      exact_mod_cast hab
    exact ⟨(neg_le_neg hcast).trans hn.1, hn.2.trans hcast⟩
  refine hmono.tendsto_atTop_finset ?_
  intro n
  refine ⟨n.natAbs, ?_⟩
  -- Every integer lies between `-|n|` and `|n|`; split into the nonnegative and nonpositive forms.
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp [Finset.mem_Icc]
  · simp [Finset.mem_Icc]

/-- Helper for Exercise 3: shifting the first Jacobi-theta variable preserves local uniform
summability on `ℂ`. -/
theorem jacobiTheta₂_term_shift_summableLocallyUniformlyOn (τ a : ℂ) (hτ : 0 < τ.im) :
    SummableLocallyUniformlyOn (fun n u ↦ jacobiTheta₂_term n (u + a) τ) Set.univ :=
by
  -- On each compact set, translate first and bound the shifted imaginary parts uniformly.
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K _ hK
  let Kshift : Set ℂ := (fun u : ℂ ↦ u + a) '' K
  have hKshift : IsCompact Kshift := hK.image (continuous_id.add continuous_const)
  let S : ℝ := sSup ((fun z : ℂ ↦ |z.im|) '' Kshift)
  refine ⟨fun n : ℤ ↦ Real.exp (-Real.pi * (τ.im * n ^ 2 - 2 * S * |n|)), ?_, ?_⟩
  · -- This is exactly the standard theta majorant with `k = 0`.
    simpa [S, pow_zero, one_mul] using summable_pow_mul_jacobiTheta₂_term_bound S hτ 0
  · intro n u hu
    have hmem : u + a ∈ Kshift := Set.mem_image_of_mem (fun u : ℂ ↦ u + a) hu
    have him : |(u + a).im| ≤ S := by
      have hcont : ContinuousOn (fun z : ℂ ↦ |z.im|) Kshift :=
        (Complex.continuous_im.continuousOn).abs
      exact le_csSup (hKshift.bddAbove_image hcont)
        (Set.mem_image_of_mem (fun z : ℂ ↦ |z.im|) hmem)
    -- Route correction: keep the source proof's M-test on shifted `jacobiTheta₂` terms instead of
    -- expanding the textbook `θ₀` and `θ₁` series separately.
    simpa [S] using norm_jacobiTheta₂_term_le hτ him le_rfl n

/-- Helper for Exercise 3: the symmetric partial sums of the shifted `jacobiTheta₂` series
converge locally uniformly on `ℂ`. -/
theorem exercise_3_shifted_jacobiTheta₂_partials_tendstoLocallyUniformly
    (τ a : ℂ) (hτ : 0 < τ.im) :
    TendstoLocallyUniformly
      (fun N : ℕ ↦ fun u ↦
        Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n ↦ jacobiTheta₂_term n (u + a) τ)
      (fun u ↦ jacobiTheta₂ (u + a) τ)
      Filter.atTop :=
by
  have hsum :
      HasSumLocallyUniformlyOn
        (fun n u ↦ jacobiTheta₂_term n (u + a) τ)
        (fun u ↦ jacobiTheta₂ (u + a) τ)
        Set.univ :=
    (jacobiTheta₂_term_shift_summableLocallyUniformlyOn τ a hτ).hasSumLocallyUniformlyOn
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn_univ] at hsum
  intro U hU x
  rcases hsum U hU x with ⟨t, ht, hpartial⟩
  refine ⟨t, ht, ?_⟩
  exact symmetric_truncations_tendsto_atTop.eventually hpartial

/-- Helper for Exercise 3: multiplying a locally uniformly summable series by a fixed continuous
factor preserves the same local uniform summability. -/
theorem hasSumLocallyUniformlyOn_mul_fixed_exercise_3
    {X ι : Type*} [TopologicalSpace X] {s : Set X} {F : ι → X → ℂ} {G g : X → ℂ}
    (h : HasSumLocallyUniformlyOn F G s) (hg : ContinuousOn g s) (hG : ContinuousOn G s) :
    HasSumLocallyUniformlyOn (fun i x ↦ g x * F i x) (fun x ↦ g x * G x) s := by
  -- Convert the claim to the locally uniform convergence owner and multiply partial sums first.
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h ⊢
  have hconst : TendstoLocallyUniformlyOn (fun _ : Finset ι => g) g Filter.atTop s := by
    -- The constant family already agrees with its limit on every neighborhood.
    intro u hu x hx
    refine ⟨s, self_mem_nhdsWithin, ?_⟩
    filter_upwards with n y hy
    exact refl_mem_uniformity hu
  refine (hconst.mul₀ h hg hG).congr ?_
  intro t
  intro x hx
  simp [Finset.mul_sum, mul_assoc]

/-- Exercise 3 (1): for `Im τ > 0`, the symmetric partial sums defining `θ₀` converge locally
uniformly on `ℂ`, hence uniformly on every compact subset of `ℂ`. -/
theorem exercise_3_theta_zero_tendstoLocallyUniformly (τ : ℂ) (hτ : 0 < τ.im) :
    TendstoLocallyUniformly
      (fun N : ℕ ↦ jacobi_theta_zero_partial τ N)
      θ₀[τ]
      Filter.atTop :=
by
  -- Rewrite `θ₀` and its partial sums as the same shifted `jacobiTheta₂` family.
  change TendstoLocallyUniformly
    (fun N : ℕ ↦ fun u ↦
      Finset.sum (Finset.Icc (-(N : ℤ)) (N : ℤ)) fun n ↦
        jacobiTheta₂_term n (u + (1 / 2 : ℂ)) τ)
    (fun u ↦ jacobiTheta₂ (u + (1 / 2 : ℂ)) τ)
    Filter.atTop
  exact exercise_3_shifted_jacobiTheta₂_partials_tendstoLocallyUniformly τ (1 / 2 : ℂ) hτ

/-- Exercise 3 (2): for `Im τ > 0`, the symmetric partial sums defining `θ₁` converge locally
uniformly on `ℂ`, hence uniformly on every compact subset of `ℂ`. -/
theorem exercise_3_theta_one_tendstoLocallyUniformly (τ : ℂ) (hτ : 0 < τ.im) :
    TendstoLocallyUniformly
      (fun N : ℕ ↦ jacobi_theta_one_partial τ N)
      θ₁[τ]
      Filter.atTop :=
by
  let g : ℂ → ℂ := fun u ↦ -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4))
  let F : ℤ → ℂ → ℂ := fun n u ↦ jacobiTheta₂_term n (u + (τ + 1) / 2) τ
  let G : ℂ → ℂ := fun u ↦ jacobiTheta₂ (u + (τ + 1) / 2) τ
  have hbase : HasSumLocallyUniformlyOn F G Set.univ :=
    (jacobiTheta₂_term_shift_summableLocallyUniformlyOn τ ((τ + 1) / 2) hτ).hasSumLocallyUniformlyOn
  have hg : ContinuousOn g Set.univ := by
    -- The exponential prefactor is an entire function of `u`.
    change ContinuousOn (fun u : ℂ ↦ -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)))
      Set.univ
    fun_prop
  have hG : ContinuousOn G Set.univ := by
    -- The shifted `jacobiTheta₂` sum is holomorphic because `Im τ > 0`.
    have hdiff : Differentiable ℂ G := by
      intro u
      dsimp [G]
      simpa using
        (differentiableAt_jacobiTheta₂_fst (u + (τ + 1) / 2) hτ).comp u
          (differentiableAt_id.add_const ((τ + 1) / 2))
    exact hdiff.continuous.continuousOn
  have hmul :
      HasSumLocallyUniformlyOn
        (fun n u ↦ g u * F n u)
        (fun u ↦ g u * G u)
        Set.univ :=
    hasSumLocallyUniformlyOn_mul_fixed_exercise_3 hbase hg hG
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn_univ] at hmul
  intro U hU x
  rcases hmul U hU x with ⟨t, ht, hpartial⟩
  refine ⟨t, ht, ?_⟩
  filter_upwards [symmetric_truncations_tendsto_atTop.eventually hpartial] with N hN u hu
  -- Route correction: multiply the shifted `jacobiTheta₂` local-uniform sum first, then rewrite
  -- the finite sums back to the source `θ₁` partial sums.
  simpa [g, F, G, jacobi_theta_one_partial_apply, jacobi_theta_one_apply, Finset.mul_sum, mul_assoc]
    using hN u hu

/-- Exercise 3 (3): for `Im τ > 0`, the function `θ₀` is entire. -/
theorem exercise_3_theta_zero_differentiable (τ : ℂ) (hτ : 0 < τ.im) :
    Differentiable ℂ θ₀[τ] := by
  intro u
  -- Rewrite `θ₀` as a translate of `jacobiTheta₂`, whose holomorphy is already in mathlib.
  change DifferentiableAt ℂ (fun z ↦ jacobiTheta₂ (z + (1 / 2 : ℂ)) τ) u
  simpa using
    (differentiableAt_jacobiTheta₂_fst (u + (1 / 2 : ℂ)) hτ).comp u
      (differentiableAt_id.add_const (1 / 2 : ℂ))

/-- Exercise 3 (4): for `Im τ > 0`, the function `θ₁` is entire. -/
theorem exercise_3_theta_one_differentiable (τ : ℂ) (hτ : 0 < τ.im) :
    Differentiable ℂ θ₁[τ] := by
  intro u
  -- Rewrite `θ₁` as the product of an entire exponential factor and a translated `jacobiTheta₂`.
  change DifferentiableAt ℂ
    (fun z ↦
      -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (z + τ / 4)) *
        jacobiTheta₂ (z + (τ + 1) / 2) τ) u
  have hexp :
      DifferentiableAt ℂ
        (fun z ↦ Complex.exp ((Real.pi : ℂ) * Complex.I * (z + τ / 4))) u := by
    simpa using
      (Complex.differentiableAt_exp.comp u
        (((differentiableAt_id.add_const (τ / 4)).const_mul ((Real.pi : ℂ) * Complex.I))))
  have htheta :
      DifferentiableAt ℂ (fun z ↦ jacobiTheta₂ (z + (τ + 1) / 2) τ) u := by
    simpa using
      (differentiableAt_jacobiTheta₂_fst (u + (τ + 1) / 2) hτ).comp u
        (differentiableAt_id.add_const ((τ + 1) / 2))
  exact (((differentiableAt_const (-Complex.I)).mul hexp).mul htheta)

/-- Exercise 3 (5): `θ₀` is periodic of period `1`. -/
theorem exercise_3_theta_zero_add_one (τ u : ℂ) :
    (θ₀[τ]) (u + 1) = (θ₀[τ]) u := by
  -- This is the period-`1` law of `jacobiTheta₂` after the half-translation defining `θ₀`.
  simpa [jacobi_theta_zero_apply, add_assoc, add_left_comm, add_comm] using
    jacobiTheta₂_add_left (u + (1 / 2 : ℂ)) τ

/-- Exercise 3 (6): `θ₁` is antiperiodic under translation by `1`. -/
theorem exercise_3_theta_one_add_one (τ u : ℂ) :
    (θ₁[τ]) (u + 1) = -(θ₁[τ]) u := by
  -- The theta factor is `1`-periodic, and the exponential prefactor picks up `exp (π I) = -1`.
  rw [jacobi_theta_one_apply, jacobi_theta_one_apply]
  have hperiod :
      jacobiTheta₂ (u + 1 + (τ + 1) / 2) τ = jacobiTheta₂ (u + (τ + 1) / 2) τ := by
    simpa [add_assoc, add_left_comm, add_comm] using
      jacobiTheta₂_add_left (u + (τ + 1) / 2) τ
  rw [hperiod]
  have hexp :
      Complex.exp ((Real.pi : ℂ) * Complex.I * (u + 1 + τ / 4)) =
        -Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)) := by
    simpa [mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      Complex.exp_add_pi_mul_I ((Real.pi : ℂ) * Complex.I * (u + τ / 4))
  rw [hexp]
  ring_nf

/-- Helper for Exercise 3: the scalar from `jacobiTheta₂_add_left'` matches the textbook
quasi-periodicity factor for `θ₀`. -/
theorem theta_zero_add_tau_scalar (τ u : ℂ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ)))) =
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) := by
  -- Split off the `τ`, `u`, and half-period contributions exactly as in the source formula.
  calc
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ))))
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * τ) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          Complex.exp (-(Real.pi : ℂ) * Complex.I) := by
            rw [show (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ)))) =
                (-(Real.pi : ℂ) * Complex.I * τ) +
                  (-(2 * Real.pi : ℂ) * Complex.I * u) +
                  (-(Real.pi : ℂ) * Complex.I) by ring]
            rw [Complex.exp_add, Complex.exp_add]
    _ = (jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) * (-1) := by
          have hexp_tau :
              Complex.exp (-(Real.pi : ℂ) * Complex.I * τ) = (jacobi_q τ)⁻¹ := by
            calc
              Complex.exp (-(Real.pi : ℂ) * Complex.I * τ)
                = Complex.exp (-((Real.pi : ℂ) * Complex.I * τ)) := by ring
              _ = (Complex.exp ((Real.pi : ℂ) * Complex.I * τ))⁻¹ := by
                    rw [Complex.exp_neg]
              _ = (jacobi_q τ)⁻¹ := by
                    rw [jacobi_q_eq_exp]
          have hexp_pi : Complex.exp (-(Real.pi : ℂ) * Complex.I) = (-1 : ℂ) := by
            simpa using Complex.exp_neg_pi_mul_I
          rw [hexp_tau, hexp_pi]
    _ = -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) := by
          ring

/-- Exercise 3 (7): translating `θ₀` by `τ` multiplies it by the standard exponential factor. -/
theorem exercise_3_theta_zero_add_tau (τ u : ℂ) :
    (θ₀[τ]) (u + τ) =
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
        (θ₀[τ]) u :=
  by
  -- Rewrite `θ₀` through `jacobiTheta₂`, then apply the canonical `+τ` quasi-periodicity law.
  rw [jacobi_theta_zero_apply, jacobi_theta_zero_apply]
  calc
    jacobiTheta₂ (u + τ + (1 / 2 : ℂ)) τ
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ)))) *
          jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := by
            convert jacobiTheta₂_add_left' (u + (1 / 2 : ℂ)) τ using 1 <;> ring
    _ = (-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u)) *
          jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := by
            rw [theta_zero_add_tau_scalar]
    _ = -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          jacobiTheta₂ (u + (1 / 2 : ℂ)) τ := by ring

/-- Helper for Exercise 3: after applying `jacobiTheta₂_add_left'` inside `θ₁`, the scalar terms
collapse to the textbook quasi-periodicity factor. -/
theorem theta_one_add_tau_scalar (τ u : ℂ) :
    -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ + τ / 4)) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (τ + 1) / 2))) =
        -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          (-Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4))) := by
  -- Reassociate the exponentials so that the same `θ₀` scalar from the previous lemma appears.
  calc
    -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ + τ / 4)) *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (τ + 1) / 2)))
      = -Complex.I * (
          Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ + τ / 4)) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (τ + 1) / 2)))) := by
            ring
    _ = -Complex.I *
          Complex.exp
            (((Real.pi : ℂ) * Complex.I * (u + τ + τ / 4)) +
              (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (τ + 1) / 2)))) := by
            rw [← Complex.exp_add]
    _ = -Complex.I *
          Complex.exp
            (((Real.pi : ℂ) * Complex.I * (u + τ / 4)) +
              (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ))))) := by
            congr 1
            ring
    _ = -Complex.I * (
          Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
            Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ))))) := by
            rw [Complex.exp_add]
    _ = -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
          Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (1 / 2 : ℂ)))) := by
            ring
    _ = -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          (-Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4))) := by
            rw [theta_zero_add_tau_scalar]
            ring

/-- Exercise 3 (8): translating `θ₁` by `τ` multiplies it by the same exponential factor. -/
theorem exercise_3_theta_one_add_tau (τ u : ℂ) :
    (θ₁[τ]) (u + τ) =
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
        (θ₁[τ]) u :=
  by
  -- Apply the `+τ` law for `jacobiTheta₂`, then normalize the prefactor by the previous lemma.
  rw [jacobi_theta_one_apply, jacobi_theta_one_apply]
  calc
    -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ + τ / 4)) *
        jacobiTheta₂ (u + τ + (τ + 1) / 2) τ
      = -Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ + τ / 4)) *
          (Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (τ + 1) / 2))) *
            jacobiTheta₂ (u + (τ + 1) / 2) τ) := by
              congr 1
              convert jacobiTheta₂_add_left' (u + (τ + 1) / 2) τ using 1 <;> ring
    _ = (-Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ + τ / 4)) *
          Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * (u + (τ + 1) / 2)))) *
          jacobiTheta₂ (u + (τ + 1) / 2) τ := by
            ring
    _ = (-(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          (-Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)))) *
          jacobiTheta₂ (u + (τ + 1) / 2) τ := by
            rw [theta_one_add_tau_scalar]
    _ = -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) *
          (-Complex.I * Complex.exp ((Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
            jacobiTheta₂ (u + (τ + 1) / 2) τ) := by
              ring

/-- Helper for Exercise 3: translating by `1` preserves the zero set of `θ₁`. -/
theorem theta_one_zero_add_one_iff (τ u : ℂ) :
    (θ₁[τ]) (u + 1) = 0 ↔ (θ₁[τ]) u = 0 := by
  -- The `+1` law only changes `θ₁` by the nonzero scalar `-1`.
  rw [exercise_3_theta_one_add_one]
  simpa using neg_eq_zero

/-- Helper for Exercise 3: translating by `τ` preserves the zero set of `θ₁`. -/
theorem theta_one_zero_add_tau_iff (τ u : ℂ) :
    (θ₁[τ]) (u + τ) = 0 ↔ (θ₁[τ]) u = 0 := by
  -- The `+τ` law only changes `θ₁` by a nonzero exponential scalar.
  rw [exercise_3_theta_one_add_tau]
  have hq : jacobi_q τ ≠ 0 := by
    simpa [jacobi_q_eq_exp] using
      (Complex.exp_ne_zero ((Real.pi : ℂ) * Complex.I * τ))
  have hscalar :
      -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * u) ≠ 0 := by
    exact mul_ne_zero
      (neg_ne_zero.mpr (inv_ne_zero hq))
      (Complex.exp_ne_zero _)
  constructor
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left hscalar
  · intro hzero
    simpa [hzero]

/-- Helper for Exercise 3: away from zeros, the logarithmic derivative of `θ₁` is `1`-periodic. -/
theorem theta_one_logDeriv_add_one (τ z : ℂ) (hτ : 0 < τ.im) :
    logDeriv (θ₁[τ]) (z + 1) = logDeriv (θ₁[τ]) z := by
  -- Rewrite the shifted logarithmic derivative through the translated function.
  have hcomp :
      logDeriv (fun w : ℂ ↦ (θ₁[τ]) (w + 1)) z = logDeriv (θ₁[τ]) (z + 1) := by
    simpa [Function.comp] using
      (logDeriv_comp
        ((exercise_3_theta_one_differentiable τ hτ) (z + 1))
        (by fun_prop) : logDeriv ((θ₁[τ]) ∘ fun w : ℂ ↦ w + 1) z =
          logDeriv (θ₁[τ]) ((fun w : ℂ ↦ w + 1) z) * deriv (fun w : ℂ ↦ w + 1) z)
  have hEq :
      (fun w : ℂ ↦ (θ₁[τ]) (w + 1)) = fun w : ℂ ↦ (-1 : ℂ) * (θ₁[τ]) w := by
    funext w
    simpa using exercise_3_theta_one_add_one τ w
  -- The multiplicative constant `-1` does not affect the logarithmic derivative.
  calc
    logDeriv (θ₁[τ]) (z + 1) = logDeriv (fun w : ℂ ↦ (θ₁[τ]) (w + 1)) z := by
      exact hcomp.symm
    _ = logDeriv (fun w : ℂ ↦ (-1 : ℂ) * (θ₁[τ]) w) z := by
      rw [hEq]
    _ = logDeriv (θ₁[τ]) z := by
      rw [logDeriv_const_mul z (-1 : ℂ) (by norm_num)]

/-- Helper for Exercise 3: away from zeros, the logarithmic derivative of `θ₁` acquires the
expected additive defect under translation by `τ`. -/
theorem theta_one_logDeriv_add_tau (τ z : ℂ) (hτ : 0 < τ.im)
    (hz : (θ₁[τ]) z ≠ 0) :
    logDeriv (θ₁[τ]) (z + τ) = logDeriv (θ₁[τ]) z - (2 * Real.pi : ℂ) * Complex.I := by
  let a : ℂ → ℂ := fun w ↦
    -(jacobi_q τ)⁻¹ * Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * w)
  have hq : jacobi_q τ ≠ 0 := by
    simpa [jacobi_q_eq_exp] using
      (Complex.exp_ne_zero ((Real.pi : ℂ) * Complex.I * τ))
  have ha_nonzero : a z ≠ 0 := by
    dsimp [a]
    exact mul_ne_zero
      (neg_ne_zero.mpr (inv_ne_zero hq))
      (Complex.exp_ne_zero _)
  have hcomp :
      logDeriv (fun w : ℂ ↦ (θ₁[τ]) (w + τ)) z = logDeriv (θ₁[τ]) (z + τ) := by
    simpa [Function.comp] using
      (logDeriv_comp
        ((exercise_3_theta_one_differentiable τ hτ) (z + τ))
        (by fun_prop) : logDeriv ((θ₁[τ]) ∘ fun w : ℂ ↦ w + τ) z =
          logDeriv (θ₁[τ]) ((fun w : ℂ ↦ w + τ) z) * deriv (fun w : ℂ ↦ w + τ) z)
  have hEq :
      (fun w : ℂ ↦ (θ₁[τ]) (w + τ)) = fun w : ℂ ↦ a w * (θ₁[τ]) w := by
    funext w
    simpa [a] using exercise_3_theta_one_add_tau τ w
  have hdiff_a : DifferentiableAt ℂ a z := by
    -- The scalar factor is an exponential of a complex-affine function.
    dsimp [a]
    fun_prop
  have hloga :
      logDeriv a z = -((2 * Real.pi : ℂ) * Complex.I) := by
    -- Only the exponential factor contributes to the logarithmic derivative.
    rw [show a = fun w : ℂ ↦
        (-(jacobi_q τ)⁻¹ : ℂ) *
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * w) by
          rfl]
    rw [logDeriv_const_mul z (-(jacobi_q τ)⁻¹ : ℂ)
      (neg_ne_zero.mpr (inv_ne_zero hq))]
    rw [show (fun w : ℂ ↦ Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * w)) =
        Complex.exp ∘ fun w : ℂ ↦ (-(2 * Real.pi : ℂ) * Complex.I) * w by
          rfl]
    rw [logDeriv_comp Complex.differentiableAt_exp (by fun_prop), Complex.logDeriv_exp]
    simp [logDeriv_apply]
  -- Split the logarithmic derivative across the nonvanishing product from the `+τ` law.
  calc
    logDeriv (θ₁[τ]) (z + τ) = logDeriv (fun w : ℂ ↦ (θ₁[τ]) (w + τ)) z := by
      exact hcomp.symm
    _ = logDeriv (fun w : ℂ ↦ a w * (θ₁[τ]) w) z := by
      rw [hEq]
    _ = logDeriv a z + logDeriv (θ₁[τ]) z := by
      rw [logDeriv_mul z ha_nonzero hz hdiff_a ((exercise_3_theta_one_differentiable τ hτ) z)]
    _ = -((2 * Real.pi : ℂ) * Complex.I) + logDeriv (θ₁[τ]) z := by
      rw [hloga]
    _ = logDeriv (θ₁[τ]) z - (2 * Real.pi : ℂ) * Complex.I := by
      ring

/-- Helper for Exercise 3: the prefactors in the half-`τ` translation identity cancel exactly. -/
theorem theta_one_prefactor_cancel (z w : ℂ) :
    Complex.I * Complex.exp (-z) * (-Complex.I * Complex.exp z * w) = w := by
  -- Rearrange the scalar factors, then use `exp (-z) * exp z = 1`.
  calc
    Complex.I * Complex.exp (-z) * (-Complex.I * Complex.exp z * w)
      = (Complex.I * -Complex.I) * (Complex.exp (-z) * Complex.exp z) * w := by
          ring_nf
    _ = w := by
          simp [Complex.exp_neg, mul_assoc]

/-- Exercise 3 (9): translating `θ₀` by `τ / 2` identifies it with `θ₁`
up to the standard factor. -/
theorem exercise_3_theta_zero_add_half_tau (τ u : ℂ) :
    (θ₀[τ]) (u + τ / 2) =
      Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u + τ / 4)) *
        (θ₁[τ]) u := by
  -- Here the two theta arguments coincide exactly, so only the prefactor needs simplification.
  rw [jacobi_theta_zero_apply, jacobi_theta_one_apply]
  rw [show u + τ / 2 + (1 / 2 : ℂ) = u + (τ + 1) / 2 by ring]
  simpa using (theta_one_prefactor_cancel
    ((Real.pi : ℂ) * Complex.I * (u + τ / 4))
    (jacobiTheta₂ (u + (τ + 1) / 2) τ)).symm

/-- Helper for Exercise 3: the origin is a zero of `θ₁`. -/
theorem jacobi_theta_one_zero_at_zero (τ : ℂ) :
    (θ₁[τ]) 0 = 0 := by
  -- Route correction: use evenness plus the `1`- and `τ`-shifts of `jacobiTheta₂` to force a sign
  -- change at the half-period point appearing in the definition of `θ₁`.
  rw [jacobi_theta_one_apply]
  suffices htheta : jacobiTheta₂ ((τ + 1) / 2) τ = 0 by
    simp [htheta]
  have hshift :
      jacobiTheta₂ ((τ - 1) / 2) τ = -jacobiTheta₂ (-(τ + 1) / 2) τ := by
    convert jacobiTheta₂_add_left' (-(τ + 1) / 2) τ using 1
    · ring
    · ring_nf
      simpa using Complex.exp_pi_mul_I
  have hperiod :
      jacobiTheta₂ ((τ + 1) / 2) τ = jacobiTheta₂ ((τ - 1) / 2) τ := by
    convert jacobiTheta₂_add_left ((τ - 1) / 2) τ using 1 <;> ring
  have hneg :
      jacobiTheta₂ (-(τ + 1) / 2) τ = jacobiTheta₂ ((τ + 1) / 2) τ := by
    convert jacobiTheta₂_neg_left ((τ + 1) / 2) τ using 1 <;> ring
  have hself : jacobiTheta₂ ((τ + 1) / 2) τ = -jacobiTheta₂ ((τ + 1) / 2) τ := by
    calc
      jacobiTheta₂ ((τ + 1) / 2) τ = jacobiTheta₂ ((τ - 1) / 2) τ := hperiod
      _ = -jacobiTheta₂ (-(τ + 1) / 2) τ := hshift
      _ = -jacobiTheta₂ ((τ + 1) / 2) τ := by rw [hneg]
  have htwo :
      (2 : ℂ) * jacobiTheta₂ ((τ + 1) / 2) τ = 0 := by
    simpa [two_mul] using add_eq_zero_iff_eq_neg.mpr hself
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- Helper for Exercise 3: the half-period `τ / 2` is a zero of `θ₀`. -/
theorem jacobi_theta_zero_zero_at_half_tau (τ : ℂ) :
    (θ₀[τ]) (τ / 2) = 0 := by
  -- Transfer the base zero of `θ₁` through the half-`τ` translation formula.
  simpa [jacobi_theta_one_zero_at_zero] using exercise_3_theta_zero_add_half_tau τ 0

/-- Helper for Exercise 3: every nonzero Fourier mode in the average of `θ₀` integrates to `0`. -/
theorem jacobi_theta_zero_term_intervalIntegral_eq_zero_of_ne_zero (τ : ℂ) (n : ℤ) (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..1, jacobiTheta₂_term n (x + (1 / 2 : ℂ)) τ = 0 :=
by
  let a : ℂ :=
      Complex.exp
        ((Real.pi : ℂ) * Complex.I * (n : ℂ) +
          (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ (2 : ℕ)) * τ)
  have hrewrite :
      (fun x : ℝ ↦ jacobiTheta₂_term n (x + (1 / 2 : ℂ)) τ) =
        fun x : ℝ ↦ a * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * x) := by
    -- Isolate the constant half-period/`τ` factor and keep only the genuine Fourier mode in `x`.
    funext x
    dsimp [a, jacobiTheta₂_term]
    calc
      Complex.exp ((2 * (Real.pi : ℂ)) * Complex.I * (n : ℂ) * (x + (1 / 2 : ℂ)) +
          (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ (2 : ℕ)) * τ)
        = Complex.exp
            (((Real.pi : ℂ) * Complex.I * (n : ℂ) +
                (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ (2 : ℕ)) * τ) +
              ((2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * x)) := by
              congr 1
              ring_nf
      _ =
          Complex.exp
            ((Real.pi : ℂ) * Complex.I * (n : ℂ) +
              (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ (2 : ℕ)) * τ) *
            Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * x) := by
              rw [Complex.exp_add]
      _ = a * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (n : ℂ) * x) := by
              rfl
  rw [hrewrite, intervalIntegral.integral_const_mul]
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I * (n : ℂ)
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have htwoPiI : ((2 * Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero htwoPiI hnC
  -- Apply the explicit primitive of `exp (c x)` and then use `exp (2π i n) = 1`.
  rw [integral_exp_mul_complex hc]
  have hexp : Complex.exp c = 1 := by
    dsimp [c]
    rw [show ((2 * Real.pi : ℂ) * Complex.I * (n : ℂ)) =
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    simpa using
      (Complex.exp_int_mul_two_pi_mul_I n :
        Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1)
  have hzero :
      ((Complex.exp (c * ((1 : ℝ) : ℂ)) - Complex.exp (c * ((0 : ℝ) : ℂ))) / c : ℂ) = 0 := by
    rw [show (((1 : ℝ) : ℂ)) = (1 : ℂ) by norm_num,
      show (((0 : ℝ) : ℂ)) = (0 : ℂ) by norm_num,
      mul_one, mul_zero, hexp]
    simp [hc]
  rw [hzero]
  ring

/-- Helper for Exercise 3: on the compact period interval `[0, 1]`, the series defining `θ₀`
may be integrated termwise. -/
theorem jacobi_theta_zero_intervalIntegral_tsum (τ : ℂ) (hτ : 0 < τ.im) :
    ∫ x in (0 : ℝ)..1, (θ₀[τ]) x =
      ∑' n : ℤ, ∫ x in (0 : ℝ)..1, jacobiTheta₂_term n (x + (1 / 2 : ℂ)) τ :=
by
  let K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩
  let termMap : ℤ → C(ℝ, ℂ) := fun n ↦
    ⟨fun x ↦ jacobiTheta₂_term n (x + (1 / 2 : ℂ)) τ, by
      -- Each summand is an exponential of a real-affine function.
      change Continuous fun x : ℝ ↦
        Complex.exp
          ((2 * (Real.pi : ℂ)) * Complex.I * (n : ℂ) * (x + (1 / 2 : ℂ)) +
            (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ (2 : ℕ)) * τ)
      fun_prop⟩
  have hnorm_le :
      ∀ n : ℤ, ‖(termMap n).restrict K‖ ≤ Real.exp (-Real.pi * (τ.im * n ^ 2)) := by
    intro n
    rw [ContinuousMap.norm_le (f := (termMap n).restrict K) (by positivity)]
    intro x
    have him : |((((x : K) : ℝ) : ℂ) + (1 / 2 : ℂ)).im| ≤ (0 : ℝ) := by
      simp
    -- Route correction: use the compact-interval supremum norm bound directly, rather than trying
    -- to interchange interval integration with the local-uniform limit inside the main theorem.
    simpa [termMap] using
      norm_jacobiTheta₂_term_le (S := 0) (T := τ.im) hτ him le_rfl n
  have hbound_sum : Summable (fun n : ℤ ↦ Real.exp (-Real.pi * (τ.im * n ^ 2))) := by
    simpa [pow_zero, one_mul] using summable_pow_mul_jacobiTheta₂_term_bound 0 hτ 0
  have hnorm_sum : Summable (fun n : ℤ ↦ ‖(termMap n).restrict K‖) :=
    hbound_sum.of_nonneg_of_le (fun n ↦ norm_nonneg _) hnorm_le
  have hswap :
      ∑' n : ℤ, ∫ x in (0 : ℝ)..1, termMap n x =
        ∫ x in (0 : ℝ)..1, ∑' n : ℤ, termMap n x :=
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (a := (0 : ℝ)) (b := 1) hnorm_sum
  have hseries :
      (fun x : ℝ ↦ (θ₀[τ]) x) = fun x : ℝ ↦ ∑' n : ℤ, termMap n x := by
    -- Identify the pointwise `tsum` with the shifted `jacobiTheta₂` series defining `θ₀`.
    ext x
    symm
    simpa [termMap, jacobi_theta_zero_apply] using
      (hasSum_jacobiTheta₂_term (x + (1 / 2 : ℂ)) hτ).tsum_eq
  have hEqIntegral :
      ∫ x in (0 : ℝ)..1, (θ₀[τ]) x = ∫ x in (0 : ℝ)..1, ∑' n : ℤ, termMap n x := by
    simpa using congrArg (fun f : ℝ → ℂ ↦ ∫ x in (0 : ℝ)..1, f x) hseries
  calc
    ∫ x in (0 : ℝ)..1, (θ₀[τ]) x = ∫ x in (0 : ℝ)..1, ∑' n : ℤ, termMap n x := hEqIntegral
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, termMap n x := hswap.symm
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, jacobiTheta₂_term n (x + (1 / 2 : ℂ)) τ := by
          simp [termMap]

/-- Helper for Exercise 3: the average of `θ₀` over one real period is `1`. -/
theorem jacobi_theta_zero_average_eq_one (τ : ℂ) (hτ : 0 < τ.im) :
    ∫ x in (0 : ℝ)..1, (θ₀[τ]) x = 1 :=
by
  -- Use the source average argument exactly: interchange sum and integral once, then isolate the
  -- zero mode and kill every nonzero Fourier mode over the unit interval.
  calc
    ∫ x in (0 : ℝ)..1, (θ₀[τ]) x
      = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, jacobiTheta₂_term n (x + (1 / 2 : ℂ)) τ :=
          jacobi_theta_zero_intervalIntegral_tsum τ hτ
    _ = ∫ x in (0 : ℝ)..1, jacobiTheta₂_term 0 (x + (1 / 2 : ℂ)) τ := by
          refine tsum_eq_single 0 ?_
          intro n hn
          exact jacobi_theta_zero_term_intervalIntegral_eq_zero_of_ne_zero τ n hn
    _ = 1 := by
          simp [jacobiTheta₂_term]

/-- Exercise 3 (10): for `Im τ > 0`, the theta function `θ₀` is not identically zero. -/
theorem exercise_3_theta_zero_ne_zero (τ : ℂ) (hτ : 0 < τ.im) :
    θ₀[τ] ≠ 0 :=
by
  intro hzero
  -- The average from the source argument would vanish for the zero function, contradicting
  -- `jacobi_theta_zero_average_eq_one`.
  have : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = ∫ x in (0 : ℝ)..1, (θ₀[τ]) x := by
        symm
        exact jacobi_theta_zero_average_eq_one τ hτ
      _ = 0 := by
        simp [hzero]
  exact one_ne_zero this

/-- Exercise 3 (11): for `Im τ > 0`, the theta function `θ₁` is not identically zero. -/
theorem exercise_3_theta_one_ne_zero (τ : ℂ) (hτ : 0 < τ.im) :
    θ₁[τ] ≠ 0 :=
by
  intro hzero
  have hzero_zero : θ₀[τ] = 0 := by
    -- Translate the vanishing of `θ₁` through the half-`τ` shift formula to force `θ₀ = 0`.
    ext u
    simpa [hzero, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      exercise_3_theta_zero_add_half_tau τ (u - τ / 2)
  exact exercise_3_theta_zero_ne_zero τ hτ hzero_zero

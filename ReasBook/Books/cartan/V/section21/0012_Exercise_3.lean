import Mathlib
import cartan.I.section04.«0013_Proposition_4_1»
import cartan.III.section11.«0008_Proposition_4_1»
import cartan.V.section19.«0011_Proposition_5_2»

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

/-- Helper for Exercise 3: every lattice point `m + nτ` is a zero of `θ₁`. -/
theorem theta_one_zero_at_lattice_point (τ : ℂ) (m n : ℤ) :
    (θ₁[τ]) (m + n * τ) = 0 := by
  have hn : ∀ k : ℤ, (θ₁[τ]) ((k : ℂ) * τ) = 0 := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · -- The base lattice zero is the origin.
      simpa using jacobi_theta_one_zero_at_zero τ
    · intro j hj
      -- Move forward by one `τ`-period step.
      have hnext :
          (θ₁[τ]) (((j : ℂ) * τ) + τ) = 0 :=
        (theta_one_zero_add_tau_iff τ ((j : ℂ) * τ)).2 hj
      simpa [Int.cast_add, add_mul, add_assoc, add_left_comm, add_comm, one_mul] using hnext
    · intro j hj
      -- Move backward by undoing one `τ`-period step.
      have hprev :
          (θ₁[τ]) ((((-((j : ℤ)) - 1 : ℤ) : ℂ) * τ) + τ) = 0 := by
        simpa [Int.cast_neg, Int.cast_natCast, Int.cast_sub, add_mul, add_assoc, add_left_comm,
          add_comm, one_mul, sub_eq_add_neg] using hj
      exact (theta_one_zero_add_tau_iff τ ((((-((j : ℤ)) - 1 : ℤ) : ℂ) * τ))).1 hprev
  have hm : ∀ j : ℤ, (θ₁[τ]) ((j : ℂ) + (n : ℂ) * τ) = 0 := by
    intro j
    refine Int.induction_on j ?_ ?_ ?_
    · -- Start from the already-known zero at `nτ`.
      simpa [zero_add] using hn n
    · intro k hk
      -- Move forward by one real period.
      have hnext :
          (θ₁[τ]) (((k : ℂ) + (n : ℂ) * τ) + 1) = 0 :=
        (theta_one_zero_add_one_iff τ ((k : ℂ) + (n : ℂ) * τ)).2 hk
      simpa [Int.cast_add, add_assoc, add_left_comm, add_comm] using hnext
    · intro k hk
      -- Move backward by undoing one real-period shift.
      have hprev :
          (θ₁[τ]) ((((-((k : ℤ)) - 1 : ℤ) : ℂ) + (n : ℂ) * τ) + 1) = 0 := by
        simpa [Int.cast_neg, Int.cast_natCast, Int.cast_sub, sub_eq_add_neg, add_assoc,
          add_left_comm, add_comm] using hk
      exact (theta_one_zero_add_one_iff τ ((((-((k : ℤ)) - 1 : ℤ) : ℂ) + (n : ℂ) * τ))).1 hprev
  simpa [add_comm, add_left_comm, add_assoc, mul_comm] using hm m

/-- Helper for Exercise 3: when `Im τ > 0`, the periods `1` and `τ` are linearly independent over
`ℝ`. -/
theorem linear_independent_one_tau_of_im_pos (τ : ℂ) (hτ : 0 < τ.im) :
    LinearIndependent ℝ ![(1 : ℂ), τ] := by
  -- The imaginary part kills the coefficient of `τ`, and the real part then kills the coefficient
  -- of `1`.
  refine LinearIndependent.pair_iff.2 ?_
  intro a b hab
  have himag : b * τ.im = 0 := by
    have hab_im := congrArg Complex.im hab
    simpa [Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using hab_im
  have hb : b = 0 := by
    nlinarith [hτ, himag]
  have hreal : a = 0 := by
    have hab_re := congrArg Complex.re hab
    simpa [hb, Complex.ofReal_re, Complex.ofReal_im, mul_comm, mul_left_comm, mul_assoc] using
      hab_re
  exact ⟨hreal, hb⟩

/-- Helper for Exercise 3: the source period pair is generated by `1` and `τ`. -/
def theta_one_period_pair (τ : ℂ) (hτ : 0 < τ.im) : PeriodPair :=
  ⟨1, τ, linear_independent_one_tau_of_im_pos τ hτ⟩

/-- Helper for Exercise 3: translating by an arbitrary lattice vector `m + nτ` preserves the zero
set of `θ₁`. -/
theorem theta_one_zero_add_lattice_shift_iff (τ u : ℂ) (m n : ℤ) :
    (θ₁[τ]) (u + m + n * τ) = 0 ↔ (θ₁[τ]) u = 0 := by
  let f : ℂ → Prop := fun z ↦ (θ₁[τ]) z = 0
  have hper1 : Function.Periodic f 1 := by
    intro z
    simpa [f] using theta_one_zero_add_one_iff τ z
  have hperτ : Function.Periodic f τ := by
    intro z
    simpa [f] using theta_one_zero_add_tau_iff τ z
  -- First remove the real-period contribution, then the `τ`-period contribution.
  calc
    (θ₁[τ]) (u + m + n * τ) = 0 ↔ f (u + n * τ) := by
      simpa [f, add_assoc, add_left_comm, add_comm, zsmul_eq_mul] using
        (hper1.int_mul m) (u + n * τ)
    _ ↔ (θ₁[τ]) u = 0 := by
      simpa [f, add_assoc, add_left_comm, add_comm, zsmul_eq_mul] using (hperτ.int_mul n) u

/-- Helper for Exercise 3: every zero of `θ₁` admits a representative zero in any chosen period
parallelogram for the lattice generated by `1` and `τ`. -/
theorem theta_one_zero_exists_periodParallelogram_representative
    (τ u z₀ : ℂ) (hτ : 0 < τ.im) (hu : (θ₁[τ]) u = 0) :
    ∃ w, w ∈ (theta_one_period_pair τ hτ).periodParallelogram z₀ ∧
      (θ₁[τ]) w = 0 ∧ w - u ∈ (theta_one_period_pair τ hτ).lattice := by
  let L : PeriodPair := theta_one_period_pair τ hτ
  obtain ⟨w, hwP, hwsub⟩ := L.exists_mem_periodParallelogram_sub_lattice u z₀
  rcases L.mem_lattice.mp hwsub with ⟨m, n, hmn_raw⟩
  have hmn : ((m : ℤ) : ℂ) + ((n : ℤ) : ℂ) * τ = w - u := by
    simpa [L, theta_one_period_pair, mul_comm, add_assoc, add_left_comm, add_comm] using hmn_raw
  have hw_eq : w = u + m + n * τ := by
    -- Unpack the lattice correction in the concrete period basis `(1, τ)`.
    calc
      w = u + (w - u) := by ring
      _ = u + (((m : ℤ) : ℂ) + ((n : ℤ) : ℂ) * τ) := by rw [hmn]
      _ = u + m + n * τ := by ring
  refine ⟨w, hwP, ?_, hwsub⟩
  -- The translated representative remains a zero because the zero set is lattice-periodic.
  rw [hw_eq]
  exact (theta_one_zero_add_lattice_shift_iff τ u m n).2 hu

/-- Helper for Exercise 3: in the shifted fundamental cell based at `-1 - τ + u + vτ` with
`u, v ∈ (0, 1)`, the only lattice point is the origin. -/
theorem eq_zero_of_mem_shifted_periodParallelogram_and_mem_lattice
    (τ z : ℂ) (hτ : 0 < τ.im) {u v : ℝ}
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hv : v ∈ Set.Ioo (0 : ℝ) 1)
    (hz :
      z ∈ (theta_one_period_pair τ hτ).periodParallelogram (-1 - τ + u + v * τ))
    (hzl : z ∈ (theta_one_period_pair τ hτ).lattice) :
    z = 0 := by
  let L : PeriodPair := theta_one_period_pair τ hτ
  let z₀ : ℂ := -1 - τ + u + v * τ
  obtain ⟨a, b, ha0, ha1, hb0, hb1, hsub0, hsub1⟩ :=
    L.basis_coords_sub_of_mem_periodParallelogram (z₀ := z₀) (by simpa [L, z₀] using hz)
  obtain ⟨m, n, hm, hn⟩ := L.exists_int_basis_coords_of_mem_lattice (by simpa [L] using hzl)
  have hz₀_eq :
      z₀ =
        (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
          (u - 1, v - 1) : ℂ) := by
    -- Express the shifted basepoint in the period basis `(1, τ)`.
    rw [L.basis_pair_homeomorph_apply]
    simp [L, z₀, theta_one_period_pair, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    ring
  have hz₀_coord0 : L.basis.equivFun z₀ 0 = u - 1 := by
    -- Read off the first basis coordinate of the shifted basepoint.
    rw [hz₀_eq]
    simpa using L.basis_equivFunL_symm_apply_zero (u - 1) (v - 1)
  have hz₀_coord1 : L.basis.equivFun z₀ 1 = v - 1 := by
    -- Read off the second basis coordinate of the shifted basepoint.
    rw [hz₀_eq]
    simpa using L.basis_equivFunL_symm_apply_one (u - 1) (v - 1)
  have hzcoord0 : L.basis.equivFun z 0 = a + (u - 1) := by
    -- Add the basepoint back to recover the first coordinate of `z`.
    calc
      L.basis.equivFun z 0 = L.basis.equivFun ((z - z₀) + z₀) 0 := by
        congr 1
        ring
      _ = L.basis.equivFun (z - z₀) 0 + L.basis.equivFun z₀ 0 := by simp
      _ = a + (u - 1) := by rw [hsub0, hz₀_coord0]
  have hzcoord1 : L.basis.equivFun z 1 = b + (v - 1) := by
    -- Add the basepoint back to recover the second coordinate of `z`.
    calc
      L.basis.equivFun z 1 = L.basis.equivFun ((z - z₀) + z₀) 1 := by
        congr 1
        ring
      _ = L.basis.equivFun (z - z₀) 1 + L.basis.equivFun z₀ 1 := by simp
      _ = b + (v - 1) := by rw [hsub1, hz₀_coord1]
  have hm_eq : (m : ℝ) = a + (u - 1) := by
    -- Compare the first integer lattice coordinate with the shifted-cell coordinate.
    calc
      (m : ℝ) = L.basis.equivFun z 0 := by simpa using hm.symm
      _ = a + (u - 1) := hzcoord0
  have hn_eq : (n : ℝ) = b + (v - 1) := by
    -- Compare the second integer lattice coordinate with the shifted-cell coordinate.
    calc
      (n : ℝ) = L.basis.equivFun z 1 := by simpa using hn.symm
      _ = b + (v - 1) := hzcoord1
  have hm_low : (-1 : ℝ) < (m : ℝ) := by
    linarith [ha0, hu.1, hm_eq]
  have hm_high : (m : ℝ) < 1 := by
    linarith [ha1, hu.2, hm_eq]
  have hn_low : (-1 : ℝ) < (n : ℝ) := by
    linarith [hb0, hv.1, hn_eq]
  have hn_high : (n : ℝ) < 1 := by
    linarith [hb1, hv.2, hn_eq]
  have hm_low_int : (-1 : ℤ) < m := by
    exact_mod_cast hm_low
  have hm_high_int : m < 1 := by
    exact_mod_cast hm_high
  have hn_low_int : (-1 : ℤ) < n := by
    exact_mod_cast hn_low
  have hn_high_int : n < 1 := by
    exact_mod_cast hn_high
  have hm_zero : m = 0 := by
    omega
  have hn_zero : n = 0 := by
    omega
  have hzcoord_zero0 : L.basis.equivFun z 0 = 0 := by
    simpa [hm_zero] using hm
  have hzcoord_zero1 : L.basis.equivFun z 1 = 0 := by
    simpa [hn_zero] using hn
  -- Vanishing of both basis coordinates forces the lattice point itself to be the origin.
  apply L.basis.equivFun.injective
  ext i
  fin_cases i
  · simpa [hzcoord_zero0]
  · simpa [hzcoord_zero1]

/-- Helper for Exercise 3: the zero set of the entire, nontrivial theta function `θ₁` is
countable. -/
theorem theta_one_zero_set_countable (τ : ℂ) (hτ : 0 < τ.im) :
    Set.Countable {z : ℂ | (θ₁[τ]) z = 0} := by
  let slice : ℕ → Set ℂ :=
    fun n ↦ Metric.closedBall (0 : ℂ) n ∩ {z : ℂ | (θ₁[τ]) z = 0}
  have hnontrivial : ¬ Set.EqOn (θ₁[τ]) 0 Set.univ := by
    -- Nontriviality of `θ₁` upgrades the compact-zero-set theorem to the whole plane.
    intro hEq
    apply exercise_3_theta_one_ne_zero τ hτ
    ext z
    simpa using hEq (x := z) (by simp)
  have hslice_countable : ∀ n : ℕ, Set.Countable (slice n) := by
    intro n
    have hfinite :
        (Metric.closedBall (0 : ℂ) n ∩ (θ₁[τ]) ⁻¹' ({0} : Set ℂ)).Finite :=
      analytic_zero_set_finite_of_isCompact_subset
        (D := Set.univ) (K := Metric.closedBall (0 : ℂ) n) (f := θ₁[τ])
        (isCompact_closedBall (0 : ℂ) n) (by simp) isConnected_univ
        ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ)
        hnontrivial
    -- Each closed-ball slice is finite, hence countable.
    simpa [slice, Set.preimage]
      using hfinite.countable
  -- Cover the plane by closed balls centered at `0` and write the zero set as a countable union.
  refine (Set.countable_iUnion hslice_countable).mono ?_
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  refine ⟨?_, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hn

/-- Helper for Exercise 3: one can choose a slanted fundamental cell for the lattice `⟨1, τ⟩`
whose boundary avoids the zero set of `θ₁`, while the cell contains no lattice point except `0`. -/
theorem exists_theta_one_boundary_regular_slanted_periodParallelogram
    (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ t : ℝ,
      0 < t ∧ t < 1 ∧
      let L := theta_one_period_pair τ hτ
      let z₀ := -(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ
      0 ∈ L.periodParallelogram z₀ ∧
        (∀ z ∈ frontier (L.periodParallelogram z₀), (θ₁[τ]) z ≠ 0) ∧
        (∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0) := by
  let L : PeriodPair := theta_one_period_pair τ hτ
  let zeroSet : Set ℂ := {z : ℂ | (θ₁[τ]) z = 0}
  let A₁ : Set ℝ := (fun z : ℂ ↦ -(L.basis.equivFun z 0)) '' zeroSet
  let A₂ : Set ℝ := (fun z : ℂ ↦ 1 - L.basis.equivFun z 0) '' zeroSet
  let A₃ : Set ℝ := (fun z : ℂ ↦ -2 * L.basis.equivFun z 1) '' zeroSet
  let A₄ : Set ℝ := (fun z : ℂ ↦ 2 * (1 - L.basis.equivFun z 1)) '' zeroSet
  let badSet : Set ℝ := A₁ ∪ (A₂ ∪ (A₃ ∪ A₄))
  have hzero_countable : Set.Countable zeroSet := by
    simpa [zeroSet] using theta_one_zero_set_countable τ hτ
  have hA₁ : Set.Countable A₁ := by
    -- Each forbidden parameter family is a countable image of the zero set.
    exact hzero_countable.image (fun z : ℂ ↦ -(L.basis.equivFun z 0))
  have hA₂ : Set.Countable A₂ := by
    exact hzero_countable.image (fun z : ℂ ↦ 1 - L.basis.equivFun z 0)
  have hA₃ : Set.Countable A₃ := by
    exact hzero_countable.image (fun z : ℂ ↦ -2 * L.basis.equivFun z 1)
  have hA₄ : Set.Countable A₄ := by
    exact hzero_countable.image (fun z : ℂ ↦ 2 * (1 - L.basis.equivFun z 1))
  have hbad : Set.Countable badSet := by
    exact hA₁.union (hA₂.union (hA₃.union hA₄))
  have hdense : Dense (badSetᶜ : Set ℝ) := by
    simpa [badSet] using (Set.Countable.dense_compl (𝕜 := ℝ) hbad)
  have hunit_nonempty : (Set.Ioo (0 : ℝ) 1).Nonempty := by
    refine ⟨1 / 2, ?_⟩
    norm_num
  have hchoice : (Set.Ioo (0 : ℝ) 1 ∩ (badSetᶜ : Set ℝ)).Nonempty :=
    hdense.inter_open_nonempty (Set.Ioo (0 : ℝ) 1) isOpen_Ioo hunit_nonempty
  rcases hchoice with ⟨t, htunit, htbad⟩
  have htbad_not : t ∉ badSet := by
    simpa [Set.mem_compl_iff] using htbad
  have ht0 : 0 < t := htunit.1
  have ht1 : t < 1 := htunit.2
  refine ⟨t, ht0, ht1, ?_⟩
  let z₀ : ℂ := -(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ
  change 0 ∈ L.periodParallelogram z₀ ∧
      (∀ z ∈ frontier (L.periodParallelogram z₀), (θ₁[τ]) z ≠ 0) ∧
      (∀ z ∈ L.periodParallelogram z₀, z ∈ L.lattice → z = 0)
  constructor
  · -- The slanted translate still contains the origin.
    refine ⟨t, t / 2, le_of_lt ht0, le_of_lt ht1, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · change 0 = z₀ + t • (1 : ℂ) + (t / 2 : ℝ) • τ
      simp [z₀, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  constructor
  · intro z hzfront
    have hparam :=
      L.parameter_eq_of_mem_frontier_slanted_periodParallelogram
        (t := t) (by simpa [L, z₀, theta_one_period_pair] using hzfront)
    intro hzzero
    -- Route correction: choose `t` outside the countable parameter image of the full zero set,
    -- rather than outside the old ad hoc shifted-cell bad set.
    have ht_mem : t ∈ badSet := by
      rcases hparam with h₁ | h₂ | h₃ | h₄
      · exact Or.inl ⟨z, hzzero, h₁.symm⟩
      · exact Or.inr <| Or.inl ⟨z, hzzero, h₂.symm⟩
      · exact Or.inr <| Or.inr <| Or.inl ⟨z, hzzero, h₃.symm⟩
      · exact Or.inr <| Or.inr <| Or.inr ⟨z, hzzero, h₄.symm⟩
    exact htbad_not ht_mem
  · intro z hzP hzL
    obtain ⟨u, v, hu0, hu1, hv0, hv1, hcoord0, hcoord1⟩ :=
      L.basis_coords_of_mem_slanted_periodParallelogram
        (t := t) (by simpa [L, z₀, theta_one_period_pair] using hzP)
    obtain ⟨m, n, hm, hn⟩ := L.exists_int_basis_coords_of_mem_lattice hzL
    have hm_eq : (m : ℝ) = u - t := by
      -- Compare the first integer coordinate with the slanted-cell coordinate.
      calc
        (m : ℝ) = L.basis.equivFun z 0 := by simpa using hm.symm
        _ = u - t := hcoord0
    have hn_eq : (n : ℝ) = v - t / 2 := by
      -- Compare the second integer coordinate with the slanted-cell coordinate.
      calc
        (n : ℝ) = L.basis.equivFun z 1 := by simpa using hn.symm
        _ = v - t / 2 := hcoord1
    have hm_low : (-1 : ℝ) < (m : ℝ) := by
      linarith [hu0, ht1, hm_eq]
    have hm_high : (m : ℝ) < 1 := by
      linarith [hu1, ht0, hm_eq]
    have hn_low : (-1 : ℝ) < (n : ℝ) := by
      linarith [hv0, ht1, hn_eq]
    have hn_high : (n : ℝ) < 1 := by
      linarith [hv1, ht0, hn_eq]
    have hm_low_int : (-1 : ℤ) < m := by
      exact_mod_cast hm_low
    have hm_high_int : m < 1 := by
      exact_mod_cast hm_high
    have hn_low_int : (-1 : ℤ) < n := by
      exact_mod_cast hn_low
    have hn_high_int : n < 1 := by
      exact_mod_cast hn_high
    have hm_zero : m = 0 := by
      omega
    have hn_zero : n = 0 := by
      omega
    have hzcoord0 : L.basis.equivFun z 0 = 0 := by
      simpa [hm_zero] using hm
    have hzcoord1 : L.basis.equivFun z 1 = 0 := by
      simpa [hn_zero] using hn
    -- Vanishing of both basis coordinates forces the lattice point itself to be the origin.
    apply L.basis.equivFun.injective
    ext i
    fin_cases i
    · simpa [hzcoord0]
    · simpa [hzcoord1]

/-- Helper for Exercise 3: the entire nontrivial theta function `θ₁` cannot vanish on a whole
neighborhood, so its analytic order is never `⊤`. -/
theorem theta_one_analyticOrderAt_ne_top (τ z : ℂ) (hτ : 0 < τ.im) :
    analyticOrderAt (θ₁[τ]) z ≠ ⊤ := by
  have hanalytic : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
    -- Entire holomorphy upgrades to analyticity on a neighborhood of every point of `ℂ`.
    exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
  intro htop
  have hzero_local : (θ₁[τ]) =ᶠ[𝓝 z] 0 := by
    -- Route correction: the local blocker is not a missing derivative identity, but the identity
    -- theorem bridge from `analyticOrderAt = ⊤` to local vanishing.
    simpa using analyticOrderAt_eq_top.mp htop
  have hzero_global : Set.EqOn (θ₁[τ]) 0 Set.univ :=
    hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (by simp) hzero_local
  apply exercise_3_theta_one_ne_zero τ hτ
  ext w
  simpa using hzero_global (x := w) (by simp)

/-- Helper for Exercise 3: boundary nonvanishing forces the divisor of `θ₁` to vanish on the
boundary of a period parallelogram. -/
theorem theta_one_boundary_divisor_zero_of_nonvanishing
    (τ : ℂ) (hτ : 0 < τ.im) {z₀ : ℂ}
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀),
      MeromorphicOn.divisor (θ₁[τ]) ((theta_one_period_pair τ hτ).periodParallelogram z₀) z = 0 := by
  let P : Set ℂ := (theta_one_period_pair τ hτ).periodParallelogram z₀
  have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
    -- The entire theta function is analytic on every neighborhood owner.
    exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
  have hanalyticP : AnalyticOnNhd ℂ (θ₁[τ]) P := hanalytic_univ.mono (by intro z hz; simp)
  have hclosedP : IsClosed P := by
    simpa [P] using (theta_one_period_pair τ hτ).isCompact_periodParallelogram z₀ |>.isClosed
  intro z hz
  -- Remove boundary points from the divisor support by the analytic nonvanishing criterion.
  exact divisor_eq_zero_of_analyticOnNhd_nonvanishing hanalyticP (hclosedP.frontier_subset hz)
    (hboundary z hz)

/-- Helper for Exercise 3: boundary nonvanishing also forces meromorphic order `0` for `θ₁` on the
frontier of the chosen period parallelogram. -/
theorem theta_one_boundary_order_zero_of_nonvanishing
    (τ : ℂ) (hτ : 0 < τ.im) {z₀ : ℂ}
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀),
      meromorphicOrderAt (θ₁[τ]) z = (0 : WithTop ℤ) := by
  intro z hz
  have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
    -- Entire holomorphy upgrades to analyticity on every neighborhood owner.
    exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
  have hanalytic : AnalyticAt ℂ (θ₁[τ]) z := by
    -- Restrict the global analytic neighborhood owner to the chosen boundary point.
    exact hanalytic_univ z (by simp)
  -- Read the meromorphic order through analyticity and collapse it to order `0` by nonvanishing.
  simpa [hanalytic.meromorphicOrderAt_eq] using
    hanalytic.analyticOrderAt_eq_zero.mpr (hboundary z hz)

/-- Helper for Exercise 3: for the entire nontrivial theta function `θ₁`, positivity of the
divisor on a set is equivalent to vanishing of the function. -/
theorem theta_one_divisor_pos_iff_eq_zero_on_set
    (τ : ℂ) (hτ : 0 < τ.im) {P : Set ℂ} {z : ℂ} (hzP : z ∈ P) :
    0 < MeromorphicOn.divisor (θ₁[τ]) P z ↔ (θ₁[τ]) z = 0 := by
  have hanalyticP : AnalyticOnNhd ℂ (θ₁[τ]) P := by
    -- Entire holomorphy restricts to the chosen owner `P`.
    exact ((exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ).mono
      (by intro w hw; simp)
  have hanalytic : AnalyticAt ℂ (θ₁[τ]) z := hanalyticP z hzP
  have hnot_top : analyticOrderAt (θ₁[τ]) z ≠ ⊤ :=
    theta_one_analyticOrderAt_ne_top τ z hτ
  constructor
  · intro hzdiv
    by_contra hzero
    have horder_zero : analyticOrderAt (θ₁[τ]) z = 0 := by
      rw [hanalytic.analyticOrderAt_eq_zero]
      exact hzero
    have hdiv_zero : MeromorphicOn.divisor (θ₁[τ]) P z = 0 := by
      -- Read the divisor through the analytic order and collapse the nonvanishing case to order
      -- `0`.
      rw [hanalyticP.meromorphicOn.divisor_apply hzP, (hanalyticP z hzP).meromorphicOrderAt_eq,
        horder_zero]
      simp
    exact (ne_of_gt hzdiv) hdiv_zero
  · intro hzero
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnot_top
    have horder_ne_zero : analyticOrderAt (θ₁[τ]) z ≠ 0 :=
      (hanalytic.analyticOrderAt_ne_zero).2 hzero
    have hn_ne_zero : n ≠ 0 := by
      intro hn_zero
      exact horder_ne_zero (by simpa [hn_zero] using hn.symm)
    have hdiv_eq : MeromorphicOn.divisor (θ₁[τ]) P z = (n : ℤ) := by
      -- Once the analytic order is a genuine finite natural number, the divisor is that same
      -- multiplicity.
      rw [hanalyticP.meromorphicOn.divisor_apply hzP, (hanalyticP z hzP).meromorphicOrderAt_eq,
        ← hn]
      simp
    have hdiv_ne_zero : MeromorphicOn.divisor (θ₁[τ]) P z ≠ 0 := by
      rw [hdiv_eq]
      exact_mod_cast hn_ne_zero
    have hnonneg : 0 ≤ MeromorphicOn.divisor (θ₁[τ]) P z := by
      rw [hdiv_eq]
      exact Int.ofNat_nonneg n
    exact lt_of_le_of_ne hnonneg (Ne.symm hdiv_ne_zero)

/-- Helper for Exercise 3: a boundary-regular period parallelogram admits a singleton oriented
boundary family whose normalized `θ₁` logarithmic-derivative integral is `1`. -/
theorem theta_one_periodParallelogram_boundary_data
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ)
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    ∃ Γ : Unit → ClosedPath ℂ,
      IsOrientedBoundaryOf ((theta_one_period_pair τ hτ).periodParallelogram z₀) Γ ∧
      (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (θ₁[τ]) dz) z)) /
        (2 * Real.pi * Complex.I : ℂ) = 1 := by
  -- Route correction: isolate the remaining source-faithful blocker as the explicit period-cell
  -- contour package, so the divisor-mass theorem below can already be reduced to the argument
  -- principle API.
  -- TODO: define the four-edge closed boundary of the period parallelogram, prove it is an
  -- oriented boundary, and evaluate the normalized integral by pairing opposite edges with
  -- `theta_one_logDeriv_add_one` and `theta_one_logDeriv_add_tau`.
  sorry

/-- Helper for Exercise 3: the source contour argument on a boundary-regular period parallelogram
should package the total divisor mass of `θ₁` on that cell as `1`. -/
theorem theta_one_zero_mass_in_boundary_regular_periodParallelogram_eq_one
    (τ : ℂ) (hτ : 0 < τ.im) (z₀ : ℂ)
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram z₀), (θ₁[τ]) z ≠ 0) :
    let P : Set ℂ := (theta_one_period_pair τ hτ).periodParallelogram z₀
    let s : Finset ℂ :=
      (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ])
        ((theta_one_period_pair τ hτ).isCompact_periodParallelogram z₀)).toFinset
    Finset.sum s (fun z ↦ (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ)) = 1 := by
  classical
  let P : Set ℂ := (theta_one_period_pair τ hτ).periodParallelogram z₀
  let s : Finset ℂ :=
    (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ])
      ((theta_one_period_pair τ hτ).isCompact_periodParallelogram z₀)).toFinset
  have hboundary_divisor_zero :
      ∀ z ∈ frontier P, MeromorphicOn.divisor (θ₁[τ]) P z = 0 := by
    -- Boundary nonvanishing removes every frontier point from the divisor support.
    simpa [P] using theta_one_boundary_divisor_zero_of_nonvanishing τ hτ hboundary
  have hmeromorphic : MeromorphicOn (θ₁[τ]) Set.univ := by
    -- Entire holomorphy of `θ₁` upgrades directly to a meromorphic owner on `ℂ`.
    have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
      exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
    exact hanalytic_univ.meromorphicOn
  obtain ⟨Γ, hΓ, hΓint⟩ :=
    theta_one_periodParallelogram_boundary_data τ hτ z₀ hboundary
  have hfinsum :
      ∑ᶠ z, (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ) = 1 := by
    have harg :
        (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (θ₁[τ]) dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) =
          ∑ᶠ z, (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ) := by
      -- Apply the argument principle to the singleton oriented boundary family from the contour
      -- package and simplify the trivial shift by `a = 0`.
      simpa [P] using
        argument_principle_on_oriented_boundary
          (Γ := Γ) (D := Set.univ) (K := P) (f := θ₁[τ]) (a := 0)
          hmeromorphic isOpen_univ (by intro z hz; simp) hΓ
          (by
            intro z hz
            simpa using hboundary_divisor_zero z hz)
    calc
      ∑ᶠ z, (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ) =
          (∑ i, ∫ᶜ z in (Γ i).toPath, ((logDeriv (θ₁[τ]) dz) z)) /
            (2 * Real.pi * Complex.I : ℂ) := harg.symm
      _ = 1 := hΓint
  -- Convert the ambient `finsum` from the argument principle back to the exact finite-support sum
  -- shape used by the later uniqueness argument.
  calc
    Finset.sum s (fun z ↦ (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ)) =
        ∑ᶠ z, (MeromorphicOn.divisor (θ₁[τ]) P z : ℂ) := by
          simpa [P, s] using
            finset_sum_divisor_eq_finsum_support
              (K := P) (g := θ₁[τ])
              ((theta_one_period_pair τ hτ).isCompact_periodParallelogram z₀)
    _ = 1 := hfinsum

/-- Helper for Exercise 3: on a boundary-regular slanted fundamental cell, the source `h'/h`
count should force every zero of `θ₁` in that cell to be the origin. -/
theorem theta_one_zero_eq_zero_of_mem_boundary_regular_slanted_cell
    (τ : ℂ) (hτ : 0 < τ.im) {t : ℝ}
    (hzero_mem :
      0 ∈ (theta_one_period_pair τ hτ).periodParallelogram
        (-(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ))
    (hboundary :
      ∀ z ∈ frontier ((theta_one_period_pair τ hτ).periodParallelogram
        (-(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ)), (θ₁[τ]) z ≠ 0)
    {w : ℂ}
    (hwP :
      w ∈ (theta_one_period_pair τ hτ).periodParallelogram
        (-(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ))
    (hwzero : (θ₁[τ]) w = 0) :
    w = 0 := by
  let L : PeriodPair := theta_one_period_pair τ hτ
  let z₀ : ℂ := -(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ
  let P : Set ℂ := L.periodParallelogram z₀
  let d : ℂ → ℤ := MeromorphicOn.divisor (θ₁[τ]) P
  have hcompact : IsCompact P := by
    simpa [L, P, z₀] using L.isCompact_periodParallelogram z₀
  have hzero_div : 0 < d 0 := by
    -- The origin is a known zero of `θ₁`, so its divisor contribution is positive.
    simpa [d, P] using
      (theta_one_divisor_pos_iff_eq_zero_on_set τ hτ (P := P)
        (by simpa [L, P, z₀] using hzero_mem)).2 (jacobi_theta_one_zero_at_zero τ)
  have hw_div : 0 < d w := by
    -- The candidate zero `w` contributes positive divisor mass inside the same cell.
    simpa [d, P] using
      (theta_one_divisor_pos_iff_eq_zero_on_set τ hτ (P := P)
        (by simpa [L, P, z₀] using hwP)).2 hwzero
  have hsupport_sum :
      let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ]) hcompact).toFinset
      Finset.sum s (fun z ↦ (d z : ℂ)) = 1 := by
    -- Apply the packaged source-faithful contour count to the chosen slanted cell.
    simpa [L, z₀, P, d] using
      theta_one_zero_mass_in_boundary_regular_periodParallelogram_eq_one τ hτ z₀
        (by simpa [L, z₀, P] using hboundary)
  by_contra hw_ne
  let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := P) (g := θ₁[τ]) hcompact).toFinset
  have hsum_int : s.sum d = 1 := by
    have hsum_cast : ((s.sum d : ℤ) : ℂ) = 1 := by
      simpa [s, d] using hsupport_sum
    exact_mod_cast hsum_cast
  have hzero_mem_support : 0 ∈ s := by
    -- Positive divisor mass puts the origin into the finite support finset.
    have hzero_ne : d 0 ≠ 0 := (ne_of_gt hzero_div)
    exact by
      simpa [s, d, Function.mem_support] using hzero_ne
  have hw_mem_support : w ∈ s := by
    have hw_ne_div : d w ≠ 0 := (ne_of_gt hw_div)
    exact by
      simpa [s, d, Function.mem_support] using hw_ne_div
  have hnonneg : ∀ z ∈ s, 0 ≤ d z := by
    intro z hz
    have hzsupport : z ∈ (MeromorphicOn.divisor (θ₁[τ]) P).support := by
      simpa [s] using hz
    have hzP : z ∈ P := (MeromorphicOn.divisor (θ₁[τ]) P).supportWithinDomain hzsupport
    by_cases hzzero : (θ₁[τ]) z = 0
    · exact le_of_lt ((theta_one_divisor_pos_iff_eq_zero_on_set τ hτ (P := P) hzP).2 hzzero)
    · have hzdiv_zero : d z = 0 := by
        -- Nonvanishing at an interior point forces divisor value `0`.
        have hanalytic_univ : AnalyticOnNhd ℂ (θ₁[τ]) Set.univ := by
          exact (exercise_3_theta_one_differentiable τ hτ).differentiableOn.analyticOnNhd isOpen_univ
        have hanalyticP : AnalyticOnNhd ℂ (θ₁[τ]) P := hanalytic_univ.mono (by
          intro u hu
          simp)
        simpa [d] using divisor_eq_zero_of_analyticOnNhd_nonvanishing hanalyticP hzP hzzero
      simpa [hzdiv_zero]
  have hzero_ge_one : 1 ≤ d 0 := by omega
  have hw_ge_one : 1 ≤ d w := by omega
  have hw_mem_erase : w ∈ s.erase 0 := by simp [hw_mem_support, hw_ne]
  have hw_le_erase : d w ≤ (s.erase 0).sum d := by
    exact Finset.single_le_sum
      (fun z hz ↦ hnonneg z (Finset.mem_of_mem_erase hz)) hw_mem_erase
  have hsplit : d 0 + (s.erase 0).sum d = s.sum d := by
    simpa [add_comm] using s.sum_erase_add d hzero_mem_support
  have hsum_lower : d 0 + d w ≤ s.sum d := by
    rw [← hsplit]
    linarith
  have hsum_two : 2 ≤ s.sum d := by
    linarith
  omega

/-- Helper for Exercise 3: the remaining source-faithful contour argument should produce a
translated period parallelogram for periods `1` and `τ` that contains `0` and has no other zero of
`θ₁` inside it. -/
theorem exists_theta_one_unique_zero_periodParallelogram
    (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ z₀ : ℂ,
      0 ∈ (theta_one_period_pair τ hτ).periodParallelogram z₀ ∧
      ∀ w ∈ (theta_one_period_pair τ hτ).periodParallelogram z₀,
        (θ₁[τ]) w = 0 → w = 0 := by
  obtain ⟨t, ht0, ht1, hcell, hboundary, _hlattice⟩ :=
    exists_theta_one_boundary_regular_slanted_periodParallelogram τ hτ
  let z₀ : ℂ := -(t : ℝ) • (1 : ℂ) - (t / 2 : ℝ) • τ
  refine ⟨z₀, by simpa [z₀] using hcell, ?_⟩
  intro w hwP hwzero
  -- Route correction: the main theorem now factors through the slanted boundary-regular cell
  -- chooser, leaving only the source contour-count uniqueness step unresolved.
  exact theta_one_zero_eq_zero_of_mem_boundary_regular_slanted_cell τ hτ
    (t := t) (by simpa [z₀] using hcell) (by simpa [z₀] using hboundary)
    (by simpa [z₀] using hwP) hwzero

/-- Exercise 3 (12): for `Im τ > 0`, the zeros of `θ₁` are exactly the lattice points
`m + nτ` with `m, n ∈ ℤ`. -/
theorem exercise_3_theta_one_zero_iff (τ u : ℂ) (hτ : 0 < τ.im) :
    (θ₁[τ]) u = 0 ↔ ∃ m n : ℤ, u = m + n * τ :=
by
  constructor
  · intro hzero
    let L : PeriodPair := theta_one_period_pair τ hτ
    obtain ⟨z₀, hz₀, hunique⟩ := exists_theta_one_unique_zero_periodParallelogram τ hτ
    obtain ⟨w, hwP, hwzero, hwsub⟩ :=
      theta_one_zero_exists_periodParallelogram_representative τ u z₀ hτ hzero
    have hw_eq_zero : w = 0 := hunique w hwP hwzero
    have hu_mem : u ∈ L.lattice := by
      have hneg : -u ∈ L.lattice := by
        simpa [hw_eq_zero] using hwsub
      simpa using L.lattice.neg_mem hneg
    rcases L.mem_lattice.mp hu_mem with ⟨m, n, hmn_raw⟩
    have hmn : ((m : ℤ) : ℂ) + ((n : ℤ) : ℂ) * τ = u := by
      simpa [L, theta_one_period_pair, mul_comm, add_assoc, add_left_comm, add_comm] using hmn_raw
    refine ⟨m, n, ?_⟩
    -- The representative reduction leaves exactly the lattice relation `u = m + nτ`.
    simpa [mul_comm, add_assoc, add_left_comm, add_comm] using hmn.symm
  · rintro ⟨m, n, rfl⟩
    -- The reverse implication is already controlled by the two translation formulas.
    exact theta_one_zero_at_lattice_point τ m n

/-- Exercise 3 (13): for `Im τ > 0`, the zeros of `θ₀` are exactly the shifted lattice points
`m + (n + 1 / 2)τ` with `m, n ∈ ℤ`. -/
theorem exercise_3_theta_zero_zero_iff (τ u : ℂ) (hτ : 0 < τ.im) :
    (θ₀[τ]) u = 0 ↔
      ∃ m n : ℤ, u = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ :=
by
  constructor
  · intro hzero
    have hshift_eq :
        (θ₀[τ]) u =
          Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u - τ / 2 + τ / 4)) *
            (θ₁[τ]) (u - τ / 2) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        exercise_3_theta_zero_add_half_tau τ (u - τ / 2)
    have hshift :
        Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u - τ / 2 + τ / 4)) *
            (θ₁[τ]) (u - τ / 2) = 0 := by
      rw [← hshift_eq]
      exact hzero
    have hscalar_ne :
        Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (u - τ / 2 + τ / 4)) ≠ 0 := by
      exact mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)
    have htheta :
        (θ₁[τ]) (u - τ / 2) = 0 :=
      (mul_eq_zero.mp hshift).resolve_left hscalar_ne
    rcases (exercise_3_theta_one_zero_iff τ (u - τ / 2) hτ).mp htheta with ⟨m, n, hu⟩
    refine ⟨m, n, ?_⟩
    calc
      u = (u - τ / 2) + τ / 2 := by ring
      _ = m + n * τ + τ / 2 := by rw [hu]
      _ = m + ((n : ℂ) + (1 / 2 : ℂ)) * τ := by ring
  · rintro ⟨m, n, rfl⟩
    have htheta :
        (θ₁[τ]) (m + n * τ) = 0 :=
      (exercise_3_theta_one_zero_iff τ (m + n * τ) hτ).mpr ⟨m, n, rfl⟩
    -- Evaluate the half-`τ` shift formula at the lattice zero of `θ₁`.
    have hshift :
        (θ₀[τ]) (m + ((n : ℂ) + (1 / 2 : ℂ)) * τ) =
          Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (m + n * τ + τ / 4)) *
            (θ₁[τ]) (m + n * τ) := by
      calc
        (θ₀[τ]) (m + ((n : ℂ) + (1 / 2 : ℂ)) * τ) = (θ₀[τ]) (m + n * τ + τ / 2) := by
          ring
        _ =
            Complex.I * Complex.exp (-(Real.pi : ℂ) * Complex.I * (m + n * τ + τ / 4)) *
              (θ₁[τ]) (m + n * τ) := by
                simpa [add_assoc, add_left_comm, add_comm] using
                  exercise_3_theta_zero_add_half_tau τ (m + n * τ)
    rw [hshift, htheta]
    simp

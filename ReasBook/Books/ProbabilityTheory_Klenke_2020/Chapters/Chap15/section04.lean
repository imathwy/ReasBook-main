import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_15_4_1 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- A real random variable satisfies the textbook finite absolute-moment root-growth limsup
hypothesis if it is measurable, all of its absolute moments are finite, and the normalized nth
roots of those absolute moments are bounded above along `atTop`. -/
def HasFiniteAbsoluteMomentRootLimsup (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) : Prop :=
  Measurable X ∧
    (∀ n : ℕ, Integrable (fun ω ↦ |X ω| ^ n) P) ∧
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n : ℕ ↦ ((n : ℝ)⁻¹) * Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ)))

/-- Finite absolute-moment root-growth limsup is exactly measurability, finiteness of all absolute
moments, and boundedness of the normalized absolute moments. -/
@[simp] theorem hasFiniteAbsoluteMomentRootLimsup_iff (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → ℝ) :
    HasFiniteAbsoluteMomentRootLimsup P X ↔
      Measurable X ∧
        (∀ n : ℕ, Integrable (fun ω ↦ |X ω| ^ n) P) ∧
          Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
            (fun n : ℕ ↦ ((n : ℝ)⁻¹) * Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ))) := by
  rfl

/-- The source-facing finite absolute-moment root-growth limsup hypothesis implies the chapter's
canonical moment-determinacy predicate. -/
-- Proof sketch: a finite limsup bounds the normalized absolute moments along `atTop`, which is
-- the growth input needed in the same moment-problem argument used in Corollary 15.32.
theorem isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimsup P X) :
    IsMomentDeterminate P X := sorry

-- Proof sketch: first pass from the source-facing limsup hypotheses to the canonical owner
-- predicate `IsMomentDeterminate`. For each Borel set `A`, use the factorization of mixed moments
-- together with nonnegativity to form the tilted measures with densities `X^m` and `Y^n`; then
-- moment determinacy shows
-- `E[X^m 1_A(Y)] = E[X^m] P[Y ∈ A]` for all `m`, then apply the same argument to the tilted
-- conditional laws of `X` given `Y ∈ A` to deduce factorization of all rectangle probabilities.
/-- Exercise 15.4.1: if nonnegative real random variables `X` and `Y` both satisfy the textbook
finite absolute-moment root-growth limsup hypothesis and all mixed moments factorize as
`E[X^m Y^n] = E[X^m] E[Y^n]`, with those mixed moments finite, then `X` and `Y` are independent. -/
theorem indepFun_of_mixed_moment_factorization_of_hasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hY_growth : HasFiniteAbsoluteMomentRootLimsup P Y)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (h_mixedMoments :
      ∀ m n : ℕ, Integrable (fun ω ↦ X ω ^ m * Y ω ^ n) P ∧
        ∫ ω, X ω ^ m * Y ω ^ n ∂P = moment X m P * moment Y n P) :
    IndepFun X Y P := by
  have hX_det : IsMomentDeterminate P X :=
    isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup P hX_growth
  have hY_det : IsMomentDeterminate P Y :=
    isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup P hY_growth
  sorry

/-! ### Exercise_15_4_2 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 15.4.2 is `source-facing`: the textbook content is the joint law of the splitting
transform `(B, Z) ↦ (B * Z, (1 - B) * Z)`.
The owner abstraction is therefore the joint `HasLaw` statement for that transformed pair; the
independence and one-coordinate laws below are derived API from this owner theorem. -/
section

variable (P : Measure Ω) {B Z : Ω → ℝ} {r s : ℝ}
variable (hr : 0 < r) (hs : 0 < s)
variable (hB : HasLaw B (betaMeasure r s) P)
variable (hZ : HasLaw Z (gammaMeasure (r + s) 1) P)
variable (hBZ : IndepFun B Z P)

-- The textbook notation `I_{1, a}` is interpreted as the Gamma law with shape `a` and unit rate,
-- namely `gammaMeasure a 1`. The source's `T_{1, r}` is treated as the same OCR-corrupted
-- notation.
-- Proof sketch: apply Exercise 15.4.1 to the change of variables `(b, z) ↦ (bz, (1 - b)z)` on
-- `(0,1) × (0,∞)`, identify the transported joint density with the product of the Gamma densities
-- of shapes `r` and `s`, and then use independence of `B` and `Z` to pass from the product law of
-- `(B, Z)` to the law of the transformed pair.
/-- Exercise 15.4.2: if `B` has Beta law `betaMeasure r s` and `Z` has Gamma law
`gammaMeasure (r + s) 1`, independently, then the pair `(B * Z, (1 - B) * Z)` has the product
Gamma law with shapes `r` and `s` and unit rate. -/
theorem beta_gamma_unit_rate_split_hasLaw_prod
    :
    HasLaw
      (fun ω ↦ (B ω * Z ω, (1 - B ω) * Z ω))
      ((gammaMeasure r 1).prod (gammaMeasure s 1)) P := sorry

-- Proof sketch: combine the main joint-law statement with
-- `indepFun_iff_map_prod_eq_prod_map_map`; the product target measure is exactly the criterion for
-- independence of the two coordinates.
/-- The Beta-Gamma splitting transform sends an independent Beta/Gamma pair to two independent
unit-rate Gamma random variables. -/
theorem beta_gamma_unit_rate_split_indepFun
    :
    IndepFun (fun ω ↦ B ω * Z ω) (fun ω ↦ (1 - B ω) * Z ω) P := sorry

-- Proof sketch: compose the joint-law statement with the first-coordinate projection and use that
-- the first marginal of a product measure is the first factor.
/-- The first coordinate in the Beta-Gamma splitting transform has Gamma law with shape `r` and
unit rate. -/
theorem beta_gamma_unit_rate_split_fst_hasLaw
    :
    HasLaw (fun ω ↦ B ω * Z ω) (gammaMeasure r 1) P := sorry

-- Proof sketch: compose the joint-law statement with the second-coordinate projection and use
-- that the second marginal of a product measure is the second factor.
/-- The second coordinate in the Beta-Gamma splitting transform has Gamma law with shape `s` and
unit rate. -/
theorem beta_gamma_unit_rate_split_snd_hasLaw
    :
    HasLaw (fun ω ↦ (1 - B ω) * Z ω) (gammaMeasure s 1) P := sorry

end

/-! ### Exercise_15_4_3 (from Items/Chap15) -/
open MeasureTheory

/-- The candidate function `t ↦ exp (-|t|^α)` appearing in Exercise 15.4.3. -/
noncomputable def phi_alpha (α : ℝ) : ℝ → ℂ :=
  fun t ↦ Complex.exp (-(Real.rpow |t| α))

-- Proof sketch: evaluate the defining formula for `phi_alpha` at `t = 0`, use `|0| = 0`,
-- `Real.zero_rpow` for positive exponent, and `Complex.exp_zero`.
/-- The function `phi_alpha` is normalized at the origin when `α` is positive. -/
theorem phi_alpha_zero (α : ℝ) (hα : 0 < α) :
    phi_alpha α 0 = 1 := sorry

-- Proof sketch: assume `charFun μ = phi_alpha α`, use the second-order expansion of
-- characteristic functions with finite second moment to identify the quadratic coefficient with the
-- variance, then compare with the flatter-than-quadratic behavior of `exp (-|t|^α)` at `0` when
-- `α > 2` to deduce zero variance and hence degeneracy, contradicting the nontrivial expansion.
/-- Exercise 15.4.3: for `α > 2`, the function `φ_α(t) = exp (-|t|^α)` is not the characteristic
function of a probability measure on `ℝ`. -/
theorem not_exists_probabilityMeasure_charFun_eq_phi_alpha (α : ℝ) (hα : 2 < α) :
    ¬ ∃ μ : ProbabilityMeasure ℝ, charFun (μ : Measure ℝ) = phi_alpha α := sorry

/-! ### Exercise_15_4_4 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

/- Exercise 15.4.4 is `source-facing`: its public objects are the characteristic function of the
common law and the empirical averages themselves. The owner abstractions are the canonical law map
`charFun` and the chapter's i.i.d. shorthand `IsIID`; the file therefore keeps the textbook
conclusions directly visible while avoiding parallel local wrappers. -/

-- Proof sketch: a characteristic function comes from a probability law, so the derivative criterion
-- for `charFun` at `0` forces the derivative to be purely imaginary; extract the real coefficient.
/-- Exercise 15.4.4 (1): if the characteristic function of a real probability law is
differentiable at `0`, then its derivative at `0` is `i m` for some real `m`. -/
theorem hasDerivAt_charFun_zero_eq_real_mul_I
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {dphi : ℂ}
    (hphi : HasDerivAt (charFun μ) dphi 0) :
    ∃ m : ℝ, dphi = (m : ℂ) * Complex.I := sorry

section IIDAverage

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: for the common law `P.map (X 0)`, differentiate the `n`th power relation for the
-- characteristic function of normalized partial sums and combine it with the weak law of large
-- numbers for i.i.d. averages.
/-- Exercise 15.4.4 (2): for a `0`-based Lean i.i.d. sequence `X 0, X 1, ...` representing the
textbook sequence `X₁, X₂, ...`, the common characteristic function has derivative `i m` at `0`
exactly when the empirical averages converge in probability to `m`. -/
theorem hasDerivAt_charFun_map_zero_iff_tendstoInMeasure_average
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX_iid : IsIID X P) (m : ℝ) :
    HasDerivAt (charFun (P.map (X 0))) ((m : ℂ) * Complex.I) 0 ↔
      TendstoInMeasure P
        (fun n ω ↦ (∑ i ∈ Finset.range n, X i ω) / n)
        atTop
        (fun _ ↦ m) := sorry

end IIDAverage

-- Proof sketch: use the derivative-at-zero criterion for characteristic functions together with
-- the nonnegativity assumption, then identify the limiting truncated first moment with the full
-- expectation and conclude integrability of `id`.
/-- Exercise 15.4.4 (3): if a real probability law is supported on `[0, ∞)` and its
characteristic function is differentiable at `0`, then the first moment is finite and the
derivative at `0` equals the expectation multiplied by `i`. Equivalently,
`μ[id] = -Complex.I * φ'(0) < ∞`. -/
theorem integrable_id_of_nonnegative_hasDerivAt_charFun_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {dphi : ℂ}
    (hphi : HasDerivAt (charFun μ) dphi 0)
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ x) :
    Integrable id μ ∧ dphi = (μ[id] : ℂ) * Complex.I := sorry

-- Proof sketch: choose a heavy-tailed real probability law whose positive and negative tails
-- cancel in the first derivative of the characteristic function, while the absolute first moment
-- remains infinite.
/-- Exercise 15.4.4 (4): there exists a real probability distribution whose characteristic
function is differentiable at `0` although the absolute first moment is infinite. -/
theorem exists_probabilityMeasure_differentiableAt_charFun_zero_not_integrable_id :
    ∃ μ : ProbabilityMeasure ℝ,
      DifferentiableAt ℝ (charFun (μ : Measure ℝ)) 0 ∧
        ¬ Integrable id (μ : Measure ℝ) := sorry

/-! ### Theorem_15_4 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']

noncomputable section

-- Proof sketch: a bounded range sits inside a compact interval `[a, b]`, hence `|X|` is bounded by
-- `max |a| |b|`. Therefore every exponential moment `E[exp (t |X|)]` with `t ≥ 0` is bounded by
-- the constant `exp (t * max |a| |b|)`, so `exp (t |X|)` is integrable under the probability
-- measure `μ`.
private theorem integrable_exp_mul_abs_of_isBounded_range
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX_bdd : Bornology.IsBounded (Set.range X)) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω ↦ Real.exp (t * |X ω|)) μ := by
  let a : ℝ := sInf (Set.range X)
  let b : ℝ := sSup (Set.range X)
  have hX_mem : ∀ ω, X ω ∈ Set.Icc a b := fun ω ↦
    hX_bdd.subset_Icc_sInf_sSup ⟨ω, rfl⟩
  refine Integrable.of_bound
    (((measurable_abs.comp hX).const_mul t).exp.aestronglyMeasurable)
    (Real.exp (t * max |a| |b|)) <|
    Filter.Eventually.of_forall fun ω ↦ ?_
  have h_abs : |X ω| ≤ max |a| |b| := abs_le_max_abs_abs (hX_mem ω).1 (hX_mem ω).2
  have h_mul : t * |X ω| ≤ t * max |a| |b| := mul_le_mul_of_nonneg_left h_abs ht
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using Real.exp_le_exp.mpr h_mul

/-- Theorem 15.4: a bounded real random variable is determined by its moments among measurable real
random variables. -/
theorem isMomentDeterminate_of_isBounded_range
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hX_bdd : Bornology.IsBounded (Set.range X)) :
    IsMomentDeterminate μ X :=
  (method_of_moments_of_integrable_exp_abs_map μ X hX zero_lt_one
    (integrable_exp_mul_abs_of_isBounded_range μ hX hX_bdd zero_le_one)).2

/-- In particular, a bounded real random variable is identically distributed with any measurable
real random variable that has the same moments. -/
theorem identDistrib_of_forall_moment_eq_of_isBounded_range
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_bdd : Bornology.IsBounded (Set.range X))
    (hY_moments : ∀ n : ℕ, Integrable (fun ω ↦ |Y ω| ^ n) ν)
    (h_moments : ∀ n : ℕ, moment X n μ = moment Y n ν) :
    IdentDistrib X Y μ ν := by
  let hX_det : IsMomentDeterminate μ X := isMomentDeterminate_of_isBounded_range μ hX hX_bdd
  exact
    { aemeasurable_fst := hX.aemeasurable
      aemeasurable_snd := hY.aemeasurable
      map_eq := hX_det.map_eq ν Y hY hY_moments h_moments }

/-! ### Exercise_15_4_5 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

/- Exercise 15.4.5 is `source-facing`: it states the Fréchet--Shohat subsequence and moment
criteria directly for weakly convergent laws on `ℝ`. Its `core/canonical` owner abstractions are
`ProbabilityMeasure ℝ` for weak convergence and `Measure.IsMomentDeterminate (μ : Measure ℝ)` for
the moment-determinate limit law; the moment equalities are derived from those owners rather than
additional primitive data. -/

section SubseqMoments

variable {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} {r : ℝ} (φ : ℕ ↪o ℕ)

-- Proof sketch: combine weak convergence of the subsequence with the uniform `r`th absolute-moment
-- bound to obtain uniform integrability of `x ↦ |x| ^ s` for `0 < s < r`, then apply the
-- portmanteau/Vitali argument to the limit law.
/-- Exercise 15.4.5 (1): Item (i). If a subsequence of laws converges weakly and the whole
sequence has uniformly bounded `r`th absolute moments, then the weak limit has finite `s`th
absolute moment for every `0 < s < r`. -/
theorem integrable_abs_rpow_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    Integrable (fun x : ℝ ↦ |x| ^ s) (μ : Measure ℝ) := sorry

-- Proof sketch: apply the previous uniform-integrability input to the test functions
-- `x ↦ |x| ^ s`; weak convergence of the laws then upgrades to convergence of the corresponding
-- absolute moments along the subsequence.
/-- Exercise 15.4.5 (2): Item (i). Under the same hypotheses, the `s`th absolute moments converge
along the weakly convergent subsequence for every `0 < s < r`. -/
theorem tendsto_integral_abs_rpow_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {s : ℝ} (hs : 0 < s) (hsr : s < r) :
    Tendsto (fun l ↦ ∫ x, |x| ^ s ∂(ν (φ l) : Measure ℝ)) atTop
      (𝓝 (∫ x, |x| ^ s ∂(μ : Measure ℝ))) := sorry

-- Proof sketch: first use the bounded `r`th absolute moments to deduce uniform integrability of
-- `x ↦ x ^ k` for each natural `k` with `0 < k < r`, then apply item (i) to identify the limit of
-- the ordinary moments along the weakly convergent subsequence.
/-- Exercise 15.4.5 (3): Item (i). Under the same hypotheses, every ordinary moment of order
`k ∈ ℕ ∩ (0, r)` converges along the weakly convergent subsequence. -/
theorem tendsto_moment_of_subseq_tendsto_of_bounded_rth_absoluteMoment
    (h_tendsto : Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ))
    (hbound :
      sSup (Set.range fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (|x| ^ r) ∂(ν n : Measure ℝ)) < ⊤)
    {k : ℕ} (hk0 : 0 < k) (hkr : (k : ℝ) < r) :
    Tendsto (fun l ↦ moment id k (ν (φ l) : Measure ℝ)) atTop
      (𝓝 (moment id k (μ : Measure ℝ))) := sorry

end SubseqMoments

-- Proof sketch: convergence of the first absolute moments implies tightness of the laws; apply
-- sequential compactness of tight probability measures on `ℝ` to extract a weakly convergent
-- subsequence, then use item (i) to identify all moments of the limit law with the prescribed
-- limits `m k` and to recover that this limit law has finite absolute moments of every order.
/-- Exercise 15.4.5 (4): Item (ii). If every moment sequence eventually exists and converges to a
finite limit, then there is a probability law on `ℝ` with exactly those moments and a weakly
convergent subsequence of the original laws converging to it; in particular, the limiting law has
finite absolute moments of every order. -/
theorem exists_subseq_tendsto_probabilityMeasure_of_eventually_defined_moments
    {ν : ℕ → ProbabilityMeasure ℝ} (m : ℕ → ℝ)
    (hfinite :
      ∀ k : ℕ, ∀ᶠ n in atTop, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (ν n : Measure ℝ))
    (hm : ∀ k : ℕ, Tendsto (fun n ↦ moment id k (ν n : Measure ℝ)) atTop (𝓝 (m k))) :
    ∃ μ : ProbabilityMeasure ℝ,
      (∀ k : ℕ, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (μ : Measure ℝ)) ∧
        (∀ k : ℕ, moment id k (μ : Measure ℝ) = m k) ∧
        ∃ φ : ℕ ↪o ℕ, Tendsto (fun l ↦ ν (φ l)) atTop (𝓝 μ) := sorry

/- The canonical chapter notion of a moment-determinate law is the owner predicate
`Measure.IsMomentDeterminate`; the corresponding owner-level theorem
`Measure.isMomentDeterminate_iff` exposes both the distinguished law's finite moments and its
uniqueness among comparison laws with the same finite moments. -/
recall Measure.isMomentDeterminate_iff

-- Proof sketch: by item (ii), every subsequence admits a further weakly convergent subsequence
-- whose limit law has moments `moment id k μ` and finite absolute moments of every order; the
-- eventual finite-moment hypothesis is needed here because `moment` is the totalized Bochner
-- integral in this project, so this genuine finite-moment content of the subsequential limit must
-- be recovered for the subsequential limits. Moment determinacy of `μ` already packages the
-- finite-moment content of the distinguished limit law together with uniqueness, so every such
-- subsequential limit equals `μ`, and the standard subsequence criterion yields convergence of
-- the whole sequence.
/-- Exercise 15.4.5 (5): Item (iii). This is the Fréchet--Shohat theorem in the source-faithful
form for the chapter's totalized moment convention: if the approximating laws eventually have all
absolute moments finite and the moments of `ν n` converge to those of a moment-determinate law
`μ`, then the laws `ν n` themselves converge weakly to `μ`. -/
theorem tendsto_probabilityMeasure_of_moments_tendsto_of_moment_determinate
    {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hfinite :
      ∀ k : ℕ, ∀ᶠ n in atTop, Integrable (fun x : ℝ ↦ |x| ^ (k : ℝ)) (ν n : Measure ℝ))
    (hm : ∀ k : ℕ,
      Tendsto (fun n ↦ moment id k (ν n : Measure ℝ)) atTop
        (𝓝 (moment id k (μ : Measure ℝ))))
    (hdet : Measure.IsMomentDeterminate (μ : Measure ℝ)) :
    Tendsto ν atTop (𝓝 μ) := sorry

/-! ### Exercise_15_4_6 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u v

variable {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
variable {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

-- Proof sketch: expand the odd power of the partial sum, group terms by mixed moments, use
-- independence and centering to discard the configurations with singleton indices, and count the
-- surviving terms to obtain an `n^(k-1)` bound.
/-- Odd moments of centered iid partial sums grow at most like `n^(k - 1)`. -/
theorem exists_odd_moment_bounds_of_iid_centered
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P) :
    ∃ d : ℕ → ℝ,
      ∀ k n : ℕ,
        1 ≤ k →
          |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ (2 * k - 1) ∂P| ≤
            d (2 * k - 1) * (n : ℝ) ^ (k - 1) := sorry

-- Proof sketch: expand the even power of the partial sum, isolate the leading contribution from
-- pairings of distinct squared factors, identify its combinatorial coefficient
-- `(2k)! / (2^k k!)`, and bound all remaining index patterns by `n^(k-1)`.
/-- Even moments of centered iid partial sums have the Gaussian leading term up to an
`n^(k - 1)` error. -/
theorem exists_even_moment_expansion_bounds_of_iid_centered
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P) :
    ∃ d : ℕ → ℝ,
      ∀ k n : ℕ,
        1 ≤ k →
          |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ (2 * k) ∂P -
              (((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
                (∫ ω, X 0 ω ^ 2 ∂P) ^ k * (n : ℝ) ^ k)| ≤
            d (2 * k) * (n : ℝ) ^ (k - 1) := sorry

-- Proof sketch: apply the characteristic-function derivative formula from Theorem 15.31(i) to a
-- standard Gaussian law and evaluate the odd derivatives at the origin.
/-- Standard Gaussian odd moments vanish. -/
theorem gaussianReal_odd_moments_eq_zero (hY : HasLaw Y (gaussianReal 0 1) P') :
    ∀ k : ℕ,
      ∫ ω, Y ω ^ (2 * k + 1) ∂P' = 0 := sorry

-- Proof sketch: differentiate the standard Gaussian characteristic function at `0`, then compare
-- the resulting even derivatives with the moment formula from Theorem 15.31(i).
/-- Standard Gaussian even moments are the factorial-ratio constants
`(2k)! / (2^k k!)`. -/
theorem gaussianReal_even_moments_eq_factorial_ratio (hY : HasLaw Y (gaussianReal 0 1) P') :
    ∀ k : ℕ,
      ∫ ω, Y ω ^ (2 * k) ∂P' =
        (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ)) := sorry

-- Proof sketch: combine the moment bounds from the odd and even expansions with the Gaussian
-- moment identities, use the moment-convergence criterion from Exercise 15.4.5, and then pass
-- from convergence of moments to convergence in distribution against a standard Gaussian limit law.
/-- Centered iid real variables with finite absolute moments of every order have standardized
partial sums converging in distribution to the standard Gaussian law. -/
theorem standardizedPartialSum_tendstoInDistribution_standardGaussian_of_iid_all_moments
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    (hvar : Var[X 0; P] ≠ 0)
    (hY : HasLaw Y (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ↦ standardizedPartialSum P X n) atTop Y (fun _ ↦ P) P' := sorry

-- Proof sketch: first obtain convergence in distribution of `standardizedPartialSum P X n` to a
-- standard Gaussian variable from the previous theorem, then rewrite this as convergence of the
-- associated pushforward probability measures in
-- `ProbabilityMeasure ℝ`.
/-- Exercise 15.4.6: item (iii). If `X₁, X₂, ...` are iid centered real random variables with
finite absolute moments of every order and nonzero variance, then the laws of the standardized
partial sums `S_n^*` converge weakly to the standard Gaussian law. -/
theorem standardizedPartialSumLaw_tendsto_standardGaussian_of_iid_all_moments
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    (hvar : Var[X 0; P] ≠ 0) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map ⟨P, inferInstance⟩
          (aemeasurable_standardizedPartialSum P X (fun n ↦ (hident n).aemeasurable_fst) n))
      atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := sorry

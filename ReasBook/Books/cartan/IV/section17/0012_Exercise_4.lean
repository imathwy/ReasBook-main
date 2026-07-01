import Mathlib
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import cartan.II.section05.«0033_Definition_II_1_extra_20»
import cartan.II.section05.«0035_Theorem_II_1_extra_22»
import cartan.IV.section16.«0002_Theorem_IV_4_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter InnerProductSpace Laplacian Metric Real Set Topology
open scoped BigOperators InnerProductSpace

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was chosen by local inspection of mathlib's `Real.circleAverage`,
-- `CircleIntegrable`, `TendstoUniformlyOn`, and Laplacian APIs, together with nearby section-IV.5
-- precedent.

/-- A real-valued function is subharmonic on `D` if it is continuous there and satisfies the
sub-mean inequality on all sufficiently small circles centered at points of `D`. -/
def IsSubharmonicOn (f : ℂ → ℝ) (D : Set ℂ) : Prop :=
  ContinuousOn f D ∧
    ∀ ⦃a : ℂ⦄, a ∈ D →
      ∃ ε > 0, ∀ ⦃r : ℝ⦄, 0 < r → r < ε →
        Metric.closedBall a r ⊆ D ∧ f a ≤ Real.circleAverage f a r

/-- A subharmonic function is continuous on its domain. -/
theorem IsSubharmonicOn.continuousOn {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D) :
    ContinuousOn f D :=
  hf.1

/-- On each admissible circle, the circle-integrability appearing in the mean inequality is
derived from continuity. -/
theorem IsSubharmonicOn.circleIntegrable {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall a r ⊆ D) :
    CircleIntegrable f a r :=
  (hf.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hr.le

/-- An unfolding theorem for `IsSubharmonicOn`. -/
theorem isSubharmonicOn_iff {f : ℂ → ℝ} {D : Set ℂ} :
    IsSubharmonicOn f D ↔
      ContinuousOn f D ∧
        ∀ ⦃a : ℂ⦄, a ∈ D →
          ∃ ε > 0, ∀ ⦃r : ℝ⦄, 0 < r → r < ε →
            Metric.closedBall a r ⊆ D ∧ f a ≤ Real.circleAverage f a r :=
  Iff.rfl

/-- Helper for Exercise 4: every domain carrying a subharmonic function is open. -/
theorem IsSubharmonicOn.isOpen {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D) :
    IsOpen D := by
  -- Each point in the domain comes with a small closed ball still contained in the domain.
  rw [Metric.isOpen_iff]
  intro a ha
  rcases hf.2 ha with ⟨ε, hε_pos, hε⟩
  have hhalf_pos : 0 < ε / 2 := by positivity
  have hhalf_lt : ε / 2 < ε := by linarith
  rcases hε hhalf_pos hhalf_lt with ⟨hball, _⟩
  refine ⟨ε / 2, hhalf_pos, ?_⟩
  intro z hz
  exact hball (ball_subset_closedBall hz)

/-- Helper for Exercise 4: constant functions are subharmonic on open sets. -/
lemma isSubharmonicOn_const {D : Set ℂ} (hD : IsOpen D) (c : ℝ) :
    IsSubharmonicOn (fun _ ↦ c) D := by
  constructor
  · -- Continuity of a constant function is immediate.
    exact continuousOn_const
  · intro a ha
    rcases Metric.isOpen_iff.mp hD a ha with ⟨ε, hε_pos, hε⟩
    refine ⟨ε, hε_pos, ?_⟩
    intro r hr_pos hr_lt
    refine ⟨?_, ?_⟩
    · -- Shrinking from the ambient open ball gives the required closed-ball inclusion.
      exact (Metric.closedBall_subset_ball hr_lt).trans hε
    · -- The circle average of a constant function is that constant.
      rw [Real.circleAverage_const]

/-- Helper for Exercise 4: nonnegative scalar multiples of subharmonic functions stay
subharmonic. -/
theorem IsSubharmonicOn.smul_nonneg {f : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D)
    {c : ℝ} (hc : 0 ≤ c) :
    IsSubharmonicOn (fun z ↦ c * f z) D := by
  constructor
  · -- Multiplication by a fixed scalar preserves continuity.
    simpa using
      (continuousOn_const.mul hf.continuousOn :
        ContinuousOn (fun z : ℂ ↦ (fun _ : ℂ ↦ c) z * f z) D)
  · intro a ha
    rcases hf.2 ha with ⟨ε, hε_pos, hε⟩
    refine ⟨ε, hε_pos, ?_⟩
    intro r hr_pos hr_lt
    rcases hε hr_pos hr_lt with ⟨hball, hmean⟩
    refine ⟨hball, ?_⟩
    -- Multiply the sub-mean inequality by the nonnegative scalar and rewrite the average.
    calc
      c * f a ≤ c * Real.circleAverage f a r := mul_le_mul_of_nonneg_left hmean hc
      _ = Real.circleAverage (fun z ↦ c * f z) a r := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (Real.circleAverage_smul (a := c) (f := f) (c := a) (R := r)).symm

/-- Helper for Exercise 4: sums of two subharmonic functions stay subharmonic. -/
theorem IsSubharmonicOn.add {f g : ℂ → ℝ} {D : Set ℂ} (hf : IsSubharmonicOn f D)
    (hg : IsSubharmonicOn g D) :
    IsSubharmonicOn (fun z ↦ f z + g z) D := by
  constructor
  · -- Continuity is preserved under pointwise addition.
    exact hf.continuousOn.add hg.continuousOn
  · intro a ha
    rcases hf.2 ha with ⟨εf, hεf_pos, hεf⟩
    rcases hg.2 ha with ⟨εg, hεg_pos, hεg⟩
    refine ⟨min εf εg, lt_min hεf_pos hεg_pos, ?_⟩
    intro r hr_pos hr_lt
    have hrf : r < εf := lt_of_lt_of_le hr_lt (min_le_left _ _)
    have hrg : r < εg := lt_of_lt_of_le hr_lt (min_le_right _ _)
    rcases hεf hr_pos hrf with ⟨hballf, hmeanf⟩
    rcases hεg hr_pos hrg with ⟨hballg, hmeang⟩
    refine ⟨hballf, ?_⟩
    -- Use linearity of the circle average on the common admissible circle.
    calc
      f a + g a ≤ Real.circleAverage f a r + Real.circleAverage g a r := add_le_add hmeanf hmeang
      _ = Real.circleAverage (fun z ↦ f z + g z) a r := by
        simpa using
          (Real.circleAverage_add (hf.circleIntegrable hr_pos hballf)
            (hg.circleIntegrable hr_pos hballg)).symm

/-- Helper for Exercise 4: a continuous function that is nonzero at an interior point stays
nonzero on some closed ball around that point. -/
lemma exists_zero_free_closedBall_of_mem_open_of_ne_zero {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : ContinuousOn f D) {a : ℂ} (ha : a ∈ D) (hfa : f a ≠ 0) :
    ∃ R > 0, Metric.closedBall a R ⊆ D ∧ ∀ z ∈ Metric.closedBall a R, f z ≠ 0 := by
  have hfa_norm : 0 < ‖f a‖ := norm_pos_iff.mpr hfa
  rcases Metric.isOpen_iff.mp hD a ha with ⟨R₁, hR₁_pos, hR₁⟩
  rcases (Metric.continuousOn_iff.mp hf) a ha ‖f a‖ hfa_norm with ⟨R₂, hR₂_pos, hR₂⟩
  let R := min (R₁ / 2) (R₂ / 2)
  have hR_pos : 0 < R := by
    dsimp [R]
    positivity
  have hR_lt_R₁ : R < R₁ := by
    dsimp [R]
    have hhalf : R₁ / 2 < R₁ := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hR_lt_R₂ : R < R₂ := by
    dsimp [R]
    have hhalf : R₂ / 2 < R₂ := by linarith
    exact lt_of_le_of_lt (min_le_right _ _) hhalf
  refine ⟨R, hR_pos, ?_⟩
  have hclosed_subset : Metric.closedBall a R ⊆ D :=
    (Metric.closedBall_subset_ball hR_lt_R₁).trans hR₁
  refine ⟨hclosed_subset, ?_⟩
  intro z hz
  have hzD : z ∈ D := hclosed_subset hz
  have hz_dist_lt : dist z a < R₂ := by
    have hz_dist_le : dist z a ≤ R := by
      simpa [Metric.mem_closedBall] using hz
    exact lt_of_le_of_lt hz_dist_le hR_lt_R₂
  have hdist : dist (f z) (f a) < ‖f a‖ := hR₂ z hzD hz_dist_lt
  -- Any point in the ball stays closer to `f a` than the distance from `f a` to `0`.
  intro hfz
  have : False := by
    have hdist' := hdist
    simp [dist_eq_norm, hfz] at hdist'
  exact this.elim

/-- Helper for Exercise 4: on a zero-free analytic closed disc, Jensen's logarithmic mean identity
can be scaled by the nonnegative exponent `p`. -/
lemma circleAverage_scaled_log_norm_eq_scaled_log_center {g : ℂ → ℂ} {c : ℂ} {R p : ℝ}
    (hR : 0 < R) (h₁g : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (h₂g : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    Real.circleAverage (fun z ↦ p * Real.log ‖g z‖) c R = p * Real.log ‖g c‖ := by
  have h₁g' : AnalyticOnNhd ℂ g (Metric.closedBall c |R|) := by
    simpa [abs_of_pos hR] using h₁g
  have h₂g' : ∀ z ∈ Metric.closedBall c |R|, g z ≠ 0 := by
    simpa [abs_of_pos hR] using h₂g
  -- Push the scalar `p` through the circle average, then invoke the zero-free logarithmic mean
  -- identity coming from Jensen's formula.
  calc
    Real.circleAverage (fun z ↦ p * Real.log ‖g z‖) c R
        = p * Real.circleAverage (fun z ↦ Real.log ‖g z‖) c R := by
          simpa [smul_eq_mul] using
            (Real.circleAverage_fun_smul (a := p) (f := fun z ↦ Real.log ‖g z‖) (c := c)
              (R := R))
    _ = p * Real.log ‖g c‖ := by
          rw [h₁g'.circleAverage_log_norm_of_ne_zero h₂g']

/-- Helper for Exercise 4: Jensen's inequality for `exp` on the circle parameter turns the
logarithmic mean into a mean inequality for exponentials. -/
lemma circleAverage_exp_scaled_log_le {g : ℂ → ℂ} {c : ℂ} {R p : ℝ} (hp : 0 ≤ p) (hR : 0 < R)
    (h₁g : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (h₂g : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    Real.exp (Real.circleAverage (fun z ↦ p * Real.log ‖g z‖) c R) ≤
      Real.circleAverage (fun z ↦ Real.exp (p * Real.log ‖g z‖)) c R := by
  have hlog_circle : CircleIntegrable (fun z ↦ Real.log ‖g z‖) c R := by
    exact
      (h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm_of_nonneg hR.le
  have hscaled_log_circle : CircleIntegrable (fun z ↦ p * Real.log ‖g z‖) c R := by
    -- Scalar multiples preserve circle integrability of the logarithmic boundary data.
    simpa [smul_eq_mul] using hlog_circle.const_fun_smul (a := p)
  have hg_contOn : ContinuousOn (fun θ : ℝ ↦ g (circleMap c R θ)) Set.univ := by
    exact h₁g.continuousOn.comp (t := Metric.closedBall c R) (continuous_circleMap c R).continuousOn
      (fun θ _ ↦ circleMap_mem_closedBall c hR.le θ)
  have hg_cont : Continuous (fun θ : ℝ ↦ g (circleMap c R θ)) := by
    simpa [continuousOn_univ] using hg_contOn
  have hrpow_cont : Continuous (fun θ : ℝ ↦ Real.rpow ‖g (circleMap c R θ)‖ p) := by
    exact hg_cont.norm.rpow_const (fun _ ↦ Or.inr hp)
  have hlogexp_eq :
      ∀ θ : ℝ,
        Real.exp (p * Real.log ‖g (circleMap c R θ)‖) =
          Real.rpow ‖g (circleMap c R θ)‖ p := by
    intro θ
    have hθ_nonzero : g (circleMap c R θ) ≠ 0 :=
      h₂g (circleMap c R θ) (circleMap_mem_closedBall c hR.le θ)
    have hθ_pos : 0 < ‖g (circleMap c R θ)‖ := norm_pos_iff.mpr hθ_nonzero
    -- On the zero-free circle, `exp (p * log ‖g‖)` is exactly `‖g‖^p`.
    simpa [mul_comm] using (Real.rpow_def_of_pos hθ_pos p).symm
  have : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    rw [Set.uIoc_of_le (by positivity : 0 ≤ 2 * Real.pi)]
    infer_instance
  have : NeZero (MeasureTheory.volume (Set.uIoc 0 (2 * Real.pi))) := ⟨by simp⟩
  -- Route correction: isolate Jensen on the interval-average surface before rewriting back to
  -- `Real.circleAverage`.
  rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
  have hJensen :
      Real.exp (⨍ θ in 0..(2 * Real.pi), p * Real.log ‖g (circleMap c R θ)‖) ≤
        ⨍ θ in 0..(2 * Real.pi), Real.exp (p * Real.log ‖g (circleMap c R θ)‖) := by
    -- Apply Jensen's inequality for the convex function `exp` on the parameter interval.
    refine convexOn_exp.map_average_le continuousOn_exp isClosed_univ (by simp) ?_ ?_
    · rw [Set.uIoc_of_le (by positivity : 0 ≤ 2 * Real.pi)]
      exact hscaled_log_circle.1
    · exact (MeasureTheory.integrable_congr (Filter.Eventually.of_forall hlogexp_eq)).mpr
        hrpow_cont.integrableOn_uIoc
  simpa only [MeasureTheory.average_congr (Filter.Eventually.of_forall hlogexp_eq)] using hJensen

/-- Helper for Exercise 4: Jensen's formula on a zero-free analytic closed disc gives the
sub-mean inequality for `‖g‖^p`. -/
lemma circleAverage_norm_rpow_ge_center_of_analytic_nonvanishing {g : ℂ → ℂ} {c : ℂ} {R p : ℝ}
    (hp : 0 ≤ p) (hR : 0 < R) (h₁g : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (h₂g : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    Real.rpow ‖g c‖ p ≤ Real.circleAverage (fun z ↦ Real.rpow ‖g z‖ p) c R := by
  have hc_nonzero : g c ≠ 0 := h₂g c (Metric.mem_closedBall_self hR.le)
  have hc_pos : 0 < ‖g c‖ := norm_pos_iff.mpr hc_nonzero
  -- First rewrite the center term as an exponential of the logarithmic mean, then invoke the
  -- interval-parameter Jensen inequality and convert the boundary exponential back to `Real.rpow`.
  calc
    Real.rpow ‖g c‖ p = Real.exp (p * Real.log ‖g c‖) := by
      simpa [mul_comm] using (Real.rpow_def_of_pos hc_pos p)
    _ = Real.exp (Real.circleAverage (fun z ↦ p * Real.log ‖g z‖) c R) := by
      rw [circleAverage_scaled_log_norm_eq_scaled_log_center hR h₁g h₂g]
    _ ≤ Real.circleAverage (fun z ↦ Real.exp (p * Real.log ‖g z‖)) c R := by
      exact circleAverage_exp_scaled_log_le hp hR h₁g h₂g
    _ = Real.circleAverage (fun z ↦ Real.rpow ‖g z‖ p) c R := by
      rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
      refine MeasureTheory.average_congr ?_
      filter_upwards with θ
      have hθ_nonzero : g (circleMap c R θ) ≠ 0 :=
        h₂g (circleMap c R θ) (circleMap_mem_closedBall c hR.le θ)
      have hθ_pos : 0 < ‖g (circleMap c R θ)‖ := norm_pos_iff.mpr hθ_nonzero
      -- The zero-free boundary again lets us rewrite the exponential expression as `‖g‖^p`.
      simpa [mul_comm] using (Real.rpow_def_of_pos hθ_pos p).symm

/-- Exercise 4 (1). If `f` is holomorphic on the open set `D`, then `z ↦ ‖f z‖^p`, written with
`Real.rpow`, is subharmonic on `D` for every real exponent `p ≥ 0`. -/
theorem differentiableOn_norm_rpow_isSubharmonicOn {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) {p : ℝ} (hp : 0 ≤ p) :
    IsSubharmonicOn (fun z ↦ Real.rpow ‖f z‖ p) D := by
  by_cases hp0 : p = 0
  · -- The exponent-zero branch is the constant-one function.
    simpa [hp0, Real.rpow_zero] using isSubharmonicOn_const hD 1
  · have hp_pos : 0 < p := lt_of_le_of_ne hp <| by simpa [eq_comm] using hp0
    refine ⟨?_, ?_⟩
    · -- Continuity follows from continuity of `f`, then `‖f‖`, then `Real.rpow`.
      simpa using
        (hf.continuousOn.norm.rpow_const (p := p) fun z hz ↦ Or.inr hp :
          ContinuousOn (fun z ↦ Real.rpow ‖f z‖ p) D)
    · intro a ha
      by_cases hfa : f a = 0
      · rcases Metric.isOpen_iff.mp hD a ha with ⟨ε, hε_pos, hε⟩
        refine ⟨ε, hε_pos, ?_⟩
        intro r hr_pos hr_lt
        refine ⟨(Metric.closedBall_subset_ball hr_lt).trans hε, ?_⟩
        -- The center value is zero, while the whole circle average is nonnegative.
        have hcenter : (fun z ↦ Real.rpow ‖f z‖ p) a = 0 := by
          simp [hfa, Real.zero_rpow hp0]
        rw [hcenter]
        exact Real.circleAverage_nonneg_of_nonneg fun z hz ↦
          Real.rpow_nonneg (norm_nonneg _) _
      · obtain ⟨R, hR_pos, hRsubset, hRzero⟩ :=
          exists_zero_free_closedBall_of_mem_open_of_ne_zero hD hf.continuousOn ha hfa
        refine ⟨R, hR_pos, ?_⟩
        intro r hr_pos hr_lt
        have hclosed : Metric.closedBall a r ⊆ D :=
          (Metric.closedBall_subset_closedBall (le_of_lt hr_lt)).trans hRsubset
        have hzero : ∀ z ∈ Metric.closedBall a r, f z ≠ 0 := fun z hz ↦
          hRzero z ((Metric.closedBall_subset_closedBall (le_of_lt hr_lt)) hz)
        have hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall a r) :=
          (hf.analyticOnNhd hD).mono hclosed
        refine ⟨hclosed, ?_⟩
        -- Route correction: once the disc is fixed inside `D` and zero-free, the source proof
        -- closes this branch by Jensen on `log ‖f‖`.
        exact circleAverage_norm_rpow_ge_center_of_analytic_nonvanishing hp hr_pos hanalytic hzero

/-- Exercise 4 (2). On an open set `D`, a finite nonnegative linear combination of subharmonic
functions on `D` is again subharmonic on `D`. -/
theorem isSubharmonicOn_finset_nonneg_sum {ι : Type} {s : Finset ι} {a : ι → ℝ}
    {f : ι → ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hf : ∀ i ∈ s, IsSubharmonicOn (f i) D)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    IsSubharmonicOn (fun z ↦ s.sum fun i ↦ a i * f i z) D := by
  classical
  -- Route correction: the original empty-set statement was false, so the induction now starts from
  -- the constant-zero function on the ambient open set `D`.
  induction s using Finset.induction_on with
  | empty =>
      -- The empty sum is the zero function.
      simpa using isSubharmonicOn_const hD 0
  | @insert i s hi ih =>
      have hfi : IsSubharmonicOn (f i) D := hf i (by simp)
      have hai : 0 ≤ a i := ha i (by simp)
      have hfs : ∀ j ∈ s, IsSubharmonicOn (f j) D := by
        intro j hj
        exact hf j (by simp [hj])
      have has : ∀ j ∈ s, 0 ≤ a j := by
        intro j hj
        exact ha j (by simp [hj])
      have hsum : IsSubharmonicOn (fun z ↦ s.sum fun j ↦ a j * f j z) D := ih hfs has
      have hscaled : IsSubharmonicOn (fun z ↦ a i * f i z) D :=
        hfi.smul_nonneg hai
      -- Split the inserted sum into the new term plus the previous partial sum.
      convert hscaled.add hsum using 1
      ext z
      simp [Finset.sum_insert, hi]

/-- Helper for Exercise 4: the pointwise maximum of two subharmonic functions is subharmonic. -/
lemma isSubharmonicOn_max {D : Set ℂ} {f g : ℂ → ℝ} (hf : IsSubharmonicOn f D)
    (hg : IsSubharmonicOn g D) :
    IsSubharmonicOn (fun z ↦ f z ⊔ g z) D := by
  constructor
  · -- Continuity is preserved under the lattice operation `sup`.
    exact hf.continuousOn.sup hg.continuousOn
  · intro a ha
    rcases hf.2 ha with ⟨εf, hεf_pos, hεf⟩
    rcases hg.2 ha with ⟨εg, hεg_pos, hεg⟩
    refine ⟨min εf εg, lt_min hεf_pos hεg_pos, ?_⟩
    intro r hr_pos hr_lt
    have hrf : r < εf := lt_of_lt_of_le hr_lt (min_le_left _ _)
    have hrg : r < εg := lt_of_lt_of_le hr_lt (min_le_right _ _)
    rcases hεf hr_pos hrf with ⟨hballf, hmeanf⟩
    rcases hεg hr_pos hrg with ⟨hballg, hmeang⟩
    refine ⟨hballf, ?_⟩
    have hsup_int : CircleIntegrable (fun z ↦ f z ⊔ g z) a r := by
      exact ((hf.continuousOn.sup hg.continuousOn).mono
        (sphere_subset_closedBall.trans hballf)).circleIntegrable hr_pos.le
    have hcircle_f :
        Real.circleAverage f a r ≤ Real.circleAverage (fun z ↦ f z ⊔ g z) a r := by
      apply Real.circleAverage_mono (hf.circleIntegrable hr_pos hballf) hsup_int
      intro z hz
      exact le_sup_left
    have hcircle_g :
        Real.circleAverage g a r ≤ Real.circleAverage (fun z ↦ f z ⊔ g z) a r := by
      apply Real.circleAverage_mono (hg.circleIntegrable hr_pos hballg) hsup_int
      intro z hz
      exact le_sup_right
    -- Each branch at the center is controlled by the same average of the pointwise supremum.
    exact sup_le (hmeanf.trans hcircle_f) (hmeang.trans hcircle_g)

/-- Exercise 4 (3). The pointwise supremum of a finite nonempty family of subharmonic functions on
`D` is subharmonic on `D`. -/
theorem isSubharmonicOn_finset_sup {ι : Type} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℂ → ℝ}
    {D : Set ℂ} (hf : ∀ i ∈ s, IsSubharmonicOn (f i) D) :
    IsSubharmonicOn (fun z ↦ s.sup' hs fun i ↦ f i z) D := by
  classical
  -- Induct over the nonempty finite set, using the binary `max` closure lemma at each step.
  revert hf
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      intro hf
      simpa using hf i (by simp)
  | cons i s hi hs ih =>
      intro hf
      have hfi : IsSubharmonicOn (f i) D := hf i (by simp)
      have hfs : IsSubharmonicOn (fun z ↦ s.sup' hs fun j ↦ f j z) D := by
        apply ih
        intro j hj
        exact hf j (by simp [hj])
      -- Rewrite the new finite supremum as a binary `sup` and reuse the helper.
      convert isSubharmonicOn_max hfi hfs using 1
      ext z
      simpa [Finset.cons_eq_insert] using
        (Finset.sup'_insert (s := s) (H := hs) (b := i) (f := fun x ↦ f x z))

/-- Helper for Exercise 4: restricting a subharmonic function to an open subset preserves
subharmonicity. -/
theorem IsSubharmonicOn.mono {f : ℂ → ℝ} {U V : Set ℂ} (hf : IsSubharmonicOn f V)
    (hU_open : IsOpen U) (hUV : U ⊆ V) :
    IsSubharmonicOn f U := by
  refine ⟨hf.continuousOn.mono hUV, ?_⟩
  intro a ha
  rcases hf.2 (hUV ha) with ⟨εV, hεV_pos, hεV⟩
  rcases Metric.isOpen_iff.mp hU_open a ha with ⟨εU, hεU_pos, hεU⟩
  refine ⟨min εV εU, lt_min hεV_pos hεU_pos, ?_⟩
  intro r hr_pos hr_lt
  have hrV : r < εV := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hrU : r < εU := lt_of_lt_of_le hr_lt (min_le_right _ _)
  rcases hεV hr_pos hrV with ⟨_, hmean⟩
  refine ⟨(Metric.closedBall_subset_ball hrU).trans hεU, hmean⟩

/-- Helper for Exercise 4: if a subharmonic function attains the closed-disc maximum at an
interior point, then it is constant on a smaller ball around that point. -/
lemma IsSubharmonicOn.eqOn_ball_of_closedBall_max {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : IsSubharmonicOn u (Metric.ball c R)) {a : ℂ} (ha : a ∈ Metric.ball c R) {M : ℝ}
    (hmax : ∀ z ∈ Metric.closedBall c R, u z ≤ M) (haM : u a = M) :
    ∃ ρ > 0, Set.EqOn u (fun _ ↦ M) (Metric.ball a ρ) := by
  rcases hu.2 ha with ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro y hy
  by_cases hya : y = a
  · simpa [hya] using haM
  · let s : ℝ := dist y a
    have hs_pos : 0 < s := by
      dsimp [s]
      exact dist_pos.mpr hya
    have hs_lt : s < ε := by
      simpa [s, Metric.mem_ball] using hy
    rcases hε hs_pos hs_lt with ⟨hclosed, hmean⟩
    have hy_closed : y ∈ Metric.closedBall a s := by
      simp [s, Metric.mem_closedBall]
    have hy_le : u y ≤ M := by
      exact hmax y (Metric.ball_subset_closedBall (hclosed hy_closed))
    have hu_int : CircleIntegrable u a s := hu.circleIntegrable hs_pos hclosed
    have hconst_int : CircleIntegrable (fun _ : ℂ ↦ M) a s := by
      exact continuousOn_const.circleIntegrable hs_pos.le
    have hmean_le : Real.circleAverage u a s ≤ M := by
      calc
        Real.circleAverage u a s ≤ Real.circleAverage (fun _ : ℂ ↦ M) a s := by
          refine Real.circleAverage_mono hu_int hconst_int ?_
          intro z hz
          have hz' : z ∈ Metric.sphere a s := by
            simpa [abs_of_pos hs_pos] using hz
          exact hmax z (Metric.ball_subset_closedBall (hclosed (Metric.sphere_subset_closedBall hz')))
        _ = M := by
          simpa using (Real.circleAverage_const M a s)
    have hmean_ge : M ≤ Real.circleAverage u a s := by
      simpa [haM] using hmean
    have hmean_eq : Real.circleAverage u a s = M := le_antisymm hmean_le hmean_ge
    by_contra hyM
    have hy_lt : u y < M := lt_of_le_of_ne hy_le hyM
    let ψ : ℝ → ℝ := fun θ ↦ u (circleMap a s θ)
    have hψ_cont : ContinuousOn ψ (Set.Icc 0 (2 * Real.pi)) := by
      exact
        (hu.continuousOn.mono hclosed).comp (t := Metric.closedBall a s)
          (continuous_circleMap a s).continuousOn
          (fun θ _ ↦ circleMap_mem_closedBall a hs_pos.le θ)
    have hψ_le : ∀ θ ∈ Set.Ioc 0 (2 * Real.pi), ψ θ ≤ M := by
      intro θ hθ
      exact hmax (circleMap a s θ)
        (Metric.ball_subset_closedBall (hclosed (circleMap_mem_closedBall a hs_pos.le θ)))
    have hy_eq_circleMap : circleMap a s (y - a).arg = y := by
      calc
        circleMap a s (y - a).arg
            = a + ‖y - a‖ * Complex.exp ((y - a).arg * Complex.I) := by
                simp [circleMap, s, dist_eq_norm]
        _ = a + (y - a) := by
            rw [Complex.norm_mul_exp_arg_mul_I]
        _ = y := by
            ring
    let θ₀ : ℝ := if 0 ≤ (y - a).arg then (y - a).arg else (y - a).arg + 2 * Real.pi
    have hθ₀_mem : θ₀ ∈ Set.Icc 0 (2 * Real.pi) := by
      by_cases harg : 0 ≤ (y - a).arg
      · simp [θ₀, harg]
        linarith [Complex.arg_le_pi (y - a), Real.pi_pos]
      · have harg_le : (y - a).arg ≤ 0 := le_of_not_ge harg
        simp [θ₀, harg]
        constructor
        · linarith [Complex.neg_pi_lt_arg (y - a), Real.pi_pos]
        · linarith
    have hθ₀_eq : circleMap a s θ₀ = y := by
      by_cases harg : 0 ≤ (y - a).arg
      · simp [θ₀, harg, hy_eq_circleMap]
      · calc
          circleMap a s θ₀ = circleMap a s ((y - a).arg + 2 * Real.pi) := by simp [θ₀, harg]
          _ = circleMap a s (y - a).arg := by
              simpa [add_comm] using periodic_circleMap a s ((y - a).arg)
          _ = y := hy_eq_circleMap
    have hψ_lt : ∃ θ ∈ Set.Icc 0 (2 * Real.pi), ψ θ < M := by
      refine ⟨θ₀, hθ₀_mem, ?_⟩
      simpa [ψ, hθ₀_eq] using hy_lt
    have hlt_int :
        (∫ θ in 0..2 * Real.pi, ψ θ) < ∫ θ in 0..2 * Real.pi, M :=
      intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (by positivity) hψ_cont continuousOn_const hψ_le hψ_lt
    have hlt_avg :
        Real.circleAverage u a s < M := by
      have hlt_avg_const :
          Real.circleAverage u a s < Real.circleAverage (fun _ : ℂ ↦ M) a s := by
        have htwo_pi_pos : 0 < 2 * Real.pi := by positivity
        rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
        rw [interval_average_eq_div, interval_average_eq_div]
        exact div_lt_div_of_pos_right hlt_int (by simpa using htwo_pi_pos)
      simpa using hlt_avg_const.trans_eq (Real.circleAverage_const M a s)
    exact (lt_irrefl M) (hmean_eq ▸ hlt_avg)

/-- Helper for Exercise 4: a continuous subharmonic function on a closed disc is bounded above by
its nonpositive boundary values. -/
lemma isSubharmonicOn_nonpos_of_boundary_nonpos_closedBall {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : IsSubharmonicOn u (Metric.ball c R))
    (hu_cont : ContinuousOn u (Metric.closedBall c R))
    (hboundary : ∀ z ∈ Metric.sphere c R, u z ≤ 0) :
    ∀ z ∈ Metric.ball c R, u z ≤ 0 := by
  by_cases hR : 0 < R
  · let K : Set ℂ := Metric.closedBall c R
    have hK_compact : IsCompact K := isCompact_closedBall c R
    obtain ⟨a, haK, haMax⟩ := hK_compact.exists_isMaxOn
      (Metric.nonempty_closedBall.mpr hR.le) hu_cont
    let M : ℝ := u a
    have hmax : ∀ z ∈ K, u z ≤ M := by
      intro z hz
      simpa [M] using haMax hz
    have htarget : M ≤ 0 := by
      by_contra hM_pos
      have hM_pos' : 0 < M := lt_of_not_ge hM_pos
      have ha_ball : a ∈ Metric.ball c R := by
        by_contra ha_ball
        have ha_sphere : a ∈ Metric.sphere c R := by
          rw [Metric.mem_sphere]
          exact le_antisymm (by simpa [K, Metric.mem_closedBall] using haK)
            (not_lt.mp (by simpa [Metric.mem_ball] using ha_ball))
        exact (not_lt_of_ge (hboundary a ha_sphere)) hM_pos'
      obtain ⟨ρ, hρ_pos, hρ_eq⟩ := hu.eqOn_ball_of_closedBall_max ha_ball hmax rfl
      let S : Set K := {x | u x = M}
      have hS_closed : IsClosed S := by
        have hu_restrict : Continuous fun x : K ↦ u x := hu_cont.restrict
        simpa [S] using isClosed_eq hu_restrict continuous_const
      have hS_open : IsOpen S := by
        rw [Metric.isOpen_iff]
        intro x hx
        have hx_not_sphere : x.1 ∉ Metric.sphere c R := by
          intro hx_sphere
          have : u x.1 ≤ 0 := hboundary x.1 hx_sphere
          rw [hx] at this
          exact (not_lt_of_ge this) hM_pos'
        have hx_ball : x.1 ∈ Metric.ball c R := by
          by_contra hx_ball
          have hx_sphere : x.1 ∈ Metric.sphere c R := by
            have hx_closed : x.1 ∈ Metric.closedBall c R := by
              change x.1 ∈ K
              exact x.2
            have hx_dist_le : dist x.1 c ≤ R := by
              rwa [Metric.mem_closedBall] at hx_closed
            rw [Metric.mem_sphere]
            exact le_antisymm hx_dist_le
              (not_lt.mp (by simpa [Metric.mem_ball] using hx_ball))
          exact hx_not_sphere hx_sphere
        obtain ⟨σ, hσ_pos, hσ_eq⟩ := hu.eqOn_ball_of_closedBall_max hx_ball hmax hx
        refine ⟨σ, hσ_pos, ?_⟩
        intro y hy
        have hy' : y.1 ∈ Metric.ball x.1 σ := by simpa using hy
        exact hσ_eq hy'
      have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
      have hS_nonempty : S.Nonempty := ⟨⟨a, haK⟩, rfl⟩
      haveI : PreconnectedSpace K := Subtype.preconnectedSpace isPreconnected_closedBall
      have hS_univ : S = Set.univ := hS_clopen.eq_univ hS_nonempty
      let b : ℂ := circleMap c R 0
      have hbK : b ∈ K := by
        exact circleMap_mem_closedBall c hR.le 0
      have hb_sphere : b ∈ Metric.sphere c R := by
        exact circleMap_mem_sphere c hR.le 0
      have hbM : u b = M := by
        have : (⟨b, hbK⟩ : K) ∈ S := by simp [hS_univ]
        exact this
      have : u b ≤ 0 := hboundary b hb_sphere
      rw [hbM] at this
      exact (not_lt_of_ge this) hM_pos'
    intro z hz
    exact (hmax z (Metric.ball_subset_closedBall hz)).trans htarget
  · intro z hz
    exfalso
    simp [Metric.ball_eq_empty.2 (le_of_not_gt hR)] at hz

/-- Helper for Exercise 4: on a ball, subtracting a harmonic function from a subharmonic one
preserves subharmonicity. -/
theorem IsSubharmonicOn.sub_harmonicContOnCl {f g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : IsSubharmonicOn f (Metric.ball c R)) (hg : HarmonicContOnCl g (Metric.ball c R)) :
    IsSubharmonicOn (fun z ↦ f z - g z) (Metric.ball c R) := by
  refine ⟨hf.continuousOn.sub (hg.continuousOn.mono subset_closure), ?_⟩
  intro a ha
  rcases hf.2 ha with ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro r hr_pos hr_lt
  rcases hε hr_pos hr_lt with ⟨hclosed, hmean⟩
  have hg_ball : HarmonicContOnCl g (Metric.ball a r) :=
    hg.mono (ball_subset_closedBall.trans hclosed)
  have hg_abs : HarmonicContOnCl g (Metric.ball a |r|) := by
    simpa [abs_of_pos hr_pos] using hg_ball
  have hg_circle : CircleIntegrable g a r := by
    -- The harmonic comparison function is continuous on the boundary circle of the smaller ball.
    exact (hg_ball.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hr_pos.le
  refine ⟨hclosed, ?_⟩
  -- Rewrite the mean inequality for `f - g` via the harmonic mean-value identity for `g`.
  calc
    (f a - g a) = f a - g a := by rfl
    _ ≤ Real.circleAverage f a r - g a := sub_le_sub_right hmean _
    _ = Real.circleAverage f a r - Real.circleAverage g a r := by
      rw [← HarmonicContOnCl.circleAverage_eq hg_abs]
    _ = Real.circleAverage (fun z ↦ f z - g z) a r := by
      rw [← Real.circleAverage_fun_sub (hf.circleIntegrable hr_pos hclosed) hg_circle]

/-- Helper for Exercise 4: on a disc, a harmonic majorant with larger boundary values dominates a
subharmonic function throughout the interior. -/
theorem isSubharmonicOn_le_harmonicContOnCl_of_boundary_le_ball {u g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hu : IsSubharmonicOn u (Metric.ball c R))
    (hu_cont : ContinuousOn u (Metric.closedBall c R))
    (hg : HarmonicContOnCl g (Metric.ball c R))
    (hboundary : ∀ z ∈ Metric.sphere c R, u z ≤ g z) :
    ∀ z ∈ Metric.ball c R, u z ≤ g z := by
  intro z hz
  have hR_pos : 0 < R := pos_of_mem_ball hz
  have hsub : IsSubharmonicOn (fun w ↦ u w - g w) (Metric.ball c R) :=
    hu.sub_harmonicContOnCl hg
  have hg_cont : ContinuousOn g (Metric.closedBall c R) := by
    simpa [closure_ball c hR_pos.ne'] using hg.continuousOn
  have hsub_cont : ContinuousOn (fun w ↦ u w - g w) (Metric.closedBall c R) :=
    hu_cont.sub hg_cont
  have hboundary_nonpos :
      ∀ w ∈ Metric.sphere c R, (u w - g w) ≤ 0 := by
    intro w hw
    exact sub_nonpos.mpr (hboundary w hw)
  exact sub_nonpos.mp <|
    isSubharmonicOn_nonpos_of_boundary_nonpos_closedBall hsub hsub_cont hboundary_nonpos z hz

/-- Helper for Exercise 4: uniform convergence on a fixed closed ball implies convergence of the
corresponding circle averages. -/
lemma tendsto_circleAverage_of_tendstoUniformlyOn_closedBall {u : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    {a : ℂ} {r : ℝ} (hr : 0 ≤ r) (hu_cont : ∀ n, ContinuousOn (u n) (Metric.closedBall a r))
    (htu : TendstoUniformlyOn u f atTop (Metric.closedBall a r)) :
    Tendsto (fun n ↦ Real.circleAverage (u n) a r) atTop (𝓝 (Real.circleAverage f a r)) := by
  let U : ℕ → ℝ → ℝ := fun n θ ↦ u n (circleMap a r θ)
  let F : ℝ → ℝ := fun θ ↦ f (circleMap a r θ)
  have hU_cont : ∀ᶠ n in atTop, ContinuousOn (U n) (Set.uIcc 0 (2 * Real.pi)) := by
    -- Continuity on the closed ball transfers to continuity of the circle parametrization.
    refine Filter.Eventually.of_forall ?_
    intro n
    dsimp [U]
    exact (hu_cont n).comp (t := Metric.closedBall a r) (continuous_circleMap a r).continuousOn
      (fun θ _ ↦ circleMap_mem_closedBall a hr θ)
  have hU_tendsto : TendstoUniformlyOn U F atTop (Set.uIcc 0 (2 * Real.pi)) := by
    -- Restrict the composed uniform convergence to the compact parameter interval.
    exact (htu.comp (circleMap a r)).mono fun θ _ ↦ circleMap_mem_closedBall a hr θ
  have hInt :
      Tendsto (fun n ↦ ∫ θ in 0..2 * Real.pi, U n θ) atTop (𝓝 (∫ θ in 0..2 * Real.pi, F θ)) := by
    -- The interval-integral convergence theorem handles the fixed compact parameter interval.
    exact TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn hU_cont hU_tendsto
  have hAvg :
      Tendsto
        (fun n ↦ ((2 * Real.pi) - 0)⁻¹ * ∫ θ in 0..2 * Real.pi, U n θ)
        atTop
        (𝓝 (((2 * Real.pi) - 0)⁻¹ * ∫ θ in 0..2 * Real.pi, F θ)) := by
    -- Multiplying by the constant normalization factor turns integral convergence into average
    -- convergence.
    simpa using tendsto_const_nhds.mul hInt
  -- Rewrite the circle averages as interval averages, then as scaled interval integrals.
  simpa [U, F, Real.circleAverage_eq_intervalAverage, interval_average_eq_div, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hAvg

/-- Exercise 4 (4). A compact-open uniform limit of subharmonic functions is subharmonic. -/
theorem isSubharmonicOn_of_tendstoUniformlyOn_compacts {D : Set ℂ} {u : ℕ → ℂ → ℝ}
    {f : ℂ → ℝ} (hu : ∀ n, IsSubharmonicOn (u n) D)
    (hlimit : ∀ ⦃K : Set ℂ⦄, IsCompact K → K ⊆ D → TendstoUniformlyOn u f atTop K) :
    IsSubharmonicOn f D := by
  have hD_open : IsOpen D := (hu 0).isOpen
  have hloc : TendstoLocallyUniformlyOn u f atTop D := by
    -- Compact-open uniform convergence is exactly local uniform convergence on the open set `D`.
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hD_open).2 ?_
    intro K hKD hK
    exact hlimit hK hKD
  have hf_cont : ContinuousOn f D := by
    -- The locally uniform limit of continuous functions remains continuous on `D`.
    exact hloc.continuousOn <| Filter.Frequently.of_forall fun n ↦ (hu n).continuousOn
  refine ⟨hf_cont, ?_⟩
  intro a ha
  rcases Metric.isOpen_iff.mp hD_open a ha with ⟨ρ, hρ_pos, hρball⟩
  refine ⟨ρ, hρ_pos, ?_⟩
  intro r hr_pos hr_lt
  have hr_nonneg : 0 ≤ r := hr_pos.le
  have hclosed : Metric.closedBall a r ⊆ D :=
    (Metric.closedBall_subset_ball hr_lt).trans hρball
  have hclosed_compact : IsCompact (Metric.closedBall a r) := isCompact_closedBall a r
  have htu_closed :
      TendstoUniformlyOn u f atTop (Metric.closedBall a r) := hlimit hclosed_compact hclosed
  have hcircle_tendsto :
      Tendsto (fun n ↦ Real.circleAverage (u n) a r) atTop (𝓝 (Real.circleAverage f a r)) := by
    -- The boundary averages converge once the functions converge uniformly on the closed ball.
    exact tendsto_circleAverage_of_tendstoUniformlyOn_closedBall hr_nonneg
      (fun n ↦ (hu n).continuousOn.mono hclosed) htu_closed
  have hcenter_tendsto : Tendsto (fun n ↦ u n a) atTop (𝓝 (f a)) := hloc.tendsto_at ha
  have hsubmean : ∀ n, u n a ≤ Real.circleAverage (u n) a r := by
    intro n
    have hun_ball : IsSubharmonicOn (u n) (Metric.ball a r) := by
      -- Restrict to the fixed ball so that the radius `r` is admissible for every approximant.
      refine (hu n).mono Metric.isOpen_ball ?_
      intro z hz
      exact hclosed (Metric.ball_subset_closedBall hz)
    have hun_cont : ContinuousOn (u n) (Metric.closedBall a r) :=
      (hu n).continuousOn.mono hclosed
    obtain ⟨g, hg, hboundary⟩ :=
      dirichlet_problem_disc_exists ((hu n).continuousOn.mono (Metric.sphere_subset_closedBall.trans hclosed))
    have hmajor :
        u n a ≤ g a := by
      -- Compare `u n` with the harmonic Dirichlet solution having the same boundary values.
      exact isSubharmonicOn_le_harmonicContOnCl_of_boundary_le_ball hun_ball hun_cont hg
        (fun z hz ↦ le_of_eq (hboundary hz).symm) a (by simpa [Metric.mem_ball] using hr_pos)
    have hg_abs : HarmonicContOnCl g (Metric.ball a |r|) := by
      simpa [abs_of_pos hr_pos] using hg
    have hboundary_abs : Set.EqOn g (u n) (Metric.sphere a |r|) := by
      simpa [abs_of_pos hr_pos] using hboundary
    calc
      u n a ≤ g a := hmajor
      _ = Real.circleAverage g a r := by
        rw [HarmonicContOnCl.circleAverage_eq hg_abs]
      _ = Real.circleAverage (u n) a r := by
        exact circleAverage_congr_sphere hboundary_abs
  refine ⟨hclosed, ?_⟩
  -- Order is closed in `ℝ`, so the fixed-radius inequalities pass to the limit.
  exact le_of_tendsto_of_tendsto' hcenter_tendsto hcircle_tendsto hsubmean

/-- Exercise 4 (5). A subharmonic function with a relative maximum at an interior point is locally
constant near that point. -/
theorem isSubharmonicOn_eqOn_ball_of_isLocalMaxOn {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : IsSubharmonicOn f D) {a : ℂ} (ha : a ∈ D) (hmax : IsLocalMaxOn f D a) :
    ∃ r > 0, Set.EqOn f (fun _ ↦ f a) (Metric.ball a r) := by
  have hupper : {z | f z ≤ f a} ∈ 𝓝[D] a := hmax
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hupper with ⟨s, hs_nhds, hs_subset⟩
  have hsD_nhds : s ∩ D ∈ 𝓝 a := Filter.inter_mem hs_nhds (hD.mem_nhds ha)
  rcases Metric.mem_nhds_iff.mp hsD_nhds with ⟨R, hR_pos, hRsubset⟩
  let ρ : ℝ := R / 2
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt : ρ < R := by
    dsimp [ρ]
    linarith
  have hclosed_subset : Metric.closedBall a ρ ⊆ s ∩ D :=
    (Metric.closedBall_subset_ball hρ_lt).trans hRsubset
  have hf_ball : IsSubharmonicOn f (Metric.ball a ρ) := by
    -- Shrink to a ball where both the domain and the local upper bound are available.
    refine hf.mono Metric.isOpen_ball ?_
    intro z hz
    exact (hclosed_subset (Metric.ball_subset_closedBall hz)).2
  have hmax_closed : ∀ z ∈ Metric.closedBall a ρ, f z ≤ f a := by
    intro z hz
    exact hs_subset (hclosed_subset hz)
  -- The closed-ball maximum lemma turns the local upper bound into local constancy.
  exact hf_ball.eqOn_ball_of_closedBall_max (by simpa [Metric.mem_ball] using hρ_pos) hmax_closed rfl

/-- Exercise 4 (6). A continuous subharmonic function on a bounded connected open set is bounded
above by any upper bound for its boundary values. -/
theorem isSubharmonicOn_le_of_le_frontier {D : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) (hD_bounded : Bornology.IsBounded D) {f : ℂ → ℝ}
    (hf_cont : ContinuousOn f (closure D)) (hf_subharmonic : IsSubharmonicOn f D) {M : ℝ}
    (hM : ∀ z ∈ frontier D, f z ≤ M) :
    ∀ z ∈ D, f z ≤ M := by
  intro z hz
  by_contra hzM
  have hz_gt : M < f z := lt_of_not_ge hzM
  let K : Set ℂ := closure D
  have hK_compact : IsCompact K := by
    simpa [K] using hD_bounded.isCompact_closure
  obtain ⟨a, haK, haMax⟩ := hK_compact.exists_isMaxOn ⟨z, subset_closure hz⟩ hf_cont
  let M₀ : ℝ := f a
  have hM₀_ge : ∀ w ∈ D, f w ≤ M₀ := by
    intro w hw
    simpa [M₀] using haMax (subset_closure hw)
  have hM₀_gt : M < M₀ := by
    exact lt_of_lt_of_le hz_gt (hM₀_ge z hz)
  have ha_union : a ∈ D ∪ frontier D := by
    simpa [K, closure_eq_self_union_frontier] using haK
  rcases ha_union with haD | haFrontier
  · let S : Set D := {x | f x = M₀}
    have hS_closed : IsClosed S := by
      have hf_restrict : Continuous fun x : D ↦ f x := hf_subharmonic.continuousOn.restrict
      simpa [S] using isClosed_eq hf_restrict continuous_const
    have hS_open : IsOpen S := by
      rw [Metric.isOpen_iff]
      intro x hx
      have hmax_x : IsMaxOn f D x := by
        intro y hy
        rw [hx]
        exact hM₀_ge y hy
      obtain ⟨r, hr_pos, hr_eq⟩ :=
        isSubharmonicOn_eqOn_ball_of_isLocalMaxOn hD_open hf_subharmonic x.2 hmax_x.localize
      refine ⟨r, hr_pos, ?_⟩
      intro y hy
      have hy' : y.1 ∈ Metric.ball x.1 r := by
        simpa using hy
      have hy_eq : f y.1 = M₀ := by
        exact (hr_eq hy').trans hx
      simpa [S] using hy_eq
    have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
    letI : PreconnectedSpace D := Subtype.preconnectedSpace hD_connected.isPreconnected
    have hS_univ : S = Set.univ := hS_clopen.eq_univ ⟨⟨a, haD⟩, rfl⟩
    have hEqD : Set.EqOn f (fun _ ↦ M₀) D := by
      intro w hw
      have : (⟨w, hw⟩ : D) ∈ S := by simpa [hS_univ]
      simpa [S] using this
    have hEqClosure : Set.EqOn f (fun _ ↦ M₀) (closure D) :=
      Set.EqOn.of_subset_closure hEqD hf_cont continuousOn_const subset_closure Subset.rfl
    have hD_ne_univ : D ≠ Set.univ := by
      intro hDu
      exact NormedSpace.unbounded_univ (𝕜 := ℂ) (E := ℂ) (hDu ▸ hD_bounded)
    obtain ⟨b, hb⟩ : (frontier D).Nonempty := by
      exact (nonempty_frontier_iff).2 ⟨⟨z, hz⟩, hD_ne_univ⟩
    have hb_eq : f b = M₀ := hEqClosure (frontier_subset_closure hb)
    exact (not_lt_of_ge (hM b hb)) (hb_eq ▸ hM₀_gt)
  · exact (not_lt_of_ge (hM a haFrontier)) hM₀_gt

/-- Exercise 4 (7). If a continuous subharmonic function on a bounded connected open set attains
its boundary supremum at an interior point, then it is constant on the domain. -/
theorem isSubharmonicOn_eq_constant_of_eq_frontier_sup {D : Set ℂ} (hD_open : IsOpen D)
    (hD_connected : IsConnected D) (hD_bounded : Bornology.IsBounded D) {f : ℂ → ℝ}
    (hf_cont : ContinuousOn f (closure D)) (hf_subharmonic : IsSubharmonicOn f D) {M : ℝ}
    (hM : ∀ z ∈ frontier D, f z ≤ M) {a : ℂ} (ha : a ∈ D) (haM : f a = M) :
    Set.EqOn f (fun _ ↦ M) D := by
  have hle : ∀ z ∈ D, f z ≤ M :=
    isSubharmonicOn_le_of_le_frontier hD_open hD_connected hD_bounded hf_cont hf_subharmonic hM
  let S : Set D := {x | f x = M}
  have hS_closed : IsClosed S := by
    have hf_restrict : Continuous fun x : D ↦ f x := hf_subharmonic.continuousOn.restrict
    simpa [S] using isClosed_eq hf_restrict continuous_const
  have hS_open : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro x hx
    have hmax_x : IsMaxOn f D x := by
      intro y hy
      rw [hx]
      exact hle y hy
    obtain ⟨r, hr_pos, hr_eq⟩ :=
      isSubharmonicOn_eqOn_ball_of_isLocalMaxOn hD_open hf_subharmonic x.2 hmax_x.localize
    refine ⟨r, hr_pos, ?_⟩
    intro y hy
    have hy' : y.1 ∈ Metric.ball x.1 r := by
      simpa using hy
    have hy_eq : f y.1 = M := by
      exact (hr_eq hy').trans hx
    simpa [S] using hy_eq
  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  letI : PreconnectedSpace D := Subtype.preconnectedSpace hD_connected.isPreconnected
  have hS_univ : S = Set.univ := hS_clopen.eq_univ ⟨⟨a, ha⟩, haM⟩
  intro z hz
  have : (⟨z, hz⟩ : D) ∈ S := by simpa [hS_univ]
  simpa [S] using this

/-- Helper for Exercise 4: varying the radius in `circleMap` differentiates to the fixed unit
complex direction at angle `θ`. -/
lemma hasDerivAt_circleMap_radius (a : ℂ) (θ s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ circleMap a t θ) (Complex.exp (θ * Complex.I)) s := by
  -- Freeze the angle and differentiate the affine radius parameterization directly.
  simpa [circleMap, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using
    (HasDerivAt.comp_ofReal
      (((hasDerivAt_id (x := (s : ℂ))).mul_const (Complex.exp (θ * Complex.I))).const_add a))

/-- Helper for Exercise 4: the derivative of the radius-parameter circle map is the fixed unit
complex direction. -/
lemma deriv_circleMap_radius (a : ℂ) (θ s : ℝ) :
    deriv (fun t : ℝ ↦ circleMap a t θ) s = Complex.exp (θ * Complex.I) := by
  -- This is the derivative extracted from the explicit affine radius parametrization.
  exact (hasDerivAt_circleMap_radius a θ s).deriv

/-- Helper for Exercise 4: the real part of `circleMap a r θ` is the expected polar-coordinate
expression. -/
lemma circleMap_re_radius (a : ℂ) (r θ : ℝ) :
    (circleMap a r θ).re = a.re + r * Real.cos θ := by
  -- Expand the circle map and read off its real part.
  rw [circleMap, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  simp [Complex.exp_ofReal_mul_I_re]

/-- Helper for Exercise 4: the imaginary part of `circleMap a r θ` is the expected
polar-coordinate expression. -/
lemma circleMap_im_radius (a : ℂ) (r θ : ℝ) :
    (circleMap a r θ).im = a.im + r * Real.sin θ := by
  -- Expand the circle map and read off its imaginary part.
  rw [circleMap, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  simp [Complex.exp_ofReal_mul_I_im]

/-- Helper for Exercise 4: the positive boundary circle of the closed disc centered at `a` with
radius `r`, parametrized on the unit interval. -/
noncomputable def positive_circle_path (a : ℂ) (r : ℝ) : Path (a + r) (a + r) :=
  Path.mk
    ⟨fun t ↦ circleMap a r (2 * Real.pi * (t : ℝ)), by
      fun_prop⟩
    (by
      -- At `t = 0`, the boundary path starts at the positive real boundary point.
      simp [circleMap])
    (by
      -- At `t = 1`, the angle is `2π`, so the path closes up again.
      simp [circleMap, Complex.exp_two_pi_mul_I])

/-- Helper for Exercise 4: the positive boundary circle has image exactly the geometric sphere
`Metric.sphere a r`. -/
lemma range_positive_circle_path_eq_sphere {a : ℂ} {r : ℝ} (hr : 0 < r) :
    Set.range (positive_circle_path a r) = Metric.sphere a r := by
  -- Every path value lies on the circle, and every circle point occurs at some angle in `(0, 2π]`.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simpa [positive_circle_path, abs_of_pos hr] using
      circleMap_mem_sphere' a r (2 * Real.pi * (t : ℝ))
  · intro hz
    have hz' : z ∈ Metric.sphere a |r| := by
      simpa [abs_of_pos hr] using hz
    rw [← image_circleMap_Ioc a r] at hz'
    rcases hz' with ⟨θ, hθ, rfl⟩
    refine ⟨⟨θ / (2 * Real.pi), ?_, ?_⟩, ?_⟩
    · exact div_nonneg hθ.1.le (by positivity)
    · exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by simpa using hθ.2)
    · have hscale : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
        field_simp [Real.pi_ne_zero]
      simp [positive_circle_path, hscale]

/-- Helper for Exercise 4: on the unit interval, the positive boundary loop is the standard
counterclockwise `circleMap`. -/
lemma positive_circle_path_extend_eq_circleMap {a : ℂ} {r t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (positive_circle_path a r).extend t = circleMap a r (2 * Real.pi * t) := by
  -- Inside the unit interval, `Path.extend` is evaluation of the original circle path.
  simpa [positive_circle_path] using
    (Path.extend_apply (γ := positive_circle_path a r) ht)

/-- Helper for Exercise 4: converting a loop path to a closed path and back only inserts the
endpoint cast forced by the oriented-boundary API. -/
lemma toClosedPath_toPath_eq_cast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath =
      γ.cast (by simpa [Path.toClosedPath] using γ.source)
        (by simpa [Path.toClosedPath] using γ.source) := by
  -- After destructing the loop, the closed-path wrapper and its unpacking are definitionally the
  -- same path up to the endpoint cast.
  cases γ
  rfl

/-- Helper for Exercise 4: the real-curve parametrization of a loop closed path is the original
path extension in real coordinates. -/
lemma toClosedPath_realCurve_eq {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.realCurve = Complex.equivRealProd ∘ γ.extend := by
  -- `ClosedPath.realCurve` only differs from the original loop by the harmless endpoint cast.
  cases γ
  rfl

/-- Helper for Exercise 4: the positive boundary circle is globally `C¹`, hence piecewise
differentiable. -/
lemma positive_circle_path_isPiecewiseDifferentiable (a : ℂ) (r : ℝ) :
    (positive_circle_path a r).IsPiecewiseDifferentiable := by
  -- The counterclockwise circle is a single smooth parametrized arc on the whole unit interval.
  have hdiff : (positive_circle_path a r).IsDifferentiable := by
    rw [Path.IsDifferentiable]
    let g : ℝ → ℂ := fun t ↦ circleMap a r (2 * Real.pi * t)
    have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ 2 * Real.pi * t) := by
      simpa [one_mul] using (contDiff_const.mul contDiff_id)
    have hg : ContDiff ℝ 1 g := by
      simpa [g] using (contDiff_circleMap a r).comp hlin
    refine hg.contDiffOn.congr ?_
    intro t ht
    simpa [g] using positive_circle_path_extend_eq_circleMap (a := a) (r := r) (t := t) ht
  exact hdiff.isPiecewiseDifferentiable

/-- Helper for Exercise 4: the positive circle only identifies equal parameters or the two
endpoints of the unit interval. -/
lemma positive_circle_path_simple_eq_or_endpoints {a : ℂ} {r : ℝ} (hr : r ≠ 0)
    {s t : Set.Icc (0 : ℝ) 1} (h : positive_circle_path a r s = positive_circle_path a r t) :
    s = t ∨ ((s : ℝ) = 0 ∧ (t : ℝ) = 1) ∨ ((s : ℝ) = 1 ∧ (t : ℝ) = 0) := by
  let α : ℝ := 2 * Real.pi * (s : ℝ)
  let β : ℝ := 2 * Real.pi * (t : ℝ)
  have hcircle : circleMap a r α = circleMap a r β := by
    simpa [positive_circle_path, α, β] using h
  have hlen : |(0 : ℝ) - 2 * Real.pi| ≤ 2 * Real.pi := by
    simpa [abs_of_nonneg Real.two_pi_pos.le]
  have hinj :=
    injOn_circleMap_of_abs_sub_le (c := a) (R := r) (a := (0 : ℝ)) (b := 2 * Real.pi) hr hlen
  by_cases hs0 : (s : ℝ) = 0
  · by_cases ht0 : (t : ℝ) = 0
    · exact Or.inl (Subtype.ext (hs0.trans ht0.symm))
    · have htpos : 0 < (t : ℝ) := by
        exact lt_of_le_of_ne t.2.1 (by
          intro htEq
          exact ht0 htEq.symm)
      have hβmem : β ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [β]
          nlinarith [Real.two_pi_pos, htpos]
        · dsimp [β]
          nlinarith [Real.two_pi_pos, t.2.2]
      have h2πmem : (2 * Real.pi : ℝ) ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · nlinarith [Real.pi_pos]
        · exact le_rfl
      have hβ2π : circleMap a r β = circleMap a r (2 * Real.pi) := by
        calc
          circleMap a r β = circleMap a r 0 := by
            simpa [α, hs0] using hcircle.symm
          _ = circleMap a r (2 * Real.pi) := by
            simp [circleMap, Complex.exp_two_pi_mul_I]
      have hβeq : β = 2 * Real.pi := hinj hβmem h2πmem hβ2π
      have ht1 : (t : ℝ) = 1 := by
        dsimp [β] at hβeq
        nlinarith [Real.two_pi_pos, hβeq]
      right
      left
      exact ⟨hs0, ht1⟩
  · by_cases ht0 : (t : ℝ) = 0
    · have hspos : 0 < (s : ℝ) := by
        exact lt_of_le_of_ne s.2.1 (by
          intro hsEq
          exact hs0 hsEq.symm)
      have hαmem : α ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [α]
          nlinarith [Real.two_pi_pos, hspos]
        · dsimp [α]
          nlinarith [Real.two_pi_pos, s.2.2]
      have h2πmem : (2 * Real.pi : ℝ) ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · nlinarith [Real.pi_pos]
        · exact le_rfl
      have hα2π : circleMap a r α = circleMap a r (2 * Real.pi) := by
        calc
          circleMap a r α = circleMap a r 0 := by
            simpa [β, ht0] using hcircle
          _ = circleMap a r (2 * Real.pi) := by
            simp [circleMap, Complex.exp_two_pi_mul_I]
      have hαeq : α = 2 * Real.pi := hinj hαmem h2πmem hα2π
      have hs1 : (s : ℝ) = 1 := by
        dsimp [α] at hαeq
        nlinarith [Real.two_pi_pos, hαeq]
      right
      right
      exact ⟨hs1, ht0⟩
    · have hspos : 0 < (s : ℝ) := by
        exact lt_of_le_of_ne s.2.1 (by
          intro hsEq
          exact hs0 hsEq.symm)
      have htpos : 0 < (t : ℝ) := by
        exact lt_of_le_of_ne t.2.1 (by
          intro htEq
          exact ht0 htEq.symm)
      have hαmem : α ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [α]
          nlinarith [Real.two_pi_pos, hspos]
        · dsimp [α]
          nlinarith [Real.two_pi_pos, s.2.2]
      have hβmem : β ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [β]
          nlinarith [Real.two_pi_pos, htpos]
        · dsimp [β]
          nlinarith [Real.two_pi_pos, t.2.2]
      have hαeqβ : α = β := hinj hαmem hβmem hcircle
      have hst : (s : ℝ) = (t : ℝ) := by
        dsimp [α, β] at hαeqβ
        nlinarith [Real.two_pi_pos, hαeqβ]
      exact Or.inl (Subtype.ext hst)

/-- Helper for Exercise 4: quarter-turning a complex tangent in real coordinates is multiplication
by `I` before converting back to `Plane`. -/
lemma rot90_equivRealProd_eq_equivRealProd_mul_I (z : ℂ) :
    rot90 (Complex.equivRealProd z) = Complex.equivRealProd (z * Complex.I) := by
  -- `Complex.equivRealProd` identifies multiplication by `I` with the standard quarter-turn.
  ext <;> simp [rot90, Complex.equivRealProd]

/-- Helper for Exercise 4: a radial tube around a `C¹` curve has the expected derivative columns. -/
lemma radial_tube_hasFDerivAt {γ n : ℝ → ℂ} {t₀ : ℝ} {v : ℂ}
    (hγCont : ContDiffAt ℝ 1 γ t₀) (hγDeriv : HasDerivAt γ v t₀)
    (hnCont : ContDiffAt ℝ 1 n t₀) :
    ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1 + p.2 • n p.1) (t₀, 0) ∧
      HasFDerivAt (fun p : Plane ↦ γ p.1 + p.2 • n p.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))
        (t₀, 0) := by
  constructor
  · -- The tube map is the sum of the curve branch and the varying transverse branch.
    have hγfst : ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1) (t₀, 0) := by
      simpa using hγCont.comp (x := (t₀, 0)) contDiffAt_fst
    have hnfst : ContDiffAt ℝ 1 (fun p : Plane ↦ n p.1) (t₀, 0) := by
      simpa using hnCont.comp (x := (t₀, 0)) contDiffAt_fst
    simpa using hγfst.add (contDiffAt_snd.smul hnfst)
  · -- At the base point, the transverse derivative contributes only the actual normal vector.
    have hγfst :
        HasFDerivAt (fun p : Plane ↦ γ p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        hγDeriv.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hnfst :
        HasFDerivAt (fun p : Plane ↦ n p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (deriv n t₀)) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        (hnCont.differentiableAt one_ne_zero).hasDerivAt.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hsnd :
        HasFDerivAt (fun p : Plane ↦ p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (t₀, (0 : ℝ)) := by
      simpa using
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    simpa [ContinuousLinearMap.smulRight_apply] using hγfst.add (hsnd.smul hnfst)

/-- Helper for Exercise 4: rescaling the second plane coordinate by a nonzero real factor is a
continuous linear automorphism. -/
noncomputable def plane_second_rescale (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
  { toLinearEquiv :=
      { toFun := fun p ↦ (p.1, p.2 / c)
        invFun := fun p ↦ (p.1, c * p.2)
        left_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        right_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        map_add' := by
          intro p q
          ext <;> simp [div_eq_mul_inv, add_mul]
        map_smul' := by
          intro x p
          ext <;> simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] }
    continuous_toFun := by
      exact continuous_fst.prodMk (continuous_snd.div_const c)
    continuous_invFun := by
      exact continuous_fst.prodMk (continuous_const.mul continuous_snd) }

/-- Helper for Exercise 4: the distance from `a` to a radial exponential point is the absolute
value of its real radial coefficient. -/
lemma dist_add_real_mul_exp_eq_abs {a : ℂ} {s θ : ℝ} :
    dist (a + (s : ℂ) * Complex.exp (θ * Complex.I)) a = |s| := by
  -- The exponential factor has norm `1`, so only the real radius contributes to the distance.
  rw [dist_eq_norm]
  calc
    ‖a + (s : ℂ) * Complex.exp (θ * Complex.I) - a‖ =
        ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ := by
          ring_nf
    _ = ‖(s : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := norm_mul _ _
    _ = |s| := by simp [Complex.norm_exp]

/-- Helper for Exercise 4: the positive angular parameter has constant derivative `2π`. -/
lemma positive_circle_arg_hasDerivAt (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ 2 * Real.pi * t) (2 * Real.pi) t₀ := by
  -- The angular variable is the affine function `t ↦ 2π t`.
  simpa [one_mul] using (hasDerivAt_id t₀).const_mul (2 * Real.pi)

/-- Helper for Exercise 4: quarter-turning the positive circle tangent yields the inward radial
direction scaled by `2πr`. -/
lemma positive_circle_rot90_tangent_eq_scaled_inward {r : ℝ} {t₀ : ℝ} :
    rot90
      (Complex.equivRealProd
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I *
          Complex.exp ((2 * Real.pi * t₀) * Complex.I))) =
      (2 * Real.pi * r) •
        Complex.equivRealProd (-Complex.exp ((2 * Real.pi * t₀) * Complex.I)) := by
  -- Multiplication by `I` turns the tangent into the inward radial direction.
  rw [rot90_equivRealProd_eq_equivRealProd_mul_I]
  have hz :
      (((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) * Complex.I =
        ((2 * Real.pi * r) : ℝ) • (-Complex.exp ((2 * Real.pi * t₀) * Complex.I)) := by
    calc
      (((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) * Complex.I =
          ((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) * (Complex.I * Complex.I) := by
              ring
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) * (-1) := by
            simp
      _ = -((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) := by
            ring
      _ = ((2 * Real.pi * r) : ℝ) • (-Complex.exp ((2 * Real.pi * t₀) * Complex.I)) := by
            simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  simpa using congrArg Complex.equivRealProd hz

/-- Helper for Exercise 4: the positive circle admits a local boundary straightening chart for the
closed disc it bounds. -/
lemma positive_circle_exists_boundary_chart_closedBall {a : ℂ} {r : ℝ} (hr : 0 < r)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((positive_circle_path a r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((positive_circle_path a r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (Metric.closedBall a r)
        ((positive_circle_path a r).toClosedPath.realCurve) t₀ δ := by
  let θ : ℝ → ℝ := fun t ↦ 2 * Real.pi * t
  let γ : ℝ → ℂ := fun t ↦ circleMap a r (θ t)
  let n : ℝ → ℂ := fun t ↦ -Complex.exp (θ t * Complex.I)
  let tangent : ℂ := (2 * Real.pi : ℝ) • (circleMap 0 r (θ t₀) * Complex.I)
  let Ψ : Plane → ℂ := fun p ↦ γ p.1 + p.2 • n p.1
  let Φ : Plane → Plane := fun p ↦ Complex.equivRealProd (Ψ p)
  have _hkeep_regular :
      DifferentiableWithinAt ℝ ((positive_circle_path a r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ := hdiff
  have _hkeep_nonzero :
      derivWithin ((positive_circle_path a r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0 := hderiv
  have hθCont : ContDiffAt ℝ 1 θ t₀ := by
    -- The angular parameter is affine.
    have hθ : ContDiff ℝ 1 θ := by
      simpa [θ, one_mul] using (contDiff_const.mul contDiff_id)
    exact hθ.contDiffAt
  have hγCont : ContDiffAt ℝ 1 γ t₀ := by
    -- The boundary branch is smooth after composing `circleMap` with the affine angle.
    simpa [γ] using (contDiff_circleMap a r).contDiffAt.comp t₀ hθCont
  have hnCont : ContDiffAt ℝ 1 n t₀ := by
    -- The inward radial unit field is also smooth along the circle.
    have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
      simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
    have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
      simpa [one_mul] using hθComplex.mul contDiffAt_const
    simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner).neg
  have hγDeriv : HasDerivAt γ tangent t₀ := by
    -- Differentiate the counterclockwise circle explicitly by the chain rule.
    simpa [γ, tangent] using
      ((hasDerivAt_circleMap a r (θ t₀)).scomp t₀ (positive_circle_arg_hasDerivAt t₀))
  have htangent_formula :
      tangent = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
        Complex.exp (θ t₀ * Complex.I) := by
    -- Rewrite the chain-rule derivative into the explicit tangent form used by the frame lemma.
    calc
      tangent = ((2 * Real.pi : ℝ) : ℂ) * (circleMap 0 r (θ t₀) * Complex.I) := by
        simp [tangent, smul_eq_mul]
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
          Complex.exp (θ t₀ * Complex.I) := by
          rw [circleMap, zero_add]
          simp [mul_assoc, mul_left_comm, mul_comm]
  obtain ⟨hΨcont, hΨderiv⟩ := radial_tube_hasFDerivAt
    (γ := γ) (n := n) (t₀ := t₀) (v := tangent) hγCont hγDeriv hnCont
  have hΦcont : ContDiffAt ℝ 1 Φ (t₀, 0) := by
    -- Converting the complex tube to real-plane coordinates preserves `C¹`.
    simpa [Φ] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_contDiffAt_iff).2 hΨcont
  let v : Plane := Complex.equivRealProd tangent
  let radial : Plane := Complex.equivRealProd (n t₀)
  have hv : v ≠ 0 := by
    -- The circle tangent never vanishes when the radius is positive.
    intro hv0
    have htangent : tangent = 0 := by
      exact Complex.equivRealProd.injective (by simpa [v] using hv0)
    have hscale : ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hr.ne'
    have hmul :
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
          Complex.exp (θ t₀ * Complex.I) = 0 := by
      simpa [htangent_formula] using htangent
    exact Complex.exp_ne_zero (θ t₀ * Complex.I) ((mul_eq_zero.mp hmul).resolve_left hscale)
  have hrot : rot90 v = (2 * Real.pi * r) • radial := by
    -- Quarter-turning the tangent gives the inward normal because the orientation is positive.
    simpa [v, radial, n, θ, htangent_formula, mul_assoc, mul_left_comm, mul_comm] using
      positive_circle_rot90_tangent_eq_scaled_inward (r := r) (t₀ := t₀)
  obtain ⟨e₀, he₀⟩ := rot90_frame_equiv_of_ne_zero v hv
  let c : ℝ := 2 * Real.pi * r
  have hc : c ≠ 0 := by
    positivity
  let e : Plane ≃L[ℝ] Plane := (plane_second_rescale c hc).trans e₀
  have hderiv_map :
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] Plane).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight tangent +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Convert the complex derivative columns into the corresponding real-plane columns.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    simp [ContinuousLinearMap.comp_apply, v, radial, ContinuousLinearMap.smulRight_apply]
  have hΦderiv :
      HasFDerivAt Φ
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial)
        (t₀, 0) := by
    -- The real-plane tube has tangent column `v` and inward normal column `radial`.
    simpa [Φ, hderiv_map] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_hasFDerivAt_iff).2 hΨderiv
  have he : (e : Plane →L[ℝ] Plane) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Rescaling the second frame coordinate turns the `rot90` column into the actual inward normal.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    change e₀ (x, y / c) = x • v + y • radial
    calc
      e₀ (x, y / c) = x • v + (y / c) • rot90 v := by
        simpa [ContinuousLinearMap.smulRight_apply] using
          congrArg (fun f : Plane →L[ℝ] Plane => f (x, y / c)) he₀
      _ = x • v + (y / c) • (c • radial) := by rw [hrot]
      _ = x • v + (((y / c) * c) • radial) := by rw [smul_smul]
      _ = x • v + y • radial := by
        have hyc : y * c⁻¹ * c = y := by
          calc
            y * c⁻¹ * c = y * (c⁻¹ * c) := by ring
            _ = y := by simp [hc]
        simp [div_eq_mul_inv, hyc]
  have hΦderiv' : HasFDerivAt Φ (e : Plane →L[ℝ] Plane) (t₀, 0) := by
    -- This is the invertible derivative needed by the inverse function theorem.
    simpa [he] using hΦderiv
  let δ₀ : OpenPartialHomeomorph Plane Plane :=
    hΦcont.toOpenPartialHomeomorph Φ hΦderiv' one_ne_zero
  let δ₁ : OpenPartialHomeomorph Plane Plane := δ₀.restrContDiff ℝ 1 (by norm_num)
  let strip : Set Plane := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-r) r
  let δ : OpenPartialHomeomorph Plane Plane := δ₁.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
  have hδ₀_source : (t₀, 0) ∈ δ₀.source := by
    -- The inverse function theorem keeps the base point in the chart source.
    exact hΦcont.mem_toOpenPartialHomeomorph_source hΦderiv' one_ne_zero
  have hδ₀_symm : ContDiffAt ℝ 1 δ₀.symm (Φ (t₀, 0)) := by
    -- The local inverse is `C¹` at the image of the base point.
    simpa [δ₀, Φ] using hΦcont.to_localInverse hΦderiv' one_ne_zero
  have hδ₁_source : (t₀, 0) ∈ δ₁.source := by
    -- Restricting to the `C¹` locus still keeps the base point in the source.
    simpa [δ₁, δ₀, Φ] using And.intro hδ₀_source (And.intro hΦcont hδ₀_symm)
  have hsource_subset : δ.source ⊆ δ₁.source := by
    intro p hp
    exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).1
  have htarget_subset : δ.target ⊆ δ₁.target := by
    intro q hq
    exact (show q ∈ δ₁.target ∩ δ₁.symm ⁻¹' strip by simpa [δ, strip] using hq).1
  refine ⟨δ, ?_⟩
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The base point lies in the strip because `t₀ ∈ (0,1)` and `0 ∈ (-r, r)`.
    have hstrip : (t₀, 0) ∈ strip := by
      refine ⟨ht₀, ?_⟩
      constructor <;> linarith
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · -- Any point of the chart source lies over the open parameter strip around the circle.
    intro p hp
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp
    exact ⟨hp'.2.1, Set.mem_univ _⟩
  · -- Restricting the inverse-function chart preserves `C¹` regularity on the smaller source.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_source (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono hsource_subset
  · -- The same inheritance applies to the local inverse on the restricted target.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono htarget_subset
  · intro t ht
    -- Along the horizontal axis, the chart reproduces the positive boundary circle.
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htStrip.1.1.le, htStrip.1.2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd ((positive_circle_path a r).extend t) := by
        congr 1
        simpa [γ, θ] using
          (positive_circle_path_extend_eq_circleMap (a := a) (r := r) (t := t) htIcc).symm
      _ = ((positive_circle_path a r).toClosedPath).realCurve t := by
        simpa [toClosedPath_realCurve_eq]
  · -- The chart image of the boundary branch is exactly the horizontal axis.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htStrip.1.1.le, htStrip.1.2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd ((positive_circle_path a r).extend t) := by
        congr 1
        simpa [γ, θ] using
          (positive_circle_path_extend_eq_circleMap (a := a) (r := r) (t := t) htIcc).symm
      _ = ((positive_circle_path a r).toClosedPath).realCurve t := by
        simpa [toClosedPath_realCurve_eq]
  · -- Negative transverse parameters move strictly outside the closed disc.
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp.1
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          a + ((r - p.2 : ℝ) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
          rw [Complex.equivRealProdCLM_symm_apply]
          exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
          simp [Ψ]
        _ = a + ((r - p.2 : ℝ) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
          simp [γ, n, θ, circleMap, smul_eq_mul]
          ring
    have houtside :
        Complex.equivRealProdCLM.symm (δ p) ∉ Metric.closedBall a r := by
      intro hzBall
      have hle : dist (Complex.equivRealProdCLM.symm (δ p)) a ≤ r := by
        simpa [Metric.mem_closedBall] using hzBall
      have hp_le_r : p.2 ≤ r := by
        exact le_of_lt (lt_trans hp.2 hr)
      have hrad_nonneg : 0 ≤ r - p.2 := by
        exact sub_nonneg.mpr hp_le_r
      rw [hformula, dist_add_real_mul_exp_eq_abs, abs_of_nonneg hrad_nonneg] at hle
      have hrad_gt : r < r - p.2 := by
        simpa [sub_eq_add_neg] using add_lt_add_left (neg_pos.mpr hp.2) r
      exact (not_lt_of_ge hle) hrad_gt
    exact houtside hz.2
  · intro z hz
    -- Positive transverse parameters move strictly inside the open disc, hence into the interior.
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp.1
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          a + ((r - p.2 : ℝ) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
          rw [Complex.equivRealProdCLM_symm_apply]
          exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
          simp [Ψ]
        _ = a + ((r - p.2 : ℝ) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
          simp [γ, n, θ, circleMap, smul_eq_mul]
          ring
    have hrad_nonneg : 0 ≤ r - p.2 := by
      exact sub_nonneg.mpr (le_of_lt hp'.2.2.2)
    have hball :
        Complex.equivRealProdCLM.symm (δ p) ∈ Metric.ball a r := by
      rw [hformula, Metric.mem_ball, dist_add_real_mul_exp_eq_abs, abs_of_nonneg hrad_nonneg]
      have hrad_lt : r - p.2 < r := by
        exact sub_lt_self _ hp.2
      simpa using hrad_lt
    simpa [interior_closedBall a hr.ne'] using hball

/-- Helper for Exercise 4: the positive boundary circle is an oriented boundary of the closed disc
it bounds. -/
lemma closedBallBoundary_isOrientedBoundaryOf {a : ℂ} {r : ℝ} (hr : 0 < r) :
    IsOrientedBoundaryOf (Metric.closedBall a r)
      (fun _ : Unit ↦ (positive_circle_path a r).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (positive_circle_path a r).toClosedPath
  change IsOrientedBoundaryOf (Metric.closedBall a r) Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The closed disc is compact.
    simpa using isCompact_closedBall a r
  · rintro ⟨⟩
    -- The singleton loop inherits piecewise differentiability from the explicit circle path.
    simpa [Γ, Path.toClosedPath] using positive_circle_path_isPiecewiseDifferentiable a r
  · rintro ⟨⟩ s t hst
    -- Simplicity reduces to injectivity of `circleMap` on `(0, 2π]`.
    let zeroI : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
    let oneI : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
    rcases positive_circle_path_simple_eq_or_endpoints (a := a) (r := r) hr.ne' hst with
      hEq | h01 | h10
    · exact Or.inl hEq
    · have hs0 : s = zeroI := Subtype.ext h01.1
      have ht1 : t = oneI := Subtype.ext h01.2
      right
      left
      simpa [zeroI, oneI, hs0, ht1]
    · have hs1 : s = oneI := Subtype.ext h10.1
      have ht0 : t = zeroI := Subtype.ext h10.2
      right
      right
      simpa [zeroI, oneI, hs1, ht0]
  · intro i j hij
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i, Set.range ((Γ i : ClosedPath ℂ) : C(Set.Icc (0 : ℝ) 1, ℂ))) =
          Set.range (positive_circle_path a r) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        cases i
        simpa [Γ, Path.toClosedPath] using hi
      · intro hx
        refine Set.mem_iUnion.mpr ?_
        refine ⟨(), ?_⟩
        simpa [Γ, Path.toClosedPath] using hx
    -- Rewrite the singleton union to the circle image, then identify it with the frontier sphere.
    simpa [ClosedPath.range_toPath, frontier_closedBall a hr.ne'] using
      hboundary.trans (range_positive_circle_path_eq_sphere (a := a) hr)
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- The explicit radial tube chart supplies the local oriented-boundary model.
    exact positive_circle_exists_boundary_chart_closedBall (a := a) (r := r) hr ht₀ hdiff hderiv

/-- Helper for Exercise 4: integrating a real `1`-form along the positive circle path is the
textbook `θ`-integral after the linear reparametrization `θ = 2π t`. -/
lemma curveIntegral_positive_circle_path_eq_intervalIntegral
    {ω : ℂ → ℂ →L[ℝ] ℝ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in positive_circle_path a r, ω z =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
  let h : ℝ → ℝ := fun θ ↦ ω (circleMap a r θ) (deriv (circleMap a r) θ)
  have hcongr :
      ∫ t in (0 : ℝ)..1,
          ω ((positive_circle_path a r).extend t) (deriv ((positive_circle_path a r).extend) t) =
        ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
    -- On the open interval, the path extension is exactly the standard circle parametrization.
    have hcongr_ae :
        (fun t ↦
            ω ((positive_circle_path a r).extend t) (deriv ((positive_circle_path a r).extend) t))
          =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)]
              (fun t ↦ (2 * Real.pi : ℝ) • h (t * (2 * Real.pi))) := by
      rw [Set.uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have hlocal :
          (positive_circle_path a r).extend =ᶠ[nhds t]
            fun s : ℝ ↦ circleMap a r (s * (2 * Real.pi)) := by
        have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
        filter_upwards [hIoo] with s hs
        rw [Path.extend_apply (positive_circle_path a r) ⟨hs.1.le, hs.2.le⟩]
        simp [positive_circle_path, mul_comm]
      have hderiv :
          deriv (positive_circle_path a r).extend t =
            (2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi)) := by
        rw [Filter.EventuallyEq.deriv_eq hlocal]
        simpa using
          (((hasDerivAt_circleMap a r (t * (2 * Real.pi))).scomp t
            (hasDerivAt_mul_const (2 * Real.pi : ℝ))).deriv)
      have hext :
          (positive_circle_path a r).extend t = circleMap a r (t * (2 * Real.pi)) :=
        Filter.EventuallyEq.eq_of_nhds hlocal
      -- Evaluate the `1`-form on the chain-rule tangent vector of the circle.
      calc
        ω ((positive_circle_path a r).extend t) (deriv ((positive_circle_path a r).extend) t) =
            ω (circleMap a r (t * (2 * Real.pi)))
              ((2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi))) := by
          rw [hext, hderiv]
        _ = (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := by
          change
            ω (circleMap a r (t * (2 * Real.pi)))
                ((2 * Real.pi : ℝ) • deriv (circleMap a r) (t * (2 * Real.pi))) =
              (2 * Real.pi : ℝ) •
                ω (circleMap a r (t * (2 * Real.pi))) (deriv (circleMap a r) (t * (2 * Real.pi)))
          rw [map_smul]
    exact intervalIntegral.integral_congr_ae_restrict hcongr_ae
  have hsmul :
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) =
        (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := by
    simpa using intervalIntegral.integral_smul (a := (0 : ℝ)) (b := 1)
      (r := (2 * Real.pi : ℝ)) (f := fun t ↦ h (t * (2 * Real.pi)))
  -- First rewrite the curve integral as a parameter integral, then perform the `θ = 2π t`
  -- change of variables.
  rw [curveIntegral_eq_intervalIntegral_deriv]
  calc
    ∫ t in (0 : ℝ)..1,
        ω ((positive_circle_path a r).extend t) (deriv ((positive_circle_path a r).extend) t) =
      ∫ t in (0 : ℝ)..1, (2 * Real.pi : ℝ) • h (t * (2 * Real.pi)) := hcongr
    _ = (2 * Real.pi : ℝ) • ∫ t in (0 : ℝ)..1, h (t * (2 * Real.pi)) := hsmul
    _ = ∫ θ in (0 : ℝ) * (2 * Real.pi)..1 * (2 * Real.pi), h θ := by
      simpa using (intervalIntegral.smul_integral_comp_mul_right
        (f := h) (a := (0 : ℝ)) (b := 1) (c := 2 * Real.pi))
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, h θ := by
      simp
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
        MeasureTheory.restrict_Ioc_eq_restrict_Icc]

/-- Helper for Exercise 4: the closed-path wrapper used by the oriented-boundary API does not
change the positive-circle integral. -/
lemma curveIntegral_positive_circle_toClosedPath_eq_intervalIntegral
    {ω : ℂ → ℂ →L[ℝ] ℝ} {a : ℂ} {r : ℝ} :
    ∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath, ω z =
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
  -- Remove the harmless endpoint cast inserted by `toClosedPath.toPath`, then use the explicit
  -- parametrization of the positive circle.
  calc
    ∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath, ω z =
        ∫ᶜ z in positive_circle_path a r, ω z := by
          rw [toClosedPath_toPath_eq_cast]
          simp
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
          exact curveIntegral_positive_circle_path_eq_intervalIntegral (ω := ω)

/-- Helper for Exercise 4: varying the real coordinate in `Complex.mk` differentiates to the
horizontal unit direction. -/
lemma hasDerivAt_complex_mk_re (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.mk t y) 1 x := by
  -- The horizontal line is the real-axis embedding followed by translation.
  have hrepr : (fun t : ℝ ↦ Complex.mk t y) = fun t : ℝ ↦ (t : ℂ) + y * Complex.I := by
    funext t
    apply Complex.ext <;> simp [Complex.mk]
  rw [hrepr]
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add (y * Complex.I)

/-- Helper for Exercise 4: varying the imaginary coordinate in `Complex.mk` differentiates to the
vertical unit direction `I`. -/
lemma hasDerivAt_complex_mk_im (x y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.mk x t) Complex.I y := by
  -- The vertical line is the real-axis embedding, then multiplication by `I`, then translation.
  have hrepr : (fun t : ℝ ↦ Complex.mk x t) = fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * Complex.I := by
    funext t
    apply Complex.ext <;> simp [Complex.mk]
  rw [hrepr]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x : ℂ)

/-- Helper for Exercise 4: the real and imaginary coordinates of a complex tangent encode
multiplication by `-I`. -/
lemma complex_mk_im_neg_re_eq_neg_I_mul (v : ℂ) :
    Complex.mk v.im (-v.re) = -Complex.I * v := by
  -- Expanding both sides shows the expected quarter-turn identity.
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- Helper for Exercise 4: differentiating the first derivative along the vertical real line in a
fixed tangent direction gives the corresponding `I,v` entry of the second iterated derivative. -/
lemma hasDerivAt_fderiv_apply_const_along_vertical {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {z v : ℂ} (hz : z ∈ D) :
    HasDerivAt (fun y : ℝ ↦ fderiv ℝ f (Complex.mk z.re y) v)
      (iteratedFDeriv ℝ 2 f z ![Complex.I, v]) z.im := by
  -- Package the second derivative as a derivative of the derivative field, then compose with the
  -- vertical coordinate line before the final `fderiv_clm_apply` rewrite.
  have h2 : ContDiffAt ℝ 2 f z := hf.contDiffAt (hD.mem_nhds hz)
  have hfd :
      DifferentiableAt ℝ (fun w : ℂ ↦ fderiv ℝ f w v) z := by
    exact (((h2.fderiv_right_succ).clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ ↦ v) z)).differentiableAt one_ne_zero)
  have hline :
      HasDerivAt (fun y : ℝ ↦ fderiv ℝ f (Complex.mk z.re y) v)
        (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ f w v) z Complex.I) z.im := by
    simpa [Function.comp] using
      hfd.hasFDerivAt.comp_hasDerivAt z.im (hasDerivAt_complex_mk_im z.re z.im)
  -- Unfold the derivative of the derivative field only at the endpoint to identify the
  -- iterated Fréchet derivative component.
  convert hline using 1
  rw [fderiv_clm_apply (h2.fderiv_right_succ.differentiableAt one_ne_zero)
    (differentiableAt_const v)]
  simpa [iteratedFDeriv_two_apply]

/-- Helper for Exercise 4: differentiating the first derivative along the horizontal real line in
a fixed tangent direction gives the corresponding `1,v` entry of the second iterated derivative. -/
lemma hasDerivAt_fderiv_apply_const_along_horizontal {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {z v : ℂ} (hz : z ∈ D) :
    HasDerivAt (fun x : ℝ ↦ fderiv ℝ f (Complex.mk x z.im) v)
      (iteratedFDeriv ℝ 2 f z ![1, v]) z.re := by
  -- Package the second derivative as a derivative of the derivative field, then compose with the
  -- horizontal coordinate line before the final `fderiv_clm_apply` rewrite.
  have h2 : ContDiffAt ℝ 2 f z := hf.contDiffAt (hD.mem_nhds hz)
  have hfd :
      DifferentiableAt ℝ (fun w : ℂ ↦ fderiv ℝ f w v) z := by
    exact (((h2.fderiv_right_succ).clm_apply
      (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ ↦ v) z)).differentiableAt one_ne_zero)
  have hline :
      HasDerivAt (fun x : ℝ ↦ fderiv ℝ f (Complex.mk x z.im) v)
        (fderiv ℝ (fun w : ℂ ↦ fderiv ℝ f w v) z 1) z.re := by
    simpa [Function.comp] using
      hfd.hasFDerivAt.comp_hasDerivAt z.re (hasDerivAt_complex_mk_re z.re z.im)
  -- Unfold the derivative of the derivative field only at the endpoint to identify the
  -- iterated Fréchet derivative component.
  convert hline using 1
  rw [fderiv_clm_apply (h2.fderiv_right_succ.differentiableAt one_ne_zero)
    (differentiableAt_const v)]
  simpa [iteratedFDeriv_two_apply]

/-- Helper for Exercise 4: evaluating the Green-Riemann boundary form on a tangent vector is the
Fréchet derivative applied to the quarter-turned tangent. -/
lemma boundary_form_apply_eq_fderiv_rotated_tangent {f : ℂ → ℝ} (z v : ℂ) :
    (((fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy) z v) =
      fderiv ℝ f z (Complex.mk v.im (-v.re)) := by
  -- Normalize the planar differential form first, then rewrite the rotated tangent in the real
  -- basis `{1, I}` so the linearity of `fderiv` applies directly.
  rw [Complex.planarDifferentialForm_apply]
  have hsplit :
      Complex.mk v.im (-v.re) = v.im • (1 : ℂ) + (-v.re) • Complex.I := by
    apply Complex.ext <;> simp [Complex.mk]
  calc
    v.re * (-fderiv ℝ f z Complex.I) + v.im * fderiv ℝ f z 1
      = v.im • fderiv ℝ f z 1 + (-v.re) • fderiv ℝ f z Complex.I := by
          ring
    _ = fderiv ℝ f z (v.im • (1 : ℂ) + (-v.re) • Complex.I) := by
          rw [map_add, map_smul, map_smul]
    _ = fderiv ℝ f z (Complex.mk v.im (-v.re)) := by
          rw [hsplit]

/-- Helper for Exercise 4: quarter-turning the angular circle tangent gives the radial vector on
the same circle. -/
lemma rotated_circle_tangent_eq_radial_vector {a : ℂ} {r θ : ℝ} :
    Complex.mk (deriv (circleMap a r) θ).im (-(deriv (circleMap a r) θ).re) = circleMap 0 r θ := by
  -- The standard circle derivative is `circleMap 0 r θ * I`, and multiplying by `-I` rotates it
  -- back to the radial vector.
  rw [complex_mk_im_neg_re_eq_neg_I_mul, deriv_circleMap]
  ring_nf
  simp

/-- Helper for Exercise 4: the Green-Riemann boundary `1`-form on the circle is exactly the radial
derivative multiplied by the radius. -/
lemma circle_boundary_form_eq_radial_deriv_mul_radius {f : ℂ → ℝ} {a : ℂ} {r θ : ℝ}
    (hf : DifferentiableAt ℝ f (circleMap a r θ)) :
    (((fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy)
        (circleMap a r θ) (deriv (circleMap a r) θ)) =
      deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
  -- Route correction: first rewrite the Green boundary form as one `fderiv` evaluation on the
  -- rotated tangent, then convert that tangent into the radial vector before using the radius
  -- derivative of `circleMap`.
  have hradial :
      HasDerivAt (fun s : ℝ ↦ f (circleMap a s θ))
        (fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I))) r := by
    -- Compose the Fréchet derivative of `f` with the affine radius parametrization.
    simpa using
      (hf.hasFDerivAt.comp r
        (hasDerivAt_circleMap_radius a θ r).hasFDerivAt).hasDerivAt
  have hradial_deriv :
      deriv (fun s : ℝ ↦ f (circleMap a s θ)) r =
        fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) := hradial.deriv
  calc
    (((fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy)
        (circleMap a r θ) (deriv (circleMap a r) θ)) =
      fderiv ℝ f (circleMap a r θ)
        (Complex.mk (deriv (circleMap a r) θ).im (-(deriv (circleMap a r) θ).re)) := by
          rw [boundary_form_apply_eq_fderiv_rotated_tangent]
    _ = fderiv ℝ f (circleMap a r θ) (circleMap 0 r θ) := by
          rw [rotated_circle_tangent_eq_radial_vector]
    _ = fderiv ℝ f (circleMap a r θ) (r • Complex.exp (θ * Complex.I)) := by
          simp [circleMap, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = r * fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) := by
          rw [ContinuousLinearMap.map_smul]
          simp [smul_eq_mul, mul_comm]
    _ = deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
          rw [hradial_deriv]
          ring

/-- Helper for Exercise 4: specialize the oriented-boundary Green-Riemann formula to the singleton
positive boundary circle of a closed disc before any concrete derivative rewrites. -/
lemma singleton_closedBall_green_riemann_formula_specialization {D : Set ℂ} (hD : IsOpen D)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall a r ⊆ D)
    {P Q dPdy dQdx : ℂ → ℝ}
    (hP_cont : ContinuousOn P D) (hQ_cont : ContinuousOn Q D)
    (hdPdy_cont : ContinuousOn dPdy D) (hdQdx_cont : ContinuousOn dQdx D)
    (hP_dy : ∀ z ∈ D, HasDerivAt (fun y : ℝ ↦ P (Complex.mk z.re y)) (dPdy z) z.im)
    (hQ_dx : ∀ z ∈ D, HasDerivAt (fun x : ℝ ↦ Q (Complex.mk x z.im)) (dQdx z) z.re) :
    (∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath, (P dx + Q dy) z) =
      ∫ z in Metric.closedBall a r, (dQdx z - dPdy z) := by
  classical
  -- Route correction: package the `Unit`-indexed oriented-boundary theorem once, then collapse the
  -- singleton boundary sum before introducing the concrete Fréchet-derivative data.
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (positive_circle_path a r).toClosedPath
  simpa [Γ] using
    (orientedBoundary_green_riemann_formula (Γ := Γ)
      (hΓ := closedBallBoundary_isOrientedBoundaryOf hr) (hKD := hclosed) (hD := hD)
      (P := P) (Q := Q) (dPdy := dPdy) (dQdx := dQdx)
      hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx)

/-- Helper for Exercise 4: Green-Riemann on the singleton positively oriented boundary of a closed
disc is first packaged on the raw closed-path integral surface. -/
lemma singleton_closedBall_green_riemann_formula {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hclosed : Metric.closedBall a r ⊆ D) :
    (∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath,
        ((fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy) z) =
      ∫ z in Metric.closedBall a r,
        (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) := by
  have hP_cont :
      ContinuousOn (fun w : ℂ ↦ -fderiv ℝ f w Complex.I) D := by
    -- Evaluate the continuous derivative field on the fixed vertical basis vector, then negate.
    simpa using
      (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).clm_apply
        continuousOn_const |>.neg
  have hQ_cont :
      ContinuousOn (fun w : ℂ ↦ fderiv ℝ f w 1) D := by
    -- Evaluate the continuous derivative field on the fixed horizontal basis vector.
    simpa using
      (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).clm_apply
        continuousOn_const
  have hiter_cont : ContinuousOn (iteratedFDeriv ℝ 2 f) D :=
    ContinuousOn.continuousOn_iteratedFDeriv (k := 2) hf hD le_rfl
  have hdQdx_cont :
      ContinuousOn (fun z : ℂ ↦ iteratedFDeriv ℝ 2 f z ![1, 1]) D := by
    -- The second derivative field is continuous, and evaluation on a fixed pair is continuous.
    intro z hz
    change ContinuousWithinAt
      ((fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ ℂ) ℝ => A ![1, 1]) ∘
        iteratedFDeriv ℝ 2 f) D z
    exact (continuous_eval_const (![1, 1] : Fin 2 → ℂ)).continuousAt.comp_continuousWithinAt
      (hiter_cont z hz)
  have hdPdy_cont :
      ContinuousOn (fun z : ℂ ↦ -(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) D := by
    -- The vertical second partial inherits continuity from the same iterated derivative field.
    have hII_cont :
        ContinuousOn (fun z : ℂ ↦ iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I]) D := by
      intro z hz
      change ContinuousWithinAt
        ((fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ ℂ) ℝ =>
            A ![Complex.I, Complex.I]) ∘
          iteratedFDeriv ℝ 2 f) D z
      exact ContinuousAt.comp_continuousWithinAt
        ((continuous_eval_const (![Complex.I, Complex.I] : Fin 2 → ℂ)).continuousAt)
        (hiter_cont z hz)
    simpa using hII_cont.neg
  have hP_dy :
      ∀ z ∈ D,
        HasDerivAt (fun y : ℝ ↦ (-fderiv ℝ f (Complex.mk z.re y) Complex.I))
          (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) z.im := by
    intro z hz
    -- Differentiate the vertical derivative slice, then negate the resulting scalar function.
    simpa using
      (hasDerivAt_fderiv_apply_const_along_vertical hD hf (z := z) (v := Complex.I) hz).neg
  have hQ_dx :
      ∀ z ∈ D,
        HasDerivAt (fun x : ℝ ↦ fderiv ℝ f (Complex.mk x z.im) 1)
          (iteratedFDeriv ℝ 2 f z ![1, 1]) z.re := by
    intro z hz
    -- Differentiate the horizontal derivative slice in the fixed horizontal direction.
    simpa using
      (hasDerivAt_fderiv_apply_const_along_horizontal hD hf (z := z) (v := (1 : ℂ)) hz)
  -- Route correction: feed the current `ContDiffOn` continuity/derivative data into the already
  -- stable singleton-boundary Green wrapper instead of unfolding the disc integral again.
  simpa using
    singleton_closedBall_green_riemann_formula_specialization (hD := hD) (a := a) (r := r)
      hr hclosed hP_cont hQ_cont hdPdy_cont hdQdx_cont hP_dy hQ_dx

/-- Helper for Exercise 4: on the open disc domain used in Green-Riemann, the Green area
integrand is exactly the within-Laplacian. -/
lemma green_disc_integrand_eq_laplacianWithin {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {z : ℂ} (hz : z ∈ D) :
    (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) =
      (Δ[D] f) z := by
  -- On an open set, the within-Laplacian is the ordinary Laplacian, whose complex-plane formula
  -- is the sum of the horizontal and vertical second partials.
  have hΔ :
      (Δ[D] f) z =
        (iteratedFDeriv ℝ 2 f z ![1, 1]) + (iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I]) := by
    rw [InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane f hD.uniqueDiffOn hz,
      iteratedFDerivWithin_eq_iteratedFDeriv hD.uniqueDiffOn (hf.contDiffAt (hD.mem_nhds hz)) hz]
  calc
    (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) =
        (iteratedFDeriv ℝ 2 f z ![1, 1]) + (iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I]) := by
          ring
    _ = (Δ[D] f) z := hΔ.symm

/-- Exercise 4 (8). For a `C²` real-valued function on an open set, the integral of the Laplacian
over a sufficiently small closed disc equals the integral of the radial derivative over the
boundary circle. -/

theorem integral_laplacianWithin_closedBall_eq_integral_deriv_circleMap {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 2 f D) {a : ℂ} (ha : a ∈ D) :
    ∃ ε > 0, ∀ ⦃r : ℝ⦄, 0 < r → r < ε →
      Metric.closedBall a r ⊆ D ∧
        (∫ z in Metric.closedBall a r, (Δ[D] f) z) =
          ∫ θ in 0..2 * Real.pi, deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
  rcases Metric.isOpen_iff.mp hD a ha with ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro r hr_pos hr_lt
  have hclosed : Metric.closedBall a r ⊆ D := (Metric.closedBall_subset_ball hr_lt).trans hε
  refine ⟨hclosed, ?_⟩
  let ω : ℂ → ℂ →L[ℝ] ℝ :=
    (fun w ↦ -fderiv ℝ f w Complex.I) dx + (fun w ↦ fderiv ℝ f w 1) dy
  have hgreen :
      (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ)) =
        ∫ z in Metric.closedBall a r,
          (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) := by
    -- Convert the raw closed-path identity from Green-Riemann into the explicit circle parameter.
    calc
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) =
          ∫ᶜ z in (positive_circle_path a r).toClosedPath.toPath, ω z := by
            symm
            exact curveIntegral_positive_circle_toClosedPath_eq_intervalIntegral (ω := ω)
      _ = ∫ z in Metric.closedBall a r,
            (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) := by
            exact singleton_closedBall_green_riemann_formula hD hf hr_pos hclosed
  have hboundary :
      (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ)) =
        ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
    -- Identify the Green boundary form pointwise with the radial derivative times `r`.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hz : circleMap a r θ ∈ D := hclosed (circleMap_mem_closedBall a hr_pos.le θ)
    have hdiff : DifferentiableAt ℝ f (circleMap a r θ) :=
      (hf.contDiffAt (hD.mem_nhds hz)).differentiableAt (by norm_num)
    exact circle_boundary_form_eq_radial_deriv_mul_radius hdiff
  have harea :
      (∫ z in Metric.closedBall a r,
          (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I]))) =
        ∫ z in Metric.closedBall a r, (Δ[D] f) z := by
    -- Rewrite the Green area integrand to the within-Laplacian pointwise on the admissible disc.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_closedBall] with z hz
    exact green_disc_integrand_eq_laplacianWithin hD hf (hclosed hz)
  calc
    ∫ z in Metric.closedBall a r, (Δ[D] f) z =
        ∫ z in Metric.closedBall a r,
          (iteratedFDeriv ℝ 2 f z ![1, 1]) - (-(iteratedFDeriv ℝ 2 f z ![Complex.I, Complex.I])) := by
          symm
          exact harea
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), ω (circleMap a r θ) (deriv (circleMap a r) θ) := by
          symm
          exact hgreen
    _ = ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
          exact hboundary
    _ = ∫ θ in 0..2 * Real.pi, deriv (fun s : ℝ ↦ f (circleMap a s θ)) r * r := by
          rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
            MeasureTheory.restrict_Ioc_eq_restrict_Icc]

/-- Helper for Exercise 4: differentiating the radial slice `s ↦ f (circleMap a s θ)` is the
Fréchet derivative of `f` applied to the fixed unit direction `exp (θ I)`. -/
lemma deriv_circleMap_comp_eq_fderiv_exp {f : ℂ → ℝ} {a : ℂ} {r θ : ℝ}
    (hf : DifferentiableAt ℝ f (circleMap a r θ)) :
    deriv (fun s : ℝ ↦ f (circleMap a s θ)) r =
      fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) := by
  -- Compose the derivative of `f` with the affine radius parameterization of the circle.
  simpa using
    (hf.hasFDerivAt.comp r (hasDerivAt_circleMap_radius a θ r).hasFDerivAt).hasDerivAt.deriv

/-- Helper for Exercise 4: before replacing the radial derivative by the Laplacian density, the
circle average is the center value plus the radial-FTC/Fubini correction term. -/
lemma circleAverage_eq_center_add_integral_radial_fderiv {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 2 f D) {a : ℂ} {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hclosed : Metric.closedBall a ρ ⊆ D) :
    Real.circleAverage f a ρ = f a +
      ∫ r in 0..ρ, (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi,
          fderiv ℝ f (circleMap a r θ) (Complex.exp (θ * Complex.I)) := by
  -- TODO: re-establish the radial FTC/Fubini decomposition with the current interval-integral and
  -- product-measure APIs; this is the theorem-(9) bridge used by the target converse proof.
  sorry

/-- Exercise 4 (9). For a `C²` real-valued function on an open set, the circle average over a
sufficiently small circle equals the center value plus the integral of the Laplacian term from the
textbook formula. -/
theorem circleAverage_eq_center_add_integral_laplacianWithin {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 2 f D) {a : ℂ} (ha : a ∈ D) :
    ∃ ε > 0, ∀ ⦃ρ : ℝ⦄, 0 < ρ → ρ < ε →
      Metric.closedBall a ρ ⊆ D ∧
        Real.circleAverage f a ρ = f a +
          ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z := by
  -- TODO: once theorem (8) and the radial FTC/Fubini identity are restored, rewrite the radial
  -- integrand pointwise to the closed-ball Laplacian density exactly as in the current skeleton.
  sorry

/-- Helper for Exercise 4: on an open set, the within-Laplacian agrees with the ordinary
Laplacian. -/
lemma laplacianWithin_eq_laplacian_on_open {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {z : ℂ} (hz : z ∈ D) :
    (Δ[D] f) z = Δ f z := by
  -- Rewrite both Laplacians via second iterated derivatives on the complex plane.
  rw [InnerProductSpace.laplacianWithin_eq_iteratedFDerivWithin_complexPlane f hD.uniqueDiffOn hz,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane f]
  -- On an open set, the within-iterated derivative matches the ordinary iterated derivative.
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hD.uniqueDiffOn
    (hf.contDiffAt (hD.mem_nhds hz)) hz]

/-- Helper for Exercise 4: the ordinary Laplacian of a `C²` real-valued function is continuous at
each point. -/
lemma continuousAt_laplacian_of_contDiffAt {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ContinuousAt (Δ f) z := by
  -- Express the Laplacian as evaluation of the continuous second derivative on the two standard
  -- complex-plane basis directions.
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  have hiter : ContinuousAt (iteratedFDeriv ℝ 2 f) z :=
    hf.continuousAt_iteratedFDeriv le_rfl
  have h_one : ContinuousAt (fun w : ℂ ↦ iteratedFDeriv ℝ 2 f w ![1, 1]) z :=
    (continuous_eval_const (![1, 1] : Fin 2 → ℂ)).continuousAt.comp hiter
  have h_I : ContinuousAt (fun w : ℂ ↦ iteratedFDeriv ℝ 2 f w ![Complex.I, Complex.I]) z :=
    (continuous_eval_const (![Complex.I, Complex.I] : Fin 2 → ℂ)).continuousAt.comp hiter
  exact h_one.add h_I

/-- Helper for Exercise 4: theorem (9) turns pointwise nonnegativity of the within-Laplacian into
the sub-mean inequality. -/
lemma isSubharmonicOn_of_nonneg_laplacianWithin {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) (hΔ : ∀ z ∈ D, 0 ≤ (Δ[D] f) z) :
    IsSubharmonicOn f D := by
  constructor
  · -- A `C²` function is continuous on its domain.
    exact hf.continuousOn
  · intro a ha
    rcases circleAverage_eq_center_add_integral_laplacianWithin hD hf ha with ⟨ε, hε_pos, hε⟩
    refine ⟨ε, hε_pos, ?_⟩
    intro r hr_pos hr_lt
    rcases hε hr_pos hr_lt with ⟨hclosed, havg⟩
    refine ⟨hclosed, ?_⟩
    have hcorr_nonneg :
        0 ≤ ∫ s in 0..r, (2 * Real.pi * s)⁻¹ * ∫ z in Metric.closedBall a s, (Δ[D] f) z := by
      refine intervalIntegral.integral_nonneg hr_pos.le ?_
      intro s hs
      have hs_nonneg : 0 ≤ s := hs.1
      have hs_le_r : s ≤ r := hs.2
      have hs_closed : Metric.closedBall a s ⊆ D := by
        intro z hz
        exact hclosed (Metric.closedBall_subset_closedBall hs_le_r hz)
      have hinner_nonneg : 0 ≤ ∫ z in Metric.closedBall a s, (Δ[D] f) z := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_closedBall] with z hz
        exact hΔ z (hs_closed hz)
      have hfactor_nonneg : 0 ≤ (2 * Real.pi * s)⁻¹ := by
        positivity
      exact mul_nonneg hfactor_nonneg hinner_nonneg
    -- The exact circle-average expansion turns the nonnegative correction term into the
    -- sub-mean inequality.
    rw [havg]
    linarith

/-- Helper for Exercise 4: a negative value of the within-Laplacian persists as a uniform
negative upper bound on some small closed ball. -/
lemma exists_closedBall_laplacianWithin_le_neg_const {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {a : ℂ} (ha : a ∈ D) (hneg : (Δ[D] f) a < 0) :
    ∃ c ε, c < 0 ∧ 0 < ε ∧ Metric.closedBall a ε ⊆ D ∧
      ∀ z ∈ Metric.closedBall a ε, (Δ[D] f) z ≤ c := by
  let c : ℝ := (Δ f a) / 2
  have hΔa : (Δ[D] f) a = Δ f a := laplacianWithin_eq_laplacian_on_open hD hf ha
  have hc_neg : c < 0 := by
    dsimp [c]
    rw [hΔa] at hneg
    linarith
  have hΔa_lt : Δ f a < c := by
    dsimp [c]
    linarith
  have hcont : ContinuousAt (Δ f) a :=
    continuousAt_laplacian_of_contDiffAt (hf.contDiffAt (hD.mem_nhds ha))
  have hballD : D ∈ 𝓝 a := hD.mem_nhds ha
  have hballΔ : {z : ℂ | Δ f z < c} ∈ 𝓝 a := by
    -- Continuity puts the ordinary Laplacian below the negative midpoint on a small neighborhood.
    exact hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hΔa_lt)
  rcases Metric.mem_nhds_iff.mp hballD with ⟨εD, hεD_pos, hεD⟩
  rcases Metric.mem_nhds_iff.mp hballΔ with ⟨εΔ, hεΔ_pos, hεΔ⟩
  let ε : ℝ := min (εD / 2) (εΔ / 2)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt_εD : ε < εD := by
    dsimp [ε]
    have hhalf : εD / 2 < εD := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hε_lt_εΔ : ε < εΔ := by
    dsimp [ε]
    have hhalf : εΔ / 2 < εΔ := by linarith
    exact lt_of_le_of_lt (min_le_right _ _) hhalf
  refine ⟨c, ε, hc_neg, hε_pos, ?_, ?_⟩
  · -- The closed ball sits inside the open neighborhood supplied by openness of `D`.
    exact (Metric.closedBall_subset_ball hε_lt_εD).trans hεD
  · intro z hz
    have hz_ball : z ∈ Metric.ball a εΔ := by
      exact Metric.closedBall_subset_ball hε_lt_εΔ hz
    have hz_lt : Δ f z < c := hεΔ hz_ball
    have hzD : z ∈ D := by
      exact hεD (Metric.closedBall_subset_ball hε_lt_εD hz)
    -- On the controlling closed ball, the within-Laplacian matches the ordinary Laplacian.
    rw [laplacianWithin_eq_laplacian_on_open hD hf hzD]
    linarith

/-- Helper for Exercise 4: a uniform negative upper bound on the within-Laplacian forces the
theorem-(9) correction term to be bounded above by a negative quadratic. -/
lemma laplacianWithin_correction_le_neg_quadratic {D : Set ℂ} {f : ℂ → ℝ} {a : ℂ} {c ε : ℝ}
    (hc : c < 0) (hε_pos : 0 < ε) (hclosed : Metric.closedBall a ε ⊆ D)
    (hbound : ∀ z ∈ Metric.closedBall a ε, (Δ[D] f) z ≤ c) :
    ∀ {ρ : ℝ}, 0 < ρ → ρ < ε →
      ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z ≤
        c * ρ ^ 2 / 4 := by
  -- TODO: prove the theorem-(9) correction estimate by bounding the inner closed-ball integral by
  -- `c * volume (closedBall a r)`, rewriting that volume with `Complex.volume_closedBall`, and
  -- then integrating the pointwise bound `(2 * π * r)⁻¹ * ... ≤ c * r / 2` over `r ∈ [0, ρ]`.
  sorry

/-- Helper for Exercise 4: a negative value of the within-Laplacian makes the theorem-(9)
correction term strictly negative on all sufficiently small radii. -/
lemma laplacianWithin_correction_neg_of_neg_at_point {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) {a : ℂ} (ha : a ∈ D) (hneg : (Δ[D] f) a < 0) :
    ∃ ε > 0, ∀ {ρ : ℝ}, 0 < ρ → ρ < ε →
      ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall a r, (Δ[D] f) z < 0 := by
  -- TODO: combine the previous closed-ball negativity lemma with the quadratic upper bound, then
  -- use `c < 0` and `ρ > 0` to conclude the correction term is strictly negative.
  sorry

/-- Exercise 4 (10). A twice continuously differentiable real-valued function on `D` is
subharmonic exactly when its Laplacian is pointwise nonnegative on `D`. -/
theorem isSubharmonicOn_iff_nonneg_laplacianWithin {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ 2 f D) :
    IsSubharmonicOn f D ↔ ∀ z ∈ D, 0 ≤ (Δ[D] f) z := by
  constructor
  · intro hsub z hz
    by_contra hneg_nonneg
    have hneg : (Δ[D] f) z < 0 := by linarith
    rcases circleAverage_eq_center_add_integral_laplacianWithin hD hf hz with ⟨ε₁, hε₁_pos, hε₁⟩
    rcases laplacianWithin_correction_neg_of_neg_at_point hD hf hz hneg with
      ⟨ε₂, hε₂_pos, hε₂⟩
    rcases hsub.2 hz with ⟨ε₃, hε₃_pos, hε₃⟩
    let ρ : ℝ := min (min (ε₁ / 2) (ε₂ / 2)) (ε₃ / 2)
    have hρ_pos : 0 < ρ := by
      dsimp [ρ]
      positivity
    have hρ_lt_ε₁ : ρ < ε₁ := by
      dsimp [ρ]
      have hhalf : ε₁ / 2 < ε₁ := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) <| lt_of_le_of_lt (min_le_left _ _) hhalf
    have hρ_lt_ε₂ : ρ < ε₂ := by
      dsimp [ρ]
      have hhalf : ε₂ / 2 < ε₂ := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) <| lt_of_le_of_lt (min_le_right _ _) hhalf
    have hρ_lt_ε₃ : ρ < ε₃ := by
      dsimp [ρ]
      have hhalf : ε₃ / 2 < ε₃ := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf
    rcases hε₁ hρ_pos hρ_lt_ε₁ with ⟨hball, havg⟩
    rcases hε₃ hρ_pos hρ_lt_ε₃ with ⟨_, hsubmean⟩
    have hcorr_neg :
        ∫ r in 0..ρ, (2 * Real.pi * r)⁻¹ * ∫ z in Metric.closedBall z r, (Δ[D] f) z < 0 :=
      hε₂ hρ_pos hρ_lt_ε₂
    have havg_lt : Real.circleAverage f z ρ < f z := by
      -- Theorem (9) rewrites the circle average as the center value plus the negative correction.
      rw [havg]
      linarith
    exact not_lt_of_ge hsubmean havg_lt
  · intro hΔ
    exact isSubharmonicOn_of_nonneg_laplacianWithin hD hf hΔ

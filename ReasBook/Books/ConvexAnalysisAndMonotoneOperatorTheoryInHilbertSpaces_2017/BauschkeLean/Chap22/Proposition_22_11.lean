import BauschkeLean.Chap21.Corollary_21_24
import BauschkeLean.Chap22.Definition_22_1

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Source/core/bridge triage:
-- - `source-facing`: the growth conclusion is the Chapter 22 statement about
--   `Metric.infEDist (0 : H) (A x)` along `‖x‖ → +∞`.
-- - `core/canonical`: Chapter 22 already fixes the operator owners
--   `IsUniformlyMonotone` and `IsStronglyMonotone`, and Chapter 21 already owns the surjectivity
--   consequence via `range_eq_univ_of_maximal_of_tendsto_infEDist_zero`.
-- - `bridge/view`: the surjectivity theorem below is only the Proposition 22.11 specialization of
--   that Chapter 21 owner theorem, so completeness belongs only to the surjectivity companion.
--
-- The source modulus lives on `NNReal`, so the supercoercive growth clause stays in the explicit
-- radial form `t ↦ φ t / t`.

/- The source has two independent conclusions. The main labeled entry below records the growth
statement, and the surjectivity conclusion is kept as a companion theorem using the same
hypotheses. -/

section

omit [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 22.11: if the graph of `A` is empty, then every value `A x` is empty. -/
private lemma value_eq_empty_of_noGraphPoint
    (A : SetValuedOperator H H) (hgraph : ¬ ∃ x u, u ∈ A x) (x : H) :
    A x = ∅ := by
  -- Any point in the fiber would already produce a graph point.
  ext u
  constructor
  · intro hu
    exact False.elim (hgraph ⟨x, u, hu⟩)
  · intro hu
    cases hu

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 22.11: a lower bound on `‖x‖` yields the corresponding lower bound on
`‖x - y‖` after subtracting the fixed translation term `‖y‖`. -/
private lemma le_norm_sub_of_add_norm_le_norm
    {x y : H} {R : ℝ} (hR : R + ‖y‖ ≤ ‖x‖) :
    R ≤ ‖x - y‖ := by
  -- Rewrite `x` as `(x - y) + y` and apply the triangle inequality once.
  have htriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by
        congr 1
        abel_nf
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  linarith

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 22.11: translating the argument by a fixed vector preserves the
norm-at-infinity filter. -/
private lemma tendsto_nnnormSub_atTop
    (y : H) :
    Filter.Tendsto (fun x : H ↦ ‖x - y‖₊)
      (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop := by
  -- Large values of `‖x‖` force large values of `‖x - y‖` by one triangle-inequality estimate.
  refine Filter.tendsto_atTop.2 ?_
  intro R
  have hnorm :
      ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop, (R : ℝ) + ‖y‖ ≤ ‖x‖ := by
    exact
      (Filter.tendsto_comap :
        Filter.Tendsto (fun x : H ↦ ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop).eventually_ge_atTop
        ((R : ℝ) + ‖y‖)
  filter_upwards [hnorm] with x hx
  exact_mod_cast (le_norm_sub_of_add_norm_le_norm hx)

/-- Helper for Proposition 22.11: a uniform monotonicity modulus controls the norm of every
value in the fiber after dividing by the source distance. -/
private lemma modulus_div_le_norm_add_norm_of_uniformlyMonotone
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (hA : A.IsUniformlyMonotone φ)
    {x u y v : H} (hu : u ∈ A x) (hv : v ∈ A y) (hdist : (1 : ℝ) ≤ ‖x - y‖) :
    φ ‖x - y‖₊ / ‖x - y‖ ≤ (‖u‖ + ‖v‖ : ℝ) := by
  have hnorm_pos_real : 0 < ‖x - y‖ := lt_of_lt_of_le zero_lt_one hdist
  have hnorm_pos : (0 : EReal) < ‖x - y‖ := by
    exact_mod_cast hnorm_pos_real
  have hinner :
      φ ‖x - y‖₊ ≤ (((‖x - y‖ * (‖u‖ + ‖v‖) : ℝ) : EReal)) := by
    calc
      φ ‖x - y‖₊ ≤ (⟪x - y, u - v⟫_ℝ : EReal) := hA.ineq hu hv
      _ ≤ (((‖x - y‖ * ‖u - v‖ : ℝ) : EReal)) := by
        exact_mod_cast (real_inner_le_norm (x - y) (u - v))
      _ ≤ (((‖x - y‖ * (‖u‖ + ‖v‖) : ℝ) : EReal)) := by
        exact_mod_cast
          (mul_le_mul_of_nonneg_left (norm_sub_le u v) (norm_nonneg (x - y)))
  have hmul_le :
      φ ‖x - y‖₊ ≤ (‖x - y‖ : EReal) * ((‖u‖ + ‖v‖ : ℝ) : EReal) := by
    simpa [EReal.coe_mul] using hinner
  exact (EReal.div_le_iff_le_mul hnorm_pos (EReal.coe_ne_top ‖x - y‖)).2 hmul_le

/-- Helper for Proposition 22.11: strong monotonicity gives a direct linear lower bound on the
norm of every value in the fiber. -/
private lemma mul_norm_le_norm_add_norm_of_stronglyMonotone
    {A : SetValuedOperator H H} {β : ℝ} (hA : A.IsStronglyMonotone β)
    {x u y v : H} (hu : u ∈ A x) (hv : v ∈ A y) :
    β * ‖x - y‖ ≤ ‖u‖ + ‖v‖ := by
  by_cases hxy : x = y
  · -- The zero-distance case is immediate.
    subst hxy
    have hnonneg : 0 ≤ ‖u‖ + ‖v‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa using hnonneg
  · -- Otherwise cancel the positive factor `‖x - y‖` from the quadratic lower bound.
    have hnorm_pos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hmul :
        β * ‖x - y‖ ^ 2 ≤ ‖x - y‖ * (‖u‖ + ‖v‖) := by
      calc
        β * ‖x - y‖ ^ 2 ≤ ⟪x - y, u - v⟫_ℝ := hA.ineq hu hv
        _ ≤ ‖x - y‖ * ‖u - v‖ := real_inner_le_norm _ _
        _ ≤ ‖x - y‖ * (‖u‖ + ‖v‖) := by
          exact mul_le_mul_of_nonneg_left (norm_sub_le u v) (norm_nonneg (x - y))
    nlinarith

omit [InnerProductSpace ℝ H] in
/-- Helper for Proposition 22.11: a uniform lower bound on the norms of all values in `A x`
induces the same lower bound on `Metric.infEDist (0 : H) (A x)`. -/
private lemma le_infEDist_of_forall_mem_norm_ge
    {A : SetValuedOperator H H} {x : H} {M : ℝ} (hbound : ∀ u, u ∈ A x → M ≤ ‖u‖) :
    ENNReal.ofReal M ≤ Metric.infEDist (0 : H) (A x) := by
  -- Push the pointwise norm estimate through `Metric.le_infEDist`.
  rw [Metric.le_infEDist]
  intro u hu
  calc
    ENNReal.ofReal M ≤ ENNReal.ofReal ‖u‖ := by
      exact ENNReal.ofReal_le_ofReal (hbound u hu)
    _ = edist (0 : H) u := by
      simp [edist_dist, dist_eq_norm]

/-- Helper for Proposition 22.11: a uniformly monotone operator with a supercoercive modulus has
`Metric.infEDist (0 : H) (A x) → +∞` as `‖x‖ → +∞`. -/
private theorem tendsto_infEDist_zero_of_uniformlyMonotone_supercoerciveModulus
    (A : SetValuedOperator H H) {φ : NNReal → EReal}
    (hA_uniform : A.IsUniformlyMonotone φ)
    (hφ_super :
      Filter.Tendsto (fun t : NNReal ↦ φ t / (t : EReal))
        Filter.atTop (nhds (⊤ : EReal))) :
    Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
      (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal)) := by
  have htarget :
      Filter.Tendsto
        (fun x : H ↦ ((Metric.infEDist (0 : H) (A x) : ENNReal) : EReal))
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal)) := by
    by_cases hgraph : ∃ y v, v ∈ A y
    · rcases hgraph with ⟨y, v, hv⟩
      have hdist_tendsto :
          Filter.Tendsto (fun x : H ↦ ‖x - y‖₊)
            (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop :=
        tendsto_nnnormSub_atTop y
      have hquot_tendsto :
          Filter.Tendsto (fun x : H ↦ φ ‖x - y‖₊ / ‖x - y‖)
            (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal)) := by
        simpa using hφ_super.comp hdist_tendsto
      rw [EReal.tendsto_nhds_top_iff_real]
      intro ξ
      let M : ℝ := max ξ 0 + 1
      have hM_nonneg : 0 ≤ M := by
        dsimp [M]
        positivity
      have hξ_lt_M : ξ < M := by
        dsimp [M]
        linarith [le_max_left ξ 0]
      have hquot_M :
          ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop,
            ((M + ‖v‖ : ℝ) : EReal) < φ ‖x - y‖₊ / ‖x - y‖ :=
        (EReal.tendsto_nhds_top_iff_real.1 hquot_tendsto) (M + ‖v‖)
      have hdist_one :
          ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop,
            (1 : NNReal) ≤ ‖x - y‖₊ :=
        hdist_tendsto.eventually_ge_atTop 1
      filter_upwards [hquot_M, hdist_one] with x hxquot hxdist
      have hxdist_real : (1 : ℝ) ≤ ‖x - y‖ := by
        exact_mod_cast hxdist
      have hpointwise : ∀ u, u ∈ A x → M ≤ ‖u‖ := by
        intro u hu
        have hupper :
            φ ‖x - y‖₊ / ‖x - y‖ ≤ (‖u‖ + ‖v‖ : ℝ) :=
          modulus_div_le_norm_add_norm_of_uniformlyMonotone hA_uniform hu hv hxdist_real
        have hlt :
            ((M + ‖v‖ : ℝ) : EReal) < ((‖u‖ + ‖v‖ : ℝ) : EReal) :=
          lt_of_lt_of_le hxquot hupper
        have hlt_real : M + ‖v‖ < ‖u‖ + ‖v‖ := by
          exact_mod_cast hlt
        linarith
      have hinf :
          ENNReal.ofReal M ≤ Metric.infEDist (0 : H) (A x) :=
        le_infEDist_of_forall_mem_norm_ge hpointwise
      have hξ_lt_lower :
          (ξ : EReal) < ((ENNReal.ofReal M : ENNReal) : EReal) := by
        simpa [EReal.coe_ennreal_ofReal, max_eq_left hM_nonneg] using hξ_lt_M
      exact lt_of_lt_of_le hξ_lt_lower (by exact_mod_cast hinf)
    · -- If the graph is empty, every value set is empty, so `Metric.infEDist` is constantly `∞`.
      have hempty : ∀ x : H, A x = ∅ := fun x ↦ value_eq_empty_of_noGraphPoint A hgraph x
      simpa [hempty, Metric.infEDist_empty] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : H ↦ (⊤ : EReal))
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal)))
  exact
    (EReal.tendsto_coe_ennreal :
      Filter.Tendsto
          (fun x : H ↦ ((Metric.infEDist (0 : H) (A x) : ENNReal) : EReal))
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds ((⊤ : ENNReal) : EReal)) ↔
        Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal))).1 <| by
      simpa using htarget

/-- Helper for Proposition 22.11: a strongly monotone operator has
`Metric.infEDist (0 : H) (A x) → +∞` as `‖x‖ → +∞`. -/
private theorem tendsto_infEDist_zero_of_stronglyMonotone
    (A : SetValuedOperator H H) {β : ℝ} (hA_strong : A.IsStronglyMonotone β) :
    Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
      (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal)) := by
  have htarget :
      Filter.Tendsto
        (fun x : H ↦ ((Metric.infEDist (0 : H) (A x) : ENNReal) : EReal))
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal)) := by
    by_cases hgraph : ∃ y v, v ∈ A y
    · rcases hgraph with ⟨y, v, hv⟩
      have hdist_tendsto :
          Filter.Tendsto (fun x : H ↦ ‖x - y‖₊)
            (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop :=
        tendsto_nnnormSub_atTop y
      -- Route correction: instead of manufacturing a quadratic modulus, use the direct linear
      -- growth estimate from strong monotonicity and the same infimum transport step.
      rw [EReal.tendsto_nhds_top_iff_real]
      intro ξ
      let M : ℝ := max ξ 0 + 1
      have hM_nonneg : 0 ≤ M := by
        dsimp [M]
        positivity
      have hξ_lt_M : ξ < M := by
        dsimp [M]
        linarith [le_max_left ξ 0]
      let R : NNReal := ⟨(M + ‖v‖) / β, by
        have hβ_pos := hA_strong.pos
        positivity⟩
      have hdist_R :
          ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop, R ≤ ‖x - y‖₊ :=
        hdist_tendsto.eventually_ge_atTop R
      filter_upwards [hdist_R] with x hxR
      have hxR_real : ((R : NNReal) : ℝ) ≤ ‖x - y‖ := by
        exact_mod_cast hxR
      have hpointwise : ∀ u, u ∈ A x → M ≤ ‖u‖ := by
        intro u hu
        have hleft : M + ‖v‖ ≤ β * ‖x - y‖ := by
          have hdiv : (M + ‖v‖) / β ≤ ‖x - y‖ := by
            simpa [R] using hxR_real
          have hmul : M + ‖v‖ ≤ ‖x - y‖ * β := by
            exact (div_le_iff₀ hA_strong.pos).1 hdiv
          simpa [mul_comm] using hmul
        have hright : β * ‖x - y‖ ≤ ‖u‖ + ‖v‖ :=
          mul_norm_le_norm_add_norm_of_stronglyMonotone hA_strong hu hv
        linarith
      have hinf :
          ENNReal.ofReal M ≤ Metric.infEDist (0 : H) (A x) :=
        le_infEDist_of_forall_mem_norm_ge hpointwise
      have hξ_lt_lower :
          (ξ : EReal) < ((ENNReal.ofReal M : ENNReal) : EReal) := by
        simpa [EReal.coe_ennreal_ofReal, max_eq_left hM_nonneg] using hξ_lt_M
      exact lt_of_lt_of_le hξ_lt_lower (by exact_mod_cast hinf)
    · -- If the graph is empty, every value set is empty, so `Metric.infEDist` is constantly `∞`.
      have hempty : ∀ x : H, A x = ∅ := fun x ↦ value_eq_empty_of_noGraphPoint A hgraph x
      simpa [hempty, Metric.infEDist_empty] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : H ↦ (⊤ : EReal))
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : EReal)))
  exact
    (EReal.tendsto_coe_ennreal :
      Filter.Tendsto
          (fun x : H ↦ ((Metric.infEDist (0 : H) (A x) : ENNReal) : EReal))
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds ((⊤ : ENNReal) : EReal)) ↔
        Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal))).1 <| by
      simpa using htarget

/-- Proposition 22.11, growth conclusion: if `A : H → 2^H` is uniformly monotone with a modulus
`φ : NNReal → EReal` satisfying `φ t / t → +∞` as `t → +∞`, or if `A` is strongly monotone, then
`Metric.infEDist (0 : H) (A x) → +∞` as `‖x‖ → +∞`. -/
theorem tendsto_infEDist_zero_of_uniformlyMonotone_supercoerciveModulus_or_stronglyMonotone
    (A : SetValuedOperator H H)
    (hcase :
      (∃ φ : NNReal → EReal,
          A.IsUniformlyMonotone φ ∧
            Filter.Tendsto (fun t : NNReal ↦ φ t / (t : EReal))
              Filter.atTop (nhds (⊤ : EReal))) ∨
        ∃ β : ℝ, A.IsStronglyMonotone β) :
    Filter.Tendsto (fun x : H ↦ Metric.infEDist (0 : H) (A x))
      (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) (nhds (⊤ : ENNReal)) := by
  -- Assemble the two source cases through the dedicated branch theorems above.
  rcases hcase with ⟨φ, hA_uniform, hφ_super⟩ | ⟨β, hA_strong⟩
  · exact tendsto_infEDist_zero_of_uniformlyMonotone_supercoerciveModulus A hA_uniform hφ_super
  · exact tendsto_infEDist_zero_of_stronglyMonotone A hA_strong

end

/-- Companion surjectivity conclusion for Proposition 22.11: under the same hypotheses,
`A.range = Set.univ`. -/
theorem
    range_eq_univ_of_maximal_of_uniformlyMonotone_supercoerciveModulus_or_stronglyMonotone
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hcase :
      (∃ φ : NNReal → EReal,
          A.IsUniformlyMonotone φ ∧
            Filter.Tendsto (fun t : NNReal ↦ φ t / (t : EReal))
              Filter.atTop (nhds (⊤ : EReal))) ∨
        ∃ β : ℝ, A.IsStronglyMonotone β) :
    A.range = Set.univ :=
  range_eq_univ_of_maximal_of_tendsto_infEDist_zero A hA
    (tendsto_infEDist_zero_of_uniformlyMonotone_supercoerciveModulus_or_stronglyMonotone A hcase)

end SetValuedOperator

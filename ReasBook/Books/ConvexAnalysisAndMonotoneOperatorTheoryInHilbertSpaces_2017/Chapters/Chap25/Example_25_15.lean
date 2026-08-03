import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap22.Definition_22_1
import BauschkeLean.Chap25.Definition_25_10

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Example 25.15 records four sufficient conditions for the Chapter 25 notion of
  `3*` monotonicity.
- `core/canonical`: the reusable Chapter 25 owner is `A.IsThreeStarMonotone`, expressed through
  the Fitzpatrick owner `F[A]`.
- `bridge/view`: the asymptotic pairing-growth hypothesis remains a source-facing local predicate,
  with companion theorems into the canonical `IsThreeStarMonotone` owner; the uniform and strong
  monotonicity clauses are exposed as companions on their existing Chapter 22 owners. -/

/-- The asymptotic pairing-growth hypothesis used in Example 25.15(i): for every `x ∈ dom A` and
every real slope `μ`, all graph points `(z, w)` with sufficiently large `‖z‖` satisfy
`μ * ‖z‖ ≤ ⟪z - x, w⟫_ℝ`. This is the source-faithful eventual form of the displayed
Brézis-Haraux limit-inf condition. -/
def HasAsymptoticPairingGrowth (A : SetValuedOperator H H) : Prop :=
  ∀ ⦃x : H⦄, x ∈ A.dom → ∀ μ : ℝ, ∃ ρ : Set.Ioi (0 : ℝ),
    ∀ ⦃z w : H⦄, w ∈ A z → (ρ : ℝ) ≤ ‖z‖ → μ * ‖z‖ ≤ ⟪z - x, w⟫_ℝ

/-- Helper for Example 25.15: a finite real upper bound on every Fitzpatrick supremand at `(x, v)`
forces `(x, v)` to belong to the effective domain of `F[A]`. -/
private theorem mem_dom_fitzpatrick_of_supremand_le
    {A : SetValuedOperator H H} {x v : H} {C : ℝ}
    (hbound :
      ∀ p : gra A,
        ((⟪p.1.1, v⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal) ≤
          (C : EReal)) :
    (x, v) ∈ ERealFunction.dom (F[A]) := by
  -- Bounding each graph-point supremand by the same finite real bounds the full supremum.
  rw [ERealFunction.mem_dom_iff, fitzpatrickFunction]
  exact lt_of_le_of_lt (iSup_le hbound) (EReal.coe_lt_top C)

/-- Helper for Example 25.15: a bounded domain makes the asymptotic pairing-growth condition
vacuous outside one ball, because large graph points cannot occur. -/
private theorem hasAsymptoticPairingGrowth_of_bounded_dom
    {A : SetValuedOperator H H} (hdom_bounded : Bornology.IsBounded A.dom) :
    A.HasAsymptoticPairingGrowth := by
  intro x hx μ
  obtain ⟨R, hR⟩ := hdom_bounded.subset_closedBall (0 : H)
  let ρ : ℝ := max 1 (R + 1)
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  refine ⟨⟨ρ, hρ_pos⟩, ?_⟩
  intro z w hw hz
  -- Any graph point gives `z ∈ dom A`, so the closed-ball bound contradicts a large norm.
  have hz_dom : z ∈ A.dom := (SetValuedOperator.mem_dom_iff A z).2 ⟨w, hw⟩
  have hz_ball : z ∈ Metric.closedBall (0 : H) R := hR hz_dom
  have hz_norm_le : ‖z‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz_ball
  have hR_lt_ρ : R < ρ := by
    dsimp [ρ]
    exact lt_of_lt_of_le (lt_add_of_pos_right R zero_lt_one) (le_max_right _ _)
  have hfalse : False := by
    exact (not_lt_of_ge hz) (lt_of_le_of_lt hz_norm_le hR_lt_ρ)
  exact False.elim hfalse

/-- Helper for Example 25.15: a supercoercive radial modulus eventually dominates every linear
slope on `NNReal`. -/
private theorem supercoerciveRadialModulus_eventually_ge_linear
    {φ : NNReal → EReal}
    (hφ_super : ERealFunction.Supercoercive fun r : ℝ ↦ φ ‖r‖₊) (M : ℝ) :
    ∃ R : Set.Ioi (0 : ℝ), ∀ ⦃r : NNReal⦄, (R : ℝ) ≤ r →
      (((M * (r : ℝ) : ℝ) : EReal) ≤ φ r) := by
  rw [ERealFunction.Supercoercive, EReal.tendsto_nhds_top_iff_real] at hφ_super
  have htail :
      ∀ᶠ t : ℝ in Bornology.cobounded ℝ, (M : EReal) < φ ‖t‖₊ / ‖t‖ :=
    hφ_super M
  rw [Filter.atTop_basis_Ioi.cobounded_of_norm.eventually_iff] at htail
  rcases htail with ⟨R, -, hR_tail⟩
  let S : ℝ := max 1 (R + 1)
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  refine ⟨⟨S, hS_pos⟩, ?_⟩
  intro r hr
  have hr_pos : 0 < (r : ℝ) := lt_of_lt_of_le hS_pos hr
  have htail_r : (M : EReal) < φ r / (r : ℝ) := by
    have hR_lt_r : R < (r : ℝ) := by
      have hR_add : R + 1 ≤ (r : ℝ) := by
        dsimp [S] at hr
        exact le_trans (le_max_right _ _) hr
      linarith
    have htail_r' :
        (M : EReal) < φ ‖(r : ℝ)‖₊ / ‖(r : ℝ)‖ :=
      hR_tail (x := (r : ℝ)) (by simpa using hR_lt_r)
    simpa using htail_r'
  have hmul : ((M : EReal) * (r : ℝ)) < φ r := by
    exact (EReal.lt_div_iff (by exact_mod_cast hr_pos) (by simp)).1 htail_r
  simpa [← EReal.coe_mul] using hmul.le

/-- A supercoercive radial modulus yields the Chapter 22 growth hypothesis
`φ t / t → +∞` as `t → +∞`. -/
theorem supercoerciveRadialModulus_tendsto_div_atTop
    {φ : NNReal → EReal}
    (hφ_super : ERealFunction.Supercoercive fun r : ℝ ↦ φ ‖r‖₊) :
    Filter.Tendsto (fun t : NNReal ↦ φ t / (t : EReal))
      Filter.atTop (nhds (⊤ : EReal)) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  rcases supercoerciveRadialModulus_eventually_ge_linear hφ_super (M + 1) with ⟨R, hR⟩
  let S : NNReal := ⟨R, le_of_lt R.2⟩
  refine Filter.eventually_atTop.2 ⟨S, ?_⟩
  intro t ht
  have hRt : (R : ℝ) ≤ t := by
    exact_mod_cast ht
  have htail : ((((M + 1 : ℝ) * (t : ℝ) : ℝ) : EReal) ≤ φ t) := hR hRt
  have ht_pos_real : 0 < (t : ℝ) := lt_of_lt_of_le R.2 hRt
  have ht_pos : (0 : EReal) < (t : EReal) := by
    exact_mod_cast ht_pos_real
  have hquot : (((M + 1 : ℝ)) : EReal) ≤ φ t / (t : EReal) := by
    have hmul :
        ((((M + 1 : ℝ)) : EReal) * (t : EReal)) ≤ φ t := by
      simpa [EReal.coe_mul] using htail
    exact (EReal.le_div_iff_mul_le ht_pos (by simp)).2 hmul
  have hM : (M : EReal) < (((M + 1 : ℝ)) : EReal) := by
    exact_mod_cast (show M < M + 1 by linarith)
  exact lt_of_lt_of_le hM hquot

/-- Example 25.15 (1): under the source clause (i) asymptotic pairing-growth hypothesis, every
pair `(x, v)` with `x ∈ dom A` belongs to the effective domain of the Fitzpatrick function. -/
theorem HasAsymptoticPairingGrowth.dom_prod_univ_subset_dom_fitzpatrickFunction
    {A : SetValuedOperator H H} (hgrowth : A.HasAsymptoticPairingGrowth)
    (hA_mono : A.IsMonotone) :
    A.dom ×ˢ (Set.univ : Set H) ⊆ ERealFunction.dom (F[A]) := by
  rintro ⟨x, v⟩ hxv
  rcases (SetValuedOperator.mem_dom_iff A x).1 hxv.1 with ⟨u, hu⟩
  let μ : ℝ := ‖v‖ + 1
  rcases hgrowth hxv.1 μ with ⟨ρ, hρ⟩
  let C : ℝ := (‖x‖ + (ρ : ℝ)) * ‖u‖ + (ρ : ℝ) * ‖v‖
  -- Fix the source witness `u ∈ A x` and bound each Fitzpatrick supremand by a uniform constant.
  refine mem_dom_fitzpatrick_of_supremand_le (A := A) (x := x) (v := v) (C := C) ?_
  intro p
  by_cases hlarge : (ρ : ℝ) ≤ ‖p.1.1‖
  · -- Outside the growth radius, the asymptotic hypothesis beats the `⟪z, v⟫` term.
    have hgrowth_p : μ * ‖p.1.1‖ ≤ ⟪p.1.1 - x, p.1.2⟫_ℝ := hρ p.2 hlarge
    have hrewrite :
        ⟪p.1.1, v⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ =
          ⟪x - p.1.1, p.1.2⟫_ℝ + ⟪p.1.1, v⟫_ℝ := by
      rw [inner_sub_left]
      ring
    have hinner_le :
        ⟪x - p.1.1, p.1.2⟫_ℝ ≤ -(μ * ‖p.1.1‖) := by
      calc
        ⟪x - p.1.1, p.1.2⟫_ℝ = -⟪p.1.1 - x, p.1.2⟫_ℝ := by
          rw [inner_sub_left, inner_sub_left]
          ring
        _ ≤ -(μ * ‖p.1.1‖) := by
          linarith
    have hv_le : ⟪p.1.1, v⟫_ℝ ≤ ‖p.1.1‖ * ‖v‖ := real_inner_le_norm _ _
    have hμ_def : μ = ‖v‖ + 1 := rfl
    have hreal :
        ⟪p.1.1, v⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ ≤ 0 := by
      rw [hrewrite]
      have hsum_le : ⟪x - p.1.1, p.1.2⟫_ℝ + ⟪p.1.1, v⟫_ℝ ≤ -‖p.1.1‖ := by
        linarith [hinner_le, hv_le, hμ_def]
      have hnorm_nonpos : -‖p.1.1‖ ≤ 0 := by
        nlinarith [norm_nonneg p.1.1]
      exact le_trans hsum_le hnorm_nonpos
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      have hρ_nonneg : 0 ≤ (ρ : ℝ) := le_of_lt (show 0 < (ρ : ℝ) from ρ.2)
      nlinarith [norm_nonneg x, norm_nonneg u, norm_nonneg v, hρ_nonneg]
    calc
      ((⟪p.1.1, v⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ : ℝ) : EReal)
          ≤ (0 : EReal) := by
            exact_mod_cast hreal
      _ ≤ (C : EReal) := by
            exact_mod_cast hC_nonneg
  · -- Inside the radius, monotonicity and Cauchy-Schwarz give a finite bound.
    have hz_lt_ρ : ‖p.1.1‖ < (ρ : ℝ) := lt_of_not_ge hlarge
    have hmono :
        0 ≤ ⟪x - p.1.1, u - p.1.2⟫_ℝ :=
      (SetValuedOperator.isMonotone_iff A).1 hA_mono hu p.2
    have hinner_le_u : ⟪x - p.1.1, p.1.2⟫_ℝ ≤ ⟪x - p.1.1, u⟫_ℝ := by
      rw [inner_sub_right] at hmono
      linarith
    have hxu_le : ⟪x - p.1.1, u⟫_ℝ ≤ ‖x - p.1.1‖ * ‖u‖ := real_inner_le_norm _ _
    have hnorm_sub_le : ‖x - p.1.1‖ ≤ ‖x‖ + ‖p.1.1‖ := norm_sub_le _ _
    have hv_le : ⟪p.1.1, v⟫_ℝ ≤ ‖p.1.1‖ * ‖v‖ := real_inner_le_norm _ _
    have hrewrite :
        ⟪p.1.1, v⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ =
          ⟪x - p.1.1, p.1.2⟫_ℝ + ⟪p.1.1, v⟫_ℝ := by
      rw [inner_sub_left]
      ring
    have hpart₁ : ⟪x - p.1.1, p.1.2⟫_ℝ ≤ (‖x‖ + (ρ : ℝ)) * ‖u‖ := by
      have haux : ⟪x - p.1.1, p.1.2⟫_ℝ ≤ (‖x‖ + ‖p.1.1‖) * ‖u‖ := by
        have hmul :
            ‖x - p.1.1‖ * ‖u‖ ≤ (‖x‖ + ‖p.1.1‖) * ‖u‖ := by
          exact mul_le_mul_of_nonneg_right hnorm_sub_le (norm_nonneg u)
        exact le_trans hinner_le_u (le_trans hxu_le hmul)
      have hmul :
          (‖x‖ + ‖p.1.1‖) * ‖u‖ ≤ (‖x‖ + (ρ : ℝ)) * ‖u‖ := by
        have hsum : ‖x‖ + ‖p.1.1‖ ≤ ‖x‖ + (ρ : ℝ) := by
          linarith
        exact mul_le_mul_of_nonneg_right hsum (norm_nonneg u)
      exact le_trans haux hmul
    have hpart₂ : ⟪p.1.1, v⟫_ℝ ≤ (ρ : ℝ) * ‖v‖ := by
      have hmul : ‖p.1.1‖ * ‖v‖ ≤ (ρ : ℝ) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right hz_lt_ρ.le (norm_nonneg v)
      exact le_trans hv_le hmul
    have hreal :
        ⟪p.1.1, v⟫_ℝ + ⟪x, p.1.2⟫_ℝ - ⟪p.1.1, p.1.2⟫_ℝ ≤ C := by
      rw [hrewrite]
      dsimp [C]
      linarith
    exact_mod_cast hreal

/-- Example 25.15 (2): under the same clause (i) asymptotic pairing-growth hypothesis, the
operator `A` is `3*` monotone. -/
theorem HasAsymptoticPairingGrowth.isThreeStarMonotone
    {A : SetValuedOperator H H} (hgrowth : A.HasAsymptoticPairingGrowth)
    (hA_mono : A.IsMonotone) :
    A.IsThreeStarMonotone := by
  rw [SetValuedOperator.isThreeStarMonotone_iff]
  intro xv hxv
  -- The `3*` domain condition only asks for range points, so we reuse the stronger `univ` bound.
  exact HasAsymptoticPairingGrowth.dom_prod_univ_subset_dom_fitzpatrickFunction hgrowth hA_mono
    ⟨hxv.1, Set.mem_univ _⟩

/-- Example 25.15 (3): source clause (ii). If a monotone operator has bounded domain, then it is
`3*` monotone. -/
theorem isThreeStarMonotone_of_bounded_dom
    {A : SetValuedOperator H H} (hA_mono : A.IsMonotone)
    (hdom_bounded : Bornology.IsBounded A.dom) :
    A.IsThreeStarMonotone := by
  -- Convert boundedness of `dom A` into the asymptotic-growth hypothesis from clause (i).
  exact (hasAsymptoticPairingGrowth_of_bounded_dom (A := A) hdom_bounded).isThreeStarMonotone
    hA_mono

/-- Example 25.15 (4): source clause (iii). A uniformly monotone operator with a supercoercive
modulus is `3*` monotone. -/
theorem IsUniformlyMonotone.isThreeStarMonotone_of_supercoercive_modulus
    {A : SetValuedOperator H H} {φ : NNReal → EReal} (huniform : A.IsUniformlyMonotone φ)
    (hφ_super : ERealFunction.Supercoercive fun r : ℝ ↦ φ ‖r‖₊) :
    A.IsThreeStarMonotone := by
  have hgrowth : A.HasAsymptoticPairingGrowth := by
    intro x hx μ
    rcases (SetValuedOperator.mem_dom_iff A x).1 hx with ⟨u, hu⟩
    let μ₀ : ℝ := max μ 0
    let M : ℝ := 2 * μ₀ + ‖u‖
    rcases supercoerciveRadialModulus_eventually_ge_linear hφ_super M with ⟨R₁, hR₁⟩
    let ρ : ℝ := max (2 * (R₁ : ℝ)) (max (2 * ‖x‖) 1)
    have hρ_pos : 0 < ρ := by
      dsimp [ρ]
      positivity
    refine ⟨⟨ρ, hρ_pos⟩, ?_⟩
    intro z w hw hz
    -- Route correction: work with the distance `‖z - x‖`, where uniform monotonicity applies.
    have hμ_le : μ ≤ μ₀ := le_max_left _ _
    have hμ₀_nonneg : 0 ≤ μ₀ := le_max_right _ _
    have htwox_le : 2 * ‖x‖ ≤ ρ := by
      dsimp [ρ]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have htwoR₁_le : 2 * (R₁ : ℝ) ≤ ρ := by
      dsimp [ρ]
      exact le_max_left _ _
    have hnorm_x_le : ‖x‖ ≤ ‖z‖ / 2 := by
      nlinarith
    have hdist_half : ‖z‖ / 2 ≤ ‖z - x‖ := by
      have htri : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_add_le (z - x) x
      nlinarith
    have hR₁_le_dist : (R₁ : ℝ) ≤ ‖z - x‖ := by
      nlinarith
    have hlinear_modulus :
        (((M * ‖z - x‖ : ℝ) : EReal) ≤ φ ‖z - x‖₊) := by
      have hR₁_nn : (R₁ : ℝ) ≤ ‖z - x‖₊ := by
        exact_mod_cast hR₁_le_dist
      simpa [M] using hR₁ hR₁_nn
    have hpairE :
        (((M * ‖z - x‖ : ℝ) : EReal) ≤ (⟪z - x, w - u⟫_ℝ : EReal)) := by
      exact le_trans hlinear_modulus (huniform.ineq hw hu)
    have hpair :
        M * ‖z - x‖ ≤ ⟪z - x, w - u⟫_ℝ := by
      exact_mod_cast hpairE
    have hu_bound : ⟪z - x, u⟫_ℝ ≤ ‖z - x‖ * ‖u‖ := by
      simpa [mul_comm] using real_inner_le_norm (z - x) u
    have hpair' :
        M * ‖z - x‖ ≤ ⟪z - x, w⟫_ℝ - ⟪z - x, u⟫_ℝ := by
      simpa [inner_sub_right] using hpair
    have hu_lower : -(‖z - x‖ * ‖u‖) ≤ ⟪z - x, u⟫_ℝ := by
      have hneg_eq : -⟪z - x, u⟫_ℝ = ⟪x - z, u⟫_ℝ := by
        rw [inner_sub_left, inner_sub_left]
        ring
      have hneg_inner : -⟪z - x, u⟫_ℝ ≤ ‖z - x‖ * ‖u‖ := by
        rw [hneg_eq]
        simpa [norm_sub_rev] using real_inner_le_norm (x - z) u
      linarith
    have hcore : 2 * μ₀ * ‖z - x‖ ≤ ⟪z - x, w⟫_ℝ := by
      dsimp [M] at hpair'
      linarith [hpair', hu_lower]
    have hμ₀_norm : μ₀ * ‖z‖ ≤ 2 * μ₀ * ‖z - x‖ := by
      nlinarith [hdist_half, hμ₀_nonneg]
    have hμ_norm : μ * ‖z‖ ≤ μ₀ * ‖z‖ := by
      exact mul_le_mul_of_nonneg_right hμ_le (norm_nonneg z)
    -- The supercoercive linear tail absorbs the `u`-error and leaves the requested slope `μ`.
    have hreal : μ * ‖z‖ ≤ ⟪z - x, w⟫_ℝ := by
      exact le_trans hμ_norm (le_trans hμ₀_norm hcore)
    exact hreal
  exact hgrowth.isThreeStarMonotone huniform.isMonotone

/-- Example 25.15 (5): source clause (iv). A strongly monotone operator is `3*` monotone. -/
theorem IsStronglyMonotone.isThreeStarMonotone
    {A : SetValuedOperator H H} {β : ℝ} (hstrong : A.IsStronglyMonotone β) :
    A.IsThreeStarMonotone := by
  let ψ : NNReal → EReal := fun r ↦ (((β * (r : ℝ) ^ 2 : ℝ) : EReal))
  have huniform : A.IsUniformlyMonotone ψ := by
    refine ⟨?_, ?_, ?_⟩
    · -- The quadratic modulus is monotone on the nonnegative reals.
      intro r s hrs
      dsimp [ψ]
      have hsq : (r : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by
        have hr_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast r.2
        have hs_nonneg : 0 ≤ (s : ℝ) := by exact_mod_cast s.2
        have hrs' : (r : ℝ) ≤ s := by exact_mod_cast hrs
        nlinarith
      exact_mod_cast mul_le_mul_of_nonneg_left hsq hstrong.pos.le
    · -- Positivity of `β` forces the quadratic modulus to vanish only at `0`.
      intro r
      constructor
      · intro hr
        dsimp [ψ] at hr
        have hreal : β * (r : ℝ) ^ 2 = 0 := by
          exact_mod_cast hr
        have hsq_zero : (r : ℝ) ^ 2 = 0 := by
          nlinarith [hstrong.pos, hreal]
        exact_mod_cast sq_eq_zero_iff.mp hsq_zero
      · intro hr
        subst hr
        simp [ψ]
    · -- Strong monotonicity gives the lower bound for the quadratic modulus directly.
      intro x u y v hu hv
      have hineq : β * ‖x - y‖ ^ 2 ≤ ⟪x - y, u - v⟫_ℝ := hstrong.ineq hu hv
      have hineqE :
          (((β * ‖x - y‖ ^ 2 : ℝ) : EReal) ≤ (⟪x - y, u - v⟫_ℝ : EReal)) := by
        exact_mod_cast hineq
      simpa [ψ] using hineqE
  have hψ_super : ERealFunction.Supercoercive fun r : ℝ ↦ ψ ‖r‖₊ := by
    rw [ERealFunction.supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
    intro ξ
    let R : ℝ := max 1 (ξ / β + 1)
    have hR :
        ∀ᶠ r : ℝ in Filter.comap (fun r : ℝ ↦ ‖r‖) Filter.atTop, R ≤ ‖r‖ := by
      exact
        (Filter.tendsto_comap :
          Filter.Tendsto (fun r : ℝ ↦ ‖r‖)
            (Filter.comap (fun r : ℝ ↦ ‖r‖) Filter.atTop) Filter.atTop).eventually_ge_atTop R
    filter_upwards [hR] with r hr
    have hr_pos : 0 < ‖r‖ := by
      have hone : 1 ≤ ‖r‖ := le_trans (le_max_left _ _) hr
      exact lt_of_lt_of_le zero_lt_one hone
    have hlinear : ξ < β * ‖r‖ := by
      have htail : ξ / β + 1 ≤ ‖r‖ := le_trans (le_max_right _ _) hr
      have hscaled : ξ + β ≤ β * ‖r‖ := by
        have hmul := mul_le_mul_of_nonneg_left htail hstrong.pos.le
        have hβ_ne : β ≠ 0 := ne_of_gt hstrong.pos
        calc
          ξ + β = β * (ξ / β + 1) := by
            field_simp [hβ_ne]
          _ ≤ β * ‖r‖ := hmul
      linarith [hstrong.pos, hscaled]
    have hmul_real : ξ * ‖r‖ < β * ‖r‖ ^ 2 := by
      nlinarith [hlinear, hr_pos]
    have hmul :
        (ξ : EReal) * ‖r‖ < ψ ‖r‖₊ := by
      dsimp [ψ]
      have hcast :
          (((ξ * ‖r‖ : ℝ) : EReal)) < (((β * ‖r‖ ^ 2 : ℝ) : EReal)) := by
        exact_mod_cast hmul_real
      simpa using hcast
    exact (EReal.lt_div_iff (by exact_mod_cast hr_pos) (by simp)).2 hmul
  -- Reduce the strong case to the uniformly monotone case with the quadratic modulus.
  exact huniform.isThreeStarMonotone_of_supercoercive_modulus hψ_super

end SetValuedOperator

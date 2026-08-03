import Mathlib
import BauschkeLean.Chap08.Example_8_10
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap11.Proposition_11_14
import BauschkeLean.Chap11.Proposition_11_15
import BauschkeLean.Chap12.Proposition_12_26
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap12.ScaledProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 12 27: the quadratic penalty used in the proximal objective. -/
private noncomputable def quadraticPenalty (x : H) : H → Set.Ioi (⊥ : EReal) :=
  (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2).toEReal

/-- Helper for Proposition 12 27: the bundled proximal objective. -/
private noncomputable def proximalObjectiveIoi
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) : H → Set.Ioi (⊥ : EReal) :=
  f + quadraticPenalty x

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 27: coercing the bundled proximal objective recovers
`proximalObjective`. -/
@[simp] private theorem proximalObjectiveIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (x y : H) :
    (proximalObjectiveIoi f x y : EReal) = proximalObjective f x y := by
  simp [proximalObjectiveIoi, proximalObjective, quadraticPenalty]

omit [CompleteSpace H] in
/-- Helper for Proposition 12 27: a continuous convex real-valued function on all of `H`
defines an element of `Γ₀(H)` after applying `toEReal`. -/
private theorem real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (φ : H → ℝ) (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · simpa [Function.toEReal_apply] using
      (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨by simp [Function.effectiveDomain_toEReal], subset_rfl, ?_⟩
    intro x hx y hy a ha0 ha1
    have hineq :
        φ (a • x + (1 - a) • y) ≤ a * φ x + (1 - a) * φ y := by
      simpa using
        hconv.2 (by simp : x ∈ (Set.univ : Set H)) (by simp : y ∈ (Set.univ : Set H))
          ha0.le (sub_nonneg.mpr ha1.le) (by linarith)
    have hcast :
        (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) ≤
          (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := by
      exact_mod_cast hineq
    simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

omit [CompleteSpace H] in
/-- Helper for Proposition 12 27: the quadratic penalty belongs to `Γ₀(H)`. -/
private theorem quadraticPenalty_mem_gammaZero (x : H) :
    quadraticPenalty x ∈ Γ₀(H) := by
  have hcont : Continuous fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    exact continuous_const.mul ((continuous_norm.comp (continuous_const.sub continuous_id)).pow 2)
  have hbase : _root_.ConvexOn ℝ Set.univ (fun z : H ↦ ‖z‖ ^ 2) := by
    -- Use the earlier strict convexity theorem as the stable convexity source for `‖·‖²`.
    exact (strictConvexOn_norm_sq (H := H)).convexOn
  have hconv : _root_.ConvexOn ℝ Set.univ (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro y hy z hz a b ha hb hab
    have hsq :
        ‖x - (a • y + b • z)‖ ^ 2 ≤ a * ‖x - y‖ ^ 2 + b * ‖x - z‖ ^ 2 := by
      have hrewrite :
          x - (a • y + b • z) = a • (x - y) + b • (x - z) := by
        calc
          x - (a • y + b • z) = (a + b) • x - (a • y + b • z) := by simp [hab]
          _ = a • x + b • x - (a • y + b • z) := by rw [add_smul]
          _ = a • (x - y) + b • (x - z) := by
            rw [smul_sub, smul_sub]
            abel_nf
      simpa [hrewrite] using
        hbase.2 (by simp : x - y ∈ (Set.univ : Set H)) (by simp : x - z ∈ (Set.univ : Set H))
          ha hb hab
    have hscaled :
        (1 / 2 : ℝ) * ‖x - (a • y + b • z)‖ ^ 2 ≤
          (1 / 2 : ℝ) * (a * ‖x - y‖ ^ 2 + b * ‖x - z‖ ^ 2) := by
      nlinarith
    have htarget :
        (1 / 2 : ℝ) * ‖x - (a • y + b • z)‖ ^ 2 ≤
          a * ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) + b * ((1 / 2 : ℝ) * ‖x - z‖ ^ 2) := by
      nlinarith
    simpa [smul_eq_mul] using htarget
  simpa [quadraticPenalty, Function.toEReal_apply] using
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
      (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) hcont hconv

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 27: the quadratic penalty is finite everywhere. -/
private theorem effectiveDomain_quadraticPenalty_eq_univ (x : H) :
    effectiveDomain (quadraticPenalty x) = Set.univ := by
  ext y
  simp [quadraticPenalty]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 27: the quadratic penalty is supercoercive. -/
private theorem quadraticPenalty_supercoercive (x : H) :
    Supercoercive (quadraticPenalty x).asEReal := by
  rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
  intro ξ
  let R : ℝ := max (2 * ‖x‖) (8 * (|ξ| + 1))
  have hR :
      ∀ᶠ y : H in Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop, R ≤ ‖y‖ := by
    simpa [R] using
      (Filter.Tendsto.eventually_ge_atTop
        (Filter.tendsto_comap : Filter.Tendsto (fun y : H ↦ ‖y‖)
          (Filter.comap (fun y : H ↦ ‖y‖) Filter.atTop) Filter.atTop) R)
  filter_upwards [hR] with y hyR
  have hyx : 2 * ‖x‖ ≤ ‖y‖ := le_trans (le_max_left _ _) hyR
  have hybig : 8 * (|ξ| + 1) ≤ ‖y‖ := le_trans (le_max_right _ _) hyR
  have hy_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
  have hy_pos : 0 < ‖y‖ := by
    have : (0 : ℝ) < 8 * (|ξ| + 1) := by
      have : (0 : ℝ) < |ξ| + 1 := by positivity
      positivity
    exact lt_of_lt_of_le this hybig
  have hdist : ‖y‖ / 2 ≤ ‖x - y‖ := by
    have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_add_le (y - x) x
    have haux : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
      simpa [norm_sub_rev, add_comm] using htri
    nlinarith
  have htail : ξ < ‖y‖ / 8 := by
    have hbound : |ξ| + 1 ≤ ‖y‖ / 8 := by
      nlinarith
    linarith [le_abs_self ξ]
  have hquad :
      ‖y‖ / 8 ≤ ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) / ‖y‖ := by
    have hsq : ‖y‖ ^ 2 ≤ 4 * ‖x - y‖ ^ 2 := by
      nlinarith [hdist]
    have hmul : (‖y‖ / 8) * ‖y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
      nlinarith [hsq]
    exact (le_div_iff₀ hy_pos).2 hmul
  have hreal :
      ξ < ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) / ‖y‖ := lt_of_lt_of_le htail hquad
  have hmul :
      (ξ : EReal) * ‖y‖ < (quadraticPenalty x y : EReal) := by
    have hmul_real : ξ * ‖y‖ < (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
      exact (lt_div_iff₀ hy_pos).1 hreal
    simpa [quadraticPenalty] using
      (show (((ξ * ‖y‖ : ℝ)) : EReal) <
        (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) from by
          exact_mod_cast hmul_real)
  exact (EReal.lt_div_iff (by exact_mod_cast hy_pos) (by simp)).2 hmul

/-- Helper for Proposition 12 27: every proximal-point set is nonempty for a `Γ₀(H)` function. -/
private theorem proximalPoints_nonempty_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    (proximalPoints f x).Nonempty := by
  have hquad : quadraticPenalty x ∈ Γ₀(H) := quadraticPenalty_mem_gammaZero x
  rcases hf.2.nonempty with ⟨p, hp⟩
  have hdom : (effectiveDomain f ∩ effectiveDomain (quadraticPenalty x)).Nonempty := by
    refine ⟨p, hp, ?_⟩
    -- The quadratic term never takes the value `⊤`, so any finite point of `f` is admissible.
    simp [effectiveDomain_quadraticPenalty_eq_univ x]
  have hsum : quadraticPenalty x + f ∈ Γ₀(H) := by
    simpa [add_comm] using pointwiseAdd_mem_gammaZero f (quadraticPenalty x) hf hquad hdom
  have hsuper : Supercoercive (quadraticPenalty x + f).asEReal := by
    simpa [add_comm] using
      pointwiseAdd_supercoercive_of_mem_gammaZero f (quadraticPenalty x) hf
        (quadraticPenalty_supercoercive x)
  have hcoe : Coercive (quadraticPenalty x + f).asEReal :=
    coercive_of_supercoercive hsuper
  have hargmin :
      (Argmin ((quadraticPenalty x + f).asEReal)).Nonempty := by
    simpa using
      argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded hsum
        isClosed_univ convex_univ Set.univ_nonempty (Or.inl hcoe)
  simpa [proximalPoints, proximalObjectiveIoi, add_comm, proximalObjectiveIoi_apply] using hargmin

/-- Helper for Proposition 12 27: the chosen scaled proximal point is genuinely proximal for
`γ • f`. -/
private theorem scaledProximityOperator_isProxPoint_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal) :
    IsProxPoint (γ • f) x (Prox[γ, f, hf] x) := by
  -- Use the canonical scaled operator owner so later files do not duplicate the `Prox[γ,f,hf]`
  -- API locally.
  simpa [scaledProximityOperator] using
    proximityOperator_isProxPoint
      (γ • f)
      (hasUniqueProxPoint_of_mem_gammaZero (γ • f) (smul_mem_gammaZero f hf γ))
      x

-- Proof sketch: the scaled proximity operator is the ordinary proximity operator of `γ • f`; a
-- proximal point cannot have value `⊤`, because it minimizes the proximal objective and that
-- objective is finite at one comparison point from the proper domain of `f`.
/-- For `f ∈ Γ₀(H)`, every scaled proximal point belongs to the effective domain of `f`. -/
theorem scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal) :
    Prox[γ, f, hf] x ∈ effectiveDomain f := by
  let p := Prox[γ, f, hf] x
  let hγf : γ • f ∈ Γ₀(H) := smul_mem_gammaZero f hf γ
  have hprox : IsProxPoint (γ • f) x p := by
    simpa [p] using scaledProximityOperator_isProxPoint_of_mem_gammaZero f hf x γ
  rcases hf.2.nonempty with ⟨q, hq⟩
  -- Compare the proximal point with one finite comparison point from the proper domain of `f`.
  have hvar := (isProxPoint_iff_forall_inner_add_le (γ • f) hγf.2 x p).mp hprox q
  by_contra hp
  have hfp_top : (f p : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hp))
  have hscaled_top : ((γ • f) p : EReal) = ⊤ := by
    rw [posReal_smul_apply, hfp_top]
    simpa using EReal.coe_mul_top_of_pos γ.2
  have hfq_top : (f q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq)
  have hscaled_q_ne_top : ((γ • f) q : EReal) ≠ ⊤ := by
    rw [posReal_smul_apply, EReal.mul_ne_top]
    exact
      ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
        Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hfq_top⟩
  have hsum_top : (⟪q - p, x - p⟫_ℝ : EReal) + ((γ • f) p : EReal) = ⊤ := by
    rw [hscaled_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  rw [hsum_top] at hvar
  exact hscaled_q_ne_top (top_le_iff.mp hvar)

/-- Helper for Proposition 12 27: a positive common right factor can be canceled from an
`EReal` inequality. -/
private theorem ereal_le_of_mul_le_mul_of_pos_right
    {a b : EReal} {c : ℝ} (h : a * c ≤ b * c) (hc : 0 < c) :
    a ≤ b := by
  -- Divide by the positive factor and simplify both quotients.
  have hdiv :
      (a * c) / (c : EReal) ≤ (b * c) / (c : EReal) := by
    exact EReal.div_le_div_right_of_nonneg
      (show (0 : EReal) ≤ (c : EReal) by exact_mod_cast hc.le) h
  have hc_bot : ((c : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hc_top : ((c : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hc_zero : ((c : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hcancel_a : (a * c) / (c : EReal) = a := by
    rw [EReal.div_eq_iff hc_bot hc_top hc_zero]
  have hcancel_b : (b * c) / (c : EReal) = b := by
    rw [EReal.div_eq_iff hc_bot hc_top hc_zero]
  simpa [hcancel_a, hcancel_b] using hdiv

-- Proof sketch: compare the scaled proximal objectives at the proximal points of parameters `γ`
-- and `μ`, add the two minimizing inequalities, and cancel the quadratic terms.
/-- Proposition 12 27 (1): for `f ∈ Γ₀(H)` and `x ∈ H`, the proximal value function
`γ ↦ f (Prox_{γ f} x)` is decreasing on `ℝ_{++}`. -/
theorem antitone_proxValue_along_parameter_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Antitone (fun γ : PosReal ↦ (f (Prox[γ, f, hf] x) : EReal).toReal) := by
  intro γ μ hγμ
  rcases lt_or_eq_of_le hγμ with hγμ' | rfl
  · let p := Prox[γ, f, hf] x
    let q := Prox[μ, f, hf] x
    let hγf : γ • f ∈ Γ₀(H) := smul_mem_gammaZero f hf γ
    let hμf : μ • f ∈ Γ₀(H) := smul_mem_gammaZero f hf μ
    have hp : IsProxPoint (γ • f) x p := by
      simpa [p] using scaledProximityOperator_isProxPoint_of_mem_gammaZero f hf x γ
    have hq : IsProxPoint (μ • f) x q := by
      simpa [q] using scaledProximityOperator_isProxPoint_of_mem_gammaZero f hf x μ
    have hp_dom : p ∈ effectiveDomain f :=
      scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero f hf x γ
    have hq_dom : q ∈ effectiveDomain f :=
      scaledProximityOperator_mem_effectiveDomain_of_mem_gammaZero f hf x μ
    have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp_dom)
    have hfp_bot : (f p : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
    have hfq_top : (f q : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hq_dom)
    have hfq_bot : (f q : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f q : EReal) from (f q).2)
    have hpq_ereal := (isProxPoint_iff_forall_inner_add_le (γ • f) hγf.2 x p).mp hp q
    have hpq :
        ⟪q - p, x - p⟫_ℝ + (γ : ℝ) * (f p : EReal).toReal ≤
          (γ : ℝ) * (f q : EReal).toReal := by
      have hcast :
          (((⟪q - p, x - p⟫_ℝ + (γ : ℝ) * (f p : EReal).toReal : ℝ) : EReal)) ≤
            ((((γ : ℝ) * (f q : EReal).toReal : ℝ) : EReal)) := by
        simpa [posReal_smul_apply, EReal.coe_toReal hfp_top hfp_bot,
          EReal.coe_toReal hfq_top hfq_bot, EReal.coe_add, EReal.coe_mul] using hpq_ereal
      exact_mod_cast hcast
    have hqp_ereal := (isProxPoint_iff_forall_inner_add_le (μ • f) hμf.2 x q).mp hq p
    have hqp :
        ⟪p - q, x - q⟫_ℝ + (μ : ℝ) * (f q : EReal).toReal ≤
          (μ : ℝ) * (f p : EReal).toReal := by
      have hcast :
          (((⟪p - q, x - q⟫_ℝ + (μ : ℝ) * (f q : EReal).toReal : ℝ) : EReal)) ≤
            ((((μ : ℝ) * (f p : EReal).toReal : ℝ) : EReal)) := by
        simpa [posReal_smul_apply, EReal.coe_toReal hfp_top hfp_bot,
          EReal.coe_toReal hfq_top hfq_bot, EReal.coe_add, EReal.coe_mul] using hqp_ereal
      exact_mod_cast hcast
    have hnorm :
        ⟪q - p, x - p⟫_ℝ + ⟪p - q, x - q⟫_ℝ = ‖p - q‖ ^ (2 : ℕ) := by
      let d : H := p - q
      have hqpd : q - p = -d := by
        dsimp [d]
        abel_nf
      have hsub : x - q - (x - p) = d := by
        dsimp [d]
        abel_nf
      calc
        ⟪q - p, x - p⟫_ℝ + ⟪p - q, x - q⟫_ℝ
            = inner ℝ (-d) (x - p) + inner ℝ d (x - q) := by rw [hqpd]
        _ = -inner ℝ d (x - p) + inner ℝ d (x - q) := by simp
        _ = inner ℝ d (x - q) - inner ℝ d (x - p) := by ring
        _ = inner ℝ d (x - q - (x - p)) := by rw [← inner_sub_right]
        _ = inner ℝ d d := by rw [hsub]
        _ = ‖d‖ ^ (2 : ℕ) := by rw [real_inner_self_eq_norm_sq]
        _ = ‖p - q‖ ^ (2 : ℕ) := by simp [d]
    have hineq :
        ‖p - q‖ ^ (2 : ℕ) ≤ ((μ : ℝ) - γ) * ((f p : EReal).toReal - (f q : EReal).toReal) := by
      nlinarith [hpq, hqp, hnorm]
    have hprod_nonneg :
        0 ≤ ((μ : ℝ) - γ) * ((f p : EReal).toReal - (f q : EReal).toReal) := by
      exact le_trans (sq_nonneg ‖p - q‖) hineq
    have hdiff_nonneg :
        0 ≤ (f p : EReal).toReal - (f q : EReal).toReal := by
      exact
        (mul_nonneg_iff_of_pos_left
          (show (0 : ℝ) < (μ : ℝ) - γ from sub_pos.mpr hγμ')).mp hprod_nonneg
    linarith
  · simp

/-- Helper for Proposition 12 27: Proposition 12.26 at `y = x` yields the textbook base
estimate for the scaled proximal point. -/
private theorem scaled_prox_base_inequality
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal) :
    (((‖x - Prox[γ, f, hf] x‖ ^ 2 : ℝ) : EReal) +
        (γ • f).asEReal (Prox[γ, f, hf] x)) ≤
      (γ • f).asEReal x := by
  let p := Prox[γ, f, hf] x
  let hγf : γ • f ∈ Γ₀(H) := smul_mem_gammaZero f hf γ
  have hprox : IsProxPoint (γ • f) x p := by
    simpa [p] using scaledProximityOperator_isProxPoint_of_mem_gammaZero f hf x γ
  -- Specialize Proposition 12.26 to the comparison point `y = x` and rewrite the inner product.
  have hvar := (isProxPoint_iff_forall_inner_add_le (γ • f) hγf.2 x p).mp hprox x
  simpa [p, Function.asEReal, real_inner_self_eq_norm_sq] using hvar

/-- Helper for Proposition 12 27: every scaled proximal value is bounded above by the value at the
base point. -/
private theorem proxValue_asEReal_le_self_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal) :
    f.asEReal (Prox[γ, f, hf] x) ≤ f.asEReal x := by
  let p := Prox[γ, f, hf] x
  have hineq := scaled_prox_base_inequality f hf x γ
  have hnorm_nonneg : (0 : EReal) ≤ (((‖x - p‖ ^ 2 : ℝ) : EReal)) := by
    exact_mod_cast sq_nonneg ‖x - p‖
  have hscaled : ((γ • f) p : EReal) ≤ ((γ • f) x : EReal) := by
    -- Drop the nonnegative squared-distance term from the normalized estimate.
    exact le_trans (le_add_of_nonneg_left hnorm_nonneg) (by simpa [p] using hineq)
  have hmul : (f p : EReal) * (γ : ℝ) ≤ (f x : EReal) * (γ : ℝ) := by
    simpa [posReal_smul_apply, mul_comm] using hscaled
  have hbase : (f p : EReal) ≤ (f x : EReal) :=
    ereal_le_of_mul_le_mul_of_pos_right hmul γ.2
  simpa [p, Function.asEReal] using hbase

-- Proof sketch: use the pointwise estimate from clause (3) to bound every value of
-- `γ ↦ f (Prox_{γ f} x)` by `f x`, then apply `sSup_le`.
/-- Proposition 12.27 (2): for `f ∈ Γ₀(H)` and `x ∈ H`, the supremum of the proximal values
`f (Prox_{γ f} x)` over `γ ∈ ℝ_{++}` is bounded above by `f x`. -/
theorem sSup_proxValue_range_le_self_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    sSup (Set.range (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x))) ≤
      f.asEReal x := by
  -- Apply the pointwise bound from the normalized proximal inequality to every parameter value.
  refine sSup_le ?_
  rintro y ⟨γ, rfl⟩
  exact proxValue_asEReal_le_self_of_mem_gammaZero f hf x γ

-- Proof sketch: test the minimizing property of the scaled proximal objective along the segment
-- from `Prox_{γ f} x` to `x`, apply convexity of `γ • f`, and let the segment parameter tend to
-- `0`.
/-- Proposition 12.27 (3): for `f ∈ Γ₀(H)`, `x ∈ H`, and `γ ∈ ℝ_{++}`, the proximal point
`Prox_{γ f} x` satisfies the estimate
`‖x - Prox_{γ f} x‖² + γ f (Prox_{γ f} x) ≤ γ f x`. -/
theorem sqDist_add_smul_proxValue_le_smul_self_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (γ : PosReal) :
    (((‖x - Prox[γ, f, hf] x‖ ^ 2 : ℝ) : EReal) +
        (γ • f).asEReal (Prox[γ, f, hf] x)) ≤
      (γ • f).asEReal x := by
  -- This is exactly the normalized `y = x` specialization recorded in the helper above.
  simpa using scaled_prox_base_inequality f hf x γ

end ERealFunction

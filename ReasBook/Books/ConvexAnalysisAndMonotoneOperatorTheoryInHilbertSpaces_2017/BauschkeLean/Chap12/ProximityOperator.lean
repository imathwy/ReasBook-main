import Mathlib
import BauschkeLean.Chap08.Example_8_10
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap10.Example_10_9
import BauschkeLean.Chap11.Corollary_11_16
import BauschkeLean.Chap11.Corollary_11_30
import BauschkeLean.Chap12.Definition_12_23

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Basic

variable {H : Type u} [NormedAddCommGroup H]
variable (f : H → Set.Ioi (⊥ : EReal))

-- Semantic search note: no deferred `lean_leansearch` tool was available in this environment, so
-- the Chapter 12 owner/API choice was verified directly against `Definition_12_23` and downstream
-- repository precedent such as `Chap19/Corollary_19_7.lean`.

/-- Helper for ProximityOperator: the quadratic penalty `y ↦ (1 / 2) ‖x - y‖²` as an
`]-∞,+∞]`-valued function. -/
private noncomputable def quadraticPenalty (x : H) : H → Set.Ioi (⊥ : EReal) :=
  (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2).toEReal

/-- Helper for ProximityOperator: the bundled proximal objective is the sum of `f` and the
quadratic penalty. -/
private noncomputable def proximalObjectiveIoi (x : H) : H → Set.Ioi (⊥ : EReal) :=
  f + quadraticPenalty x

/-- Helper for ProximityOperator: coercing the quadratic penalty back to `EReal` gives the
expected real formula. -/
@[simp] private theorem quadraticPenalty_apply (x y : H) :
    (quadraticPenalty (H := H) x y : EReal) = (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
  -- Unfold the bundled `toEReal` wrapper to recover the defining real expression.
  simp [quadraticPenalty]

/-- Helper for ProximityOperator: coercing the bundled proximal objective back to `EReal`
recovers the proximal objective from Definition 12.23. -/
@[simp] private theorem proximalObjectiveIoi_asEReal (x : H) :
    (proximalObjectiveIoi (f := f) x).asEReal = proximalObjective f x := by
  -- The bundled sum is definitionally the same regularized objective after coercion.
  funext y
  simp [proximalObjectiveIoi, proximalObjective, quadraticPenalty]

section Inner

variable [InnerProductSpace ℝ H]

/-- Helper for ProximityOperator: a continuous convex real-valued function on all of `H`
canonically yields a member of `Γ₀(H)` after applying `toEReal`. -/
private theorem real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (φ : H → ℝ) (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(H) := by
  -- Package lower semicontinuity and global convexity through the everywhere-finite `toEReal`.
  rw [mem_gammaZero_iff]
  constructor
  · simpa using (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨?_, ?_, ?_⟩
    · rw [Function.effectiveDomain_toEReal]
      exact (Set.univ_nonempty : (Set.univ : Set H).Nonempty)
    · rw [Function.effectiveDomain_toEReal]
    · intro x _ y _ a ha0 ha1
      have hreal :
          φ (a • x + (1 - a) • y) ≤ a * φ x + (1 - a) * φ y := by
        simpa [smul_eq_mul] using
          hconv.2 (by simp : x ∈ (Set.univ : Set H)) (by simp : y ∈ (Set.univ : Set H))
            ha0.le (sub_nonneg.mpr ha1.le) (by ring)
      have hcast :
          (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) ≤
            (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := by
        exact_mod_cast hreal
      simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

/-- Helper for ProximityOperator: the quadratic penalty belongs to `Γ₀(H)`. -/
private theorem quadraticPenalty_mem_gammaZero (x : H) :
    quadraticPenalty (H := H) x ∈ Γ₀(H) := by
  have hcont : Continuous fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    -- The quadratic term is a continuous scalar multiple of the squared distance map.
    exact continuous_const.mul ((continuous_norm.comp (continuous_const.sub continuous_id)).pow 2)
  have hbase : _root_.ConvexOn ℝ Set.univ (fun z : H ↦ ‖z‖ ^ 2) := by
    -- Reuse the established strict convexity of `‖·‖²` as the canonical convexity source.
    exact (strictConvexOn_norm_sq (H := H)).convexOn
  have hconv : _root_.ConvexOn ℝ Set.univ (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
    -- Translate the norm-square Jensen inequality from `z ↦ ‖z‖²` to `y ↦ ‖x - y‖²`.
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
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
    have htarget :
        (1 / 2 : ℝ) * ‖x - (a • y + b • z)‖ ^ 2 ≤
          a * ((1 / 2 : ℝ) * ‖x - y‖ ^ 2) + b * ((1 / 2 : ℝ) * ‖x - z‖ ^ 2) := by
      nlinarith
    simpa [smul_eq_mul] using htarget
  -- Package the real quadratic penalty through the general `toEReal` bridge.
  simpa [quadraticPenalty, Function.toEReal_apply] using
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ (H := H)
      (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) hcont hconv

omit [InnerProductSpace ℝ H] in
/-- Helper for ProximityOperator: the quadratic penalty is finite everywhere. -/
private theorem effectiveDomain_quadraticPenalty_eq_univ (x : H) :
    effectiveDomain (quadraticPenalty (H := H) x) = Set.univ := by
  -- The `toEReal` quadratic term is real-valued at every point, hence never equals `⊤`.
  ext y
  simp [quadraticPenalty]

/-- Helper for ProximityOperator: the bundled proximal objective again belongs to `Γ₀(H)`. -/
private theorem proximalObjectiveIoi_mem_gammaZero_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (x : H) :
    proximalObjectiveIoi (f := f) x ∈ Γ₀(H) := by
  have hquad : quadraticPenalty (H := H) x ∈ Γ₀(H) :=
    quadraticPenalty_mem_gammaZero (H := H) x
  rcases hf.2.nonempty with ⟨p, hp⟩
  have hdom : (effectiveDomain f ∩ effectiveDomain (quadraticPenalty (H := H) x)).Nonempty := by
    -- The quadratic term has full effective domain, so any finite point of `f` is admissible.
    refine ⟨p, hp, ?_⟩
    simp [effectiveDomain_quadraticPenalty_eq_univ (H := H) x]
  -- The proximal objective is exactly the pointwise sum of the two `Γ₀(H)` owners.
  simpa [proximalObjectiveIoi] using
    pointwiseAdd_mem_gammaZero f (quadraticPenalty (H := H) x) hf hquad hdom

/-- Helper for ProximityOperator: the real quadratic penalty is strictly convex on `Set.univ`. -/
private theorem quadraticPenalty_real_strictConvexOn_univ (x : H) :
    _root_.StrictConvexOn ℝ Set.univ (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
  have hbase' :
      _root_.StrictConvexOn ℝ Set.univ (((fun z : H ↦ ‖z‖ ^ 2) ∘ fun z : H ↦ z - x)) := by
    -- Translate the strict convexity of `‖·‖²` from the origin to the base point `x`.
    simpa [Function.comp, sub_eq_add_neg, add_comm] using
      (strictConvexOn_norm_sq (H := H)).translate_right (-x)
  have hbase :
      _root_.StrictConvexOn ℝ Set.univ (fun z : H ↦ ‖x - z‖ ^ 2) := by
    convert hbase' using 1
    ext z
    simp [Function.comp, norm_sub_rev]
  have hscaled :
      _root_.StrictConvexOn ℝ Set.univ (fun z : H ↦ (1 / 2 : ℝ) * ‖x - z‖ ^ 2) := by
    refine ⟨hbase.1, ?_⟩
    intro z₁ _ z₂ _ hz a b ha hb hab
    have hineq :
        ‖x - (a • z₁ + b • z₂)‖ ^ 2 <
          a * ‖x - z₁‖ ^ 2 + b * ‖x - z₂‖ ^ 2 :=
      hbase.2 (by simp) (by simp) hz ha hb hab
    calc
      (1 / 2 : ℝ) * ‖x - (a • z₁ + b • z₂)‖ ^ 2
          < (1 / 2 : ℝ) * (a * ‖x - z₁‖ ^ 2 + b * ‖x - z₂‖ ^ 2) := by
              exact mul_lt_mul_of_pos_left hineq (by positivity)
      _ = a * ((1 / 2 : ℝ) * ‖x - z₁‖ ^ 2) + b * ((1 / 2 : ℝ) * ‖x - z₂‖ ^ 2) := by
            ring
  exact hscaled

/-- Helper for ProximityOperator: strict convexity on `Set.univ` survives the everywhere-finite
`toEReal` coercion. -/
private theorem strictlyConvex_toEReal_of_strictConvexOn_univ
    {φ : H → ℝ} (hφ : _root_.StrictConvexOn ℝ Set.univ φ) :
    StrictlyConvex φ.toEReal := by
  -- Convert the strict Jensen inequality for the real representative into the owner inequality.
  intro x hx y hy hxy a ha0 ha1
  have hb0 : 0 < 1 - a := sub_pos.mpr ha1
  have hab : a + (1 - a) = 1 := by
    ring
  have hineq :
      φ (a • x + (1 - a) • y) < a * φ x + (1 - a) * φ y :=
    hφ.2 (by simp) (by simp) hxy ha0 hb0 hab
  have hineqE :
      (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) <
        (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := by
    exact_mod_cast hineq
  calc
    (φ.toEReal (a • x + (1 - a) • y) : EReal)
        = (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) := by
            simp [Function.toEReal_apply]
    _ < (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := hineqE
    _ = (a : EReal) * (φ.toEReal x : EReal) + (1 - a : EReal) * (φ.toEReal y : EReal) := by
          simp [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add]

/-- Helper for ProximityOperator: the quadratic penalty is strictly convex. -/
private theorem quadraticPenalty_strictlyConvex (x : H) :
    StrictlyConvex (quadraticPenalty (H := H) x) := by
  -- Apply the `toEReal` strict-convexity bridge to the translated squared norm.
  simpa [quadraticPenalty, Function.toEReal_apply] using
    strictlyConvex_toEReal_of_strictConvexOn_univ
      (H := H) (quadraticPenalty_real_strictConvexOn_univ (H := H) x)

/-- Helper for ProximityOperator: the real quadratic penalty is strongly convex with constant `1`
on all of `H`. -/
private theorem quadraticPenalty_strongConvexOn_univ (x : H) :
    StrongConvexOn (Set.univ : Set H) (1 : ℝ) (fun y : H ↦ (1 / 2 : ℝ) * ‖x - y‖ ^ 2) := by
  -- Rewrite strong convexity into convexity after subtracting the unit quadratic correction.
  rw [strongConvexOn_iff_convex]
  have hconst :
      _root_.ConvexOn ℝ (Set.univ : Set H) (fun _ : H ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2) :=
    convexOn_const _ convex_univ
  have hlin : _root_.ConvexOn ℝ (Set.univ : Set H) (fun y : H ↦ -⟪x, y⟫_ℝ) := by
    -- The residual term is affine, hence convex on all of `H`.
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    apply le_of_eq
    have hreal :
        -⟪x, a • y + b • z⟫_ℝ = a * (-⟪x, y⟫_ℝ) + b * (-⟪x, z⟫_ℝ) := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      ring
    simpa [smul_eq_mul] using hreal
  have haff :
      _root_.ConvexOn ℝ (Set.univ : Set H) (fun y : H ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2 - ⟪x, y⟫_ℝ) := by
    -- Add the constant term to the linear functional to obtain the affine comparison function.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hconst.add hlin
  -- Expand the squared norm to identify the comparison function explicitly.
  convert haff using 1
  ext y
  rw [norm_sub_sq_real]
  ring

omit [InnerProductSpace ℝ H] in
/-- Helper for ProximityOperator: the quadratic penalty is supercoercive. -/
private theorem quadraticPenalty_supercoercive (x : H) :
    Supercoercive (quadraticPenalty (H := H) x).asEReal := by
  -- Use an explicit quadratic lower tail to dominate any prescribed linear level.
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
  have hy_pos : 0 < ‖y‖ := by
    have hpos : (0 : ℝ) < 8 * (|ξ| + 1) := by
      positivity
    exact lt_of_lt_of_le hpos hybig
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
      (ξ : EReal) * ‖y‖ < (quadraticPenalty (H := H) x y : EReal) := by
    have hmul_real : ξ * ‖y‖ < (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
      exact (lt_div_iff₀ hy_pos).1 hreal
    simpa [quadraticPenalty] using
      (show (((ξ * ‖y‖ : ℝ) : EReal)) <
          (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) from by
            exact_mod_cast hmul_real)
  exact (EReal.lt_div_iff (by exact_mod_cast hy_pos) (by simp)).2 hmul

end Inner

end Basic

section GammaZero

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal))

/-- ProximityOperator: a function in `Γ₀(H)` has a unique proximal point at every base point. -/
theorem hasUniqueProxPoint_of_mem_gammaZero (hf : f ∈ Γ₀(H)) :
    HasUniqueProxPoint f := by
  intro x
  have hsum_gamma : proximalObjectiveIoi (f := f) x ∈ Γ₀(H) :=
    proximalObjectiveIoi_mem_gammaZero_of_mem_gammaZero (f := f) hf x
  have hsum_super : Supercoercive (proximalObjectiveIoi (f := f) x).asEReal := by
    -- The proximal objective inherits supercoercivity from the quadratic term.
    simpa [proximalObjectiveIoi] using
      pointwiseAdd_supercoercive_of_mem_gammaZero
        f (quadraticPenalty (H := H) x) hf (quadraticPenalty_supercoercive (H := H) x)
  have hsum_coe : Coercive (proximalObjectiveIoi (f := f) x).asEReal :=
    coercive_of_supercoercive hsum_super
  have hsum_strict : StrictlyConvex (proximalObjectiveIoi (f := f) x) := by
    -- Strict convexity comes from adding the strictly convex quadratic regularizer.
    simpa [proximalObjectiveIoi] using
      hf.2.add_strictlyConvex_effectiveDomain (quadraticPenalty_strictlyConvex (H := H) x)
  have hargmin :
      ∃! p : H, p ∈ Argmin (proximalObjectiveIoi (f := f) x).asEReal :=
    existsUnique_mem_argmin_of_mem_gammaZero_of_coercive_of_strictlyConvex
      hsum_gamma hsum_coe hsum_strict
  -- Rewrite the unique argmin witness of the proximal objective as a unique proximal point.
  simpa [proximalPoints, proximalObjectiveIoi_asEReal (f := f) x] using hargmin

/-- Source-facing notation for the proximity operator of a `Γ₀(H)` function. -/
notation "Prox[" f ", " hf "]" =>
  proximityOperator f (hasUniqueProxPoint_of_mem_gammaZero f hf)

end GammaZero

end ERealFunction

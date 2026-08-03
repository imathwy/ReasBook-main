import Mathlib
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap05.Example_5_18
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap12.Proposition_12_28
import BauschkeLean.Chap12.ScaledProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section GammaZero

variable (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 30: multiplying an `EReal`-valued lower semicontinuous function by
a positive real preserves lower semicontinuity. -/
private theorem lowerSemicontinuous_coe_mul_of_pos_local {X : Type*} [TopologicalSpace X]
    {a : ℝ} (ha : 0 < a) {g : X → EReal} (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x ↦ (a : EReal) * g x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  have ha_nonneg : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha.le
  calc
    (a : EReal) * g x ≤ (a : EReal) * Filter.liminf g (nhds x) :=
      mul_le_mul_of_nonneg_left (hg.le_liminf x) ha_nonneg
    _ = Filter.liminf (fun y ↦ (a : EReal) * g y) (nhds x) := by
      symm
      exact EReal.liminf_const_mul_of_nonneg_of_ne_top ha_nonneg (EReal.coe_ne_top a)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 30: on the effective domain, the proximal objective is the
corresponding finite real-valued expression. -/
private theorem proximalObjective_eq_coe_toReal_add_quadratic
    (g : H → Set.Ioi (⊥ : EReal)) (x z : H) (hz : z ∈ effectiveDomain g) :
    proximalObjective g x z =
      (((g z : EReal).toReal + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal) := by
  have hz_top : (g z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz)
  have hz_bot : (g z : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (g z : EReal) from (g z).2)
  rw [proximalObjective, ← EReal.coe_toReal hz_top hz_bot, ← EReal.coe_add]
  simp

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 30: outside the effective domain, the proximal objective is `⊤`. -/
private theorem proximalObjective_eq_top_of_not_mem_effectiveDomain
    (g : H → Set.Ioi (⊥ : EReal)) (x z : H) (hz : z ∉ effectiveDomain g) :
    proximalObjective g x z = ⊤ := by
  have hz_top : (g z : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hz))
  rw [proximalObjective, hz_top, EReal.top_add_coe]

omit [CompleteSpace H] in
/-- Helper for Proposition 12 30: subtracting the left endpoint from a line-map point produces
the scaled chord. -/
private theorem lineMap_sub_eq_smul_sub (p y : H) (α : ℝ) :
    AffineMap.lineMap p y α - p = α • (y - p) := by
  simpa [vsub_eq_sub] using AffineMap.lineMap_vsub_left p y α

omit [CompleteSpace H] in
/-- Helper for Proposition 12 30: subtracting a point on the segment from `x` isolates the
residual `x - p` minus the scaled chord. -/
private theorem sub_lineMap_eq_sub_smul_sub (x p y : H) (α : ℝ) :
    x - AffineMap.lineMap p y α = (x - p) - α • (y - p) := by
  rw [sub_eq_add_neg, AffineMap.lineMap_apply_module', sub_eq_add_neg]
  abel_nf

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 30: positive scaling preserves the effective domain. -/
private theorem mem_effectiveDomain_posReal_smul_iff (x : H) :
    x ∈ effectiveDomain (γ • f) ↔ x ∈ effectiveDomain f := by
  rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, posReal_smul_apply,
    lt_top_iff_ne_top, lt_top_iff_ne_top]
  constructor
  · intro hmul htop
    have htop_mul :
        (((γ : ℝ) : EReal) * (⊤ : EReal)) = (⊤ : EReal) :=
      EReal.coe_mul_top_of_pos γ.2
    exact hmul (by simpa [htop] using htop_mul)
  · intro hf_top
    rw [EReal.mul_ne_top]
    exact
      ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
        Or.inl (EReal.coe_ne_top (γ : ℝ)), Or.inr hf_top⟩

/-- Helper for Proposition 12 30: `Prox[γ, f, hf] x` is a proximal point of `γ • f` at `x`. -/
private theorem scaledProximityOperator_isProxPoint
    (hf : f ∈ Γ₀(H)) (x : H) :
    IsProxPoint (γ • f) x (Prox[γ, f, hf] x) := by
  simpa [ERealFunction.scaledProximityOperator] using
    proximityOperator_isProxPoint
      (γ • f)
      (hasUniqueProxPoint_of_mem_gammaZero (γ • f) (smul_mem_gammaZero f hf γ))
      x

omit [CompleteSpace H] in
/-- Helper for Proposition 12 30: a proximal point of a `Γ₀(H)` function has finite value. -/
private theorem mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {x p : H} (hp : IsProxPoint g x p) :
    p ∈ effectiveDomain g := by
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp
  rcases hg.2.nonempty with ⟨q, hq⟩
  have hobj_q_ne_top : proximalObjective g x q ≠ ⊤ := by
    rw [proximalObjective_eq_coe_toReal_add_quadratic g x q hq]
    exact EReal.coe_ne_top _
  by_contra hp_dom
  have hobj_p_top : proximalObjective g x p = ⊤ :=
    proximalObjective_eq_top_of_not_mem_effectiveDomain g x p hp_dom
  have hpq : proximalObjective g x p ≤ proximalObjective g x q := hp q
  rw [hobj_p_top] at hpq
  exact hobj_q_ne_top (top_le_iff.mp hpq)

omit [CompleteSpace H] in
/-- Helper for Proposition 12 30: along a short segment from a proximal point toward an
effective-domain point, the textbook variational inequality holds up to a quadratic error. -/
private theorem inner_add_le_add_quadratic_error_of_isProxPoint
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {x p : H} (hp : IsProxPoint g x p)
    {y : H} (hy : y ∈ effectiveDomain g) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ⟪y - p, x - p⟫_ℝ + (g p : EReal).toReal ≤
      (g y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2 := by
  have hp_dom : p ∈ effectiveDomain g :=
    mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero (g := g) hg hp
  rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp
  let z : H := AffineMap.lineMap p y α
  have hz_eq : z = α • y + (1 - α) • p := by
    simpa [z, add_comm, add_left_comm, add_assoc] using (AffineMap.lineMap_apply_module p y α)
  have hz : z ∈ effectiveDomain g := by
    rw [hz_eq]
    exact hg.2.convex_effectiveDomain hy hp_dom hα0.le (sub_nonneg.mpr hα1.le) (by linarith)
  have hmin :
      (g p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
        (g z : EReal).toReal + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    have hpz : proximalObjective g x p ≤ proximalObjective g x z := hp z
    rw [proximalObjective_eq_coe_toReal_add_quadratic g x p hp_dom,
      proximalObjective_eq_coe_toReal_add_quadratic g x z hz] at hpz
    exact_mod_cast hpz
  have hconv_real :
      (g z : EReal).toReal ≤
        α * (g y : EReal).toReal + (1 - α) * (g p : EReal).toReal := by
    rw [hz_eq]
    exact hg.2.toReal_convexOn_effectiveDomain.2 hy hp_dom hα0.le (sub_nonneg.mpr hα1.le)
      (by linarith)
  have hstep :
      (g p : EReal).toReal + (1 / 2 : ℝ) * ‖x - p‖ ^ 2 ≤
        (α * (g y : EReal).toReal + (1 - α) * (g p : EReal).toReal) +
          (1 / 2 : ℝ) * ‖x - z‖ ^ 2 := by
    exact le_trans hmin (add_le_add hconv_real le_rfl)
  have hnorm :
      ‖x - z‖ ^ 2 =
        ‖x - p‖ ^ 2 - 2 * α * ⟪y - p, x - p⟫_ℝ + α ^ 2 * ‖y - p‖ ^ 2 := by
    simpa [z, sub_lineMap_eq_sub_smul_sub, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hα0.le, pow_two, mul_assoc, mul_left_comm, mul_comm,
      real_inner_comm] using
      (norm_sub_sq_real (x - p) (α • (y - p)))
  have hscaled :
      α * (⟪y - p, x - p⟫_ℝ + (g p : EReal).toReal) ≤
        α * (g y : EReal).toReal + (α ^ 2 / 2 : ℝ) * ‖y - p‖ ^ 2 := by
    nlinarith [hstep, hnorm]
  have hscaled' :
      α * (⟪y - p, x - p⟫_ℝ + (g p : EReal).toReal) ≤
        α * ((g y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2) := by
    have hfactor :
        α * ((g y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2) =
          α * (g y : EReal).toReal + (α ^ 2 / 2 : ℝ) * ‖y - p‖ ^ 2 := by
      ring
    rwa [hfactor]
  exact le_of_mul_le_mul_left hscaled' hα0

omit [CompleteSpace H] in
/-- Helper for Proposition 12 30: proximal points satisfy the finite variational inequality
against every finite comparison point. -/
private theorem inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero
    {g : H → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(H)) {x p y : H} (hp : IsProxPoint g x p)
    (hy : y ∈ effectiveDomain g) :
    ⟪y - p, x - p⟫_ℝ + (g p : EReal).toReal ≤ (g y : EReal).toReal := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let δ : ℝ := min 1 (2 * ε / (‖y - p‖ ^ 2 + 1))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    positivity
  rcases exists_nat_one_div_lt hδ_pos with ⟨n, hn⟩
  let α : ℝ := 1 / (n + 1 : ℝ)
  have hα0 : 0 < α := by
    dsimp [α]
    positivity
  have hα_lt_δ : α < δ := by
    simpa [α] using hn
  have hα1 : α < 1 := lt_of_lt_of_le hα_lt_δ (min_le_left _ _)
  have hαε : (α / 2 : ℝ) * ‖y - p‖ ^ 2 ≤ ε := by
    have hα_lt :
        α < 2 * ε / (‖y - p‖ ^ 2 + 1) := lt_of_lt_of_le hα_lt_δ (min_le_right _ _)
    have hden_pos : 0 < ‖y - p‖ ^ 2 + 1 := by
      positivity
    have hmain : α * (‖y - p‖ ^ 2 + 1) < 2 * ε := by
      exact (lt_div_iff₀ hden_pos).mp hα_lt
    have hle :
        α * ‖y - p‖ ^ 2 ≤ α * (‖y - p‖ ^ 2 + 1) := by
      nlinarith [show 0 ≤ α by exact le_of_lt hα0]
    have haux : α * ‖y - p‖ ^ 2 < 2 * ε := lt_of_le_of_lt hle hmain
    nlinarith
  have herr :=
    inner_add_le_add_quadratic_error_of_isProxPoint (g := g) hg hp hy hα0 hα1
  have hbound : (g y : EReal).toReal + (α / 2 : ℝ) * ‖y - p‖ ^ 2 ≤ (g y : EReal).toReal + ε := by
    nlinarith
  exact le_trans herr hbound

/-- Helper for Proposition 12 30: every scaled proximal point of a `Γ₀(H)` function has finite
`f`-value. -/
private theorem scaled_proximityOperator_mem_effectiveDomain_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (x : H) :
    Prox[γ, f, hf] x ∈ effectiveDomain f := by
  have hp_scaled : Prox[γ, f, hf] x ∈ effectiveDomain (γ • f) := by
    exact mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero
      (g := γ • f)
      (smul_mem_gammaZero f hf γ)
      (scaledProximityOperator_isProxPoint f γ hf x)
  exact (mem_effectiveDomain_posReal_smul_iff f γ (Prox[γ, f, hf] x)).1 hp_scaled

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 30: multiplying an indexed `EReal` infimum by a positive real can be
transported through the infimum. -/
private theorem coe_real_mul_iInf_ereal_of_pos_local
    {ι : Sort*} {a : ℝ} (ha : 0 < a) (φ : ι → EReal) :
    (a : EReal) * (⨅ i, φ i) = ⨅ i, (a : EReal) * φ i := by
  let F : EReal → EReal := fun t ↦ (a : EReal) * t
  have hcont_mul :
      ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) ((a : EReal), ⨅ i, φ i) := by
    refine EReal.continuousAt_mul ?_ ?_ ?_ ?_
    · left
      norm_num [ha.ne']
    · left
      norm_num [ha.ne']
    · left
      exact EReal.coe_ne_bot a
    · left
      exact EReal.coe_ne_top a
  have hcont : ContinuousAt F (⨅ i, φ i) := by
    simpa [F] using hcont_mul.comp (Continuous.prodMk_right (a : EReal)).continuousAt
  have hmono : Monotone F := by
    intro x y hxy
    exact mul_le_mul_of_nonneg_left hxy (EReal.coe_nonneg.mpr ha.le)
  have htop : F ⊤ = ⊤ := by
    simpa [F] using EReal.coe_mul_top_of_pos ha
  simpa [F, Function.comp] using
    (Monotone.map_iInf_of_continuousAt (ι := ι) (f := F) (g := φ) hcont hmono htop)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 30: scaling commutes with the Moreau envelope after adjusting the
parameter. -/
private theorem moreauEnvelope_smul_eq_smul_moreauEnvelope_local
    (μ : PosReal) :
    {}^[μ] (γ • f) = (γ : EReal) • {}^[(γ * μ)] f := by
  ext x
  have hγ_nonneg : (0 : EReal) ≤ (γ : EReal) := EReal.coe_nonneg.mpr γ.2.le
  have hγ_ne_top : (γ : EReal) ≠ ⊤ := EReal.coe_ne_top (γ : ℝ)
  rw [Pi.smul_apply, moreauEnvelope_apply, moreauEnvelope_apply]
  calc
    (⨅ y : H, ((γ • f) y : EReal) +
        ((((1 / (2 * (μ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal))) =
      ⨅ y : H, (γ : EReal) *
        ((f y : EReal) +
          ((((1 / (2 * (((γ * μ : PosReal) : ℝ)))) * ‖x - y‖ ^ 2 : ℝ) : EReal))) := by
        refine iInf_congr fun y ↦ ?_
        have hquadratic :
            ((((1 / (2 * (μ : ℝ))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) =
              (γ : EReal) *
                ((((1 / (2 * (((γ * μ : PosReal) : ℝ)))) * ‖x - y‖ ^ 2 : ℝ) : EReal)) := by
          rw [← EReal.coe_mul]
          congr 1
          calc
            (1 / (2 * (μ : ℝ))) * ‖x - y‖ ^ 2 =
                ((γ : ℝ) * (1 / (2 * (((γ * μ : PosReal) : ℝ))))) * ‖x - y‖ ^ 2 := by
                  rw [posReal_coe_mul]
                  field_simp [γ.2.ne', μ.2.ne']
            _ = (γ : ℝ) * ((1 / (2 * (((γ * μ : PosReal) : ℝ)))) * ‖x - y‖ ^ 2) := by
                  ring
        rw [posReal_smul_apply, hquadratic]
        symm
        rw [EReal.left_distrib_of_nonneg_of_ne_top hγ_nonneg hγ_ne_top]
    _ = (γ : EReal) *
          (⨅ y : H, (f y : EReal) +
            ((((1 / (2 * (((γ * μ : PosReal) : ℝ)))) * ‖x - y‖ ^ 2 : ℝ) : EReal))) := by
        symm
        exact coe_real_mul_iInf_ereal_of_pos_local (a := (γ : ℝ)) γ.2 _

/-- Helper for Proposition 12 30: the Moreau envelope can be written explicitly using the scaled
proximal point at the same base point. -/
private theorem moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (x : H) :
    ({}^[γ] f) x =
      (f (Prox[γ, f, hf] x) : EReal) +
        ((((‖x - Prox[γ, f, hf] x‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
  let p := Prox[γ, f, hf] x
  have hone : γ * (1 : PosReal) = γ := by
    ext
    simp
  have hscale := congrArg (fun g : H → EReal ↦ g x)
    (moreauEnvelope_smul_eq_smul_moreauEnvelope_local f γ (1 : PosReal))
  have hscale' : {}^[(1 : PosReal)] (γ • f) x = (γ : EReal) * ({}^[γ] f) x := by
    simpa [hone, smul_eq_mul] using hscale
  have hprox : IsProxPoint (γ • f) x p := by
    simpa [p] using scaledProximityOperator_isProxPoint f γ hf x
  have hunit := (isProxPoint_iff_moreauEnvelope_eq (γ • f) x p).mp hprox
  have hγ_pos_real : 0 < (γ : ℝ) := γ.2
  have hγ_pos : 0 < (γ : EReal) := by
    exact_mod_cast hγ_pos_real
  have hγ_ne_zero : (γ : EReal) ≠ 0 := ne_of_gt hγ_pos
  have hγ_ne_top : (γ : EReal) ≠ ⊤ := by
    simp
  have hscaled :
      (γ : EReal) * ({}^[γ] f) x =
        (γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
    calc
      (γ : EReal) * ({}^[γ] f) x = {}^[(1 : PosReal)] (γ • f) x := hscale'.symm
      _ = ((γ • f) p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := hunit
      _ = (γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
        simp [Pi.smul_apply]
  calc
    ({}^[γ] f) x = (γ : EReal) * (({}^[γ] f) x / (γ : EReal)) := by
      symm
      exact EReal.mul_div_cancel (show (γ : EReal) ≠ ⊥ by simp) hγ_ne_top hγ_ne_zero
    _ = ((γ : EReal) * ({}^[γ] f) x) / (γ : EReal) := by
      rw [EReal.mul_div]
    _ =
        ((γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal))) /
          (γ : EReal) := by
      rw [hscaled]
    _ =
        ((γ : EReal) * (f p : EReal)) / (γ : EReal) +
          ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) / (γ : EReal) := by
      rw [EReal.add_div_of_nonneg_right (le_of_lt hγ_pos)]
    _ = (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) / (γ : EReal) := by
      rw [← EReal.mul_div]
      rw [EReal.mul_div_cancel (show (γ : EReal) ≠ ⊥ by simp) hγ_ne_top hγ_ne_zero]
    _ = (f p : EReal) + ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      rw [← EReal.coe_div]
      ring_nf

/-- Helper for Proposition 12 30: the `γ`-Moreau envelope of a `Γ₀(H)` function takes finite
values everywhere. -/
private theorem moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) (x : H) :
    ({}^[γ] f) x ≠ ⊤ ∧ ({}^[γ] f) x ≠ ⊥ := by
  let p := Prox[γ, f, hf] x
  have hpdom : p ∈ effectiveDomain f := by
    simpa [p] using scaled_proximityOperator_mem_effectiveDomain_of_mem_gammaZero f γ hf x
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hpdom)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hmoreau :
      ({}^[γ] f) x =
        (f p : EReal) +
          ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
    simpa [p] using moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero f γ hf x
  constructor
  · rw [hmoreau]
    exact EReal.add_ne_top hfp_top (EReal.coe_ne_top _)
  · rw [hmoreau]
    exact (EReal.add_ne_bot_iff.2 ⟨hfp_bot, EReal.coe_ne_bot _⟩)

/-- Helper for Proposition 12 30: evaluating the Moreau-envelope infimum at `Prox_{γ f} x`
produces the quadratic upper tangent estimate centered at `x`. -/
private theorem moreauEnvelope_toReal_sub_le_residual_inner_add_quadratic
    (hf : f ∈ Γ₀(H)) (x y : H) :
    (({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal ≤
      ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), y - x⟫_ℝ +
        (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
  let p := Prox[γ, f, hf] x
  have hpdom : p ∈ effectiveDomain f := by
    simpa [p] using scaled_proximityOperator_mem_effectiveDomain_of_mem_gammaZero f γ hf x
  have hfp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hpdom)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have henvy_fin :
      ({}^[γ] f) y ≠ ⊤ ∧ ({}^[γ] f) y ≠ ⊥ :=
    moreauEnvelope_ne_top_ne_bot_of_mem_gammaZero f γ hf y
  have hmajor :
      ({}^[γ] f) y ≤
        (f p : EReal) +
          ((((1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 : ℝ) : EReal)) := by
    simpa [moreauEnvelope_apply, p] using
      (iInf_le
        (fun z : H ↦
          (f z : EReal) +
            ((((1 / (2 * (γ : ℝ))) * ‖y - z‖ ^ 2 : ℝ) : EReal)))
        p)
  have hmajor_real :
      (({}^[γ] f) y).toReal ≤
        (f p : EReal).toReal + (1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 := by
    have hsum_top :
        (f p : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 : ℝ) : EReal)) ≠ ⊤ := by
      exact EReal.add_ne_top hfp_top (EReal.coe_ne_top _)
    have hsum_real :
        ((f p : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 : ℝ) : EReal))).toReal =
          (f p : EReal).toReal + (1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 := by
      rw [EReal.toReal_add hfp_top hfp_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      rw [EReal.toReal_coe]
    calc
      (({}^[γ] f) y).toReal ≤
          ((f p : EReal) + ((((1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 : ℝ) : EReal))).toReal :=
        EReal.toReal_le_toReal hmajor henvy_fin.2 hsum_top
      _ = (f p : EReal).toReal + (1 / (2 * (γ : ℝ))) * ‖y - p‖ ^ 2 :=
        hsum_real
  have henvx :
      (({}^[γ] f) x).toReal =
        (f p : EReal).toReal + (1 / (2 * (γ : ℝ))) * ‖x - p‖ ^ 2 := by
    have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
    have hmoreau :
        ({}^[γ] f) x =
          (f p : EReal) +
            ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      simpa [p] using moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero f γ hf x
    rw [hmoreau, EReal.toReal_add hfp_top hfp_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    have hdiv :
        ‖x - p‖ ^ 2 / (2 * (γ : ℝ)) = (1 / (2 * (γ : ℝ))) * ‖x - p‖ ^ 2 := by
      field_simp [hγ_ne]
    rw [hdiv]
    rw [EReal.toReal_coe]
  have hsplit : y - p = (x - p) + (y - x) := by
    abel_nf
  have hnorm :
      ‖y - p‖ ^ 2 = ‖x - p‖ ^ 2 + 2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
    rw [hsplit, norm_add_sq_real]
  have hstep :
      (({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal ≤
        (1 / (2 * (γ : ℝ))) *
          (2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2) := by
    have hstep' :
        (({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal ≤
          (1 / (2 * (γ : ℝ))) * (‖y - p‖ ^ 2 - ‖x - p‖ ^ 2) := by
      linarith [hmajor_real, henvx]
    have hnorm' :
        ‖y - p‖ ^ 2 - ‖x - p‖ ^ 2 = 2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
      linarith [hnorm]
    simpa [hnorm'] using hstep'
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  have hcoeff :
      (1 / (2 * (γ : ℝ))) * (2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2) =
        ⟪(γ : ℝ)⁻¹ • (x - p), y - x⟫_ℝ +
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
    rw [real_inner_smul_left]
    field_simp [hγ_ne]
  calc
    (({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal ≤
        (1 / (2 * (γ : ℝ))) * (2 * ⟪x - p, y - x⟫_ℝ + ‖y - x‖ ^ 2) :=
      hstep
    _ =
        ⟪(γ : ℝ)⁻¹ • (x - p), y - x⟫_ℝ +
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 :=
      hcoeff

/-- Helper for Proposition 12 30: swapping the quadratic majorization estimate yields the
corresponding lower tangent estimate involving the residual at `y`. -/
private theorem residual_inner_sub_le_moreauEnvelope_toReal_sub_add_quadratic
    (hf : f ∈ Γ₀(H)) (x y : H) :
    ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, f, hf] y), y - x⟫_ℝ -
        (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 ≤
      (({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal := by
  have hswap :
      (({}^[γ] f) x).toReal - (({}^[γ] f) y).toReal ≤
        ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, f, hf] y), x - y⟫_ℝ +
          (1 / (2 * (γ : ℝ))) * ‖x - y‖ ^ 2 :=
    moreauEnvelope_toReal_sub_le_residual_inner_add_quadratic f γ hf y x
  have hsub : x - y = -(y - x) := by
    abel_nf
  have hinner :
      ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, f, hf] y), x - y⟫_ℝ =
        -⟪(γ : ℝ)⁻¹ • (y - Prox[γ, f, hf] y), y - x⟫_ℝ := by
    rw [hsub, inner_neg_right]
  have hswap' :
      (({}^[γ] f) x).toReal - (({}^[γ] f) y).toReal ≤
        -⟪(γ : ℝ)⁻¹ • (y - Prox[γ, f, hf] y), y - x⟫_ℝ +
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
    simpa [hinner, norm_sub_rev] using hswap
  nlinarith [hswap']

/-- Helper for Proposition 12 30: the scaled proximity operator is firmly nonexpansive. -/
private theorem scaled_proximityOperator_firmlyNonexpansive_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) :
    FirmlyNonexpansive (fun x : H ↦ Prox[γ, f, hf] x) := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  let p := Prox[γ, f, hf] x
  let q := Prox[γ, f, hf] y
  have hp : IsProxPoint (γ • f) x p := by
    simpa [p] using scaledProximityOperator_isProxPoint f γ hf x
  have hq : IsProxPoint (γ • f) y q := by
    simpa [q] using scaledProximityOperator_isProxPoint f γ hf y
  have hp_dom : p ∈ effectiveDomain (γ • f) :=
    mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero
      (g := γ • f) (smul_mem_gammaZero f hf γ) hp
  have hq_dom : q ∈ effectiveDomain (γ • f) :=
    mem_effectiveDomain_of_isProxPoint_of_mem_gammaZero
      (g := γ • f) (smul_mem_gammaZero f hf γ) hq
  have hpq :
      ⟪q - p, x - p⟫_ℝ + ((γ • f) p : EReal).toReal ≤ ((γ • f) q : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero
      (g := γ • f) (smul_mem_gammaZero f hf γ) hp hq_dom
  have hqp :
      ⟪p - q, y - q⟫_ℝ + ((γ • f) q : EReal).toReal ≤ ((γ • f) p : EReal).toReal :=
    inner_add_toReal_le_toReal_of_isProxPoint_of_mem_gammaZero
      (g := γ • f) (smul_mem_gammaZero f hf γ) hq hp_dom
  have hsum : ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    linarith
  let d : H := p - q
  have hsub : y - q - (x - p) = d - (x - y) := by
    dsimp [d]
    abel_nf
  have hqpd : q - p = -d := by
    dsimp [d]
    abel_nf
  have hrewrite :
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ =
        ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by
    calc
      ⟪q - p, x - p⟫_ℝ + ⟪p - q, y - q⟫_ℝ
          = inner ℝ (-d) (x - p) + inner ℝ d (y - q) := by
              rw [hqpd]
      _ = -inner ℝ d (x - p) + inner ℝ d (y - q) := by simp
      _ = inner ℝ d (y - q) - inner ℝ d (x - p) := by ring_nf
      _ = inner ℝ d ((y - q) - (x - p)) := by
            symm
            rw [inner_sub_right]
      _ = inner ℝ d (d - (x - y)) := by rw [hsub]
      _ = inner ℝ d d - inner ℝ d (x - y) := by rw [inner_sub_right]
      _ = ‖d‖ ^ (2 : ℕ) - inner ℝ d (x - y) := by rw [real_inner_self_eq_norm_sq]
  rw [hrewrite] at hsum
  have hfinal : ‖d‖ ^ (2 : ℕ) ≤ inner ℝ d (x - y) := by
    linarith
  simpa [d] using hfinal

/-- Helper for Proposition 12 30: the scaled residual map `Id - Prox_{γ f}` is firmly
nonexpansive. -/
private theorem scaled_residual_firmlyNonexpansive_of_mem_gammaZero
    (hf : f ∈ Γ₀(H)) :
    FirmlyNonexpansive (fun x : H ↦ x - Prox[γ, f, hf] x) := by
  have hfirm :
      FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ Prox[γ, f, hf] x) := by
    simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using
      scaled_proximityOperator_firmlyNonexpansive_of_mem_gammaZero f γ hf
  rw [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ]
  simpa [residualMap] using
    (firmlyNonexpansiveOn_residualMap_iff
      (Set.univ : Set H) (fun x : Set.univ ↦ Prox[γ, f, hf] x)).2 hfirm

/-- Helper for Proposition 12 30: firm nonexpansiveness of the residual map makes the residual
cross term monotone in the source displacement. -/
private theorem scaled_residual_inner_nonneg
    (hf : f ∈ Γ₀(H)) (x y : H) :
    0 ≤ ⟪(y - Prox[γ, f, hf] y) - (x - Prox[γ, f, hf] x), y - x⟫_ℝ := by
  have hfirm :
      FirmlyNonexpansive (fun z : H ↦ z - Prox[γ, f, hf] z) :=
    scaled_residual_firmlyNonexpansive_of_mem_gammaZero f γ hf
  have hineq :
      ‖((y - Prox[γ, f, hf] y) - (x - Prox[γ, f, hf] x))‖ ^ 2 ≤
        ⟪(y - Prox[γ, f, hf] y) - (x - Prox[γ, f, hf] x), y - x⟫_ℝ := by
    simpa using (firmlyNonexpansive_iff_norm_sq_le_inner.mp hfirm) y x
  exact le_trans (sq_nonneg _) hineq

/-- Helper for Proposition 12 30: after scaling by `γ⁻¹`, residual monotonicity compares the
linear terms at two base points in the source proof. -/
private theorem scaled_residual_inner_mono
    (hf : f ∈ Γ₀(H)) (x y : H) :
    ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), y - x⟫_ℝ ≤
      ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, f, hf] y), y - x⟫_ℝ := by
  -- Scale the residual monotonicity inequality from Proposition 12.28 by the positive factor
  -- `γ⁻¹` so the linear term matches the envelope tangent estimate.
  have hres :
      0 ≤ ⟪(y - Prox[γ, f, hf] y) - (x - Prox[γ, f, hf] x), y - x⟫_ℝ :=
    scaled_residual_inner_nonneg f γ hf x y
  have hbase :
      0 ≤
        ⟪y - Prox[γ, f, hf] y, y - x⟫_ℝ -
          ⟪x - Prox[γ, f, hf] x, y - x⟫_ℝ := by
    simpa [inner_sub_left] using hres
  have hscaled :
      0 ≤
        (γ : ℝ)⁻¹ *
          (⟪y - Prox[γ, f, hf] y, y - x⟫_ℝ -
            ⟪x - Prox[γ, f, hf] x, y - x⟫_ℝ) := by
    exact mul_nonneg (inv_nonneg.mpr γ.2.le) hbase
  have hdiff :
      0 ≤
        ⟪(γ : ℝ)⁻¹ • (y - Prox[γ, f, hf] y), y - x⟫_ℝ -
          ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), y - x⟫_ℝ := by
    rw [real_inner_smul_left, real_inner_smul_left]
    simpa [mul_sub] using hscaled
  linarith

/-- Helper for Proposition 12 30: the Moreau envelope remainder after subtracting the linear
term at `x` is bounded by a quadratic error. -/
private theorem moreauEnvelope_toReal_remainder_bound
    (hf : f ∈ Γ₀(H)) (x h : H) :
    |(({}^[γ] f) (x + h)).toReal - (({}^[γ] f) x).toReal -
        ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), h⟫_ℝ| ≤
      (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 := by
  let g := (γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x)
  let delta := (({}^[γ] f) (x + h)).toReal - (({}^[γ] f) x).toReal
  have hupper :
      delta ≤ ⟪g, h⟫_ℝ + (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 := by
    simpa [g, delta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      moreauEnvelope_toReal_sub_le_residual_inner_add_quadratic f γ hf x (x + h)
  have hlower_y :
      ⟪(γ : ℝ)⁻¹ • ((x + h) - Prox[γ, f, hf] (x + h)), h⟫_ℝ -
          (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 ≤
        delta := by
    simpa [delta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      residual_inner_sub_le_moreauEnvelope_toReal_sub_add_quadratic f γ hf x (x + h)
  have hmono :
      ⟪g, h⟫_ℝ ≤ ⟪(γ : ℝ)⁻¹ • ((x + h) - Prox[γ, f, hf] (x + h)), h⟫_ℝ := by
    -- Reuse the scaled residual monotonicity bridge to keep the remainder proof flat.
    simpa [g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      scaled_residual_inner_mono f γ hf x (x + h)
  have hlower :
      ⟪g, h⟫_ℝ - (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 ≤ delta := by
    exact le_trans (sub_le_sub_right hmono _) hlower_y
  have hquad_nonneg : 0 ≤ (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 := by
    have hcoeff_nonneg : 0 ≤ 1 / (2 * (γ : ℝ)) := by
      have hden_nonneg : 0 ≤ 2 * (γ : ℝ) := by
        nlinarith [γ.2]
      exact one_div_nonneg.mpr hden_nonneg
    exact mul_nonneg hcoeff_nonneg (sq_nonneg ‖h‖)
  have habs :
      |delta - ⟪g, h⟫_ℝ| ≤ (1 / (2 * (γ : ℝ))) * ‖h‖ ^ 2 := by
    refine abs_le.mpr ?_
    constructor
    · nlinarith [hlower, hquad_nonneg]
    · nlinarith [hupper, hquad_nonneg]
  simpa [g, delta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using habs

-- Proof sketch: combine the pointwise envelope identity from Proposition 12.26 with the firm
-- nonexpansiveness of the residual map from Proposition 12.28 to identify the first-order term
-- with `γ⁻¹ • (x - Prox_{γ f} x)`.
/-- Proposition 12 30: for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, the `γ`-Moreau envelope, viewed as the
real-valued function `x ↦ ({}^γ f x).toReal`, is Fréchet differentiable at every point with
gradient `γ⁻¹ • (x - Prox_{γ f} x)`. -/
theorem moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    (x : H) :
    HasGradientAt (fun y : H ↦ (({}^[γ] f) y).toReal)
      ((γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x)) x := by
  rw [hasGradientAt_iff_tendsto]
  have hbound :
      ∀ y : H,
        ‖y - x‖⁻¹ *
            ‖(({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal -
                ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), y - x⟫_ℝ‖ ≤
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ := by
    intro y
    have hyx :
        x + (y - x) = y := by
      abel_nf
    have hrem :
        |(({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal -
            ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), y - x⟫_ℝ| ≤
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
      simpa [hyx, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        moreauEnvelope_toReal_remainder_bound f γ hf x (y - x)
    have hrem_norm :
        ‖(({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal -
            ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), y - x⟫_ℝ‖ ≤
          (1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2 := by
      simpa [Real.norm_eq_abs] using hrem
    by_cases hy : y = x
    · simp [hy]
    · have hnorm_ne : ‖y - x‖ ≠ 0 := by
        exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)
      have hmul :
          ‖y - x‖⁻¹ *
              ‖(({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal -
                  ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), y - x⟫_ℝ‖ ≤
            ‖y - x‖⁻¹ * ((1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hrem_norm (inv_nonneg.mpr (norm_nonneg _))
      calc
        ‖y - x‖⁻¹ *
            ‖(({}^[γ] f) y).toReal - (({}^[γ] f) x).toReal -
                ⟪(γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x), y - x⟫_ℝ‖ ≤
            ‖y - x‖⁻¹ * ((1 / (2 * (γ : ℝ))) * ‖y - x‖ ^ 2) :=
          hmul
        _ = (1 / (2 * (γ : ℝ))) * ‖y - x‖ := by
          rw [pow_two]
          calc
            ‖y - x‖⁻¹ * ((1 / (2 * (γ : ℝ))) * (‖y - x‖ * ‖y - x‖)) =
                (1 / (2 * (γ : ℝ))) * (‖y - x‖⁻¹ * ‖y - x‖) * ‖y - x‖ := by
                  ring
            _ = (1 / (2 * (γ : ℝ))) * 1 * ‖y - x‖ := by
                  rw [inv_mul_cancel₀ hnorm_ne]
            _ = (1 / (2 * (γ : ℝ))) * ‖y - x‖ := by
                  ring
  have hnorm :
      Filter.Tendsto (fun y : H ↦ ‖y - x‖) (nhds x) (nhds (0 : ℝ)) := by
    have hcont : Continuous fun y : H ↦ ‖y - x‖ := by
      exact continuous_norm.comp
        (continuous_id.sub (continuous_const : Continuous fun _ : H ↦ x))
    simpa using
      (show Filter.Tendsto (fun y : H ↦ ‖y - x‖) (nhds x) (nhds (‖x - x‖)) from
        (hcont.continuousAt : ContinuousAt (fun y : H ↦ ‖y - x‖) x))
  have hupper :
      Filter.Tendsto (fun y : H ↦ (1 / (2 * (γ : ℝ))) * ‖y - x‖)
        (nhds x) (nhds (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hnorm)
  exact squeeze_zero
    (fun y ↦ mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    hbound
    hupper

-- Proof sketch: apply `gradient_eq` to the pointwise gradient formula from
-- `moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero`.
/-- The gradient of the real-valued `γ`-Moreau envelope is the scaled residual
`γ⁻¹ • (Id - Prox_{γ f})`. -/
theorem gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    :
    ∇ (fun y : H ↦ (({}^[γ] f) y).toReal) =
      fun x ↦ (γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x) :=
  gradient_eq <| moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero f γ hf

-- Proof sketch: Proposition 12.28 makes the residual map `Id - Prox_{γ f}` firmly nonexpansive;
-- invoke the existing owner lemma `lipschitzWith_one_of_firmlyNonexpansive` and then scale by
-- `γ⁻¹`, using the gradient formula above to rewrite the result.
/-- The gradient field of the real-valued `γ`-Moreau envelope is `γ⁻¹`-Lipschitz. -/
theorem lipschitzWith_inv_of_gradient_moreauEnvelope_toReal_of_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    :
    LipschitzWith (Real.toNNReal ((γ : ℝ)⁻¹))
      (∇ (fun y : H ↦ (({}^[γ] f) y).toReal)) := by
  rw [gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero
    f γ hf]
  have hres :
      LipschitzWith 1 (fun x : H ↦ x - Prox[γ, f, hf] x) := by
    exact lipschitzWith_one_of_firmlyNonexpansive <|
      scaled_residual_firmlyNonexpansive_of_mem_gammaZero f γ hf
  have hscaled :
      LipschitzWith (‖(γ : ℝ)⁻¹‖₊ * 1)
        (fun x : H ↦ (γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x)) :=
    (lipschitzWith_smul ((γ : ℝ)⁻¹)).comp hres
  simpa [Real.toNNReal_eq_nnnorm_of_nonneg (inv_nonneg.mpr γ.2.le)] using hscaled

end GammaZero

end ERealFunction

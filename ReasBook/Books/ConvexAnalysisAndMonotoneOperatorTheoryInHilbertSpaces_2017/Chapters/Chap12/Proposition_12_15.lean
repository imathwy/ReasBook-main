import Mathlib
import BauschkeLean.Chap08.Corollary_8_39
import BauschkeLean.Chap08.Example_8_23
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Corollary_11_9
import BauschkeLean.Chap11.Corollary_11_16
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Proposition_12_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section HilbertSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 15: infimal convolution is commutative on additive commutative
groups. -/
theorem infimalConvolution_comm (g h : H → EReal) :
    g □ h = h □ g := by
  ext x
  rw [infimalConvolution_apply, infimalConvolution_apply]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun y ↦ ?_
    simpa [sub_sub_cancel, add_comm] using
      (iInf_le (fun z : H ↦ g z + h (x - z)) (x - y))
  · refine le_iInf fun y ↦ ?_
    simpa [sub_sub_cancel, add_comm] using
      (iInf_le (fun z : H ↦ h z + g (x - z)) (x - y))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 15: exactness of infimal convolution is symmetric at a fixed
point. -/
lemma exactAt_symm_of_exactAt
    {g h : H → Set.Ioi (⊥ : EReal)} {x : H} :
    infimalConvolution.ExactAt g h x →
      infimalConvolution.ExactAt h g x := by
  rintro ⟨y, hy⟩
  refine ⟨x - y, ?_⟩
  simpa [infimalConvolution_comm, sub_sub_cancel, add_comm] using hy

/-- Helper for Proposition 12 15: the `p`-power norm kernel as an `]-∞,+∞]`-valued function. -/
noncomputable def normPowerKernel (p : Set.Ici (1 : ℝ)) (γ : PosReal) :
    H → Set.Ioi (⊥ : EReal) :=
  (fun x : H ↦ ‖x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ))).toEReal

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 15: coercing the `p`-power norm kernel to `EReal` recovers the
usual formula. -/
@[simp] theorem normPowerKernel_apply (p : Set.Ici (1 : ℝ)) (γ : PosReal) (x : H) :
    (normPowerKernel (H := H) p γ x : EReal) =
      (((‖x‖ ^ (p : ℝ) / ((γ : ℝ) * (p : ℝ)) : ℝ) : EReal)) := by
  simp [normPowerKernel]

/-- Helper for Proposition 12 15: the `p`-power envelope is the infimal convolution with the
`p`-power kernel. -/
noncomputable def normPowerEnvelope
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ)) (γ : PosReal) :
    H → EReal :=
  f □ normPowerKernel (H := H) p γ

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 15: the value of the `p`-power envelope is the defining infimum
over translated penalties. -/
theorem normPowerEnvelope_apply
    (f : H → Set.Ioi (⊥ : EReal)) (p : Set.Ici (1 : ℝ)) (γ : PosReal) (x : H) :
    normPowerEnvelope (H := H) f p γ x =
      ⨅ y : H, (f y : EReal) + (normPowerKernel (H := H) p γ (x - y) : EReal) := by
  simp [normPowerEnvelope, infimalConvolution_apply]

omit [CompleteSpace H] in
/-- Helper for Proposition 12 15: a continuous convex real-valued function on all of `H`
packages canonically as a member of `Γ₀(H)`. -/
lemma real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
    (φ : H → ℝ) (hcont : Continuous φ) (hconv : _root_.ConvexOn ℝ Set.univ φ) :
    φ.toEReal ∈ Γ₀(H) := by
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
          hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by ring)
      have hcast :
          (((φ (a • x + (1 - a) • y) : ℝ) : EReal)) ≤
            (((a * φ x + (1 - a) * φ y : ℝ) : EReal)) := by
        exact_mod_cast hreal
      simpa [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add] using hcast

omit [CompleteSpace H] in
/-- Helper for Proposition 12 15: the `p`-power kernel belongs to `Γ₀(H)`. -/
lemma normPowerKernel_mem_gammaZero
    (p : Set.Ici (1 : ℝ)) (γ : PosReal) (hp : (1 : ℝ) < p) :
    normPowerKernel (H := H) p γ ∈ Γ₀(H) := by
  let c : ℝ := 1 / ((γ : ℝ) * (p : ℝ))
  have hc_pos : 0 < c := by
    have hden_pos : 0 < (γ : ℝ) * (p : ℝ) := by
      exact mul_pos γ.2 (lt_trans zero_lt_one hp)
    exact one_div_pos.mpr hden_pos
  have hcont :
      Continuous (fun x : H ↦ c * ‖x‖ ^ (p : ℝ)) := by
    have hpow :
        Continuous (fun x : H ↦ ‖x‖ ^ (p : ℝ)) := by
      exact continuous_norm.rpow_const fun _ ↦ Or.inr (le_trans zero_le_one hp.le)
    exact continuous_const.mul hpow
  have hconv :
      _root_.ConvexOn ℝ Set.univ (fun x : H ↦ c * ‖x‖ ^ (p : ℝ)) := by
    have hbase :
        _root_.ConvexOn ℝ Set.univ (fun x : H ↦ ‖x‖ ^ (p : ℝ)) :=
      (strictConvexOn_norm_rpow (H := H) (p := (p : ℝ)) hp).convexOn
    have hc_nonneg : 0 ≤ c := hc_pos.le
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hineq :
        ‖a • x + b • y‖ ^ (p : ℝ) ≤ a * ‖x‖ ^ (p : ℝ) + b * ‖y‖ ^ (p : ℝ) := by
      exact hbase.2 (by simp) (by simp) ha hb hab
    simpa [c, mul_add, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hineq hc_nonneg
  simpa [normPowerKernel, c, Function.toEReal_apply, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using
    real_toEReal_mem_gammaZero_of_continuous_convexOn_univ
      (H := H) (fun x : H ↦ c * ‖x‖ ^ (p : ℝ)) hcont hconv

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 12 15: the `p`-power kernel is supercoercive when `p > 1`. -/
lemma supercoercive_normPowerKernel
    (p : Set.Ici (1 : ℝ)) (γ : PosReal) (hp : (1 : ℝ) < p) :
    Supercoercive (normPowerKernel (H := H) p γ).asEReal := by
  let c : ℝ := 1 / ((γ : ℝ) * (p : ℝ))
  have hc_pos : 0 < c := by
    have hden_pos : 0 < (γ : ℝ) * (p : ℝ) := by
      exact mul_pos γ.2 (lt_trans zero_lt_one hp)
    exact one_div_pos.mpr hden_pos
  have hp_sub_pos : 0 < (p : ℝ) - 1 := by
    linarith
  rw [supercoercive_iff_tendsto_norm_atTop, EReal.tendsto_nhds_top_iff_real]
  intro ξ
  have hnorm :
      ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop, (1 : ℝ) ≤ ‖x‖ := by
    exact
      (Filter.tendsto_comap :
        Filter.Tendsto (fun x : H ↦ ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop).eventually_ge_atTop 1
  have htail :
      Filter.Tendsto (fun x : H ↦ c * ‖x‖ ^ ((p : ℝ) - 1))
        (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop := by
    have hbase :
        Filter.Tendsto (fun t : ℝ ↦ c * t ^ ((p : ℝ) - 1))
          Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.const_mul_atTop hc_pos (tendsto_rpow_atTop hp_sub_pos)
    exact hbase.comp
      (Filter.tendsto_comap :
        Filter.Tendsto (fun x : H ↦ ‖x‖)
          (Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop) Filter.atTop)
  have hlarge :
      ∀ᶠ x : H in Filter.comap (fun x : H ↦ ‖x‖) Filter.atTop,
        max ξ 0 + 1 ≤ c * ‖x‖ ^ ((p : ℝ) - 1) := by
    exact Filter.tendsto_atTop.mp htail (max ξ 0 + 1)
  filter_upwards [hnorm, hlarge] with x hxnorm hxlarge
  have hnorm_pos_real : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hxnorm
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact_mod_cast hnorm_pos_real
  have hξ_lt : ξ < c * ‖x‖ ^ ((p : ℝ) - 1) := by
    exact lt_of_lt_of_le
      (lt_of_le_of_lt (le_max_left ξ 0) (lt_add_one (max ξ 0)))
      hxlarge
  have hmul_real : ξ * ‖x‖ < c * ‖x‖ ^ (p : ℝ) := by
    have hmul :
        ξ * ‖x‖ < (c * ‖x‖ ^ ((p : ℝ) - 1)) * ‖x‖ :=
      mul_lt_mul_of_pos_right hξ_lt hnorm_pos_real
    calc
      ξ * ‖x‖ < (c * ‖x‖ ^ ((p : ℝ) - 1)) * ‖x‖ := hmul
      _ = c * ‖x‖ ^ (p : ℝ) := by
        rw [mul_assoc]
        congr 1
        calc
          ‖x‖ ^ ((p : ℝ) - 1) * ‖x‖ = ‖x‖ ^ ((p : ℝ) - 1) * ‖x‖ ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = ‖x‖ ^ (((p : ℝ) - 1) + 1) := by
            rw [← Real.rpow_add hnorm_pos_real ((p : ℝ) - 1) 1]
          _ = ‖x‖ ^ (p : ℝ) := by
            ring_nf
  have hmul :
      (ξ : EReal) * ‖x‖ < (normPowerKernel (H := H) p γ x : EReal) := by
    simpa [c, normPowerKernel_apply, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (show (((ξ * ‖x‖ : ℝ) : EReal)) <
          (((c * ‖x‖ ^ (p : ℝ) : ℝ) : EReal)) by
        exact_mod_cast hmul_real)
  exact (EReal.lt_div_iff hnorm_pos (by simp)).2 hmul

omit [CompleteSpace H] in
/-- Helper for Proposition 12 15: strict convexity on `Set.univ` survives the everywhere-finite
`toEReal` coercion. -/
lemma strictlyConvex_toEReal_of_strictConvexOn_univ
    {φ : H → ℝ} (hφ : _root_.StrictConvexOn ℝ Set.univ φ) :
    StrictlyConvex φ.toEReal := by
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

omit [CompleteSpace H] in
/-- Helper for Proposition 12 15: translating a `Γ₀(H)` function by `y ↦ x - y` preserves
membership in `Γ₀(H)`. -/
lemma sub_right_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    (fun y : H ↦ f (x - y)) ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff]
  constructor
  · have hsub : Continuous fun y : H ↦ x - y := continuous_const.sub continuous_id
    simpa using hf.1.comp hsub
  · refine ⟨?_, subset_rfl, ?_⟩
    · rcases hf.2.nonempty with ⟨z, hz⟩
      refine ⟨x - z, ?_⟩
      simpa [mem_effectiveDomain_iff] using hz
    · intro y₁ hy₁ y₂ hy₂ a ha0 ha1
      have hy₁' : x - y₁ ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff] using hy₁
      have hy₂' : x - y₂ ∈ effectiveDomain f := by
        simpa [mem_effectiveDomain_iff] using hy₂
      have hcombo :
          a • (x - y₁) + (1 - a) • (x - y₂) = x - (a • y₁ + (1 - a) • y₂) := by
        have hxsplit : a • x + (1 - a) • x = x := by
          calc
            a • x + (1 - a) • x = (a + (1 - a)) • x := by
              rw [← add_smul]
            _ = (1 : ℝ) • x := by
              ring_nf
            _ = x := by
              simp
        calc
          a • (x - y₁) + (1 - a) • (x - y₂)
              = a • x + (1 - a) • x - (a • y₁ + (1 - a) • y₂) := by
                  rw [smul_sub, smul_sub]
                  abel
          _ = x - (a • y₁ + (1 - a) • y₂) := by
                rw [hxsplit]
      simpa [hcombo] using
        hf.2.ineq hy₁' hy₂' ha0 ha1

omit [CompleteSpace H] in
/-- Helper for Proposition 12 15: the `p`-power envelope is finite above at every point. -/
lemma mem_dom_normPowerEnvelope_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))
    (hf : f ∈ Γ₀(H)) (x : H) :
    x ∈ dom (normPowerEnvelope (H := H) f p γ) := by
  rcases hf.2.nonempty with ⟨y, hy⟩
  rw [mem_dom_iff]
  calc
    normPowerEnvelope (H := H) f p γ x ≤
        (f y : EReal) + (normPowerKernel (H := H) p γ (x - y) : EReal) := by
          rw [normPowerEnvelope_apply]
          exact iInf_le _ y
    _ < ⊤ := by
      exact EReal.add_lt_top
        (ne_of_lt (mem_effectiveDomain_iff.mp hy))
        (EReal.coe_ne_top _)

omit [CompleteSpace H] in
/-- Helper for Proposition 12 15: the `p`-power envelope has full domain. -/
lemma dom_normPowerEnvelope_eq_univ_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))
    (hf : f ∈ Γ₀(H)) :
    dom (normPowerEnvelope (H := H) f p γ) = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    exact mem_dom_normPowerEnvelope_of_mem_gammaZero (H := H) f γ p hf x

/-- Helper for Proposition 12 15: lower semicontinuity identifies the continuity points of a
convex bundled function with the interior of its effective domain. -/
lemma continuous_points_eq_interior_effectiveDomain_of_lowerSemicontinuous
    (g : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) :
    {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain g ∧
      ContinuousAt (fun y : H ↦ (g y : EReal).toReal) x} = interior (effectiveDomain g) := by
  exact
    continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
      g
      hg.2
      (Or.inr (Or.inl hg.1))

/-- Helper for Proposition 12 15: Proposition 12.14 makes the `p`-power envelope exact on its
full domain. -/
lemma exactAt_normPowerEnvelope_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) (x : H) :
    infimalConvolution.ExactAt f (normPowerKernel (H := H) p γ) x := by
  have hexact : infimalConvolution.Exact (normPowerKernel (H := H) p γ) f := by
    have hkernel : normPowerKernel (H := H) p γ ∈ Γ₀(H) :=
      normPowerKernel_mem_gammaZero (H := H) p γ hp
    exact
      infimalConvolution_exact_of_supercoercive_or_coercive_bddBelow
        (H := H)
        (f := normPowerKernel (H := H) p γ)
        (g := f)
        (hf := hkernel)
        (hg := hf)
        (hcase := Or.inl (supercoercive_normPowerKernel (H := H) p γ hp))
  have hdom : dom (normPowerEnvelope f p γ) = Set.univ :=
    dom_normPowerEnvelope_eq_univ_of_mem_gammaZero f γ p hf
  have hxdom : x ∈ dom (normPowerKernel (H := H) p γ □ f) := by
    simpa [normPowerEnvelope, infimalConvolution_comm] using
      mem_dom_normPowerEnvelope_of_mem_gammaZero f γ p hf x
  exact exactAt_symm_of_exactAt (hexact (x := x) hxdom)

/-- Helper for Proposition 12 15: exactness rules out the value `-∞` for the `p`-power
envelope. -/
lemma normPowerEnvelope_ne_bot_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) (x : H) :
    normPowerEnvelope f p γ x ≠ ⊥ := by
  rcases exactAt_normPowerEnvelope_of_mem_gammaZero (H := H) f γ p hf hp x with ⟨y, hy⟩
  rw [normPowerEnvelope, hy]
  exact (EReal.add_ne_bot_iff).2 ⟨ne_of_gt (f y).2, EReal.coe_ne_bot _⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 12 15: translating the `p`-power kernel preserves strict convexity. -/
lemma strictlyConvex_translated_normPowerKernel
    (p : Set.Ici (1 : ℝ)) (γ : PosReal) (hp : (1 : ℝ) < p) (x : H) :
    StrictlyConvex (fun z : H ↦ normPowerKernel (H := H) p γ (x - z)) := by
  let c : ℝ := 1 / ((γ : ℝ) * (p : ℝ))
  have hc_pos : 0 < c := by
    have hden_pos : 0 < (γ : ℝ) * (p : ℝ) := by
      exact mul_pos γ.2 (lt_trans zero_lt_one hp)
    exact one_div_pos.mpr hden_pos
  have hbase' :
      _root_.StrictConvexOn ℝ Set.univ (((fun z : H ↦ ‖z‖ ^ (p : ℝ))) ∘ fun z : H ↦ z - x) := by
    simpa [Function.comp, sub_eq_add_neg, add_comm] using
      (strictConvexOn_norm_rpow (H := H) (p := (p : ℝ)) hp).translate_right (-x)
  have hbase :
      _root_.StrictConvexOn ℝ Set.univ (fun z : H ↦ ‖x - z‖ ^ (p : ℝ)) := by
    convert hbase' using 1
    ext z
    simp [Function.comp, norm_sub_rev]
  have hscaled :
      _root_.StrictConvexOn ℝ Set.univ (fun z : H ↦ c * ‖x - z‖ ^ (p : ℝ)) := by
    refine ⟨hbase.1, ?_⟩
    intro z₁ _ z₂ _ hz a b ha hb hab
    have hineq :
        ‖x - (a • z₁ + b • z₂)‖ ^ (p : ℝ) <
          a * ‖x - z₁‖ ^ (p : ℝ) + b * ‖x - z₂‖ ^ (p : ℝ) :=
      hbase.2 (by simp) (by simp) hz ha hb hab
    calc
      c * ‖x - (a • z₁ + b • z₂)‖ ^ (p : ℝ)
          < c * (a * ‖x - z₁‖ ^ (p : ℝ) + b * ‖x - z₂‖ ^ (p : ℝ)) := by
              exact mul_lt_mul_of_pos_left hineq hc_pos
      _ = a * (c * ‖x - z₁‖ ^ (p : ℝ)) + b * (c * ‖x - z₂‖ ^ (p : ℝ)) := by
            ring
  simpa [normPowerKernel, c, Function.toEReal_apply, div_eq_mul_inv, one_div, mul_comm,
    mul_left_comm, mul_assoc] using
    strictlyConvex_toEReal_of_strictConvexOn_univ hscaled

-- Proof sketch: Proposition 12.14 places the `p`-power envelope in `Γ₀(H)`, and Proposition
-- 12.9 identifies its effective domain with all of `H`.
/-- Proposition 12 15 (Proposition 12.15 (1)): if `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, and `p > 1`, then
the real-valued
representative of the `p`-power envelope is convex on `H`. -/
theorem convexOn_univ_toReal_normPowerEnvelope_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) :
    _root_.ConvexOn ℝ Set.univ
      (fun x : H ↦ (normPowerEnvelope f p γ x).toReal) := by
  have hkernel : normPowerKernel (H := H) p γ ∈ Γ₀(H) :=
    normPowerKernel_mem_gammaZero (H := H) p γ hp
  have henv :
      (fun x ↦
        ⟨normPowerEnvelope f p γ x,
          bot_lt_iff_ne_bot.2
            (normPowerEnvelope_ne_bot_of_mem_gammaZero (H := H) f γ p hf hp x)⟩) ∈ Γ₀(H) := by
    simpa [normPowerEnvelope, infimalConvolution_comm] using
      infimalConvolution_mem_gammaZero_of_supercoercive_or_coercive_bddBelow
        (H := H)
        (f := normPowerKernel (H := H) p γ)
        (g := f)
        (hf := hkernel)
        (hg := hf)
        (hcase := Or.inl (supercoercive_normPowerKernel (H := H) p γ hp))
  have hdom : dom (normPowerEnvelope f p γ) = Set.univ :=
    dom_normPowerEnvelope_eq_univ_of_mem_gammaZero f γ p hf
  have heff :
      effectiveDomain
        (fun x ↦
          ⟨normPowerEnvelope f p γ x,
            bot_lt_iff_ne_bot.2
              (normPowerEnvelope_ne_bot_of_mem_gammaZero (H := H) f γ p hf hp x)⟩) = Set.univ := by
    ext x
    rw [mem_effectiveDomain_iff]
    simpa [mem_dom_iff] using
      mem_dom_normPowerEnvelope_of_mem_gammaZero f γ p hf x
  simpa [heff] using henv.2.toReal_convexOn_effectiveDomain

-- Proof sketch: Proposition 12.14 rules out `-∞`, while Proposition 12.9 rules out `+∞`.
/-- Proposition 12.15 (2): if `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, and `p > 1`, then the `p`-power
envelope is real-valued at every point of `H`. -/
theorem normPowerEnvelope_mem_Ioo_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) (x : H) :
    normPowerEnvelope f p γ x ∈ Set.Ioo (⊥ : EReal) ⊤ := by
  have hbot : (⊥ : EReal) < normPowerEnvelope f p γ x := by
    exact bot_lt_iff_ne_bot.2 <|
      normPowerEnvelope_ne_bot_of_mem_gammaZero (H := H) f γ p hf hp x
  have htop : normPowerEnvelope f p γ x < ⊤ := by
    simpa [mem_dom_iff] using
      mem_dom_normPowerEnvelope_of_mem_gammaZero f γ p hf x
  exact ⟨hbot, htop⟩

-- Proof sketch: clause (1) yields convexity on the open set `Set.univ`, so continuity follows
-- from the standard convex-on-open-set theorem.
/-- Proposition 12.15 (3): if `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, and `p > 1`, then the real-valued
representative of the `p`-power envelope is continuous on `H`. -/
theorem continuous_toReal_normPowerEnvelope_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) :
    Continuous (fun x : H ↦ (normPowerEnvelope f p γ x).toReal) := by
  let g : H → Set.Ioi (⊥ : EReal) := fun x ↦
    ⟨normPowerEnvelope f p γ x,
      bot_lt_iff_ne_bot.2
        (normPowerEnvelope_ne_bot_of_mem_gammaZero (H := H) f γ p hf hp x)⟩
  have hg_gamma : g ∈ Γ₀(H) := by
    have hkernel : normPowerKernel (H := H) p γ ∈ Γ₀(H) :=
      normPowerKernel_mem_gammaZero (H := H) p γ hp
    simpa [g, normPowerEnvelope, infimalConvolution_comm] using
      infimalConvolution_mem_gammaZero_of_supercoercive_or_coercive_bddBelow
        (H := H)
        (f := normPowerKernel (H := H) p γ)
        (g := f)
        (hf := hkernel)
        (hg := hf)
        (hcase := Or.inl (supercoercive_normPowerKernel (H := H) p γ hp))
  have heff : effectiveDomain g = Set.univ := by
    ext x
    rw [mem_effectiveDomain_iff]
    simpa [mem_dom_iff] using
      mem_dom_normPowerEnvelope_of_mem_gammaZero f γ p hf x
  have hcont_points :
      {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain g ∧
        ContinuousAt (fun y : H ↦ (g y : EReal).toReal) x} = interior (effectiveDomain g) :=
    continuous_points_eq_interior_effectiveDomain_of_lowerSemicontinuous
      (H := H) g hg_gamma
  refine continuous_iff_continuousAt.2 ?_
  intro x
  have hx :
      x ∈ {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain g ∧
        ContinuousAt (fun y : H ↦ (g y : EReal).toReal) x} := by
    rw [hcont_points]
    simp [heff]
  rcases hx with ⟨ρ, hρ, hball, hcont⟩
  simpa [g] using hcont

-- Proof sketch: Proposition 12.14 gives exact attainment, and Corollary 11.16 upgrades the
-- translated objective to have at most one minimizer because the translated kernel is strictly
-- convex.
/-- Proposition 12.15 (4): for `f ∈ Γ₀(H)`, `γ ∈ ℝ_{++}`, `p > 1`, and every `x ∈ H`, the
infimal convolution defining the `p`-power regularization is exact at `x`, and the translated
objective `y ↦ f y + ‖x - y‖^p / (γ p)` has a unique global minimizer. -/
theorem exactAt_and_existsUnique_mem_argmin_normPowerEnvelope_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) (p : Set.Ici (1 : ℝ))
    (hf : f ∈ Γ₀(H)) (hp : (1 : ℝ) < p) (x : H) :
    infimalConvolution.ExactAt f (normPowerKernel (H := H) p γ) x ∧
      ∃! y : H,
        y ∈ Argmin
          (fun z : H ↦
            (f z : EReal) + (normPowerKernel (H := H) p γ (x - z) : EReal)) := by
  have hexact :
      infimalConvolution.ExactAt f (normPowerKernel (H := H) p γ) x :=
    exactAt_normPowerEnvelope_of_mem_gammaZero (H := H) f γ p hf hp x
  rcases hexact with ⟨y, hyExact⟩
  have hyArg :
      y ∈ Argmin
        (fun z : H ↦ (f z : EReal) + (normPowerKernel (H := H) p γ (x - z) : EReal)) := by
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro z
    have hle :
        normPowerEnvelope f p γ x ≤
          (f z : EReal) + (normPowerKernel (H := H) p γ (x - z) : EReal) := by
      rw [normPowerEnvelope, infimalConvolution_apply]
      exact iInf_le _ z
    rw [normPowerEnvelope, hyExact] at hle
    simpa using hle
  have htranslated :
      (fun z : H ↦ normPowerKernel (H := H) p γ (x - z)) ∈ Γ₀(H) := by
    simpa using
      sub_right_mem_gammaZero (H := H) (normPowerKernel (H := H) p γ)
        (normPowerKernel_mem_gammaZero (H := H) p γ hp) x
  have hinter :
      (effectiveDomain f ∩
        effectiveDomain (fun z : H ↦ normPowerKernel (H := H) p γ (x - z))).Nonempty := by
    rcases hf.2.nonempty with ⟨z, hz⟩
    refine ⟨z, hz, ?_⟩
    rw [mem_effectiveDomain_iff]
    rw [normPowerKernel_apply]
    exact EReal.coe_lt_top _
  have hsub :
      (Argmin
        (fun z : H ↦
          (f z : EReal) + (normPowerKernel (H := H) p γ (x - z) : EReal))).Subsingleton := by
    simpa [Function.asEReal, pointwiseAdd_apply] using
      pointwiseAdd_argmin_subsingleton_of_inter_nonempty_of_strictlyConvex
        (H := H)
        (f := f)
        (g := fun z : H ↦ normPowerKernel (H := H) p γ (x - z))
        htranslated
        hf
        hinter
        (Or.inr (strictlyConvex_translated_normPowerKernel (H := H) p γ hp x))
  refine ⟨⟨y, hyExact⟩, ⟨y, hyArg, ?_⟩⟩
  intro z hz
  exact (hsub hyArg hz).symm

end HilbertSpace

end ERealFunction

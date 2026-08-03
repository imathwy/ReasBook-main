import BauschkeLean.Chap11.Proposition_11_7
import BauschkeLean.Chap17.Proposition_17_2
import BauschkeLean.Chap17.Proposition_17_16
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap24.Definition_24_48
import BauschkeLean.Chap24.Proposition_24_27
import BauschkeLean.Chap24.Proposition_24_49

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

namespace ERealFunction

noncomputable section

section ProximalThresholding

-- Source/core/bridge triage:
-- - `source-facing`: Example 24.51 is the radial proximal-thresholding formula on `ℝ`.
-- - `core/canonical`: the Chapter 24 owner is `Function.IsProximalThresholderOn`.
-- - `bridge/view`: Proposition 24.27 supplies the piecewise `Prox` formula, Proposition 24.49
--   identifies the actual thresholder set with `(∂ φ) 0`, and the source endpoint `φ′₊(0)` is a
--   view of the canonical threshold `sSup ((∂ φ) 0)`.

/-- On `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (s t : ℝ) :
    inner ℝ s t = s * t := by
  calc
    inner ℝ s t = (starRingEnd ℝ) s * t := RCLike.inner_apply' s t
    _ = s * t := by simp

private theorem effectiveDomain_eq_univ_of_nonzero_mem_effectiveDomain
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ) :
    effectiveDomain φ = Set.univ := by
  have heven_asEReal : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  have hzero_dom : (0 : ℝ) ∈ effectiveDomain φ :=
    zero_mem_effectiveDomain_of_even_convexOn φ hφ.2 heven_asEReal
  ext t
  constructor
  · intro _
    simp
  · intro _
    by_cases ht : t = 0
    · simpa [ht] using hzero_dom
    · exact hdom (by simpa [Set.mem_compl_iff] using ht)

private theorem toEReal_toReal_eq
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ) :
    (fun t : ℝ ↦ (φ t : EReal).toReal).toEReal = φ := by
  let g : ℝ → ℝ := fun t ↦ (φ t : EReal).toReal
  have hall : effectiveDomain φ = Set.univ :=
    effectiveDomain_eq_univ_of_nonzero_mem_effectiveDomain φ hφ heven hdom
  funext t
  apply Subtype.ext
  change ((g t : ℝ) : EReal) = (φ t : EReal)
  have ht_dom : t ∈ effectiveDomain φ := by simp [hall]
  have ht_top : (φ t : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ht_dom)
  have ht_bot : (φ t : EReal) ≠ ⊥ := ne_of_gt (φ t).2
  simp [g, EReal.coe_toReal ht_top ht_bot]

/-- Helper for Example 24.51: when both endpoints are finite, the directional difference quotient
is the coercion of the corresponding ordinary real quotient. -/
private theorem directionalDifferenceQuotient_eq_coe_toRealQuotient
    (f : ℝ → Set.Ioi (⊥ : EReal)) {x d : ℝ} (hx : x ∈ effectiveDomain f)
    (a : Set.Ioi (0 : ℝ)) (ha : x + (a : ℝ) • d ∈ effectiveDomain f) :
    directionalDifferenceQuotient f x d a =
      ((((f (x + (a : ℝ) • d) : EReal).toReal - (f x : EReal).toReal) / (a : ℝ) : ℝ) : EReal) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hxa_top : (f (x + (a : ℝ) • d) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ha)
  have hxa_bot : (f (x + (a : ℝ) • d) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + (a : ℝ) • d) : EReal) from (f _).2)
  -- Make both finite endpoints explicit before collapsing subtraction and division back to `ℝ`.
  rw [directionalDifferenceQuotient, ← EReal.coe_toReal hxa_top hxa_bot,
    ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_sub, ← EReal.coe_div]
  simp

private theorem toReal_convexOn_univ
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ) :
    _root_.ConvexOn ℝ Set.univ (fun t : ℝ ↦ (φ t : EReal).toReal) := by
  have hall : effectiveDomain φ = Set.univ :=
    effectiveDomain_eq_univ_of_nonzero_mem_effectiveDomain φ hφ heven hdom
  -- The finiteness bridge upgrades convexity on the effective domain to convexity on all of `ℝ`.
  simpa [hall] using hφ.2.toReal_convexOn_effectiveDomain

private theorem toReal_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (heven : Function.Even φ) :
    Function.Even (fun t : ℝ ↦ (φ t : EReal).toReal) := by
  intro t
  exact congrArg EReal.toReal <| congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)

private theorem subdifferential_zero_neg_mem_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (heven : Function.Even φ)
    {a : ℝ} (ha : a ∈ (∂ φ) 0) :
    -a ∈ (∂ φ) 0 := by
  have hevenE : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  rw [mem_subdifferential_iff] at ha ⊢
  intro y
  calc
    ((⟪y - 0, -a⟫_ℝ : EReal) + (φ 0 : EReal))
        = ((⟪-y - 0, a⟫_ℝ : EReal) + (φ 0 : EReal)) := by
            simp [real_inner_eq_mul]
    _ ≤ (φ (-y) : EReal) := by simpa using ha (-y)
    _ = (φ y : EReal) := by simpa using hevenE y

private theorem zero_mem_subdifferential_zero_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) :
    (0 : ℝ) ∈ (∂ φ) 0 := by
  have heven_asEReal : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  have hzero_argmin : (0 : ℝ) ∈ Argmin φ.asEReal :=
    zero_mem_argmin_of_proper_even_convexOn
      φ (isProper_of_mem_gammaZero hφ) hφ.2 heven_asEReal
  have hzero_zero : (0 : ℝ) ∈ (∂ φ).zeros := by
    simpa [argmin_eq_zeros_subdifferential φ] using hzero_argmin
  simpa [SetValuedOperator.mem_zeros_iff] using hzero_zero

private theorem rightDerivative_toReal_nonneg_and_support_line_on_nonnegative
    (g : ℝ → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ g)
    (hmono : MonotoneOn g (Set.Ici (0 : ℝ))) :
    0 ≤ ((g.toEReal)′₊(0)).toReal ∧
      ∀ t : ℝ, 0 ≤ t → g 0 + ((g.toEReal)′₊(0)).toReal * t ≤ g t := by
  have hconv_toEReal : ConvexOn g.toEReal (effectiveDomain g.toEReal) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Function.effectiveDomain_toEReal]
    · simp [Function.effectiveDomain_toEReal]
    · intro s hs t ht a ha0 ha1
      have hreal :
          g (a • s + (1 - a) • t) ≤ a * g s + (1 - a) * g t := by
        simpa [smul_eq_mul] using
          hconv.2 (by simp) (by simp) ha0.le (sub_nonneg.mpr ha1.le) (by ring)
      change ((g (a • s + (1 - a) • t) : ℝ) : EReal) ≤
        ((a * g s + (1 - a) * g t : ℝ) : EReal)
      exact_mod_cast hreal
  have hzero_mem : (0 : ℝ) ∈ effectiveDomain g.toEReal := by
    simp [Function.effectiveDomain_toEReal]
  have hright_nonneg : (0 : EReal) ≤ (g.toEReal)′₊(0) := by
    change (0 : EReal) ≤ sInf (Set.range (directionalDifferenceQuotient g.toEReal 0 1))
    refine le_sInf ?_
    rintro _ ⟨a, rfl⟩
    have hmono_a : g 0 ≤ g (a : ℝ) := by
      exact hmono (by simp) (show 0 ≤ (a : ℝ) by exact a.2.le) a.2.le
    have hquot_nonneg : 0 ≤ ((g (a : ℝ) - g 0) / (a : ℝ) : ℝ) := by
      exact div_nonneg (sub_nonneg.mpr hmono_a) a.2.le
    have hquot_eq :
        directionalDifferenceQuotient g.toEReal 0 1 a =
          ((((g (a : ℝ) - g 0) / (a : ℝ) : ℝ)) : EReal) := by
      simpa [Function.toEReal_apply, sub_eq_add_neg] using
        directionalDifferenceQuotient_eq_coe_toRealQuotient
          (f := g.toEReal) (x := (0 : ℝ)) (d := (1 : ℝ)) (hx := by simp) a (by simp)
    rw [hquot_eq]
    exact EReal.coe_nonneg.2 hquot_nonneg
  have hright_ne_top : (g.toEReal)′₊(0) ≠ ⊤ := by
    have hbound :
        (g.toEReal)′₊(0) ≤ directionalDifferenceQuotient g.toEReal 0 1 ⟨1, by norm_num⟩ := by
      change sInf (Set.range (directionalDifferenceQuotient g.toEReal 0 1)) ≤ _
      exact sInf_le ⟨⟨1, by norm_num⟩, rfl⟩
    intro htop
    have htop_le :
        (⊤ : EReal) ≤ directionalDifferenceQuotient g.toEReal 0 1 ⟨1, by norm_num⟩ := by
      simpa [htop] using hbound
    have hquot_top :
        directionalDifferenceQuotient g.toEReal 0 1 ⟨1, by norm_num⟩ = ⊤ := top_unique htop_le
    have hquot_top' : (↑(g 1) - ↑(g 0) : EReal) = ⊤ := by
      simpa [directionalDifferenceQuotient, Function.toEReal_apply] using hquot_top
    have hfinite : (↑(g 1) - ↑(g 0) : EReal) ≠ ⊤ := by
      rw [← EReal.coe_sub]
      exact EReal.coe_ne_top _
    exact hfinite hquot_top'
  have hright_ne_bot : (g.toEReal)′₊(0) ≠ ⊥ := by
    intro hbot
    have htmp := hright_nonneg
    simp [hbot] at htmp
  let ρ : ℝ := ((g.toEReal)′₊(0)).toReal
  have hρ_coe : ((ρ : ℝ) : EReal) = (g.toEReal)′₊(0) := by
    dsimp [ρ]
    simpa using EReal.coe_toReal hright_ne_top hright_ne_bot
  have hρ_mem_sub : ρ ∈ (∂ g.toEReal) (0 : ℝ) := by
    rw [subdifferential_eq_Icc_oneSidedDerivatives
      (f := g.toEReal) (hconv := hconv_toEReal) hzero_mem]
    change ((ρ : ℝ) : EReal) ∈ Set.Icc ((g.toEReal)′₋(0)) ((g.toEReal)′₊(0))
    constructor
    · simpa [hρ_coe] using
        leftDerivative_le_rightDerivative
          (f := g.toEReal) (hconv := hconv_toEReal) hzero_mem
    · simp [hρ_coe]
  have hρ_nonneg : 0 ≤ ρ := by
    have hρ_nonnegE : (0 : EReal) ≤ ((ρ : ℝ) : EReal) := by
      simpa [hρ_coe] using hright_nonneg
    exact EReal.coe_nonneg.mp hρ_nonnegE
  refine ⟨hρ_nonneg, ?_⟩
  intro t ht
  -- The extremal right derivative is itself a subgradient, hence yields the supporting line.
  have hsub :=
    (ERealFunction.mem_subdifferential_iff
      (f := g.toEReal) (x := (0 : ℝ)) (u := ρ)).1 hρ_mem_sub t
  have hsub_real : inner ℝ t ρ + g 0 ≤ g t := by
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [Function.toEReal_apply, EReal.coe_add] using hsub
  have hinner : inner ℝ t ρ = t * ρ := by
    simpa [RCLike.inner_apply] using (mul_comm ρ t)
  simpa [ρ, hinner, add_comm, add_left_comm, add_assoc, mul_comm] using hsub_real

private theorem slope_le_rightDerivative_toReal_of_support_line_on_nonnegative
    (g : ℝ → ℝ) {a : ℝ} (ha_nonneg : 0 ≤ a)
    (hminor : ∀ t : ℝ, 0 ≤ t → g 0 + a * t ≤ g t) :
    a ≤ ((g.toEReal)′₊(0)).toReal := by
  have ha_le_dir : ((a : ℝ) : EReal) ≤ (g.toEReal)′₊(0) := by
    change ((a : ℝ) : EReal) ≤ sInf (Set.range (directionalDifferenceQuotient g.toEReal 0 1))
    refine le_sInf ?_
    rintro _ ⟨t, rfl⟩
    have hminor_t : g 0 + a * (t : ℝ) ≤ g (t : ℝ) := hminor (t : ℝ) t.2.le
    have hquot_lower : a ≤ (g (t : ℝ) - g 0) / (t : ℝ) := by
      have ht_pos : 0 < (t : ℝ) := t.2
      exact (le_div_iff₀ ht_pos).2 <| by linarith
    have hquot_eq :
        directionalDifferenceQuotient g.toEReal 0 1 t =
          ((((g (t : ℝ) - g 0) / (t : ℝ) : ℝ)) : EReal) := by
      simpa [Function.toEReal_apply, sub_eq_add_neg] using
        directionalDifferenceQuotient_eq_coe_toRealQuotient
          (f := g.toEReal) (x := (0 : ℝ)) (d := (1 : ℝ)) (hx := by simp) t (by simp)
    rw [hquot_eq]
    exact EReal.coe_le_coe_iff.mpr hquot_lower
  have hright_ne_top : (g.toEReal)′₊(0) ≠ ⊤ := by
    have hbound :
        (g.toEReal)′₊(0) ≤ directionalDifferenceQuotient g.toEReal 0 1 ⟨1, by norm_num⟩ := by
      change sInf (Set.range (directionalDifferenceQuotient g.toEReal 0 1)) ≤ _
      exact sInf_le ⟨⟨1, by norm_num⟩, rfl⟩
    intro htop
    have htop_le :
        (⊤ : EReal) ≤ directionalDifferenceQuotient g.toEReal 0 1 ⟨1, by norm_num⟩ := by
      simpa [htop] using hbound
    have hquot_top :
        directionalDifferenceQuotient g.toEReal 0 1 ⟨1, by norm_num⟩ = ⊤ := top_unique htop_le
    have hquot_top' : (↑(g 1) - ↑(g 0) : EReal) = ⊤ := by
      simpa [directionalDifferenceQuotient, Function.toEReal_apply] using hquot_top
    have hfinite : (↑(g 1) - ↑(g 0) : EReal) ≠ ⊤ := by
      rw [← EReal.coe_sub]
      exact EReal.coe_ne_top _
    exact hfinite hquot_top'
  have hright_ne_bot : (g.toEReal)′₊(0) ≠ ⊥ := by
    intro hbot
    have hnonnegE : (0 : EReal) ≤ ((a : ℝ) : EReal) := by
      exact_mod_cast ha_nonneg
    have : (0 : EReal) ≤ (⊥ : EReal) := by
      simpa [hbot] using le_trans hnonnegE ha_le_dir
    simp at this
  have ha_le_dir_real :
      ((a : ℝ) : EReal) ≤ ((((g.toEReal)′₊(0)).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hright_ne_top hright_ne_bot] using ha_le_dir
  exact EReal.coe_le_coe_iff.mp ha_le_dir_real

/-- Scalar interval companion for Example 24.51: if an even scalar `Γ₀(ℝ)` owner is finite on
`ℝ \ {0}`, then its zero-fiber subdifferential is the centered interval cut out by the source
endpoint `(φ′₊(0)).toReal`. -/
theorem subdifferential_zero_eq_Icc_rightDerivative
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ) :
    (∂ φ) 0 = Set.Icc (-((φ′₊(0)).toReal)) ((φ′₊(0)).toReal) := by
  let g : ℝ → ℝ := fun t ↦ (φ t : EReal).toReal
  have hg_eq : g.toEReal = φ := by
    simpa [g] using toEReal_toReal_eq φ hφ heven hdom
  have hg_conv : _root_.ConvexOn ℝ Set.univ g := by
    simpa [g] using toReal_convexOn_univ φ hφ heven hdom
  have hg_even : Function.Even g := by
    simpa [g] using toReal_even φ heven
  have hall : effectiveDomain φ = Set.univ :=
    effectiveDomain_eq_univ_of_nonzero_mem_effectiveDomain φ hφ heven hdom
  have heven_asEReal : Function.Even φ.asEReal := by
    intro t
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (heven t)
  have hmono_asEReal : MonotoneOn φ.asEReal (Set.Ici (0 : ℝ)) :=
    monotoneOn_nonnegative_of_proper_even_convexOn
      φ (isProper_of_mem_gammaZero hφ) hφ.2 heven_asEReal
  have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    intro s hs t ht hst
    have hs_dom : s ∈ effectiveDomain φ := by simp [hall]
    have ht_dom : t ∈ effectiveDomain φ := by simp [hall]
    have hs_top : (φ s : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hs_dom)
    have ht_top : (φ t : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp ht_dom)
    simpa [g, Function.asEReal_apply] using
      EReal.toReal_le_toReal (hmono_asEReal hs ht hst) (ne_of_gt (φ s).2) ht_top
  let ρ : ℝ := ((g.toEReal)′₊(0)).toReal
  have hρ_eq : ρ = (φ′₊(0)).toReal := by
    simp [ρ, hg_eq]
  have hρ_pack :=
    rightDerivative_toReal_nonneg_and_support_line_on_nonnegative g hg_conv hg_mono
  rcases hρ_pack with ⟨hρ_nonneg, hρ_support⟩
  have subgradientSupportLine {b : ℝ} (hb : b ∈ (∂ g.toEReal) 0) :
      ∀ t : ℝ, 0 ≤ t → g 0 + b * t ≤ g t := by
    intro t ht
    -- Work in the finite real spelling `g.toEReal` and descend the affine minorant to `ℝ`.
    have hsub := (mem_subdifferential_iff (f := g.toEReal) (x := (0 : ℝ)) (u := b)).1 hb t
    have hsub_real : t * b + g 0 ≤ g t := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [Function.toEReal_apply, EReal.coe_add, sub_zero, real_inner_eq_mul,
          add_comm, add_left_comm, add_assoc, mul_comm] using hsub
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hsub_real
  ext a
  constructor
  · intro ha
    have ha_g : a ∈ (∂ g.toEReal) 0 := by
      simpa [hg_eq] using ha
    have hupper : a ≤ ρ := by
      by_cases ha_nonneg : 0 ≤ a
      · -- A nonnegative subgradient gives a support line whose slope is controlled by `ρ`.
        exact slope_le_rightDerivative_toReal_of_support_line_on_nonnegative
          g ha_nonneg (subgradientSupportLine ha_g)
      · linarith
    have hlower : -ρ ≤ a := by
      have hneg : -a ∈ (∂ φ) 0 := subdifferential_zero_neg_mem_of_even φ heven ha
      have hneg_g : -a ∈ (∂ g.toEReal) 0 := by
        simpa [hg_eq] using hneg
      have hneg_upper : -a ≤ ρ := by
        by_cases hneg_nonneg : 0 ≤ -a
        · exact slope_le_rightDerivative_toReal_of_support_line_on_nonnegative
            g hneg_nonneg (subgradientSupportLine hneg_g)
        · linarith
      linarith
    have hlower' : -((φ′₊(0)).toReal) ≤ a := by
      simpa [hρ_eq] using hlower
    have hupper' : a ≤ (φ′₊(0)).toReal := by
      simpa [hρ_eq] using hupper
    exact ⟨hlower', hupper'⟩
  · intro ha
    have ha_upper : a ≤ ρ := by
      simpa [hρ_eq] using ha.2
    have hneg_upper : -a ≤ ρ := by
      have ha_lower : -ρ ≤ a := by
        simpa [hρ_eq] using ha.1
      linarith
    have ha_g : a ∈ (∂ g.toEReal) 0 := by
      -- Route correction: prove the affine minorant directly from the support line at slope `ρ`.
      rw [mem_subdifferential_iff]
      intro y
      by_cases hy : 0 ≤ y
      · have hreal : g 0 + a * y ≤ g y := by
          have hmul : a * y ≤ ρ * y := mul_le_mul_of_nonneg_right ha_upper hy
          calc
            g 0 + a * y ≤ g 0 + ρ * y := by linarith
            _ ≤ g y := hρ_support y hy
        exact EReal.coe_le_coe_iff.mpr <| by
          simpa [Function.toEReal_apply, EReal.coe_add, sub_zero, real_inner_eq_mul,
            add_comm, add_left_comm, add_assoc, mul_comm] using hreal
      · have hy_nonneg : 0 ≤ -y := by linarith
        have hreal_neg : g 0 + (-a) * (-y) ≤ g (-y) := by
          have hmul : (-a) * (-y) ≤ ρ * (-y) := mul_le_mul_of_nonneg_right hneg_upper hy_nonneg
          calc
            g 0 + (-a) * (-y) ≤ g 0 + ρ * (-y) := by linarith
            _ ≤ g (-y) := hρ_support (-y) hy_nonneg
        have hreal : g 0 + a * y ≤ g y := by
          simpa [hg_even y, mul_comm, add_comm, add_left_comm, add_assoc] using hreal_neg
        exact EReal.coe_le_coe_iff.mpr <| by
          simpa [Function.toEReal_apply, EReal.coe_add, sub_zero, real_inner_eq_mul,
            add_comm, add_left_comm, add_assoc, mul_comm] using hreal
    simpa [hg_eq] using ha_g

/-- Bridge companion for Example 24.51: if an even scalar `Γ₀(ℝ)` owner is finite on
`ℝ \ {0}`, then the canonical Chapter 24 threshold `sSup ((∂ φ) 0)` agrees with the source
endpoint `(φ′₊(0)).toReal`. -/
theorem sSup_subdifferential_zero_eq_rightDerivative_toReal
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ) :
    sSup ((∂ φ) 0) = (φ′₊(0)).toReal := by
  have hρ_nonneg :
      0 ≤ (φ′₊(0)).toReal := by
    have hsub_nonempty : ((∂ φ) 0).Nonempty :=
      ⟨0, zero_mem_subdifferential_zero_of_even φ hφ heven⟩
    rw [subdifferential_zero_eq_Icc_rightDerivative φ hφ heven hdom] at hsub_nonempty
    have hIcc : -((φ′₊(0)).toReal) ≤ (φ′₊(0)).toReal := Set.nonempty_Icc.mp hsub_nonempty
    linarith
  have hIcc : -((φ′₊(0)).toReal) ≤ (φ′₊(0)).toReal := by linarith
  rw [subdifferential_zero_eq_Icc_rightDerivative φ hφ heven hdom]
  simpa using (csSup_Icc hIcc)

/-- Helper for Example 24.51: specializing `distanceProfile C φ` to `C = {0}` recovers the
original even scalar owner `φ`. -/
private theorem distanceProfile_singleton_zero_eq
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (heven : Function.Even φ) :
    distanceProfile ({0} : Set ℝ) φ = φ := by
  funext x
  by_cases hx : 0 ≤ x
  · simp [distanceProfile_apply, Metric.infDist_singleton, dist_eq_norm,
      Real.norm_eq_abs, abs_of_nonneg hx]
  · simp [distanceProfile_apply, Metric.infDist_singleton, dist_eq_norm, Real.norm_eq_abs,
      abs_of_neg (lt_of_not_ge hx), heven x]

/-- Helper for Example 24.51: `{0}` is Chebyshev by the standard nonempty closed convex owner. -/
private abbrev singletonZeroIsChebyshev : IsChebyshev ({0} : Set ℝ) :=
  isChebyshev_of_nonempty_isClosed_convex
    (show ({0} : Set ℝ).Nonempty from ⟨0, by simp⟩)
    isClosed_singleton
    (convex_singleton (0 : ℝ))

/-- Helper for Example 24.51: the metric projection onto `{0}` is the constant zero map. -/
private theorem projectionPoint_singleton_zero_eq_zero (x : ℝ) :
    P[({0} : Set ℝ), singletonZeroIsChebyshev] x = 0 := by
  have hbest : IsBestApproximation x ({0} : Set ℝ) 0 := by
    simp [IsBestApproximation, Metric.infDist_singleton]
  exact
    (eq_projectionPoint_of_isBestApproximation
      ({0} : Set ℝ)
      singletonZeroIsChebyshev
      hbest).symm

/-- Bridge companion for Example 24.51: the canonical proximity operator `Prox[φ, hφ]` is the
displayed piecewise radial map, written with the canonical threshold `sSup ((∂ φ) 0)`. -/
theorem prox_eq_radial_piecewise_sSup_subdifferential_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdiff : DifferentiableOn ℝ (fun t : ℝ ↦ (φ t : EReal).toReal) (({0} : Set ℝ)ᶜ)) :
    Prox[φ, hφ] =
      (fun x : ℝ ↦
        if ‖x‖ > sSup ((∂ φ) 0) then
          x -
            ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] ‖x‖) / ‖x‖) * x
        else
          0) := by
  funext x
  have hγ : distanceProfile ({0} : Set ℝ) φ ∈ Γ₀(ℝ) :=
    distanceProfile_mem_gammaZero_of_even
      (show ({0} : Set ℝ).Nonempty from ⟨0, by simp⟩)
      isClosed_singleton
      (convex_singleton (0 : ℝ))
      φ hφ heven
  simpa [distanceProfile_singleton_zero_eq φ heven, projectionPoint_singleton_zero_eq_zero x,
    Metric.infDist_singleton, dist_eq_norm, smul_eq_mul] using
    (prox_distanceProfile_eq_piecewise
      (show ({0} : Set ℝ).Nonempty from ⟨0, by simp⟩)
      isClosed_singleton
      (convex_singleton (0 : ℝ))
      φ hφ heven hdiff hγ x)

/-- Canonical thresholder version of Example 24.51: for an even scalar `Γ₀(ℝ)` owner, the
proximity operator `Prox[φ, hφ]` is a proximal thresholder on its actual zero set `(∂ φ) 0`. -/
theorem prox_isProximalThresholderOn_subdifferential_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ) :
    Function.IsProximalThresholderOn (Prox[φ, hφ]) ((∂ φ) 0) := by
  have hsub_nonempty : ((∂ φ) 0).Nonempty :=
    ⟨0, zero_mem_subdifferential_zero_of_even φ hφ heven⟩
  have hprox :
      Function.IsProximalThresholderOn (Prox[φ, hφ]) ((∂ φ) 0) ↔
        (∂ φ) 0 = (∂ φ) 0 :=
    prox_isProximalThresholderOn_iff_subdifferential_zero_eq hφ hsub_nonempty
  exact
    hprox.2 rfl

/-- Interval bridge for Example 24.51: if an even scalar `Γ₀(ℝ)` owner is finite on
`ℝ \ {0}`, then `Prox[φ, hφ]` is a proximal thresholder on the centered interval cut out by the
canonical threshold `sSup ((∂ φ) 0)`. -/
theorem prox_isProximalThresholderOn_Icc_sSup_subdifferential_zero
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ) :
    Function.IsProximalThresholderOn
      (Prox[φ, hφ])
      (Set.Icc (-(sSup ((∂ φ) 0))) (sSup ((∂ φ) 0))) := by
  rw [sSup_subdifferential_zero_eq_rightDerivative_toReal φ hφ heven hdom]
  simpa [subdifferential_zero_eq_Icc_rightDerivative φ hφ heven hdom] using
    prox_isProximalThresholderOn_subdifferential_zero φ hφ heven

/-- Example 24.51: if an even scalar `Γ₀(ℝ)` owner is finite on `ℝ \ {0}`, then `Prox[φ, hφ]`
is a proximal thresholder on the displayed centered interval
`[-(φ′₊(0)).toReal, (φ′₊(0)).toReal]`. -/
theorem prox_isProximalThresholderOn_Icc_rightDerivative
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ) :
    Function.IsProximalThresholderOn
      (Prox[φ, hφ])
      (Set.Icc (-((φ′₊(0)).toReal)) ((φ′₊(0)).toReal)) := by
  simpa [sSup_subdifferential_zero_eq_rightDerivative_toReal φ hφ heven hdom] using
    prox_isProximalThresholderOn_Icc_sSup_subdifferential_zero φ hφ heven hdom

/-- Source-facing bridge companion for Example 24.51: rewriting the canonical threshold
`sSup ((∂ φ) 0)` as `(φ′₊(0)).toReal` yields the displayed scalar radial formula. -/
theorem prox_eq_radial_piecewise_rightDerivative
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ)
    (hdiff : DifferentiableOn ℝ (fun t : ℝ ↦ (φ t : EReal).toReal) (({0} : Set ℝ)ᶜ)) :
    Prox[φ, hφ] =
      (fun x : ℝ ↦
        if ‖x‖ > (φ′₊(0)).toReal then
          x -
            ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] ‖x‖) / ‖x‖) * x
        else
          0) := by
  simpa [sSup_subdifferential_zero_eq_rightDerivative_toReal φ hφ heven hdom] using
    prox_eq_radial_piecewise_sSup_subdifferential_zero φ hφ heven hdiff

/-- Bridge companion for Example 24.51: if `φ : ℝ → Set.Ioi (⊥ : EReal)` is an even scalar
`Γ₀(ℝ)` owner that is finite and differentiable on `ℝ \ {0}`, then `Prox[φ, hφ]` is the
displayed radial piecewise map and is a proximal thresholder on
`[-(φ′₊(0)).toReal, (φ′₊(0)).toReal]`. -/
theorem prox_eq_radial_piecewise_and_isProximalThresholderOn_Icc_rightDerivative
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (heven : Function.Even φ)
    (hdom : (({0} : Set ℝ)ᶜ) ⊆ effectiveDomain φ)
    (hdiff : DifferentiableOn ℝ (fun t : ℝ ↦ (φ t : EReal).toReal) (({0} : Set ℝ)ᶜ)) :
    Prox[φ, hφ] =
        (fun x : ℝ ↦
          if ‖x‖ > (φ′₊(0)).toReal then
            x -
              ((Prox[φ∗[hφ], gammaZeroConjugate_mem_gammaZero hφ] ‖x‖) / ‖x‖) * x
          else
            0) ∧
      Function.IsProximalThresholderOn
        (Prox[φ, hφ])
        (Set.Icc (-((φ′₊(0)).toReal)) ((φ′₊(0)).toReal)) := by
  -- Package the source-facing formula and the thresholder property already proved above.
  refine ⟨?_, ?_⟩
  · exact prox_eq_radial_piecewise_rightDerivative φ hφ heven hdom hdiff
  · exact prox_isProximalThresholderOn_Icc_rightDerivative φ hφ heven hdom

end ProximalThresholding

end

end ERealFunction

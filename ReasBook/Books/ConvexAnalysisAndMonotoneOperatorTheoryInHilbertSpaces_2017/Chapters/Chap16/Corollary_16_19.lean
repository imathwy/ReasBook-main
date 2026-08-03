import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap07.Corollary_7_12
import BauschkeLean.Chap08.Proposition_8_2
import BauschkeLean.Chap03.Proposition_3_44
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Corollary_9_10
import BauschkeLean.Chap09.Proposition_9_14
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap09.Proposition_9_6
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap09.Proposition_9_33
import BauschkeLean.Chap10.Proposition_10_3
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_12
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_16
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_17

open Set Filter
open scoped InnerProductSpace

universe u

namespace ERealFunction

section Corollary_16_19

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (h : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn h (effectiveDomain h))
variable (D : Set H) (hD_nonempty : D.Nonempty) (hD_open : IsOpen D) (hD_convex : Convex ℝ D)
variable (hD_cont : D ⊆ {x : H | ContinuousAtOnEffectiveDomain h x})

include hconv hD_nonempty hD_open hD_convex hD_cont

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

omit h hconv D hD_nonempty hD_open hD_convex hD_cont

/-- Helper for Corollary 16 19: the effective domain of an `EReal`-valued function consists of
the points where the value is neither `⊤` nor `⊥`. -/
private def effectiveDom (f : H → EReal) : Set H := {x : H | f x ≠ ⊤ ∧ f x ≠ ⊥}

/-- Helper for Corollary 16 19: membership in the effective domain is exactly the two finiteness
conditions. -/
private theorem mem_effectiveDom_iff {f : H → EReal} {x : H} :
    x ∈ effectiveDom f ↔ f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  rfl

/-- Helper for Corollary 16 19: a proper `Γ(H)` function has the same lower semicontinuous convex
envelope as itself. -/
private theorem lowerSemicontinuousConvexEnvelope_eq_self_of_mem_gamma
    {f : H → EReal} (hf : f ∈ Γ(H)) :
    lowerSemicontinuousConvexEnvelope f = f := by
  rcases (mem_gamma_iff f).mp hf with ⟨hf_conv, hf_lsc⟩
  have hf_conv_epi : Convex ℝ (epigraph f) := by
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro x y hx hy a ha ha_lt_one
    exact hf_conv (x := x) (y := y) ha.le ha_lt_one.le
  apply le_antisymm
  · exact lowerSemicontinuousConvexEnvelope_le f
  · exact
      le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
        hf_lsc hf_conv_epi le_rfl

/-- Helper for Corollary 16 19: a finite-domain point gives the canonical real-height epigraph
point. -/
private theorem mem_epigraph_toReal_of_mem_dom
    {f : H → EReal} (hproper : IsProper f) {x : H} (hx : x ∈ dom f) :
    (x, (f x).toReal) ∈ epigraph f := by
  have hx_top : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
  have hx_bot : f x ≠ ⊥ := hproper.1 x
  rw [mem_epigraph_iff]
  simp [EReal.coe_toReal hx_top hx_bot]

/-- Helper for Corollary 16 19: outside the domain, a proper extended-real-valued function takes
the value `⊤`. -/
private theorem value_eq_top_of_not_mem_dom
    {f : H → EReal} {x : H} (hx : x ∉ dom f) :
    f x = ⊤ := by
  simpa using (not_mem_dom_iff f x).mp hx

/-- Helper for Corollary 16 19: a proper `Γ(H)` function has a real-height epigraph point. -/
private theorem exists_mem_epigraph_of_isProper
    {f : H → EReal} (hproper : IsProper f) :
    (epigraph f).Nonempty := by
  rcases hproper.2 with ⟨x, hx⟩
  refine ⟨(x, (f x).toReal), ?_⟩
  exact mem_epigraph_toReal_of_mem_dom (f := f) hproper hx

/-- Helper for Corollary 16 19: the `ℓ²` product inner product on `H × ℝ` splits componentwise.
-/
private theorem inner_pair_eq {z w : H × ℝ} :
    ⟪z, w⟫_ℝ = ⟪z.1, w.1⟫_ℝ + z.2 * w.2 := by
  rcases z with ⟨z₁, z₂⟩
  rcases w with ⟨w₁, w₂⟩
  change ⟪z₁, w₁⟫_ℝ + ⟪z₂, w₂⟫_ℝ = ⟪z₁, w₁⟫_ℝ + z₂ * w₂
  have hreal : ⟪z₂, w₂⟫_ℝ = z₂ * w₂ := by
    calc
      ⟪z₂, w₂⟫_ℝ = w₂ * star z₂ := by
        exact RCLike.inner_apply z₂ w₂
      _ = w₂ * z₂ := by
        simp
      _ = z₂ * w₂ := by ring
  rw [hreal]

/-- Helper for Corollary 16 19: a point below the graph of a proper `Γ(H)` function admits a
strict supporting affine minorant. -/
private theorem exists_strict_affine_minorant_of_lt_of_mem_gamma_of_mem_closure_dom
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H))
    {x : H} (hx_closure : x ∈ closure (dom f)) {ξ : ℝ} (hξ : (ξ : EReal) < f x) :
    ∃ u : H, ∃ η : ℝ,
      (∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y)) ∧
        (ξ : EReal) < (((⟪x, u⟫_ℝ + η : ℝ) : EReal)) := by
  rcases (mem_gamma_iff f).mp hf with ⟨hf_conv, hf_lsc⟩
  have hEpi_conv : Convex ℝ (epigraph f) := by
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro y z hy hz a ha ha_lt_one
    exact hf_conv ha.le ha_lt_one.le
  have hEpi_closed : IsClosed (epigraph f) :=
    (lowerSemicontinuous_iff_isClosed_epigraph f).mp hf_lsc
  have hq_not_mem : (x, ξ) ∉ epigraph f := by
    intro hxξ
    exact (not_le_of_gt hξ) ((mem_epigraph_iff f x ξ).mp hxξ)
  obtain ⟨w, β, hsep, hq_out⟩ :=
    exists_closedHalfspace_separating_of_not_mem_of_isClosed_of_convex
      hEpi_closed hEpi_conv hq_not_mem
  have hw₂_nonpos : w.2 ≤ 0 := by
    by_contra hw₂_pos
    rcases exists_mem_epigraph_of_isProper (f := f) hproper with ⟨⟨p, π⟩, hpπ⟩
    let t : ℝ := |β - ⟪(p, π), w⟫_ℝ| / w.2 + 1
    have ht_nonneg : 0 ≤ t := by
      have hw₂_pos' : 0 < w.2 := lt_of_not_ge hw₂_pos
      dsimp [t]
      positivity
    have hpπt : (p, π + t) ∈ epigraph f := by
      rw [mem_epigraph_iff] at hpπ ⊢
      exact le_trans hpπ <| by
        exact_mod_cast (le_add_of_nonneg_right ht_nonneg)
    have hpair_base : ⟪(p, π), w⟫_ℝ = ⟪p, w.1⟫_ℝ + π * w.2 := by
      simp [inner_pair_eq]
    have hpair_shift : ⟪(p, π + t), w⟫_ℝ = ⟪(p, π), w⟫_ℝ + t * w.2 := by
      calc
        ⟪(p, π + t), w⟫_ℝ = ⟪p, w.1⟫_ℝ + (π + t) * w.2 := by
          simp [inner_pair_eq]
        _ = (⟪p, w.1⟫_ℝ + π * w.2) + t * w.2 := by ring
        _ = ⟪(p, π), w⟫_ℝ + t * w.2 := by rw [hpair_base]
    have hlarge : β < ⟪(p, π + t), w⟫_ℝ := by
      have habs : |β - ⟪(p, π), w⟫_ℝ| ≤ t * w.2 := by
        dsimp [t]
        have hw₂_pos' : 0 < w.2 := lt_of_not_ge hw₂_pos
        have hmul :
            |β - ⟪(p, π), w⟫_ℝ| ≤ |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
          linarith
        have hdiv :
            |β - ⟪(p, π), w⟫_ℝ| ≤
              (|β - ⟪(p, π), w⟫_ℝ| / w.2 + 1) * w.2 := by
          have hEq :
              (|β - ⟪(p, π), w⟫_ℝ| / w.2 + 1) * w.2 =
                |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
            field_simp [hw₂_pos'.ne']
          simpa [t, hEq] using hmul
        exact hdiv
      have hbase : β - ⟪(p, π), w⟫_ℝ < t * w.2 := by
        have hstrict : |β - ⟪(p, π), w⟫_ℝ| < t * w.2 := by
          dsimp [t]
          have hplus : |β - ⟪(p, π), w⟫_ℝ| < |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
            linarith
          have hEq :
              (|β - ⟪(p, π), w⟫_ℝ| / w.2 + 1) * w.2 =
                |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
            field_simp [(lt_of_not_ge hw₂_pos).ne']
          simpa [t, hEq] using hplus
        exact (abs_lt.mp hstrict).2
      linarith [hpair_shift]
    exact (not_le_of_gt hlarge) (hsep hpπt)
  have hw₂_neg : w.2 < 0 := by
    by_cases hw₂_zero : w.2 = 0
    · have hdom_half :
          dom f ⊆ {y : H | ⟪y, w.1⟫_ℝ ≤ β} := by
        intro y hy
        have hy_epi : (y, (f y).toReal) ∈ epigraph f :=
          mem_epigraph_toReal_of_mem_dom (f := f) hproper hy
        have hy_sep : ⟪(y, (f y).toReal), w⟫_ℝ ≤ β := hsep hy_epi
        have hy_sep' : ⟪y, w.1⟫_ℝ + (f y).toReal * w.2 ≤ β := by
          simpa [inner_pair_eq] using hy_sep
        simpa [hw₂_zero] using hy_sep'
      have hhalf_closed : IsClosed {y : H | ⟪y, w.1⟫_ℝ ≤ β} := by
        exact isClosed_le (continuous_id.inner continuous_const) continuous_const
      have hx_half : x ∈ {y : H | ⟪y, w.1⟫_ℝ ≤ β} :=
        (closure_minimal hdom_half hhalf_closed) hx_closure
      have hq_half : (x, ξ) ∈ {z : H × ℝ | ⟪z, w⟫_ℝ ≤ β} := by
        simpa [inner_pair_eq, hw₂_zero] using hx_half
      exact False.elim (hq_out hq_half)
    · exact lt_of_le_of_ne hw₂_nonpos hw₂_zero
  let δ : ℝ := -w.2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  let u : H := δ⁻¹ • w.1
  let η : ℝ := -β / δ
  refine ⟨u, η, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ dom f
    · have hy_epi : (y, (f y).toReal) ∈ epigraph f :=
        mem_epigraph_toReal_of_mem_dom (f := f) hproper hy
      have hy_sep : ⟪(y, (f y).toReal), w⟫_ℝ ≤ β := hsep hy_epi
      have hreal_base :
          ⟪y, w.1⟫_ℝ + (f y).toReal * w.2 ≤ β := by
        simpa [inner_pair_eq] using hy_sep
      have hreal_num :
          ⟪y, w.1⟫_ℝ - β ≤ (f y).toReal * δ := by
        dsimp [δ] at *
        linarith
      have hreal_div :
          (⟪y, w.1⟫_ℝ - β) / δ ≤ (f y).toReal := by
        exact (div_le_iff₀ hδ_pos).2 hreal_num
      have hrewrite :
          ⟪y, u⟫_ℝ + η = (⟪y, w.1⟫_ℝ - β) / δ := by
        dsimp [u, η]
        rw [real_inner_smul_right]
        field_simp [hδ_pos.ne']
        ring
      have hcast :
          (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ (((f y).toReal : ℝ) : EReal)) := by
        rw [hrewrite]
        exact_mod_cast hreal_div
      have hy_top : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
      have hy_bot : f y ≠ ⊥ := hproper.1 y
      simpa [EReal.coe_toReal hy_top hy_bot] using hcast
    · rw [value_eq_top_of_not_mem_dom (f := f) hy]
      exact le_top
  · have hq_real : β < ⟪(x, ξ), w⟫_ℝ := by
      exact lt_of_not_ge hq_out
    have hq_real' : β < ⟪x, w.1⟫_ℝ + ξ * w.2 := by
      simpa [inner_pair_eq] using hq_real
    have hnum : β + ξ * δ < ⟪x, w.1⟫_ℝ := by
      dsimp [δ] at *
      simpa using hq_real'
    have hdiv : ξ < (⟪x, w.1⟫_ℝ - β) / δ := by
      refine (lt_div_iff₀ hδ_pos).2 ?_
      linarith
    have hrewrite :
        ⟪x, u⟫_ℝ + η = (⟪x, w.1⟫_ℝ - β) / δ := by
      dsimp [u, η]
      rw [real_inner_smul_right]
      field_simp [hδ_pos.ne']
      ring
    exact_mod_cast (hrewrite ▸ hdiv)

/-- Helper for Corollary 16 19: every proper member of `Γ(H)` admits a global continuous affine
minorant. -/
private theorem exists_global_affine_minorant_of_isProper_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    ∃ u : H, ∃ η : ℝ, ∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y) := by
  rcases hproper.2 with ⟨x, hx⟩
  have hx_top : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
  have hx_bot : f x ≠ ⊥ := hproper.1 x
  let ξ : ℝ := (f x).toReal - 1
  have hξ : (ξ : EReal) < f x := by
    have hreal : ξ < (f x).toReal := by
      dsimp [ξ]
      linarith
    have hcast : ((ξ : ℝ) : EReal) < (((f x).toReal : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [EReal.coe_toReal hx_top hx_bot] using hcast
  rcases exists_strict_affine_minorant_of_lt_of_mem_gamma_of_mem_closure_dom
      hproper hf (subset_closure hx) hξ with ⟨u, η, hminor, _⟩
  exact ⟨u, η, hminor⟩

/-- Helper for Corollary 16 19: a strict affine minorant yields a lower bound on the Fenchel
biconjugate. -/
private theorem strict_lower_bound_le_biconjugate_of_affine_minorant
    {f : H → EReal} {x u : H} {η ξ : ℝ}
    (hminor : ∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y))
    (hξ : (ξ : EReal) < (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) :
    (ξ : EReal) ≤ f∗∗ x := by
  have hmem : (u, -η) ∈ epigraph f∗ := by
    refine (mem_epigraph_conjugate_iff f u (-η)).2 ?_
    intro y
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hminor y
  have hconj : f∗ u ≤ ((-η : ℝ) : EReal) := (mem_epigraph_iff _ _ _).mp hmem
  have hneg : ((η : ℝ) : EReal) ≤ -f∗ u := by
    rw [← EReal.neg_le_neg_iff]
    simpa using hconj
  have haffine_le :
      (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal) - f∗ u)) := by
    calc
      (((⟪x, u⟫_ℝ + η : ℝ) : EReal))
          = (((⟪x, u⟫_ℝ : ℝ) : EReal) + ((η : ℝ) : EReal)) := by
              rw [EReal.coe_add]
      _ ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal) + -f∗ u) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hneg (((⟪x, u⟫_ℝ : ℝ) : EReal))
      _ = (((⟪x, u⟫_ℝ : ℝ) : EReal) - f∗ u) := by
        rfl
  have hdefect_le : (((⟪x, u⟫_ℝ : ℝ) : EReal) - f∗ u) ≤ f∗∗ x := by
    simpa [conjugate_apply, real_inner_comm] using
      (le_iSup (fun y : H ↦ (((⟪y, x⟫_ℝ : ℝ) : EReal) - f∗ y)) u)
  exact hξ.le.trans (haffine_le.trans hdefect_le)

/-- Helper for Corollary 16 19: outside the closure of the domain of a proper member of `Γ(H)`,
its Fenchel biconjugate is `⊤`. -/
private theorem biconjugate_eq_top_of_not_mem_closure_dom_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H))
    {x : H} (hx : x ∉ closure (dom f)) :
    f∗∗ x = ⊤ := by
  rcases (mem_gamma_iff f).mp hf with ⟨hf_conv, _⟩
  have hEpi_conv : Convex ℝ (epigraph f) := by
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro y z hy hz a ha ha_lt_one
    exact hf_conv ha.le ha_lt_one.le
  have hdom_conv : Convex ℝ (dom f) := convex_dom_of_convex_epigraph f hEpi_conv
  obtain ⟨u₀, β₀, hdom_half, hx_out⟩ :=
    exists_closedHalfspace_separating_of_not_mem_of_isClosed_of_convex
      isClosed_closure hdom_conv.closure hx
  rcases exists_global_affine_minorant_of_isProper_of_mem_gamma hproper hf with ⟨v, η, hminor⟩
  have hgap : β₀ < ⟪x, u₀⟫_ℝ := by
    exact lt_of_not_ge hx_out
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro M
  let t : ℝ := |M - (⟪x, v⟫_ℝ + η)| / (⟪x, u₀⟫_ℝ - β₀) + 1
  have hgap_pos : 0 < ⟪x, u₀⟫_ℝ - β₀ := by
    linarith
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  let w : H := v + t • u₀
  have hw_conj : f∗ w ≤ ((t * β₀ - η : ℝ) : EReal) := by
    rw [conjugate_apply]
    refine iSup_le ?_
    intro y
    by_cases hy : y ∈ dom f
    · have hy_top : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
      have hy_bot : f y ≠ ⊥ := hproper.1 y
      have hy_half : ⟪y, u₀⟫_ℝ ≤ β₀ := by
        exact hdom_half (subset_closure hy)
      have hminor_real : ⟪y, v⟫_ℝ + η ≤ (f y).toReal := by
        have hcast : (((⟪y, v⟫_ℝ + η : ℝ) : EReal) ≤ (((f y).toReal : ℝ) : EReal)) := by
          exact le_trans (hminor y) (by
            simp [EReal.coe_toReal hy_top hy_bot])
        exact_mod_cast hcast
      have hlinear : ⟪y, w⟫_ℝ - (f y).toReal ≤ t * β₀ - η := by
        dsimp [w]
        rw [inner_add_right, real_inner_smul_right]
        have htbeta : t * ⟪y, u₀⟫_ℝ ≤ t * β₀ := by
          exact mul_le_mul_of_nonneg_left hy_half ht_pos.le
        linarith
      have hcast :
          (((⟪y, w⟫_ℝ : ℝ) : EReal) - (((f y).toReal : ℝ) : EReal)) ≤
            ((t * β₀ - η : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
        exact_mod_cast hlinear
      simpa [EReal.coe_toReal hy_top hy_bot] using hcast
    · rw [value_eq_top_of_not_mem_dom (f := f) hy]
      simp
  have hbase_lt :
      (M : EReal) < (((⟪x, w⟫_ℝ : ℝ) : EReal) - ((t * β₀ - η : ℝ) : EReal)) := by
    have hreal : M < ⟪x, w⟫_ℝ - (t * β₀ - η) := by
      dsimp [w, t]
      rw [inner_add_right, real_inner_smul_right]
      have habs : |M - (⟪x, v⟫_ℝ + η)| < |M - (⟪x, v⟫_ℝ + η)| + (⟪x, u₀⟫_ℝ - β₀) := by
        linarith
      have hEq :
          (|M - (⟪x, v⟫_ℝ + η)| / (⟪x, u₀⟫_ℝ - β₀) + 1) *
              (⟪x, u₀⟫_ℝ - β₀) =
            |M - (⟪x, v⟫_ℝ + η)| + (⟪x, u₀⟫_ℝ - β₀) := by
        field_simp [hgap_pos.ne']
      have hboost :
          |M - (⟪x, v⟫_ℝ + η)| <
            t * (⟪x, u₀⟫_ℝ - β₀) := by
        simpa [t, hEq] using habs
      have hdiff : M - (⟪x, v⟫_ℝ + η) < t * (⟪x, u₀⟫_ℝ - β₀) := by
        exact (abs_lt.mp hboost).2
      linarith
    rw [← EReal.coe_sub]
    exact_mod_cast hreal
  have hterm_le :
      (((⟪x, w⟫_ℝ : ℝ) : EReal) - ((t * β₀ - η : ℝ) : EReal)) ≤ f∗∗ x := by
    have hdefect : (((⟪x, w⟫_ℝ : ℝ) : EReal) - f∗ w) ≤ f∗∗ x := by
      simpa [conjugate_apply, real_inner_comm] using
        (le_iSup (fun y : H ↦ (((⟪y, x⟫_ℝ : ℝ) : EReal) - f∗ y)) w)
    have hsub :
        (((⟪x, w⟫_ℝ : ℝ) : EReal) - ((t * β₀ - η : ℝ) : EReal)) ≤
          (((⟪x, w⟫_ℝ : ℝ) : EReal) - f∗ w) := by
      exact EReal.sub_le_sub le_rfl hw_conj
    exact le_trans hsub hdefect
  exact lt_of_lt_of_le hbase_lt hterm_le

/-- Helper for Corollary 16 19: every proper member of `Γ(H)` lies below its Fenchel biconjugate.
-/
private theorem le_biconjugate_of_isProper_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    f ≤ f∗∗ := by
  intro x
  by_cases hx_closure : x ∈ closure (dom f)
  · refine le_of_forall_lt fun ξ hξ ↦ ?_
    rcases EReal.lt_iff_exists_real_btwn.mp hξ with ⟨ξ₀, hξ_lt, hξ₀_lt⟩
    rcases exists_strict_affine_minorant_of_lt_of_mem_gamma_of_mem_closure_dom
        hproper hf hx_closure hξ₀_lt with ⟨u, η, hminor, hstrict⟩
    exact lt_of_lt_of_le hξ_lt
      (strict_lower_bound_le_biconjugate_of_affine_minorant hminor hstrict)
  · have hx_top : f x = ⊤ := by
      by_contra hx_top
      have hx_dom : x ∈ dom f := (mem_dom_iff_ne_top f x).2 hx_top
      exact hx_closure (subset_closure hx_dom)
    rw [hx_top]
    rw [biconjugate_eq_top_of_not_mem_closure_dom_of_mem_gamma hproper hf hx_closure]

/-- Helper for Corollary 16 19: a proper member of `Γ(H)` coincides with its Fenchel biconjugate.
-/
theorem mem_gamma_iff_eq_biconjugate_of_is_proper
    {f : H → EReal} (hproper : IsProper f) :
    f ∈ Γ(H) ↔ f∗∗ = f := by
  constructor
  · intro hf
    apply le_antisymm
    · exact biconjugate_le f
    · exact le_biconjugate_of_isProper_of_mem_gamma hproper hf
  · intro hEq
    rw [← hEq]
    exact conjugate_mem_gamma (f := f∗)

/-- Helper for Corollary 16 19: Jensen convexity implies convexity of the real-height epigraph.
-/
private theorem convex_epigraph_of_isConvex_local
    {f : H → EReal} (hconv : IsConvex f) :
    Convex ℝ (epigraph f) := by
  refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
  intro x y hx hy α hα hα_lt_one
  exact hconv hα.le hα_lt_one.le

/-- Helper for Corollary 16 19: a point outside the domain of an extended-real-valued function has
value `⊤`. -/
private theorem value_eq_top_of_not_mem_dom_convex
    {f : H → EReal} {x : H} (hx : x ∉ dom f) :
    f x = ⊤ := by
  simpa [mem_dom_iff_ne_top] using hx

/-- Helper for Corollary 16 19: a lower semicontinuous function with convex epigraph and one
finite point cannot take the value `⊥` anywhere on its domain. -/
private theorem ne_bot_of_mem_dom_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
    {g : H → EReal} (hconv : Convex ℝ (epigraph g)) (hlsc : LowerSemicontinuous g)
    {x₀ y : H} (hx₀ : x₀ ∈ effectiveDom g) (hy : y ∈ dom g) :
    g y ≠ ⊥ := by
  intro hy_bot
  have hx₀_fin := (mem_effectiveDom_iff (f := g) (x := x₀)).mp hx₀
  have hx₀_dom : x₀ ∈ dom g := (mem_dom_iff_ne_top g x₀).2 hx₀_fin.1
  let u : ℕ → H := fun n ↦ (1 / (n + 2 : ℝ)) • y + (1 - 1 / (n + 2 : ℝ)) • x₀
  have hu_tendsto : Tendsto u atTop (nhds x₀) :=
    tendsto_reciprocal_convex_combination_to_right y x₀
  have hu_bot : ∀ n : ℕ, g (u n) = ⊥ := by
    intro n
    have hα_pos : 0 < 1 / (n + 2 : ℝ) := by
      exact one_div_pos.mpr (by positivity : (0 : ℝ) < n + 2)
    have hα_lt_one : 1 / (n + 2 : ℝ) < 1 := by
      have h : 1 / (n + 2 : ℝ) < 1 / (1 : ℝ) := by
        refine (one_div_lt_one_div (α := ℝ) ?_ ?_).2 ?_
        · positivity
        · norm_num
        · exact_mod_cast Nat.succ_lt_succ (Nat.succ_pos n)
      simpa using h
    have hineq :
        g (u n) ≤
          ((1 / (n + 2 : ℝ) : ℝ) : EReal) * g y +
            (((1 - 1 / (n + 2 : ℝ) : ℝ) : EReal) * g x₀) := by
      simpa [u] using
        (convex_epigraph_iff_jensen_on_dom g).1 hconv hy hx₀_dom hα_pos hα_lt_one
    have hαE : 0 < (((1 / (n + 2 : ℝ) : ℝ) : EReal)) := EReal.coe_pos.mpr hα_pos
    have hineq_bot : g (u n) ≤ ⊥ := by
      calc
        g (u n)
            ≤ ((1 / (n + 2 : ℝ) : ℝ) : EReal) * g y +
                (((1 - 1 / (n + 2 : ℝ) : ℝ) : EReal) * g x₀) := hineq
        _ = ⊥ + (((1 - 1 / (n + 2 : ℝ) : ℝ) : EReal) * g x₀) := by
          rw [hy_bot, EReal.mul_bot_of_pos hαE]
        _ = ⊥ := by
          rw [EReal.bot_add]
    exact le_bot_iff.mp hineq_bot
  have hseq :
      g x₀ ≤ Filter.liminf (g ∘ u) atTop := by
    calc
      g x₀ ≤ Filter.liminf g (nhds x₀) := hlsc.le_liminf x₀
      _ ≤ Filter.liminf g (Filter.map u atTop) := Filter.liminf_le_liminf_of_le hu_tendsto
      _ = Filter.liminf (g ∘ u) atTop := by rw [Filter.liminf_comp]
  have hconst : (g ∘ u) = fun _ : ℕ ↦ (⊥ : EReal) := by
    funext n
    exact hu_bot n
  rw [hconst, Filter.liminf_const] at hseq
  exact hx₀_fin.2 (le_bot_iff.mp hseq)

/-- Helper for Corollary 16 19: a lower semicontinuous function with convex epigraph and one
finite point is convex in the Jensen sense. -/
private theorem isConvex_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
    {g : H → EReal} (hconv : Convex ℝ (epigraph g)) (hlsc : LowerSemicontinuous g)
    {x₀ : H} (hx₀ : x₀ ∈ effectiveDom g) :
    IsConvex g := by
  intro x y a ha₀ ha₁
  have hcoef_eq : (1 - (a : EReal)) = ((1 - a : ℝ) : EReal) := by
    norm_num
  by_cases ha_zero : a = 0
  · subst ha_zero
    simp
  by_cases ha_one : a = 1
  · subst ha_one
    rw [hcoef_eq]
    simp
  have ha_pos : 0 < a := lt_of_le_of_ne ha₀ (Ne.symm ha_zero)
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha₁ ha_one
  by_cases hx : x ∈ dom g
  · by_cases hy : y ∈ dom g
    · rw [hcoef_eq]
      exact (convex_epigraph_iff_jensen_on_dom g).1 hconv hx hy ha_pos ha_lt_one
    · have hy_top : g y = ⊤ := value_eq_top_of_not_mem_dom_convex (f := g) hy
      have hx_term_ne_bot : (a : EReal) * g x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot a), ?_, Or.inl (EReal.coe_ne_top a),
          Or.inl (EReal.coe_nonneg.mpr ha₀)⟩
        exact Or.inr
          (ne_bot_of_mem_dom_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
            hconv hlsc hx₀ hx)
      have hrhs_top :
          (a : EReal) * g x + (1 - (a : EReal)) * g y = ⊤ := by
        rw [hcoef_eq, hy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
        exact EReal.add_top_of_ne_bot hx_term_ne_bot
      rw [hrhs_top]
      exact le_top
  · have hx_top : g x = ⊤ := value_eq_top_of_not_mem_dom_convex (f := g) hx
    have hy_term_ne_bot : (((1 - a : ℝ) : EReal) * g y) ≠ ⊥ := by
      by_cases hy : y ∈ dom g
      · rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - a)), ?_, Or.inl (EReal.coe_ne_top (1 - a)),
          Or.inl (EReal.coe_nonneg.mpr (sub_nonneg.mpr ha₁))⟩
        exact Or.inr
          (ne_bot_of_mem_dom_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
            hconv hlsc hx₀ hy)
      · have hy_top : g y = ⊤ := value_eq_top_of_not_mem_dom_convex (f := g) hy
        rw [hy_top, EReal.mul_top_of_pos (EReal.coe_pos.mpr (sub_pos.mpr ha_lt_one))]
        simp
    have hrhs_top :
        (a : EReal) * g x + (1 - (a : EReal)) * g y = ⊤ := by
      rw [hx_top, hcoef_eq, EReal.mul_top_of_pos (EReal.coe_pos.mpr ha_pos)]
      exact EReal.top_add_of_ne_bot hy_term_ne_bot
    simp [hrhs_top]

/-- Helper for Corollary 16 19: a lower semicontinuous function with convex epigraph and one
finite point is proper. -/
private theorem isProper_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
    {g : H → EReal} (hconv : Convex ℝ (epigraph g)) (hlsc : LowerSemicontinuous g)
    {x₀ : H} (hx₀ : x₀ ∈ effectiveDom g) :
    IsProper g := by
  have hx₀_fin := (mem_effectiveDom_iff (f := g) (x := x₀)).mp hx₀
  refine ⟨?_, ⟨x₀, (mem_dom_iff_ne_top g x₀).2 hx₀_fin.1⟩⟩
  intro y
  by_cases hy : y ∈ dom g
  · exact
      ne_bot_of_mem_dom_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
        hconv hlsc hx₀ hy
  · simp [value_eq_top_of_not_mem_dom_convex (f := g) hy]

/-- Helper for Corollary 16 19: at a finite lower-semicontinuity point of a convex
extended-real-valued function, the lower semicontinuous convex envelope is the Fenchel
biconjugate. -/
private theorem lowerSemicontinuousConvexEnvelope_eq_biconjugate_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    lowerSemicontinuousConvexEnvelope f = f∗∗ := by
  let g : H → EReal := lowerSemicontinuousConvexEnvelope f
  have hg_lsc : LowerSemicontinuous g := by
    simpa [g] using lowerSemicontinuous_lowerSemicontinuousConvexEnvelope f
  have hg_conv_epi : Convex ℝ (epigraph g) := by
    simpa [g] using convex_epigraph_lowerSemicontinuousConvexEnvelope f
  have hg_eq_fx : g x = f x := by
    have henv_eq_hull :
        lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f :=
      lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
        f (convex_epigraph_of_isConvex_local hconv)
    exact
      (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f x).mp hlsc |>.symm ▸ by
        simp [g, henv_eq_hull]
  have hxg : x ∈ effectiveDom g := by
    rw [mem_effectiveDom_iff] at hx ⊢
    simpa [hg_eq_fx] using hx
  have hg_proper : IsProper g :=
    isProper_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom hg_conv_epi hg_lsc hxg
  have hg_conv : g ∈ Γ(H) := by
    rw [mem_gamma_iff]
    exact ⟨isConvex_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
      hg_conv_epi hg_lsc hxg, hg_lsc⟩
  have hconj : g∗ = f∗ := by
    simpa [g] using conjugate_lowerSemicontinuousConvexEnvelope_eq f
  have hbiconj : g∗∗ = f∗∗ := congrArg conjugate hconj
  calc
    lowerSemicontinuousConvexEnvelope f = g := rfl
    _ = g∗∗ := by
      exact ((mem_gamma_iff_eq_biconjugate_of_is_proper hg_proper).mp hg_conv).symm
    _ = f∗∗ := hbiconj

/-- Helper for Corollary 16 19: at a finite point of a convex extended-real-valued function,
lower semicontinuity is equivalent to equality with the Fenchel biconjugate. -/
theorem lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f) :
    LowerSemicontinuousAt f x ↔ f∗∗ x = f x := by
  constructor
  · intro hlsc
    have henv_eq_biconj :
        lowerSemicontinuousConvexEnvelope f = f∗∗ :=
      lowerSemicontinuousConvexEnvelope_eq_biconjugate_of_lscAt_of_convex_at_finite_point
        hconv hx hlsc
    have henv_eq_hull :
        lowerSemicontinuousConvexEnvelope f = lowerSemicontinuousEnvelope f :=
      lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
        f (convex_epigraph_of_isConvex_local hconv)
    have hhull_eq_self :
        lowerSemicontinuousEnvelope f x = f x :=
      (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f x).mp hlsc
    calc
      f∗∗ x = lowerSemicontinuousConvexEnvelope f x := by
        simpa using congrArg (fun g : H → EReal ↦ g x) henv_eq_biconj.symm
      _ = lowerSemicontinuousEnvelope f x := by
        simpa using congrArg (fun g : H → EReal ↦ g x) henv_eq_hull
      _ = f x := hhull_eq_self
  · intro hEq
    have hbiconj_gamma : f∗∗ ∈ Γ(H) := conjugate_mem_gamma f∗
    have hbiconj_lsc : LowerSemicontinuous (f∗∗) := (mem_gamma_iff (f∗∗)).mp hbiconj_gamma |>.2
    have hbiconj_le_hull :
        f∗∗ ≤ lowerSemicontinuousEnvelope f :=
      (lowerSemicontinuousHull_isGreatest f).2 ⟨hbiconj_lsc, biconjugate_le f⟩
    refine (lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq f x).2 ?_
    apply le_antisymm
    · exact (lowerSemicontinuousHull_isGreatest f).1.2 x
    · calc
        f x = f∗∗ x := hEq.symm
        _ ≤ lowerSemicontinuousEnvelope f x := hbiconj_le_hull x

/-- Helper for Corollary 16 19: at a finite lower-semicontinuity point of a convex
extended-real-valued function, the Fenchel biconjugate is proper. -/
theorem biconjugate_isProper_of_lscAt_of_convex_at_finite_point
    {f : H → EReal} (hconv : IsConvex f) {x : H} (hx : x ∈ effectiveDom f)
    (hlsc : LowerSemicontinuousAt f x) :
    IsProper (f∗∗) := by
  have hbiconj_gamma : f∗∗ ∈ Γ(H) := conjugate_mem_gamma f∗
  have hbiconj_data := (mem_gamma_iff (f∗∗)).mp hbiconj_gamma
  have hx_biconj : x ∈ effectiveDom (f∗∗) := by
    have hEq := (lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point hconv hx).mp hlsc
    rw [mem_effectiveDom_iff] at hx ⊢
    constructor
    · rw [hEq]
      exact hx.1
    · rw [hEq]
      exact hx.2
  exact
    isProper_of_convex_epigraph_of_lowerSemicontinuous_of_mem_effectiveDom
      (convex_epigraph_of_isConvex_local hbiconj_data.1) hbiconj_data.2 hx_biconj

include h hconv D hD_nonempty hD_open hD_convex hD_cont

/-- Helper for Corollary 16 19: every point of the open constraint set lies in the effective
domain of `h`. -/
theorem constraint_subset_effectiveDomain_of_continuity :
    D ⊆ effectiveDomain h := by
  -- Extract the effective-domain component from the assumed continuity-on-domain predicate.
  intro x hx
  exact ContinuousAtOnEffectiveDomain.mem_effectiveDomain (hD_cont hx)

/-- Helper for Corollary 16 19: adding the indicator of `D` cuts the effective domain down exactly
to `D`. -/
theorem effectiveDomain_add_indicator_eq :
    effectiveDomain (h + ι[D]) = D := by
  -- The indicator contributes finiteness exactly on `D`, and the continuity hypothesis supplies
  -- the needed finiteness of `h` there.
  ext x
  constructor
  · intro hx
    simpa [effectiveDomain_indicator] using
      ((mem_effectiveDomain_pointwiseAdd_iff h (ι[D]) x).1 hx).2
  · intro hx
    have hx_indicator : x ∈ effectiveDomain (ι[D]) := by
      simpa using hx
    exact (mem_effectiveDomain_pointwiseAdd_iff h (ι[D]) x).2
      ⟨constraint_subset_effectiveDomain_of_continuity
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx,
        hx_indicator⟩

/-- Helper for Corollary 16 19: the constrained owner `h + ι[D]` is convex on its effective
domain. -/
theorem convexOn_add_indicator :
    ConvexOn (h + ι[D]) (effectiveDomain (h + ι[D])) := by
  -- Rewrite the effective domain as `D`, where the constrained function agrees with `h`.
  rw [effectiveDomain_add_indicator_eq
    (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
    (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)]
  refine ⟨hD_nonempty, ?_, ?_⟩
  · intro x hx
    simpa [effectiveDomain_add_indicator_eq
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hx
  · intro x hx y hy α hα0 hα1
    have hcombo : α • x + (1 - α) • y ∈ D := by
      refine hD_convex hx hy hα0.le (sub_nonneg.mpr hα1.le) ?_
      ring
    have hineq :=
      hconv.ineq
        (constraint_subset_effectiveDomain_of_continuity
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx)
        (constraint_subset_effectiveDomain_of_continuity
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hy)
        hα0 hα1
    simpa [hx, hy, hcombo] using hineq

/-- Helper for Corollary 16 19: the `EReal` coercion of `h + ι[D]` is globally convex. -/
theorem isConvex_asEReal_add_indicator :
    IsConvex ((h + ι[D]).asEReal) := by
  -- Route correction: obtain global convexity by passing through the convex real-height epigraph
  -- of the constrained owner and then applying the Chapter 10 epigraph bridge.
  exact isConvex_of_convex_epigraph (h + ι[D])
    ((convexOn_add_indicator
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)).convex_epigraph_asEReal)

/-- Helper for Corollary 16 19: points of `D` remain continuity points after adding the indicator
of `D`. -/
theorem continuousAtOnEffectiveDomain_add_indicator_of_mem_D
    {x : H} (hx : x ∈ D) :
    ContinuousAtOnEffectiveDomain (h + ι[D]) x := by
  -- Restrict the original continuity datum from `effectiveDomain h` down to `D`, where the
  -- indicator term vanishes identically.
  have hxcont_h :
      ContinuousWithinAt (fun y : H ↦ (h y : EReal).toReal) (effectiveDomain h) x :=
    (hD_cont hx).continuousWithinAt
  have hxcont_D_h :
      ContinuousWithinAt (fun y : H ↦ (h y : EReal).toReal) D x :=
    hxcont_h.mono (constraint_subset_effectiveDomain_of_continuity
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
  have hxcont_D_g :
      ContinuousWithinAt (fun y : H ↦ (((h + ι[D]) y : EReal).toReal)) D x := by
    refine hxcont_D_h.congr_of_mem ?_ hx
    intro y hy
    simp [hy]
  refine ⟨?_, ?_⟩
  · simpa [effectiveDomain_add_indicator_eq
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hx
  · simpa [effectiveDomain_add_indicator_eq
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hxcont_D_g

/-- Helper for Corollary 16 19: the real-valued finite representative of `h + ι[D]` is continuous
on `D`. -/
theorem continuousOn_toReal_add_indicator :
    ContinuousOn (fun x : H ↦ (((h + ι[D]) x : Set.Ioi (⊥ : EReal)) : EReal).toReal) D := by
  -- Package the pointwise continuity-on-domain bridge into the `ContinuousOn` API shape required
  -- by Proposition 9.33.
  intro x hx
  simpa [effectiveDomain_add_indicator_eq
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using
    (continuousAtOnEffectiveDomain_add_indicator_of_mem_D
      h hconv D hD_nonempty hD_open hD_convex hD_cont hx).continuousWithinAt

/-- Helper for Corollary 16 19: continuity points of `h + ι[D]` on `D` are lower semicontinuity
points of its `EReal` coercion. -/
theorem lowerSemicontinuousAt_asEReal_add_indicator_of_mem_D
    {x : H} (hx : x ∈ D) :
    LowerSemicontinuousAt ((h + ι[D]).asEReal) x := by
  -- Continuity on the constrained effective domain gives a subgradient at `x`.
  have hxcont :
      ContinuousAtOnEffectiveDomain (h + ι[D]) x :=
    continuousAtOnEffectiveDomain_add_indicator_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx
  rcases
      (subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
        (h + ι[D])
        (convexOn_add_indicator
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
        hxcont).1 with
    ⟨u, hu⟩
  -- Proposition 16.4 converts the subgradient witness into lower semicontinuity.
  exact SubdifferentiableAt.lowerSemicontinuousAt (show SubdifferentiableAt (h + ι[D]) x from
    ⟨u, hu⟩)

/-- Helper for Corollary 16 19: a subgradient of `h + ι[D]` yields a continuous affine minorant of
its `EReal` coercion with the same slope. -/
theorem hasContinuousAffineMinorantWithSlope_asEReal_add_indicator_of_mem_subdifferential
    {x u : H} (hu : u ∈ (∂ (h + ι[D])) x) :
    HasContinuousAffineMinorantWithSlope ((h + ι[D]).asEReal) u := by
  have hdom : (effectiveDomain (h + ι[D])).Nonempty := by
    let y : H := hD_nonempty.choose
    have hy : y ∈ D := hD_nonempty.choose_spec
    refine ⟨y, ?_⟩
    simpa [effectiveDomain_add_indicator_eq
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hy
  have hx_sub : x ∈ SetValuedOperator.dom (∂ (h + ι[D])) := by
    -- The chosen subgradient witnesses subdifferentiability at `x`.
    exact ⟨u, hu⟩
  have hx_dom : x ∈ effectiveDomain (h + ι[D]) :=
    subdifferential_domain_subset_effectiveDomain (h + ι[D]) hdom hx_sub
  let fx : EReal := (((h + ι[D]) x : Set.Ioi (⊥ : EReal)) : EReal)
  have hx_top : fx ≠ ⊤ := by
    exact ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
  have hx_bot : fx ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (((h + ι[D]) x : Set.Ioi (⊥ : EReal)) : EReal) from
      ((h + ι[D]) x).2)
  rw [mem_subdifferential_iff] at hu
  let η : ℝ := fx.toReal - ⟪x, u⟫_ℝ
  refine ⟨η, ?_⟩
  intro y
  have hshift :
      (((⟪y, u⟫_ℝ + η : ℝ) : EReal)) =
        (⟪y - x, u⟫_ℝ : EReal) + fx := by
    -- Recenter the affine formula at `x` exactly as in Corollary 16.18.
    calc
      (((⟪y, u⟫_ℝ + η : ℝ) : EReal)) =
          (((⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ + fx.toReal : ℝ) : EReal)) := by
            simp [η, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (((⟪y - x, u⟫_ℝ + fx.toReal : ℝ) : EReal)) := by
            rw [inner_sub_left]
      _ = (⟪y - x, u⟫_ℝ : EReal) + (((fx.toReal : ℝ) : EReal)) := by
            rw [EReal.coe_add]
      _ = (⟪y - x, u⟫_ℝ : EReal) + fx := by
            rw [EReal.coe_toReal hx_top hx_bot]
  -- After recentering, the minorant inequality is the defining subgradient inequality.
  rw [hshift]
  change
    (⟪y - x, u⟫_ℝ : EReal) + ((((h + ι[D]) x : Set.Ioi (⊥ : EReal)) : EReal)) ≤
      ((((h + ι[D]) y : Set.Ioi (⊥ : EReal)) : EReal))
  exact hu y

/-- Helper for Corollary 16 19: the conjugate domain of the constrained owner is nonempty. -/
theorem dom_conjugate_nonempty_add_indicator :
    (dom (((h + ι[D]).asEReal)∗)).Nonempty := by
  let y : H := hD_nonempty.choose
  have hy : y ∈ D := hD_nonempty.choose_spec
  have hycont :
      ContinuousAtOnEffectiveDomain (h + ι[D]) y :=
    continuousAtOnEffectiveDomain_add_indicator_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hy
  rcases
      (subdifferential_nonempty_and_weaklyCompact_of_continuousAtOnEffectiveDomain
        (h + ι[D])
        (convexOn_add_indicator
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
        hycont).1 with
    ⟨u, hu⟩
  refine ⟨u, ?_⟩
  -- Proposition 13.12 turns the affine minorant into conjugate-domain membership.
  exact
    (mem_dom_conjugate_iff_hasContinuousAffineMinorantWithSlope ((h + ι[D]).asEReal) u).2
      (hasContinuousAffineMinorantWithSlope_asEReal_add_indicator_of_mem_subdifferential
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hu)

/-- Helper for Corollary 16 19: coercing `h + ι[D]` to `EReal` does not change its finite domain.
-/
theorem dom_asEReal_add_indicator_eq :
    dom ((h + ι[D]).asEReal) = D := by
  -- Both sides express the same finiteness condition for the constrained owner.
  ext x
  constructor
  · intro hx
    have hx_ne_top : ((h + ι[D]).asEReal x) ≠ ⊤ := (mem_dom_iff_ne_top _ _).1 hx
    have hx_eff : x ∈ effectiveDomain (h + ι[D]) := by
      rw [mem_effectiveDomain_iff]
      exact lt_of_le_of_ne le_top hx_ne_top
    simpa [effectiveDomain_add_indicator_eq
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hx_eff
  · intro hx
    have hx_eff : x ∈ effectiveDomain (h + ι[D]) := by
      simpa [effectiveDomain_add_indicator_eq
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hx
    exact (mem_dom_iff_ne_top _ _).2 (ne_of_lt (mem_effectiveDomain_iff.mp hx_eff))

/-- Helper for Corollary 16 19: every point of `D` is a finite point of the `EReal`-valued
constrained owner. -/
theorem mem_effectiveDom_asEReal_add_indicator_of_mem_D
    {x : H} (hx : x ∈ D) :
    x ∈ effectiveDom ((h + ι[D]).asEReal) := by
  have hx_eff : x ∈ effectiveDomain (h + ι[D]) := by
    simpa [effectiveDomain_add_indicator_eq
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hx
  rw [mem_effectiveDom_iff]
  constructor
  · exact ne_of_lt (by simpa [Function.asEReal_apply] using (mem_effectiveDomain_iff.mp hx_eff))
  · exact ne_of_gt (by simpa [Function.asEReal_apply] using ((h + ι[D]) x).2)

/-- Helper for Corollary 16 19: points on the segment from a closure point to an interior point of
`D` lie in `D` for all sufficiently small positive parameters. -/
theorem lineMap_eventually_mem_D_of_mem_closure_of_mem_D
    {x y : H} (hx : x ∈ closure D) (hy : y ∈ D) :
    ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), AffineMap.lineMap x y α ∈ D := by
  -- Proposition 3.44 places the punctured segment inside the interior of `D`, and openness
  -- identifies `interior D` with `D`.
  have hy_int : y ∈ interior D := by
    simpa [hD_open.interior_eq] using hy
  have hα_lt_one : ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), α < 1 := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin, hα_lt_one] with α hα_pos hα_lt_one
  have hseg :
      AffineMap.lineMap y x (1 - α) ∈ interior D := by
    have hα_mem : 1 - α ∈ Set.Ico (0 : ℝ) 1 := by
      exact ⟨sub_nonneg.mpr hα_lt_one.le, sub_lt_self 1 hα_pos⟩
    exact lineMap_mem_interior_of_mem_Ico_of_mem_interior_of_mem_closure
      hD_convex hy_int hx hα_mem
  have hline :
      AffineMap.lineMap y x (1 - α) = AffineMap.lineMap x y α := by
    simp [AffineMap.lineMap_apply_one_sub]
  exact hline ▸ interior_subset hseg

/-- Helper for Corollary 16 19: the lower semicontinuous convex envelope of the constrained
`EReal` owner agrees with its Fenchel biconjugate. -/
theorem lowerSemicontinuousConvexEnvelope_eq_biconjugate_add_indicator :
    lowerSemicontinuousConvexEnvelope ((h + ι[D]).asEReal) = ((h + ι[D]).asEReal)∗∗ := by
  let y : H := hD_nonempty.choose
  have hy : y ∈ D := hD_nonempty.choose_spec
  have hy_effDom :
      y ∈ effectiveDom ((h + ι[D]).asEReal) :=
    mem_effectiveDom_asEReal_add_indicator_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hy
  have hy_lsc :
      LowerSemicontinuousAt ((h + ι[D]).asEReal) y :=
    lowerSemicontinuousAt_asEReal_add_indicator_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hy
  exact
    lowerSemicontinuousConvexEnvelope_eq_biconjugate_of_lscAt_of_convex_at_finite_point
      (f := (h + ι[D]).asEReal)
      (isConvex_asEReal_add_indicator
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
      hy_effDom hy_lsc

/-- Helper for Corollary 16 19: at each point of `D`, Proposition 16.5 identifies the
biconjugate of the constrained owner with `h`. -/
theorem biconjugate_add_indicator_eq_at_mem_D
    {x : H} (hx : x ∈ D) :
    (((h + ι[D]).asEReal)∗∗ x) = h.asEReal x := by
  have hx_effDom :
      x ∈ effectiveDom ((h + ι[D]).asEReal) :=
    mem_effectiveDom_asEReal_add_indicator_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx
  have hx_lsc :
      LowerSemicontinuousAt ((h + ι[D]).asEReal) x :=
    lowerSemicontinuousAt_asEReal_add_indicator_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx
  -- Proposition 13.44 identifies the biconjugate with the constrained owner at finite
  -- lower-semicontinuity points.
  have hx_eq_owner :
      (((h + ι[D]).asEReal)∗∗ x) = ((h + ι[D]).asEReal x) :=
    (lscAt_iff_biconjugate_eq_self_of_convex_at_finite_point
      (f := (h + ι[D]).asEReal)
      (isConvex_asEReal_add_indicator
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
      hx_effDom).mp hx_lsc
  -- On `D`, the indicator vanishes, so the constrained owner agrees with `h`.
  simpa [hx] using hx_eq_owner

-- Proof sketch: pick a continuity point `y ∈ D`, use continuity to identify
-- `(h.asEReal + (ι[D]).asEReal)∗∗ y` with `h y`, and then apply the finite-point
-- biconjugation theorem to obtain properness of the biconjugate.
/-- The biconjugate of `h + ι_D` is proper once `D` is a nonempty open convex subset of the
effective-domain continuity set of `h`. -/
theorem isProper_biconjugate_add_indicator_of_open_convex_subset_continuity
    : IsProper (((h + ι[D]).asEReal)∗∗) := by
  let y : H := hD_nonempty.choose
  have hy : y ∈ D := hD_nonempty.choose_spec
  have hy_effDom :
      y ∈ effectiveDom ((h + ι[D]).asEReal) :=
    mem_effectiveDom_asEReal_add_indicator_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hy
  have hy_lsc :
      LowerSemicontinuousAt ((h + ι[D]).asEReal) y :=
    lowerSemicontinuousAt_asEReal_add_indicator_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hy
  exact
    biconjugate_isProper_of_lscAt_of_convex_at_finite_point
      (f := (h + ι[D]).asEReal)
      (isConvex_asEReal_add_indicator
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
      hy_effDom hy_lsc

-- Proof sketch: combine properness of `(h + ι[D])∗∗` with the general
-- fact that every Fenchel conjugate belongs to `Γ(H)`, then apply this to the conjugate
-- `conjugate (h + ι[D])`.
/-- The biconjugate of `h + ι_D` belongs to the convex lower-semicontinuous class `Γ(H)`. -/
theorem biconjugate_add_indicator_mem_gamma_of_open_convex_subset_continuity
    : ((h + ι[D]).asEReal)∗∗ ∈ gamma H := by
  -- The Fenchel conjugate of any extended-real-valued function lies in `Γ(H)`.
  exact conjugate_mem_gamma (((h + ι[D]).asEReal)∗)

-- Proof sketch: continuity points in `D` are subdifferentiability points for `h + ι[D]`, so the
-- biconjugate agrees with `h` there and has a nonempty affine-minorant set. Proposition
-- 13.46 then yields the domain inclusion into `closure D`.
/-- The effective domain of the biconjugate of `h + ι_D` is contained in `closure D`. -/
theorem dom_biconjugate_add_indicator_subset_closure_of_open_convex_subset_continuity
    : dom (((h + ι[D]).asEReal)∗∗) ⊆ closure D := by
  have hdom_env :
      dom (lowerSemicontinuousConvexEnvelope ((h + ι[D]).asEReal)) ⊆ closure D := by
    calc
      dom (lowerSemicontinuousConvexEnvelope ((h + ι[D]).asEReal))
          ⊆ closure (convexHull ℝ (dom ((h + ι[D]).asEReal))) :=
        dom_lowerSemicontinuousConvexEnvelope_subset_closure_convexHull_dom
          ((h + ι[D]).asEReal)
      _ = closure (convexHull ℝ D) := by
        rw [dom_asEReal_add_indicator_eq
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)]
      _ = closure D := by
        rw [hD_convex.convexHull_eq]
  -- Replace the lower semicontinuous convex envelope by the biconjugate using the finite-point
  -- equality already established above.
  simpa [lowerSemicontinuousConvexEnvelope_eq_biconjugate_add_indicator
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hdom_env

-- Proof sketch: every point of `D` is a continuity point of `h + ι[D]`, hence a
-- subdifferentiability point. Proposition 16.5 identifies the biconjugate with the original
-- function at such points, and `h + ι[D]` agrees there with `h`.
/-- On `D`, the biconjugate of `h + ι_D` agrees with `h`. -/
theorem biconjugate_add_indicator_eqOn_domain_of_open_convex_subset_continuity
    : EqOn (((h + ι[D]).asEReal)∗∗) h.asEReal D := by
  intro x hx
  exact biconjugate_add_indicator_eq_at_mem_D
    (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
    (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx

-- Proof sketch: apply Corollary 16.19 to the canonical constrained function `h + ι[D]`, then
-- identify the resulting `Γ₀(H)` extension with the Chapter 9 boundary-liminf extension owner.
/-- The canonical constrained biconjugate from Corollary 16.19 is exactly the Chapter 9
boundary-liminf extension of `h + ι_D`. -/
theorem biconjugate_add_indicator_eq_boundaryLiminfExtensionEReal_of_open_convex_subset_continuity
    : ((h + ι[D]).asEReal)∗∗ = boundaryLiminfExtensionEReal (h + ι[D]) := by
  -- Route correction: rewrite both owners through the same lower semicontinuous convex envelope.
  calc
    ((h + ι[D]).asEReal)∗∗ =
        lowerSemicontinuousConvexEnvelope ((h + ι[D]).asEReal) := by
      symm
      exact lowerSemicontinuousConvexEnvelope_eq_biconjugate_add_indicator
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)
    _ = boundaryLiminfExtensionEReal (h + ι[D]) := by
      symm
      exact boundaryLiminfExtensionEReal_eq_lowerSemicontinuousConvexEnvelope
        (h + ι[D])
        (convexOn_add_indicator
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
        (by
          simpa [effectiveDomain_add_indicator_eq
            (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
            (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hD_open)
        (by
          simpa [effectiveDomain_add_indicator_eq
            (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
            (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using
            continuousOn_toReal_add_indicator
              (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
              (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))

/-- Helper for Corollary 16 19: if `f` agrees with `h` on `D`, then every point of `D` lies in
the effective domain of `f`. -/
theorem subset_effectiveDomain_of_eqOn
    {f : H → Set.Ioi (⊥ : EReal)} (hEq : EqOn f h D) :
    D ⊆ effectiveDomain f := by
  -- Points of `D` are finite for `h` by the continuity hypothesis, and the trace equality carries
  -- that finiteness over to `f`.
  intro x hx
  have hx_h : x ∈ effectiveDomain h :=
    constraint_subset_effectiveDomain_of_continuity
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx
  rw [mem_effectiveDomain_iff]
  simpa [Function.asEReal_apply, hEq hx] using (mem_effectiveDomain_iff.mp hx_h)

section

omit h hconv D hD_nonempty hD_open hD_convex hD_cont

/-- Helper for Corollary 16 19: a `Γ₀(H)` function agrees with its right-sided segment trace at
every closure point of its effective domain. -/
theorem tendsto_lineMap_to_value_at_mem_closure_effectiveDomain_of_mem_gammaZero
    {g : H → Set.Ioi (⊥ : EReal)} {x : H} (hg : g ∈ Γ₀(H))
    (hx : x ∈ closure (effectiveDomain g)) (y : effectiveDomain g) :
    Tendsto (fun α : ℝ ↦ (g (AffineMap.lineMap x y α) : EReal))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (g x : EReal)) := by
  let _ := hx
  rcases (mem_gammaZero_iff.mp hg) with ⟨hg_lsc, _hg_conv⟩
  by_cases hx_dom : x ∈ effectiveDomain g
  · -- At finite endpoints, Proposition 9.14 gives the segment limit directly.
    exact
      tendsto_apply_lineMap_right_zero_of_lowerSemicontinuous_epigraph_convex
        hg_lsc
        (convex_epigraph_asEReal_of_mem_gammaZero hg)
        (mem_effectiveDomain_iff.mp hx_dom)
        (mem_effectiveDomain_iff.mp y.2)
  · have hx_top : (g x : EReal) = ⊤ := by
      -- Outside the effective domain, an `]-∞,+∞]`-valued function can only take the value `+∞`.
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx_dom))
    rw [hx_top, EReal.tendsto_nhds_top_iff_real]
    intro ξ
    have hline_tendsto :
        Tendsto (fun α : ℝ ↦ AffineMap.lineMap x y α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds x) := by
      -- The affine segment map is continuous and evaluates to `x` at `0`.
      simpa using
        ((AffineMap.lineMap_continuous (p := x) (q := (y : H))).tendsto (0 : ℝ)).mono_left
          nhdsWithin_le_nhds
    have hlevel_closed : IsClosed (lowerLevelSet g.asEReal ξ) := by
      -- Lower semicontinuity turns every lower level set into a closed set.
      exact (lowerSemicontinuous_iff_isClosed_lowerLevelSet g.asEReal).1 hg_lsc ξ
    have hx_not_level : x ∉ lowerLevelSet g.asEReal ξ := by
      intro hx_level
      rw [mem_lowerLevelSet_iff] at hx_level
      have htop_le : (⊤ : EReal) ≤ (ξ : EReal) := by
        simpa [hx_top] using hx_level
      exact (not_le_of_gt (EReal.coe_lt_top ξ)) htop_le
    have havoid :
        ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          AffineMap.lineMap x y α ∉ lowerLevelSet g.asEReal ξ := by
      -- A path converging to a point outside a closed set eventually avoids that set.
      exact hline_tendsto.eventually (hlevel_closed.isOpen_compl.mem_nhds hx_not_level)
    -- Eventual avoidance of every lower level set is exactly the `+∞` convergence criterion.
    exact havoid.mono fun α hα ↦ by
      rw [mem_lowerLevelSet_iff] at hα
      exact lt_of_not_ge hα

end

/-- Helper for Corollary 16 19: the canonical boundary-liminf extension of `h + ι[D]` is the
right-sided segment limit along every segment from `closure D` to a point of `D`. -/
theorem tendsto_lineMap_to_boundaryLiminfExtension_of_mem_closure_of_mem_D
    {x y : H} (hx : x ∈ closure D) (hy : y ∈ D) :
    Tendsto (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (boundaryLiminfExtensionEReal (h + ι[D]) x)) := by
  let fext : H → Set.Ioi (⊥ : EReal) :=
    boundaryLiminfExtension
      (h + ι[D])
      (convexOn_add_indicator
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
      (by
        simpa [effectiveDomain_add_indicator_eq
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hD_open)
      (by
        simpa [effectiveDomain_add_indicator_eq
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using
          continuousOn_toReal_add_indicator
            (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
            (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
  have hfext_gamma : fext ∈ Γ₀(H) :=
    boundaryLiminfExtension_mem_gammaZero
      (h + ι[D])
      (convexOn_add_indicator
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
      (by
        simpa [effectiveDomain_add_indicator_eq
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hD_open)
      (by
        simpa [effectiveDomain_add_indicator_eq
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using
          continuousOn_toReal_add_indicator
            (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
            (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
  have hdom_subset : D ⊆ effectiveDomain fext := by
    intro z hz
    have hz_dom : z ∈ effectiveDomain (h + ι[D]) := by
      simpa [effectiveDomain_add_indicator_eq
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hz
    -- On the original domain, the boundary extension uses the finite interior branch.
    rw [mem_effectiveDomain_iff, boundaryLiminfExtension_coe]
    simpa [boundaryLiminfExtensionEReal_of_mem_effectiveDomain (h + ι[D]) hz_dom] using
      (mem_effectiveDomain_iff.mp hz_dom)
  have hx_ext_closure : x ∈ closure (effectiveDomain fext) := closure_mono hdom_subset hx
  have hy_ext : y ∈ effectiveDomain fext := hdom_subset hy
  have htrace_ext :
      Tendsto (fun α : ℝ ↦ (fext (AffineMap.lineMap x y α) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (fext x : EReal)) := by
    -- Apply the generic closure-point `Γ₀(H)` segment theorem to the boundary owner itself.
    exact
      tendsto_lineMap_to_value_at_mem_closure_effectiveDomain_of_mem_gammaZero
        (g := fext) (x := x) hfext_gamma hx_ext_closure ⟨y, hy_ext⟩
  have hEq :
      (fun α : ℝ ↦ (fext (AffineMap.lineMap x y α) : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal)) := by
    filter_upwards
      [lineMap_eventually_mem_D_of_mem_closure_of_mem_D
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx hy] with α hαD
    have hline_dom : AffineMap.lineMap x y α ∈ effectiveDomain (h + ι[D]) := by
      simpa [effectiveDomain_add_indicator_eq
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hαD
    -- Along the punctured segment, the boundary extension is on its interior branch and `ι[D]`
    -- vanishes.
    calc
      (fext (AffineMap.lineMap x y α) : EReal)
          = boundaryLiminfExtensionEReal (h + ι[D]) (AffineMap.lineMap x y α) := by
            rw [boundaryLiminfExtension_coe]
      _ = ((h + ι[D]) (AffineMap.lineMap x y α) : EReal) :=
        boundaryLiminfExtensionEReal_of_mem_effectiveDomain (h + ι[D]) hline_dom
      _ = h (AffineMap.lineMap x y α) := by
        simp [hαD]
  have htrace :
      Tendsto (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (fext x : EReal)) :=
    Filter.Tendsto.congr' hEq htrace_ext
  -- The target value is the explicit `EReal` branch of the same boundary owner.
  simpa [fext, boundaryLiminfExtension_coe] using htrace

/-- Helper for Corollary 16 19: every `Γ₀(H)` extension supported in `closure D` and agreeing with
`h` on `D` is the same boundary-liminf owner as `h + ι[D]`. -/
theorem eq_boundaryLiminfExtensionEReal_of_mem_gammaZero_subset_closure_eqOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdom : effectiveDomain f ⊆ closure D) (hEq : EqOn f h D) :
    f.asEReal = boundaryLiminfExtensionEReal (h + ι[D]) := by
  let y : H := hD_nonempty.choose
  have hy : y ∈ D := hD_nonempty.choose_spec
  funext x
  rw [Function.asEReal_apply]
  by_cases hx : x ∈ closure D
  · have hsubset_eff :
        D ⊆ effectiveDomain f :=
      subset_effectiveDomain_of_eqOn
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hEq
    have hx_eff_closure : x ∈ closure (effectiveDomain f) := closure_mono hsubset_eff hx
    have hy_eff : y ∈ effectiveDomain f := hsubset_eff hy
    have hf_trace :
        Tendsto (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (f x : EReal)) := by
      have hf_line :
          Tendsto (fun α : ℝ ↦ (f (AffineMap.lineMap x y α) : EReal))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (f x : EReal)) :=
        tendsto_lineMap_to_value_at_mem_closure_effectiveDomain_of_mem_gammaZero
          (g := f) (x := x) hf hx_eff_closure ⟨y, hy_eff⟩
      have hline_eq :
          (fun α : ℝ ↦ (f (AffineMap.lineMap x y α) : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
            (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal)) := by
        filter_upwards
          [lineMap_eventually_mem_D_of_mem_closure_of_mem_D
            (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
            (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx hy] with α hαD
        simpa [Function.asEReal_apply] using
          congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) (hEq hαD)
      -- Both traces agree eventually on the punctured segment inside `D`.
      exact Filter.Tendsto.congr' hline_eq hf_line
    have hboundary_trace :
        Tendsto (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (boundaryLiminfExtensionEReal (h + ι[D]) x)) :=
      tendsto_lineMap_to_boundaryLiminfExtension_of_mem_closure_of_mem_D
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx hy
    -- Uniqueness of limits identifies the two owners at the closure point.
    exact tendsto_nhds_unique hf_trace hboundary_trace
  · have hx_not_eff : x ∉ effectiveDomain f := by
      intro hx_eff
      exact hx (hdom hx_eff)
    have hfx_top : (f x : EReal) = ⊤ := by
      -- Outside the effective domain, the only possible value is `+∞`.
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx_not_eff))
    have hx_not_eff_add : x ∉ effectiveDomain (h + ι[D]) := by
      intro hx_eff_add
      exact hx <| subset_closure <| by
        simpa [effectiveDomain_add_indicator_eq
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hx_eff_add
    have hx_not_frontier : x ∉ frontier (effectiveDomain (h + ι[D])) := by
      intro hx_frontier
      exact hx <| by
        simpa [effectiveDomain_add_indicator_eq
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)] using hx_frontier.1
    have hboundary_top : boundaryLiminfExtensionEReal (h + ι[D]) x = ⊤ := by
      -- Away from `closure D`, the boundary-liminf extension is on its exterior branch.
      simp [boundaryLiminfExtensionEReal, hx_not_eff_add, hx_not_frontier]
    rw [hfx_top, hboundary_top]

-- Proof sketch: first show that `(h + ι[D])∗∗` itself has the three
-- required properties: it belongs to `Γ(H)` and is proper, its domain lies in `closure D`, and it
-- agrees with `h` on `D`. Then compare any other `Γ₀(H)` extension `f` with the same support and
-- trace, and use the boundary-limit formula along segments from `D` to force pointwise equality.
/-- Corollary 16 19: if `h` is convex and `D` is a nonempty open convex subset of the
effective-domain continuity set of `h`, then every `Γ₀(H)` function whose effective domain is
contained in `closure D` and which agrees with `h` on `D` coincides with `(h + ι_D)^{**}`. -/
theorem eq_biconjugate_add_indicator_of_mem_gammaZero_subset_closure_eqOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdom : effectiveDomain f ⊆ closure D) (hEq : EqOn f h D) :
    f.asEReal = ((h + ι[D]).asEReal)∗∗ := by
  -- Route correction: compare `f` with the canonical boundary-liminf owner first, then rewrite
  -- that owner back to the constrained biconjugate.
  calc
    f.asEReal = boundaryLiminfExtensionEReal (h + ι[D]) :=
      eq_boundaryLiminfExtensionEReal_of_mem_gammaZero_subset_closure_eqOn
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)
        hf hdom hEq
    _ = ((h + ι[D]).asEReal)∗∗ := by
      symm
      exact
        biconjugate_add_indicator_eq_boundaryLiminfExtensionEReal_of_open_convex_subset_continuity
          (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
          (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont)

-- Proof sketch: once the domain inclusion is known, points outside `closure D` lie outside the
-- domain of the biconjugate and therefore take the value `+∞`.
/-- Outside `closure D`, the biconjugate of `h + ι_D` takes the value `+∞`. -/
theorem biconjugate_add_indicator_eq_top_of_not_mem_closure
    {x : H} (hx : x ∉ closure D) :
    ((h + ι[D]).asEReal)∗∗ x = ⊤ := by
  have hx_not_dom : x ∉ dom (((h + ι[D]).asEReal)∗∗) := by
    intro hx_dom
    exact hx <|
      dom_biconjugate_add_indicator_subset_closure_of_open_convex_subset_continuity
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx_dom
  -- Outside the domain, the only possible value is `+∞`.
  exact le_antisymm le_top ((not_lt.mp (by simpa [dom] using hx_not_dom) : ⊤ ≤ _))

-- Proof sketch: if `x ∈ closure D` and `y ∈ D`, Proposition 3.44 keeps the punctured segment
-- `]x,y]` inside `D`, where the biconjugate agrees with `h`. Apply Proposition 9.14 to the
-- `Γ₀(H)` extension `((h + ι[D]).asEReal)∗∗` to identify its value at `x`
-- with the
-- right limit along that segment.
/-- At points of `closure D`, the biconjugate of `h + ι_D` is the right-limit of the values of
`h` along any segment from `x` to a point `y ∈ D`. -/
theorem tendsto_add_indicator_lineMap_to_biconjugate_of_mem_closure
    {x y : H} (hx : x ∈ closure D) (hy : y ∈ D) :
    Tendsto (fun α : ℝ ↦ (h (AffineMap.lineMap x y α) : EReal))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((h + ι[D]).asEReal)∗∗ x)) := by
  -- Rewrite the limit value through the canonical boundary-liminf owner and invoke the
  -- segment-limit theorem already established for that owner.
  have hEq :
      ((h + ι[D]).asEReal)∗∗ x = boundaryLiminfExtensionEReal (h + ι[D]) x := by
    exact congrArg (fun g : H → EReal ↦ g x)
      (biconjugate_add_indicator_eq_boundaryLiminfExtensionEReal_of_open_convex_subset_continuity
        (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
        (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont))
  rw [hEq]
  exact
    tendsto_lineMap_to_boundaryLiminfExtension_of_mem_closure_of_mem_D
      (h := h) (hconv := hconv) (D := D) (hD_nonempty := hD_nonempty)
      (hD_open := hD_open) (hD_convex := hD_convex) (hD_cont := hD_cont) hx hy

end Corollary_16_19

end ERealFunction

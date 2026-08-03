import Mathlib
import BauschkeLean.Chap01.Definition_1_4
import BauschkeLean.Chap01.Lemma_1_24
import BauschkeLean.Chap07.Corollary_7_12
import BauschkeLean.Chap08.Proposition_8_2
import BauschkeLean.Chap08.Proposition_8_4
import BauschkeLean.Chap09.Definition_9_2
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap09.Proposition_9_8
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap13.Proposition_13_12
import BauschkeLean.Chap13.Proposition_13_13
import BauschkeLean.Chap13.Proposition_13_15
import BauschkeLean.Chap13.Proposition_13_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

omit [CompleteSpace H] in
/-- Helper for Theorem 13 37: a function in `Γ(H)` already equals its lower semicontinuous convex
envelope. -/
private theorem lowerSemicontinuousConvexEnvelope_eq_self_of_mem_gamma
    {f : H → EReal} (hf : f ∈ Γ(H)) :
    lowerSemicontinuousConvexEnvelope f = f := by
  rcases (mem_gamma_iff f).mp hf with ⟨hf_conv, hf_lsc⟩
  have hf_conv_epi : Convex ℝ (epigraph f) := by
    -- Rewrite Jensen convexity into the real-height epigraph formulation used by Chapter 9.
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro x y hx hy a ha ha_lt_one
    exact hf_conv (x := x) (y := y) ha.le ha_lt_one.le
  apply le_antisymm
  · -- Proposition 9.8 always places the envelope below the original function.
    exact lowerSemicontinuousConvexEnvelope_le f
  · -- The original function itself is one admissible lower semicontinuous convex minorant.
    exact
      le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
        hf_lsc hf_conv_epi le_rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 13 37: a domain point yields the canonical real-height epigraph point at
`toReal`. -/
private theorem mem_epigraph_toReal_of_mem_dom
    {f : H → EReal} (hproper : IsProper f) {x : H} (hx : x ∈ dom f) :
    (x, (f x).toReal) ∈ epigraph f := by
  -- Properness removes the `⊥` branch, and domain membership removes the `⊤` branch.
  have hx_top : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
  have hx_bot : f x ≠ ⊥ := hproper.1 x
  rw [mem_epigraph_iff]
  simp [EReal.coe_toReal hx_top hx_bot]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 13 37: points outside the domain are exactly the `⊤`-valued points. -/
private theorem value_eq_top_of_not_mem_dom
    {f : H → EReal} {x : H} (hx : x ∉ dom f) :
    f x = ⊤ := by
  -- This is just the complement form of domain membership.
  simpa using (not_mem_dom_iff f x).mp hx

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 13 37: properness provides one real-height epigraph point. -/
private theorem exists_mem_epigraph_of_isProper
    {f : H → EReal} (hproper : IsProper f) :
    (epigraph f).Nonempty := by
  rcases hproper.2 with ⟨x, hx⟩
  refine ⟨(x, (f x).toReal), ?_⟩
  -- Evaluate the canonical real ordinate at the domain witness.
  exact mem_epigraph_toReal_of_mem_dom hproper hx

omit [CompleteSpace H] in
/-- Helper for Theorem 13 37: the `ℓ²` product inner product on `H × ℝ` splits componentwise. -/
private theorem inner_pair_eq {z w : H × ℝ} :
    ⟪z, w⟫_ℝ = ⟪z.1, w.1⟫_ℝ + z.2 * w.2 := by
  rcases z with ⟨z₁, z₂⟩
  rcases w with ⟨w₁, w₂⟩
  change ⟪z₁, w₁⟫_ℝ + ⟪z₂, w₂⟫_ℝ = ⟪z₁, w₁⟫_ℝ + z₂ * w₂
  have hreal : ⟪z₂, w₂⟫_ℝ = z₂ * w₂ := by
    rw [real_inner_eq_re_inner]
    simp [RCLike.inner_apply, mul_comm]
  simp [hreal]

/-- Helper for Theorem 13 37: if `x` lies in `closure (dom f)` and `ξ < f x`, then some
continuous affine minorant of `f` lies strictly above `ξ` at `x`. -/
private theorem exists_strict_affine_minorant_of_lt_of_mem_gamma_of_mem_closure_dom
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H))
    {x : H} (hx_closure : x ∈ closure (dom f)) {ξ : ℝ} (hξ : (ξ : EReal) < f x) :
    ∃ u : H, ∃ η : ℝ,
      (∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y)) ∧
        (ξ : EReal) < (((⟪x, u⟫_ℝ + η : ℝ) : EReal)) := by
  rcases (mem_gamma_iff f).mp hf with ⟨hf_conv, hf_lsc⟩
  have hEpi_conv : Convex ℝ (epigraph f) := by
    -- Rewrite Jensen convexity into the real-height epigraph formulation.
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro y z hy hz a ha ha_lt_one
    exact hf_conv ha.le ha_lt_one.le
  have hEpi_closed : IsClosed (epigraph f) :=
    (lowerSemicontinuous_iff_isClosed_epigraph f).mp hf_lsc
  have hq_not_mem : (x, ξ) ∉ epigraph f := by
    -- A point strictly below the function value cannot lie in the epigraph.
    intro hxξ
    exact (not_le_of_gt hξ) ((mem_epigraph_iff f x ξ).mp hxξ)
  obtain ⟨w, β, hsep, hq_out⟩ :=
    exists_closedHalfspace_separating_of_not_mem_of_isClosed_of_convex
      hEpi_closed hEpi_conv hq_not_mem
  have hw₂_nonpos : w.2 ≤ 0 := by
    by_contra hw₂_pos
    rcases exists_mem_epigraph_of_isProper hproper with ⟨⟨p, π⟩, hpπ⟩
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
      have hbase :
          β - ⟪(p, π), w⟫_ℝ < t * w.2 := by
        have hw₂_pos' : 0 < w.2 := lt_of_not_ge hw₂_pos
        have hstrict : |β - ⟪(p, π), w⟫_ℝ| < t * w.2 := by
          dsimp [t]
          have hplus : |β - ⟪(p, π), w⟫_ℝ| < |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
            linarith
          have hEq :
              (|β - ⟪(p, π), w⟫_ℝ| / w.2 + 1) * w.2 =
                |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
            field_simp [hw₂_pos'.ne']
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
          mem_epigraph_toReal_of_mem_dom hproper hy
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
    · -- Evaluate the separating halfspace at the canonical epigraph point `(y, f y)`.
      have hy_epi : (y, (f y).toReal) ∈ epigraph f :=
        mem_epigraph_toReal_of_mem_dom hproper hy
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
    · -- Off the domain the function value is `⊤`, so the affine minorant inequality is automatic.
      rw [value_eq_top_of_not_mem_dom hy]
      exact le_top
  · -- Evaluate the separator at the excluded point `(x, ξ)` and normalize by the negative height.
    have hq_real : β < ⟪(x, ξ), w⟫_ℝ := by
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

/-- Helper for Theorem 13 37: proper `Γ(H)` functions admit a global continuous affine minorant in
the canonical textbook form `y ↦ ⟪y,u⟫ + η`. -/
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

omit [CompleteSpace H] in
/-- Helper for Theorem 13 37: a canonical affine minorant strictly above `ξ` at `x` forces the
Fenchel biconjugate value at `x` to dominate `ξ`. -/
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
    -- Evaluate the defining supremum of `f** x` at the chosen dual point `u`.
    simpa [conjugate_apply, real_inner_comm] using
      (le_iSup (fun y : H ↦ (((⟪y, x⟫_ℝ : ℝ) : EReal) - f∗ y)) u)
  exact hξ.le.trans (haffine_le.trans hdefect_le)

/-- Helper for Theorem 13 37: outside `closure (dom f)`, the Fenchel biconjugate of a proper
member of `Γ(H)` is identically `⊤`. -/
private theorem biconjugate_eq_top_of_not_mem_closure_dom_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H))
    {x : H} (hx : x ∉ closure (dom f)) :
    f∗∗ x = ⊤ := by
  rcases (mem_gamma_iff f).mp hf with ⟨hf_conv, _⟩
  have hEpi_conv : Convex ℝ (epigraph f) := by
    -- The Jensen inequality packages the convexity of the epigraph.
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
  have hw_conj :
      f∗ w ≤ ((t * β₀ - η : ℝ) : EReal) := by
    rw [conjugate_apply]
    refine iSup_le ?_
    intro y
    by_cases hy : y ∈ dom f
    · have hy_top : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
      have hy_bot : f y ≠ ⊥ := hproper.1 y
      have hy_half : ⟪y, u₀⟫_ℝ ≤ β₀ := by
        exact hdom_half (subset_closure hy)
      have hminor_real :
          ⟪y, v⟫_ℝ + η ≤ (f y).toReal := by
        have hcast : (((⟪y, v⟫_ℝ + η : ℝ) : EReal) ≤ (((f y).toReal : ℝ) : EReal)) := by
          exact le_trans (hminor y) (by
            simp [EReal.coe_toReal hy_top hy_bot])
        exact_mod_cast hcast
      have hlinear :
          ⟪y, w⟫_ℝ - (f y).toReal ≤ t * β₀ - η := by
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
    · rw [value_eq_top_of_not_mem_dom hy]
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
  have hterm_le : (((⟪x, w⟫_ℝ : ℝ) : EReal) - ((t * β₀ - η : ℝ) : EReal)) ≤ f∗∗ x := by
    have hdefect : (((⟪x, w⟫_ℝ : ℝ) : EReal) - f∗ w) ≤ f∗∗ x := by
      simpa [conjugate_apply, real_inner_comm] using
        (le_iSup (fun y : H ↦ (((⟪y, x⟫_ℝ : ℝ) : EReal) - f∗ y)) w)
    have hsub :
        (((⟪x, w⟫_ℝ : ℝ) : EReal) - ((t * β₀ - η : ℝ) : EReal)) ≤
          (((⟪x, w⟫_ℝ : ℝ) : EReal) - f∗ w) := by
      exact EReal.sub_le_sub le_rfl hw_conj
    exact le_trans hsub hdefect
  exact lt_of_lt_of_le hbase_lt hterm_le

/-- Helper for Theorem 13 37: every proper member of `Γ(H)` is bounded above by its Fenchel
biconjugate. -/
private theorem le_biconjugate_of_isProper_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    f ≤ f∗∗ := by
  intro x
  by_cases hx_closure : x ∈ closure (dom f)
  · -- Inside the closure of the domain, strict affine support of every sub-epigraph point yields
    -- the desired `EReal` lower bound.
    refine le_of_forall_lt fun ξ hξ ↦ ?_
    rcases EReal.lt_iff_exists_real_btwn.mp hξ with ⟨ξ₀, hξ_lt, hξ₀_lt⟩
    rcases exists_strict_affine_minorant_of_lt_of_mem_gamma_of_mem_closure_dom
        hproper hf hx_closure hξ₀_lt with ⟨u, η, hminor, hstrict⟩
    exact lt_of_lt_of_le hξ_lt
      (strict_lower_bound_le_biconjugate_of_affine_minorant hminor hstrict)
  · -- Outside the closure of the domain, the function is already `⊤`, and so is its biconjugate.
    have hx_top : f x = ⊤ := by
      by_contra hx_top
      have hx_dom : x ∈ dom f := (mem_dom_iff_ne_top f x).2 hx_top
      exact hx_closure (subset_closure hx_dom)
    rw [hx_top]
    rw [biconjugate_eq_top_of_not_mem_closure_dom_of_mem_gamma hproper hf hx_closure]

omit [CompleteSpace H] in
/-- Helper for Theorem 13 37: a global affine minorant furnishes a finite conjugate value, hence a
domain point of the conjugate. -/
private theorem mem_dom_conjugate_of_affine_minorant
    {f : H → EReal} {u : H} {η : ℝ}
    (hminor : ∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y)) :
    u ∈ dom f∗ := by
  have hmem : (u, -η) ∈ epigraph f∗ := by
    -- The affine minorant is exactly the epigraph criterion for the conjugate at `(u,-η)`.
    refine (mem_epigraph_conjugate_iff f u (-η)).2 ?_
    intro y
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hminor y
  have hu_lt_top : f∗ u < ⊤ := by
    -- The epigraph witness bounds `f∗ u` by a real number.
    exact lt_of_le_of_lt ((mem_epigraph_iff _ _ _).mp hmem) (EReal.coe_lt_top (-η))
  exact (mem_dom_iff (f∗) u).2 hu_lt_top

-- Proof sketch: if `f** = f`, then `f` is a Fenchel conjugate by Definition 13.1, so
-- Proposition 13.13 puts it in `Γ(H)`. Conversely, if `f ∈ Γ(H)`, apply the supporting
-- hyperplane argument of the Fenchel--Moreau theorem to get `f ≤ f**`, then combine with
-- Proposition 13.16(i), which always gives `f** ≤ f`.
/-- Theorem 13 37: for a proper extended-real-valued function on a real Hilbert space, being lower
semicontinuous and convex, equivalently belonging to `Γ(H)`, is equivalent to coinciding with its
Fenchel biconjugate. -/
theorem mem_gamma_iff_eq_biconjugate_of_is_proper
    {f : H → EReal} (hproper : IsProper f) :
    f ∈ Γ(H) ↔ f∗∗ = f := by
  constructor
  · intro hf
    -- Route correction: split the source Chapter 9 support argument into the closure-of-domain
    -- branch, where strict epigraph separation gives a direct affine minorant, and the exterior
    -- branch, where one global affine minorant plus domain separation forces `f** x = ⊤`.
    apply le_antisymm
    · exact biconjugate_le f
    · exact le_biconjugate_of_isProper_of_mem_gamma hproper hf
  · intro hEq
    -- If `f = f**`, then `f` is itself a Fenchel conjugate and hence belongs to `Γ(H)`.
    rw [← hEq]
    exact conjugate_mem_gamma (f := f∗)

-- Proof sketch: Theorem 13.37 identifies `f**` with `f`, so `f*` has proper conjugate. Applying
-- the global affine minorant from the `Γ(H)` hypothesis gives one finite value of `f*`, while any
-- finite domain point of `f` gives a finite affine defect lower bound, so `f*` never attains
-- `-∞`.
/-- If a proper extended-real-valued function on a real Hilbert space is lower semicontinuous and
convex, equivalently lies in `Γ(H)`, then its Fenchel conjugate is proper. -/
theorem conjugate_is_proper_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    IsProper f∗ := by
  rcases exists_global_affine_minorant_of_isProper_of_mem_gamma hproper hf with ⟨u, η, hminor⟩
  refine ⟨fun v ↦ conjugate_ne_bot_of_isProper hproper v, ?_⟩
  -- The same supporting affine functional provides a concrete dual point in `dom f∗`.
  exact ⟨u, mem_dom_conjugate_of_affine_minorant hminor⟩

end FenchelMoreau

end ERealFunction

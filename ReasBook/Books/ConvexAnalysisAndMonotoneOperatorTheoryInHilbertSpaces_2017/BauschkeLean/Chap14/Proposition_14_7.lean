import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Proposition_12_36
import BauschkeLean.Chap12.Proposition_12_15
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap10.Example_10_4
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap14.Definition_14_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace

noncomputable section

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ H] in
/-- Helper for Proposition 14 7: the kernel is finite exactly when both coordinate values are
finite. -/
theorem effectiveDomain_proximalAverageKernel
    (f g : H → Set.Ioi (⊥ : EReal)) :
    effectiveDomain (proximalAverageKernel f g) = effectiveDomain f ×ˢ effectiveDomain g := by
  -- The quadratic summand is always finite, so finiteness comes exactly from the two endpoint
  -- values.
  ext p
  rcases p with ⟨y, z⟩
  constructor
  · intro hp
    have hkernel_top : (proximalAverageKernel f g (y, z) : EReal) ≠ ⊤ := by
      exact ne_of_lt (mem_effectiveDomain_iff.mp hp)
    have hy_top : (f y : EReal) ≠ ⊤ := by
      intro htop
      have hhalf_pos : (0 : EReal) < ((1 / 2 : ℝ) : EReal) := by
        exact_mod_cast (show (0 : ℝ) < 1 / 2 by norm_num)
      have hterm_top :
          (((1 / 2 : ℝ) : EReal) * (f y : EReal)) = ⊤ := by
        simpa [htop] using EReal.mul_top_of_pos hhalf_pos
      have hsum_top :
          (((1 / 2 : ℝ) : EReal) * (f y : EReal) +
              ((1 / 2 : ℝ) : EReal) * (g z : EReal)) = ⊤ := by
        rw [hterm_top, EReal.top_add_of_ne_bot]
        exact EReal.mul_ne_bot _ _ |>.2
          ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inr (ne_of_gt (g z).2),
            Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
            Or.inl (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num))⟩
      have hquad_ne_bot :
          ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊥ := EReal.coe_ne_bot _
      have hfull_top :
          (proximalAverageKernel f g (y, z) : EReal) = ⊤ := by
        rw [proximalAverageKernel_apply, hsum_top, EReal.top_add_of_ne_bot hquad_ne_bot]
      exact hkernel_top hfull_top
    have hz_top : (g z : EReal) ≠ ⊤ := by
      intro htop
      have hhalf_pos : (0 : EReal) < ((1 / 2 : ℝ) : EReal) := by
        exact_mod_cast (show (0 : ℝ) < 1 / 2 by norm_num)
      have hterm_top :
          (((1 / 2 : ℝ) : EReal) * (g z : EReal)) = ⊤ := by
        simpa [htop] using EReal.mul_top_of_pos hhalf_pos
      have hleft_ne_bot :
          (((1 / 2 : ℝ) : EReal) * (f y : EReal)) ≠ ⊥ := by
        exact EReal.mul_ne_bot _ _ |>.2
          ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)), Or.inr (ne_of_gt (f y).2),
            Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
            Or.inl (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num))⟩
      have hsum_top :
          (((1 / 2 : ℝ) : EReal) * (f y : EReal) +
              ((1 / 2 : ℝ) : EReal) * (g z : EReal)) = ⊤ := by
        rw [hterm_top, EReal.add_top_of_ne_bot hleft_ne_bot]
      have hquad_ne_bot :
          ((((1 / 8 : ℝ) * ‖y - z‖ ^ 2 : ℝ) : EReal)) ≠ ⊥ := EReal.coe_ne_bot _
      have hfull_top :
          (proximalAverageKernel f g (y, z) : EReal) = ⊤ := by
        rw [proximalAverageKernel_apply, hsum_top, EReal.top_add_of_ne_bot hquad_ne_bot]
      exact hkernel_top hfull_top
    exact ⟨mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hy_top),
      mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hz_top)⟩
  · rintro ⟨hy, hz⟩
    rw [mem_effectiveDomain_iff, proximalAverageKernel_apply]
    refine EReal.add_lt_top ?_ (EReal.coe_ne_top _)
    exact EReal.add_ne_top
      (by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)),
          Or.inl (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)),
          Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
          Or.inr (ne_of_lt (mem_effectiveDomain_iff.mp hy))⟩)
      (by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 / 2 : ℝ)),
          Or.inl (by exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)),
          Or.inl (EReal.coe_ne_top (1 / 2 : ℝ)),
          Or.inr (ne_of_lt (mem_effectiveDomain_iff.mp hz))⟩)

/-- Helper for Proposition 14 7: the midpoint map sends the product effective domain onto the
weighted Minkowski sum from the textbook domain formula. -/
theorem proximalAverageMidpointMap_image_prod_effectiveDomain
    (f g : H → Set.Ioi (⊥ : EReal)) :
    proximalAverageMidpointMap '' (effectiveDomain f ×ˢ effectiveDomain g) =
      ((1 / 2 : ℝ) • effectiveDomain f) + ((1 / 2 : ℝ) • effectiveDomain g) := by
  -- The midpoint image is exactly the sum of the two half-scaled domain points.
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨hy, hz⟩
    refine ⟨(1 / 2 : ℝ) • p.1, ?_, (1 / 2 : ℝ) • p.2, ?_, ?_⟩
    · exact ⟨p.1, hy, rfl⟩
    · exact ⟨p.2, hz, rfl⟩
    · simp [proximalAverageMidpointMap_apply, smul_add]
  · rintro ⟨u, hu, v, hv, rfl⟩
    rcases hu with ⟨y, hy, rfl⟩
    rcases hv with ⟨z, hz, rfl⟩
    refine ⟨(y, z), ⟨hy, hz⟩, ?_⟩
    simp [proximalAverageMidpointMap_apply, smul_add]

/- Source/core/bridge triage:
- `source-facing`: Proposition 14.7 records the symmetry, domain formula, and convex/properness
  properties of the proximal average.
- `core/canonical`: the owner abstraction is `proximalAverage`, with primitive data
  `proximalAverageMidpointMap` and `proximalAverageKernel`.
- `bridge/view`: Proposition 12.36 supplies the infimal-postcomposition domain and epigraph API
  used to derive the specialized proximal-average clauses below. -/

section NormedSpaceRoute

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/- 
The lower-bound route below stays on the current file's ambient `NormedSpace` instance, so it
avoids transporting `Γ₀(H)` facts across a second normed-space structure induced by the inner
product.
-/
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: on a real normed space, every `Γ₀(H)` function admits a global
affine lower bound in the norm. -/
theorem exists_linear_lower_bound_of_mem_gammaZero_on_normed_space
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) :
    ∃ R C : ℝ, 0 ≤ R ∧ ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (φ x : EReal)) := by
  -- Work from a finite point and a local strict lower bound, then use convex interpolation to
  -- turn that local control into a global affine lower bound in `‖x‖`.
  rcases hφ.2.nonempty with ⟨p, hp⟩
  let ξ : ℝ := (φ p : EReal).toReal - 1
  have hp_top : (φ p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hp_bot : (φ p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ p : EReal) from (φ p).2)
  have hξ_lt_fp : (ξ : EReal) < (φ p : EReal) := by
    rw [show (φ p : EReal) = (((φ p : EReal).toReal : ℝ) : EReal) by
      symm
      exact EReal.coe_toReal hp_top hp_bot]
    exact_mod_cast (show ξ < (φ p : EReal).toReal by
      dsimp [ξ]
      linarith)
  have hopen : IsOpen (φ.asEReal ⁻¹' Set.Ioi (ξ : EReal)) := hφ.1.isOpen_preimage (ξ : EReal)
  have hp_mem : p ∈ φ.asEReal ⁻¹' Set.Ioi (ξ : EReal) := by
    simpa [Function.asEReal] using hξ_lt_fp
  rcases Metric.isOpen_iff.mp hopen p hp_mem with ⟨r, hr_pos, hr_subset⟩
  let δ : ℝ := r / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨δ⁻¹, 1 + ‖p‖ / δ - (φ p : EReal).toReal, by positivity, ?_⟩
  intro x
  by_cases hx : x ∈ effectiveDomain φ
  · have hx_top : (φ x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (φ x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (φ x : EReal) from (φ x).2)
    by_cases hnear : ‖x - p‖ < δ
    · -- Near `p`, the local strict lower bound is already enough.
      have hball : x ∈ Metric.ball p r := by
        have : ‖x - p‖ < r := by
          dsimp [δ] at hnear
          linarith
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hξ_lt_fx : (ξ : EReal) < (φ x : EReal) := hr_subset hball
      have hbound_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) ≤ ξ := by
        dsimp [ξ]
        have hnonneg : 0 ≤ δ⁻¹ * ‖x‖ + ‖p‖ / δ := by
          positivity
        linarith
      have hbound_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) : ℝ) : EReal)) ≤
            (ξ : EReal) := by
        exact_mod_cast hbound_real
      exact le_trans hbound_ereal hξ_lt_fx.le
    · -- Far from `p`, interpolate back to the local neighborhood and use convexity.
      have hfar : δ ≤ ‖x - p‖ := le_of_not_gt hnear
      have hxp_pos : 0 < ‖x - p‖ := lt_of_lt_of_le hδ_pos hfar
      let t : ℝ := δ / ‖x - p‖
      let y : H := t • x + (1 - t) • p
      have ht_pos : 0 < t := by
        dsimp [t]
        exact div_pos hδ_pos hxp_pos
      have ht_le_one : t ≤ 1 := by
        dsimp [t]
        exact (div_le_iff₀ hxp_pos).2 (by simpa [one_mul] using hfar)
      have hy_sub : y - p = t • (x - p) := by
        dsimp [y]
        calc
          t • x + (1 - t) • p - p = t • x + ((1 - t) • p - p) := by abel
          _ = t • x + ((1 - t) • p - (1 : ℝ) • p) := by simp
          _ = t • x + ((1 - t - 1) • p) := by rw [← sub_smul]
          _ = t • x + (-t) • p := by ring_nf
          _ = t • x - t • p := by rw [sub_eq_add_neg, neg_smul]
          _ = t • (x - p) := by rw [smul_sub]
      have hy_ball : y ∈ Metric.ball p r := by
        have hnorm : ‖y - p‖ < r := by
          calc
            ‖y - p‖ = ‖t • (x - p)‖ := by rw [hy_sub]
            _ = |t| * ‖x - p‖ := norm_smul t (x - p)
            _ = t * ‖x - p‖ := by rw [abs_of_pos ht_pos]
            _ = δ := by
                  dsimp [t]
                  field_simp [hxp_pos.ne']
            _ < r := by
                  dsimp [δ]
                  linarith
        simpa [Metric.mem_ball, dist_eq_norm] using hnorm
      have hξ_lt_fy : (ξ : EReal) < (φ y : EReal) := hr_subset hy_ball
      have hconv :
          (φ y : EReal) ≤ (t : EReal) * (φ x : EReal) + ((1 - t : ℝ) : EReal) * (φ p : EReal) := by
        by_cases ht_one : t = 1
        · simp [y, ht_one]
        · have ht_lt_one : t < 1 := lt_of_le_of_ne ht_le_one ht_one
          simpa [y] using hφ.2.ineq (x := x) hx (y := p) hp (α := t) ht_pos ht_lt_one
      have hterm1_ne_top : (t : EReal) * (φ x : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot t), Or.inl ?_, Or.inl (EReal.coe_ne_top t), Or.inr hx_top⟩
        exact_mod_cast ht_pos.le
      have hterm2_ne_top : ((1 - t : ℝ) : EReal) * (φ p : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - t)), Or.inl ?_,
          Or.inl (EReal.coe_ne_top (1 - t)), Or.inr hp_top⟩
        exact_mod_cast sub_nonneg.mpr ht_le_one
      have hright_ne_top :
          (t : EReal) * (φ x : EReal) + ((1 - t : ℝ) : EReal) * (φ p : EReal) ≠ ⊤ :=
        EReal.add_ne_top hterm1_ne_top hterm2_ne_top
      have hy_top : (φ y : EReal) ≠ ⊤ := by
        intro hy_top
        have : (⊤ : EReal) ≤
            (t : EReal) * (φ x : EReal) + ((1 - t : ℝ) : EReal) * (φ p : EReal) := by
          simpa [hy_top] using hconv
        exact hright_ne_top (top_unique this)
      have hy_bot : (φ y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (φ y : EReal) from (φ y).2)
      have hξ_lt_fy_real : ξ < (φ y : EReal).toReal := by
        rw [← EReal.coe_toReal hy_top hy_bot] at hξ_lt_fy
        exact EReal.coe_lt_coe_iff.1 hξ_lt_fy
      have hconv_real :
          (φ y : EReal).toReal ≤ t * (φ x : EReal).toReal + (1 - t) * (φ p : EReal).toReal := by
        have hconv_cast :
            (((φ y : EReal).toReal : ℝ) : EReal) ≤
              (t : EReal) * (((φ x : EReal).toReal : ℝ) : EReal) +
                ((1 - t : ℝ) : EReal) * (((φ p : EReal).toReal : ℝ) : EReal) := by
          simpa [EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot,
            EReal.coe_toReal hp_top hp_bot] using hconv
        exact EReal.coe_le_coe_iff.1 (by
          simpa [EReal.coe_mul, EReal.coe_add] using hconv_cast)
      have hfx_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) < (φ x : EReal).toReal := by
        have hdist : ‖x - p‖ ≤ ‖x‖ + ‖p‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x p
        have hmain : (φ p : EReal).toReal - 1 / t < (φ x : EReal).toReal := by
          have haux : ξ < t * (φ x : EReal).toReal + (1 - t) * (φ p : EReal).toReal :=
            lt_of_lt_of_le hξ_lt_fy_real hconv_real
          have hsub : -1 < t * ((φ x : EReal).toReal - (φ p : EReal).toReal) := by
            dsimp [ξ] at haux
            linarith
          have hdiv : -1 / t < (φ x : EReal).toReal - (φ p : EReal).toReal := by
            exact (div_lt_iff₀ ht_pos).2 (by simpa [mul_comm] using hsub)
          have hmain_shift :
              (φ p : EReal).toReal + (-1 / t) <
                (φ p : EReal).toReal + ((φ x : EReal).toReal - (φ p : EReal).toReal) :=
            add_lt_add_right hdiv (φ p : EReal).toReal
          calc
            (φ p : EReal).toReal - 1 / t = (φ p : EReal).toReal + (-1 / t) := by ring
            _ < (φ p : EReal).toReal + ((φ x : EReal).toReal - (φ p : EReal).toReal) :=
              hmain_shift
            _ = (φ x : EReal).toReal := by ring
        have ht_inv : 1 / t = ‖x - p‖ / δ := by
          dsimp [t]
          field_simp [hxp_pos.ne', hδ_pos.ne']
        rw [ht_inv] at hmain
        have hratio : ‖x - p‖ / δ ≤ ‖x‖ / δ + ‖p‖ / δ := by
          have := div_le_div_of_nonneg_right hdist hδ_pos.le
          simpa [add_div] using this
        have hleft_le :
            (φ p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) ≤
              (φ p : EReal).toReal - ‖x - p‖ / δ := by
          linarith
        have hfinal :
            (φ p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) < (φ x : EReal).toReal :=
          lt_of_le_of_lt hleft_le hmain
        have hrewrite :
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) =
              (φ p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        rw [hrewrite]
        exact hfinal
      have hfx_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (φ p : EReal).toReal) : ℝ) : EReal)) <
            (φ x : EReal) := by
        rw [show (φ x : EReal) = (((φ x : EReal).toReal : ℝ) : EReal) by
          symm
          exact EReal.coe_toReal hx_top hx_bot]
        exact_mod_cast hfx_real
      exact hfx_ereal.le
  · have hx_top : (φ x : EReal) = ⊤ := by
      apply le_antisymm le_top
      apply not_lt.mp
      intro hxtop
      exact hx (mem_effectiveDomain_iff.mpr hxtop)
    simp [hx_top]

end NormedSpaceRoute

section ProximalAverageProposition

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 14 7: precomposing a `Γ₀` function with a continuous linear map
preserves `Γ₀` membership when the range meets the effective domain. -/
private theorem comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty_local
    {E : Type*} {F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (g : F → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(F))
    (L : E →L[ℝ] F)
    (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    g ∘ L ∈ Γ₀(E) := by
  -- Transport lower semicontinuity and Jensen convexity through the linear map `L`.
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · simpa using hg.1.comp L.continuous
  · refine ⟨effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    have hx' : L x ∈ effectiveDomain g := by
      simpa [mem_effectiveDomain_iff] using hx
    have hy' : L y ∈ effectiveDomain g := by
      simpa [mem_effectiveDomain_iff] using hy
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hg.2.ineq hx' hy' hα hα_lt_one

/-- Helper for Proposition 14 7: the positive scalar `1 / 2` packaged as a `PosReal`. -/
private noncomputable def gammaHalf : PosReal :=
  ⟨(1 / 2 : ℝ), by positivity⟩

/-- Helper for Proposition 14 7: the separable sum `(y, z) ↦ f y + g z` on `H × H`. -/
private noncomputable def separableSumIoi
    (f g : H → Set.Ioi (⊥ : EReal)) :
    H × H → Set.Ioi (⊥ : EReal) :=
  pointwiseAdd (f ∘ Prod.fst) (g ∘ Prod.snd)

omit [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: coercing the separable sum back to `EReal` recovers the
textbook formula `(y, z) ↦ f y + g z`. -/
@[simp] private theorem separableSumIoi_apply
    (f g : H → Set.Ioi (⊥ : EReal)) (p : H × H) :
    (separableSumIoi f g p : EReal) = (f p.1 : EReal) + (g p.2 : EReal) := by
  simp [separableSumIoi, pointwiseAdd_apply]

/-- Helper for Proposition 14 7: the quadratic term
`(y, z) ↦ (1 / 8) * ‖y - z‖ ^ 2` as an `]-∞,+∞]`-valued function. -/
private noncomputable def quadraticDifferenceKernel :
    H × H → Set.Ioi (⊥ : EReal) :=
  (fun p : H × H ↦ (1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2).toEReal

/-- Helper for Proposition 14 7: the everywhere-finite kernel `z ↦ (1 / 8) * ‖z‖ ^ 2`. -/
private noncomputable def scaledSquaredNormKernel :
    H → Set.Ioi (⊥ : EReal) :=
  (fun z : H ↦ (1 / 8 : ℝ) * ‖z‖ ^ 2).toEReal

omit [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: coercing the scaled squared-norm kernel to `EReal` recovers its
real formula. -/
@[simp] private theorem scaledSquaredNormKernel_apply (z : H) :
    (scaledSquaredNormKernel (H := H) z : EReal) =
      (((1 / 8 : ℝ) * ‖z‖ ^ 2 : ℝ) : EReal) := by
  simp [scaledSquaredNormKernel]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: the everywhere-finite kernel `z ↦ (1 / 8) * ‖z‖ ^ 2`
belongs to `Γ₀(H)`. -/
private theorem scaledSquaredNormKernel_mem_gammaZero :
    scaledSquaredNormKernel (H := H) ∈ Γ₀(H) := by
  -- View the quadratic kernel as a continuous convex real-valued function and package it via
  -- `toEReal`.
  have hrepr :
      ((fun z : H ↦ ((‖z‖ ^ 2) / 8 : ℝ)).toEReal) =
        scaledSquaredNormKernel (H := H) := by
    funext z
    apply Subtype.ext
    simp [scaledSquaredNormKernel, Function.toEReal_apply, div_eq_mul_inv, mul_comm]
  rw [← hrepr]
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    have hnorm_sq :
        _root_.ConvexOn ℝ (Set.univ : Set H) (fun z : H ↦ ‖z‖ ^ 2) :=
      (convexOn_univ_norm : _root_.ConvexOn ℝ (Set.univ : Set H) (fun z : H ↦ ‖z‖)).pow
        (fun z _ ↦ norm_nonneg z) 2
    have hconv :
        ‖a • x + (1 - a) • y‖ ^ 2 / 8 ≤
          a * (‖x‖ ^ 2 / 8) + (1 - a) * (‖y‖ ^ 2 / 8) := by
      have hnorm_sq' :
          ‖a • x + (1 - a) • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 := by
        simpa [smul_eq_mul] using
          hnorm_sq.2 (by simp) (by simp) ha0 (sub_nonneg.mpr ha1) (by ring)
      nlinarith
    change (((‖a • x + (1 - a) • y‖ ^ 2 / 8 : ℝ) : EReal)) ≤
        (((a * (‖x‖ ^ 2 / 8) + (1 - a) * (‖y‖ ^ 2 / 8) : ℝ) : EReal))
    exact_mod_cast hconv
  · have hcont : Continuous fun z : H ↦ ((‖z‖ ^ 2) / 8 : ℝ) := by
      simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_norm.pow 2).const_mul (1 / 8 : ℝ)
    have hcontE : Continuous fun z : H ↦ ((((‖z‖ ^ 2) / 8 : ℝ) : EReal)) := by
      simpa using continuous_coe_real_ereal.comp hcont
    simpa using hcontE.lowerSemicontinuous

/-- Helper for Proposition 14 7: the continuous linear map `(y, z) ↦ y - z`. -/
private noncomputable def productDifferenceMap :
    H × H →L[ℝ] H :=
  ContinuousLinearMap.fst ℝ H H - ContinuousLinearMap.snd ℝ H H

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: evaluating the product difference map gives the coordinate
difference `y - z`. -/
@[simp] private theorem productDifferenceMap_apply (p : H × H) :
    productDifferenceMap (H := H) p = p.1 - p.2 := by
  simp [productDifferenceMap]

omit [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: coercing the quadratic difference kernel to `EReal` recovers
the displayed quadratic formula. -/
@[simp] private theorem quadraticDifferenceKernel_apply (p : H × H) :
    (quadraticDifferenceKernel (H := H) p : EReal) =
      (((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal) := by
  -- This is just the defining `toEReal` coercion.
  simp [quadraticDifferenceKernel]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: the quadratic difference kernel belongs to `Γ₀(H × H)`. -/
private theorem quadraticDifferenceKernel_mem_gammaZero :
    quadraticDifferenceKernel (H := H) ∈ Γ₀(H × H) := by
  have hdom :
      (Set.range (productDifferenceMap (H := H)) ∩
        effectiveDomain (scaledSquaredNormKernel (H := H))).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · exact ⟨(0, 0), by simp [productDifferenceMap_apply]⟩
    · simp [scaledSquaredNormKernel, Function.effectiveDomain_toEReal]
  have hcomp :
      scaledSquaredNormKernel (H := H) ∘ productDifferenceMap (H := H) ∈
        Γ₀(H × H) :=
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty_local
      (scaledSquaredNormKernel (H := H))
      scaledSquaredNormKernel_mem_gammaZero
      (productDifferenceMap (H := H))
      hdom
  have hrepr :
      scaledSquaredNormKernel (H := H) ∘ productDifferenceMap (H := H) =
        quadraticDifferenceKernel (H := H) := by
    funext p
    apply Subtype.ext
    simp [scaledSquaredNormKernel, quadraticDifferenceKernel, productDifferenceMap_apply,
      Function.toEReal_apply]
  simpa [hrepr] using hcomp

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: the product-space separable sum `f ⊕ g` belongs to `Γ₀(H × H)`
whenever `f, g ∈ Γ₀(H)`. -/
private theorem separableSum_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    separableSumIoi f g ∈ Γ₀(H × H) := by
  have hfst_dom :
      (Set.range (ContinuousLinearMap.fst ℝ H H) ∩ effectiveDomain f).Nonempty := by
    -- Realize any finite point of `f` as the first coordinate of a product point.
    rcases hf.2.nonempty with ⟨x, hx⟩
    exact ⟨x, ⟨(x, 0), by simp⟩, hx⟩
  have hsnd_dom :
      (Set.range (ContinuousLinearMap.snd ℝ H H) ∩ effectiveDomain g).Nonempty := by
    -- Realize any finite point of `g` as the second coordinate of a product point.
    rcases hg.2.nonempty with ⟨y, hy⟩
    exact ⟨y, ⟨(0, y), by simp⟩, hy⟩
  have hfst : f ∘ ContinuousLinearMap.fst ℝ H H ∈ Γ₀(H × H) :=
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty_local
      f hf (ContinuousLinearMap.fst ℝ H H) hfst_dom
  have hsnd : g ∘ ContinuousLinearMap.snd ℝ H H ∈ Γ₀(H × H) :=
    comp_continuousLinearMap_mem_gammaZero_of_range_inter_nonempty_local
      g hg (ContinuousLinearMap.snd ℝ H H) hsnd_dom
  have hsum_dom :
      (effectiveDomain (f ∘ ContinuousLinearMap.fst ℝ H H) ∩
        effectiveDomain (g ∘ ContinuousLinearMap.snd ℝ H H)).Nonempty := by
    -- Combine finite points of `f` and `g` into a finite point of the product-space sum.
    rcases hf.2.nonempty with ⟨x, hx⟩
    rcases hg.2.nonempty with ⟨y, hy⟩
    refine ⟨(x, y), ?_, ?_⟩
    · simpa [Function.comp]
    · simpa [Function.comp]
  have hsum :
      (f ∘ ContinuousLinearMap.fst ℝ H H) +
          (g ∘ ContinuousLinearMap.snd ℝ H H) ∈
        Γ₀(H × H) :=
    pointwiseAdd_mem_gammaZero
      (f ∘ ContinuousLinearMap.fst ℝ H H)
      (g ∘ ContinuousLinearMap.snd ℝ H H)
      hfst hsnd hsum_dom
  simpa [separableSumIoi, Function.comp] using hsum

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: the proximal-average kernel belongs to `Γ₀(H × H)`. -/
private theorem proximalAverageKernel_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    proximalAverageKernel f g ∈ Γ₀(H × H) := by
  have hsep : separableSumIoi f g ∈ Γ₀(H × H) := separableSum_mem_gammaZero f g hf hg
  have hscaled : gammaHalf • separableSumIoi f g ∈ Γ₀(H × H) :=
    smul_mem_gammaZero (separableSumIoi f g) hsep gammaHalf
  have hquad : quadraticDifferenceKernel ∈ Γ₀(H × H) := quadraticDifferenceKernel_mem_gammaZero
  rcases hscaled.2.nonempty with ⟨p, hp⟩
  have hquad_dom : p ∈ effectiveDomain quadraticDifferenceKernel := by
    simp [quadraticDifferenceKernel, Function.effectiveDomain_toEReal]
  have hsum :
      gammaHalf • separableSumIoi f g + quadraticDifferenceKernel ∈ Γ₀(H × H) :=
    pointwiseAdd_mem_gammaZero
      (gammaHalf • separableSumIoi f g)
      quadraticDifferenceKernel
      hscaled hquad ⟨p, hp, hquad_dom⟩
  have hrepr :
      gammaHalf • separableSumIoi f g + quadraticDifferenceKernel =
        proximalAverageKernel f g := by
    -- The scaled separable part plus the quadratic difference term is exactly the kernel.
    have hhalf_nonneg : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) := by
      exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    have hhalf_ne_top : ((1 / 2 : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    funext p
    apply Subtype.ext
    have hdist :
        (((1 / 2 : ℝ) : EReal) * ((f p.1 : EReal) + (g p.2 : EReal))) =
          ((1 / 2 : ℝ) : EReal) * (f p.1 : EReal) +
            ((1 / 2 : ℝ) : EReal) * (g p.2 : EReal) := by
      simpa using
        EReal.left_distrib_of_nonneg_of_ne_top hhalf_nonneg hhalf_ne_top
          (f p.1 : EReal) (g p.2 : EReal)
    simpa [gammaHalf, separableSumIoi, quadraticDifferenceKernel, proximalAverageKernel,
      pointwiseAdd_apply, posReal_smul_value_apply, Function.toEReal_apply, add_assoc] using
      congrArg
        (fun t : EReal ↦ t + (((1 / 8 : ℝ) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal))
        hdist
  simpa [hrepr] using hsum

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: affine lower bounds for `f` and `g` yield a uniform lower bound
on the single-variable midpoint integrand from `pav(f, g)`. -/
private theorem proximalAverageMidpointIntegrand_lowerBound
    (f g : H → Set.Ioi (⊥ : EReal))
    {Rf Cf Rg Cg : ℝ} (hRf : 0 ≤ Rf) (hRg : 0 ≤ Rg)
    (hf_lower : ∀ u : H, (((-Rf * ‖u‖ - Cf : ℝ) : EReal) ≤ (f u : EReal)))
    (hg_lower : ∀ u : H, (((-Rg * ‖u‖ - Cg : ℝ) : EReal) ≤ (g u : EReal)))
    (x y : H) :
    ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal) ≤
      (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal) := by
  -- Bound the two endpoint norms by `‖x‖ + ‖x - y‖` and absorb the quadratic term with a square.
  let z : H := (2 : ℝ) • x - y
  let d : ℝ := ‖x - y‖
  have hy_norm : ‖y‖ ≤ ‖x‖ + d := by
    calc
      ‖y‖ = ‖x + (y - x)‖ := by
        congr 1
        abel_nf
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ = ‖x‖ + d := by
        simp [d, norm_sub_rev]
  have hz_norm : ‖z‖ ≤ ‖x‖ + d := by
    calc
      ‖z‖ = ‖x + (x - y)‖ := by
        dsimp [z]
        congr 1
        simp [two_smul, sub_eq_add_neg, add_assoc]
      _ ≤ ‖x‖ + ‖x - y‖ := norm_add_le _ _
      _ = ‖x‖ + d := by
        simp [d]
  have hreal :
      -(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) ≤
        (-Rf * ‖y‖ - Cf) + (-Rg * ‖z‖ - Cg) + d ^ 2 := by
    have hd_nonneg : 0 ≤ d := by
      simp [d]
    have hsquare : 0 ≤ (d - (Rf + Rg) / 2) ^ 2 := sq_nonneg _
    nlinarith [hy_norm, hz_norm, hRf, hRg, hd_nonneg, hsquare]
  have hreal_cast :
      ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal) ≤
        (((-Rf * ‖y‖ - Cf) + (-Rg * ‖z‖ - Cg) + d ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hreal
  have hreal_sum :
      ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal) ≤
        (((-Rf * ‖y‖ - Cf : ℝ) : EReal) + ((-Rg * ‖z‖ - Cg : ℝ) : EReal) +
          ((d ^ 2 : ℝ) : EReal)) := by
    simpa [EReal.coe_add, add_assoc] using hreal_cast
  have hfz :
      (((-Rf * ‖y‖ - Cf : ℝ) : EReal) + ((-Rg * ‖z‖ - Cg : ℝ) : EReal) +
          ((d ^ 2 : ℝ) : EReal)) ≤
        (f y : EReal) + (g z : EReal) + ((d ^ 2 : ℝ) : EReal) := by
    exact add_le_add (add_le_add (hf_lower y) (hg_lower z)) le_rfl
  exact le_trans hreal_sum (by simpa [z, d, add_assoc] using hfz)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: the proximal-average kernel has convex real-height epigraph. -/
private theorem convex_epigraph_proximalAverageKernel
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    Convex ℝ (epigraph (proximalAverageKernel f g).asEReal) := by
  -- Read epigraph convexity directly from the packaged `Γ₀(H × H)` kernel membership.
  exact convex_epigraph_asEReal_of_mem_gammaZero (proximalAverageKernel_mem_gammaZero f g hf hg)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: the proximal average has convex real-height epigraph. -/
private theorem convex_epigraph_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    Convex ℝ (epigraph (pav(f, g))) := by
  let Lmid : (H × H) →ᵃ[ℝ] H :=
    (((1 / 2 : ℝ) • (LinearMap.fst ℝ H H + LinearMap.snd ℝ H H))).toAffineMap
  have hLmid :
      (fun p : H × H ↦ Lmid p) = proximalAverageMidpointMap := by
    -- The affine-map adapter is exactly the midpoint map from Definition 14.6.
    funext p
    simp [Lmid, proximalAverageMidpointMap_apply, smul_add]
  have hconv :
      Convex ℝ (epigraph (Lmid ▷ proximalAverageKernel f g)) :=
    convex_epigraph_infimalPostcomposition
      (proximalAverageKernel f g)
      Lmid
      (convex_epigraph_proximalAverageKernel f g hf hg)
  -- Rewrite the transport theorem along the midpoint affine map back to the textbook owner.
  simpa [proximalAverage, hLmid] using hconv

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: swapping the two midpoint-fiber coordinates leaves the kernel
value unchanged once `f` and `g` are swapped. -/
private theorem proximalAverageKernel_midpoint_swap
    (f g : H → Set.Ioi (⊥ : EReal)) (x y : H) :
    (proximalAverageKernel f g
        ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) =
      (proximalAverageKernel g f (y, (2 : ℝ) • x - y) : EReal) := by
  have hcompanion : (2 : ℝ) • x - ((2 : ℝ) • x - y) = y := by
    simp
  have hnorm : ‖(2 : ℝ) • x - y - y‖ = ‖y - ((2 : ℝ) • x - y)‖ := by
    have hneg : (2 : ℝ) • x - y - y = -(y - ((2 : ℝ) • x - y)) := by
      simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hneg, norm_neg]
  rw [proximalAverageKernel_apply, proximalAverageKernel_apply]
  simp [hcompanion, hnorm, add_assoc, add_comm]

-- Proof sketch: unfold `proximalAverage`; swap the roles of `f` and `g`, then reindex the
-- defining infimum by `y ↦ 2 • x - y`.
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Symmetry clause of Proposition 14.7: the proximal average is symmetric in its two
arguments. -/
theorem proximalAverage_comm
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g) = pav(g, f) := by
  -- Reindex the parameterized infimum by the involution `y ↦ (2 : ℝ) • x - y`.
  have hdomf : (effectiveDomain f).Nonempty := hf.2.nonempty
  have hdomg : (effectiveDomain g).Nonempty := hg.2.nonempty
  let _ := hdomf
  let _ := hdomg
  ext x
  rw [proximalAverage_apply_eq_iInf_parameterized (f := f) (g := g) (x := x)]
  rw [proximalAverage_apply_eq_iInf_parameterized (f := g) (g := f) (x := x)]
  apply le_antisymm
  · refine le_iInf fun y ↦ ?_
    have hterm :
        (⨅ z : H, (proximalAverageKernel f g (z, (2 : ℝ) • x - z) : EReal)) ≤
          (proximalAverageKernel f g
            ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) :=
      iInf_le
        (fun z : H ↦
          (proximalAverageKernel f g (z, (2 : ℝ) • x - z) : EReal))
        ((2 : ℝ) • x - y)
    calc
      (⨅ z : H, (proximalAverageKernel f g (z, (2 : ℝ) • x - z) : EReal)) ≤
          (proximalAverageKernel f g
            ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) := hterm
      _ = (proximalAverageKernel g f (y, (2 : ℝ) • x - y) : EReal) :=
        proximalAverageKernel_midpoint_swap (f := f) (g := g) (x := x) (y := y)
  · refine le_iInf fun y ↦ ?_
    have hterm :
        (⨅ z : H, (proximalAverageKernel g f (z, (2 : ℝ) • x - z) : EReal)) ≤
          (proximalAverageKernel g f
            ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) :=
      iInf_le
        (fun z : H ↦
          (proximalAverageKernel g f (z, (2 : ℝ) • x - z) : EReal))
        ((2 : ℝ) • x - y)
    calc
      (⨅ z : H, (proximalAverageKernel g f (z, (2 : ℝ) • x - z) : EReal)) ≤
          (proximalAverageKernel g f
            ((2 : ℝ) • x - y, (2 : ℝ) • x - ((2 : ℝ) • x - y)) : EReal) := hterm
      _ = (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal) :=
        proximalAverageKernel_midpoint_swap (f := g) (g := f) (x := x) (y := y)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Infimal-postcomposition clause of Proposition 14.7: by Definition 14.6, the proximal
average is exactly the infimal postcomposition of the proximal-average kernel along the midpoint
map. -/
theorem proximalAverage_eq_infimalPostcomposition
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    pav(f, g) = proximalAverageMidpointMap ▷ proximalAverageKernel f g := by
  -- This is exactly the owner definition of `pav`.
  have hdomf : (effectiveDomain f).Nonempty := hf.2.nonempty
  have hdomg : (effectiveDomain g).Nonempty := hg.2.nonempty
  let _ := hdomf
  let _ := hdomg
  rfl

-- Proof sketch: combine Definition 14.6 with `dom_infimalPostcomposition`.
-- Then compute the
-- domain of `proximalAverageKernel f g` and the image of that set under the midpoint map.
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Domain clause of Proposition 14.7: the effective domain of the proximal average is
`(1 / 2) dom f + (1 / 2) dom g`. -/
theorem dom_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    dom (pav(f, g)) =
      ((1 / 2 : ℝ) • effectiveDomain f) + ((1 / 2 : ℝ) • effectiveDomain g) := by
  -- Rewrite the infimal-postcomposition domain and then compute the midpoint image of the kernel
  -- domain.
  rw [proximalAverage_eq_infimalPostcomposition f g hf hg, dom_infimalPostcomposition,
    effectiveDomain_proximalAverageKernel, proximalAverageMidpointMap_image_prod_effectiveDomain]

/-
Semantic recall note: `ConvexOn` is the canonical mathlib surface for convexity of a function on
its effective domain, so clause (4) packages properness together with that `ConvexOn` statement.
-/
-- Proof sketch: use Definition 14.6 and Proposition 12.36 to obtain convexity of the epigraph
-- from convexity of the kernel under the linear midpoint map, then repackage that as function-level
-- convexity on the effective domain. The helper theorem `isProper_proximalAverage` supplies the
-- properness witness used in the `properIoi` representation, while the labeled clause records the
-- full textbook conclusion.
omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- If `f, g ∈ Γ₀(H)`, then the proximal average is proper as an `EReal`-valued function. -/
theorem isProper_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    IsProper (pav(f, g)) := by
  -- Use the domain formula for nonemptiness, and bound the single-variable midpoint integrand
  -- from below by a finite affine function of `‖x‖`.
  rcases exists_linear_lower_bound_of_mem_gammaZero_on_normed_space hf with
    ⟨Rf, Cf, hRf, hf_lower⟩
  rcases exists_linear_lower_bound_of_mem_gammaZero_on_normed_space hg with
    ⟨Rg, Cg, hRg, hg_lower⟩
  refine ⟨?_, ?_⟩
  · intro x
    let lowerConst : ℝ :=
      (1 / 2 : ℝ) * (-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4))
    have hinf_lower :
        ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal) ≤
          ⨅ y : H,
            (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal) := by
      refine le_iInf fun y ↦ ?_
      exact proximalAverageMidpointIntegrand_lowerBound f g hRf hRg hf_lower hg_lower x y
    have hhalf_nonneg : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) := by
      exact_mod_cast (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    have hlower :
        ((lowerConst : EReal) ≤ pav(f, g) x) := by
      have hscaled_lower :
          (((1 / 2 : ℝ) : EReal) *
              ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal)) ≤
            ((1 / 2 : ℝ) : EReal) *
              (⨅ y : H,
                (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal)) :=
        mul_le_mul_of_nonneg_left hinf_lower hhalf_nonneg
      calc
        (lowerConst : EReal) =
            (((1 / 2 : ℝ) : EReal) *
              ((-(Rf + Rg) * ‖x‖ - (Cf + Cg + (Rf + Rg) ^ 2 / 4) : ℝ) : EReal)) := by
                simp [lowerConst, EReal.coe_mul]
        _ ≤ ((1 / 2 : ℝ) : EReal) *
              (⨅ y : H,
                (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) + ((‖x - y‖ ^ 2 : ℝ) : EReal)) :=
              hscaled_lower
        _ = pav(f, g) x := by
              calc
                ((1 / 2 : ℝ) : EReal) *
                    (⨅ y : H,
                      (f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
                        ((‖x - y‖ ^ 2 : ℝ) : EReal)) =
                  ⨅ y : H,
                    ((1 / 2 : ℝ) : EReal) *
                      ((f y : EReal) + (g ((2 : ℝ) • x - y) : EReal) +
                        ((‖x - y‖ ^ 2 : ℝ) : EReal)) := by
                      exact ereal_mul_iInf_of_pos (a := 1 / 2) (by norm_num) _
                _ = ⨅ y : H, (proximalAverageKernel f g (y, (2 : ℝ) • x - y) : EReal) := by
                      congr 1
                      funext y
                      symm
                      exact proximalAverageKernel_midpoint_substitution f g x y
                _ = pav(f, g) x := by
                      symm
                      exact proximalAverage_apply_eq_iInf_parameterized (f := f) (g := g) (x := x)
    have hbound_lt :
        (⊥ : EReal) < (lowerConst : EReal) := by
      exact EReal.bot_lt_coe _
    have hbot_lt_px : (⊥ : EReal) < pav(f, g) x :=
      lt_of_lt_of_le hbound_lt hlower
    exact ne_of_gt hbot_lt_px
  · rcases hf.2.nonempty with ⟨y, hy⟩
    rcases hg.2.nonempty with ⟨z, hz⟩
    refine ⟨(1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z, ?_⟩
    change (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z ∈ dom (pav(f, g))
    rw [dom_proximalAverage f g hf hg]
    exact ⟨(1 / 2 : ℝ) • y, ⟨y, hy, rfl⟩, (1 / 2 : ℝ) • z, ⟨z, hz, rfl⟩, rfl⟩

omit [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: packaging a proper `EReal`-valued function through `properIoi`
does not change its effective domain. -/
private theorem effectiveDomain_properIoi
    {F : H → EReal} (hproper : IsProper F) :
    effectiveDomain (properIoi F hproper) = dom F := by
  -- Rewriting the packaged value back to `F` turns effective-domain membership into the usual
  -- finite-value condition defining `dom F`.
  ext x
  rw [mem_effectiveDomain_iff, mem_dom_iff, properIoi_apply]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 14 7: convexity of the epigraph of a proper `EReal`-valued function
induces convexity of its canonical `properIoi` packaging on its effective domain. -/
private theorem convexOn_properIoi_of_convex_epigraph
    {F : H → EReal} (hproper : IsProper F) (hconv : Convex ℝ (epigraph F)) :
    ConvexOn (properIoi F hproper) (effectiveDomain (properIoi F hproper)) := by
  -- Route correction: apply the epigraph/Jensen bridge to the packaged `properIoi` owner
  -- directly, instead of proving Jensen for raw `F` and transporting it at the last step.
  have hconv_properIoi : Convex ℝ (epigraph (properIoi F hproper).asEReal) := by
    simpa [asEReal_properIoi] using hconv
  refine ⟨?_, subset_rfl, ?_⟩
  · -- Properness gives a finite point of `F`, and the packaging preserves that domain.
    simpa [effectiveDomain_properIoi (hproper := hproper)] using hproper.2
  · intro x hx y hy α hα0 hα1
    have hx' : x ∈ dom (properIoi F hproper).asEReal := by
      simpa [dom, effectiveDomain, Function.asEReal_apply] using hx
    have hy' : y ∈ dom (properIoi F hproper).asEReal := by
      simpa [dom, effectiveDomain, Function.asEReal_apply] using hy
    -- Jensen's inequality on the `asEReal` view is exactly the desired inequality for
    -- `properIoi F hproper`.
    simpa [Function.asEReal_apply] using
      (convex_epigraph_iff_jensen_on_dom (properIoi F hproper).asEReal).1
        hconv_properIoi hx' hy' hα0 hα1

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Proposition 14.7 (4): if `f, g ∈ Γ₀(H)`, then the proximal average is a proper convex
function. -/
theorem convexOn_proximalAverage
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    IsProper (pav(f, g)) ∧
      ConvexOn
        (properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg))
        (effectiveDomain (properIoi (pav(f, g)) (isProper_proximalAverage f g hf hg))) := by
  let hproper : IsProper (pav(f, g)) := isProper_proximalAverage f g hf hg
  have hconv_epi : Convex ℝ (epigraph (pav(f, g))) :=
    convex_epigraph_proximalAverage f g hf hg
  refine ⟨hproper, ?_⟩
  -- Route correction: finish through the general `properIoi` epigraph-to-convexity adapter,
  -- rather than transporting a raw `EReal` Jensen statement in the final line.
  exact convexOn_properIoi_of_convex_epigraph (hproper := hproper) hconv_epi

end ProximalAverageProposition

end ERealFunction

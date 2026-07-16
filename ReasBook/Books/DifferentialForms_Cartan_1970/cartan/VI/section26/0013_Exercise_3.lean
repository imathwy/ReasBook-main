import Mathlib
import DifferentialForms_Cartan_1970.cartan.III.section09.«0001_Theorem_III_3_extra_1»
import DifferentialForms_Cartan_1970.cartan.III.section12.«0022_Exercise_10»
import DifferentialForms_Cartan_1970.cartan.VI.section22.«0005_Corollary_VI_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.VI.section22.«0006_Definition_VI_1_extra_4»
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0011_Exercise_1»

-- Declarations for this item will be appended below by the statement pipeline.

open Function Set
open scoped ComplexConjugate

noncomputable section

/-- Helper for Exercise 3: a holomorphic isomorphism maps its prescribed source into its
prescribed target. -/
private theorem holomorphicIsomorph_mapsTo {D D' : Set ℂ} (e : HolomorphicIsomorph D D') :
    MapsTo e D D' := by
  -- Rewrite source and target membership to the underlying partial-homeomorphism owner.
  intro z hz
  have hz_source : z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
    simpa [e.source_eq] using hz
  simpa [e.target_eq] using (e : OpenPartialHomeomorph ℂ ℂ).map_source hz_source

/-- Helper for Exercise 3: the inverse of a holomorphic isomorphism is again a holomorphic
isomorphism. -/
private def holomorphicIsomorph_symm {D D' : Set ℂ} (e : HolomorphicIsomorph D D') :
    HolomorphicIsomorph D' D :=
  ⟨(e : OpenPartialHomeomorph ℂ ℂ).symm,
    { source_eq := e.target_eq
      target_eq := e.source_eq
      analyticOn_toFun := e.analyticOn_invFun
      analyticOn_symm := e.analyticOn_toFun }⟩

/-- Helper for Exercise 3: the raw Möbius uncentering map packages to a holomorphic automorphism
of the unit disc. -/
private theorem disc_uncenter_automorphism_local {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    ∃ ψ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1),
      EqOn ψ (discUncenter a) (Metric.ball (0 : ℂ) 1) := by
  have hneg : -a ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, norm_neg] using ha
  have hright : Set.LeftInvOn (discCenter a) (discUncenter a) (Metric.ball (0 : ℂ) 1) := by
    -- The reverse inverse identity is the centering/uncentering identity for the opposite center.
    intro z hz
    simpa [discUncenter] using (disc_uncenter_leftInvOn_disc_center hneg hz)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine
        { toFun := discUncenter a
          invFun := discCenter a
          source := Metric.ball (0 : ℂ) 1
          target := Metric.ball (0 : ℂ) 1
          map_source' := disc_uncenter_mapsTo_unit_ball ha
          map_target' := disc_center_mapsTo_unit_ball ha
          left_inv' := hright
          right_inv' := disc_uncenter_leftInvOn_disc_center ha
          open_source := Metric.isOpen_ball
          open_target := Metric.isOpen_ball
          continuousOn_toFun := by
            -- Holomorphicity of the raw Möbius formula gives continuity on the open disc.
            exact ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_uncenter_differentiableOn ha)).continuousOn
          continuousOn_invFun := by
            -- The inverse branch is the corresponding centering map.
            exact ((Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_center_differentiableOn ha)).continuousOn }
    · refine
        { source_eq := rfl
          target_eq := rfl
          analyticOn_toFun := by
            -- Package differentiability of the explicit Möbius branch back into analyticity.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_uncenter_differentiableOn ha)
          analyticOn_symm := by
            -- The inverse centering map is analytic on the same open disc.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2
              (disc_center_differentiableOn ha) }
  · intro z hz
    rfl

-- Domain sampling note: this file lies in one-variable complex analysis on simply connected plane
-- domains obtained as univalent images of the unit disc. The relevant owner declarations are:
-- * `HolomorphicIsomorph D D` for holomorphic automorphisms of a domain;
-- * `f.IsFixedPt a` for the fixed-point hypothesis;
-- * the source-facing family `discImage f r = f '' ball 0 r`.
-- The source-facing layer here is the family `D_r = f(B_r)`, written below with notation
-- `D_[r]` once `f` is fixed. The core/canonical owner for the automorphism acting on it is
-- `HolomorphicIsomorph`, and the fixed-point condition is derived from the canonical function-
-- level predicate rather than a separate equality binder.

/-- The image of the open disc of radius `r` centered at `0` under `f`. -/
def discImage (f : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  f '' Metric.ball (0 : ℂ) r

section

variable {f : ℂ → ℂ}

/- With `f` fixed, the textbook subdomains `D_r = f(B_r)` are written as `D_[r]`. -/
local notation "D_[" r "]" => discImage f r

/-- Helper for `discImage`: membership means having a preimage in the open disc of radius `r`. -/
theorem mem_discImage {r : ℝ} {w : ℂ} :
    w ∈ D_[r] ↔ ∃ z ∈ Metric.ball (0 : ℂ) r, f z = w :=
  Iff.rfl

/-- Helper for Exercise 3: the inverse branch `Function.invFunOn f (ball 0 1)` is holomorphic on
`D_[1]`, hence differentiable there. -/
private theorem invFunOn_discImage_differentiableOn
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) :
    DifferentiableOn ℂ (Function.invFunOn f (Metric.ball (0 : ℂ) 1)) D_[1] := by
  -- Reuse the earlier inverse-on-image theorem specialized to the unit disc.
  simpa [discImage] using
    (corollary_VI_1_extra_3_invFunOn_analyticOnNhd
      (D := Metric.ball (0 : ℂ) 1) hf_analytic hf_inj Metric.isOpen_ball).differentiableOn

/-- Helper for Exercise 3: conjugating a holomorphic map into `D_[1]` by the inverse of `f`
produces a disc self-map fixing `0`, so Schwarz's lemma forces every smaller source disc to map
into the corresponding image disc. -/
theorem subordinate_discImage_subset
    {g : ℂ → ℂ} {r : ℝ}
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hg_maps : MapsTo g (Metric.ball (0 : ℂ) 1) D_[1])
    (hg0 : g 0 = f 0)
    (hr1 : r < 1) :
    g '' Metric.ball (0 : ℂ) r ⊆ D_[r] := by
  let φ : ℂ → ℂ := Function.invFunOn f (Metric.ball (0 : ℂ) 1) ∘ g
  have h_inv_diff :
      DifferentiableOn ℂ (Function.invFunOn f (Metric.ball (0 : ℂ) 1)) D_[1] :=
    invFunOn_discImage_differentiableOn hf_analytic hf_inj
  have hφ_diff : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) := by
    -- Differentiate the conjugated map by composing `g` with the inverse branch of `f`.
    simpa [φ] using h_inv_diff.comp hg_diff hg_maps
  have hφ_maps : MapsTo φ (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rcases (mem_discImage).mp (hg_maps hz) with ⟨w, hw, hfw⟩
    exact Function.invFunOn_mem ⟨w, hw, hfw⟩
  have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    exact mem_ball_zero_iff.mpr (by norm_num : ‖(0 : ℂ)‖ < 1)
  have hφ0 : φ 0 = 0 := by
    -- The conjugated self-map fixes the origin because `g 0 = f 0`.
    calc
      φ 0 = Function.invFunOn f (Metric.ball (0 : ℂ) 1) (f 0) := by
        simpa [φ, hg0]
      _ = 0 := hf_inj.leftInvOn_invFunOn hzero_mem
  intro w hw
  rcases hw with ⟨z, hz, rfl⟩
  have hz_unit : z ∈ Metric.ball (0 : ℂ) 1 := by
    exact mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hr1)
  have hφ_norm : ‖φ z‖ ≤ ‖z‖ :=
    schwarz_lemma_norm_le φ hφ_diff hφ_maps hφ0 z hz_unit
  have hφ_mem_r : φ z ∈ Metric.ball (0 : ℂ) r := by
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt hφ_norm (mem_ball_zero_iff.mp hz))
  rcases (mem_discImage).mp (hg_maps hz_unit) with ⟨u, hu, hfu⟩
  refine (mem_discImage).mpr ⟨φ z, hφ_mem_r, ?_⟩
  -- Push the Schwarz estimate back through `f` using the inverse-branch identity.
  exact Function.invFunOn_eq ⟨u, hu, hfu⟩

/-- Exercise 3 (1): a holomorphic automorphism of `D = f(B)` fixing `f(0)` preserves every
subimage `D_r = f(B_r)` for `r < 1`. For `r ≤ 0`, the source disc is empty. -/
theorem automorphism_discImage_eq
    {r : ℝ}
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (h : HolomorphicIsomorph D_[1] D_[1])
    (hfix : (h : ℂ → ℂ).IsFixedPt (f 0))
    (hr1 : r < 1) :
    h '' D_[r] = D_[r] := by
  have hf_maps : MapsTo f (Metric.ball (0 : ℂ) 1) D_[1] := by
    -- A point of the unit disc maps into its own image by definition.
    intro z hz
    exact (mem_discImage).mpr ⟨z, hz, rfl⟩
  have h_preserves_subset :
      ∀ e : HolomorphicIsomorph D_[1] D_[1], (e : ℂ → ℂ).IsFixedPt (f 0) →
        e '' D_[r] ⊆ D_[r] := by
    intro e efix
    have he_maps : MapsTo ((e : ℂ → ℂ) ∘ f) (Metric.ball (0 : ℂ) 1) D_[1] := by
      intro z hz
      have hfz : f z ∈ D_[1] := hf_maps hz
      have hfz_source : f z ∈ (e : OpenPartialHomeomorph ℂ ℂ).source := by
        simpa [e.source_eq] using hfz
      simpa [e.target_eq] using (e : OpenPartialHomeomorph ℂ ℂ).map_source hfz_source
    have he_diff : DifferentiableOn ℂ ((e : ℂ → ℂ) ∘ f) (Metric.ball (0 : ℂ) 1) := by
      -- The automorphism and `f` are both holomorphic, so their composition is holomorphic too.
      exact (e.analyticOn_toFun.differentiableOn).comp hf_analytic.differentiableOn hf_maps
    have hsub :
        ((e : ℂ → ℂ) ∘ f) '' Metric.ball (0 : ℂ) r ⊆ D_[r] :=
      subordinate_discImage_subset hf_analytic hf_inj he_diff he_maps efix.eq hr1
    intro w hw
    rcases hw with ⟨u, hu, rfl⟩
    rcases (mem_discImage).mp hu with ⟨z, hz, rfl⟩
    -- Evaluate the subordinate-map inclusion at the chosen preimage `z`.
    exact hsub ⟨z, hz, rfl⟩
  have h_subset : h '' D_[r] ⊆ D_[r] := h_preserves_subset h hfix
  have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    exact mem_ball_zero_iff.mpr (by norm_num : ‖(0 : ℂ)‖ < 1)
  have hf0_mem : f 0 ∈ D_[1] := by
    exact (mem_discImage).mpr ⟨0, hzero_mem, rfl⟩
  let h_symm : HolomorphicIsomorph D_[1] D_[1] :=
    ⟨(h : OpenPartialHomeomorph ℂ ℂ).symm,
      { source_eq := h.target_eq
        target_eq := h.source_eq
        analyticOn_toFun := h.analyticOn_invFun
        analyticOn_symm := h.analyticOn_toFun }⟩
  have h_symm_coe : (h_symm : ℂ → ℂ) = (h : OpenPartialHomeomorph ℂ ℂ).symm := rfl
  have hfix_symm_eq : (h_symm : ℂ → ℂ) (f 0) = f 0 := by
    -- The inverse fixes `f 0` because `h` fixes it and `h⁻¹ ∘ h = id` on the image disc.
    have hf0_source : f 0 ∈ (h : OpenPartialHomeomorph ℂ ℂ).source := by
      simpa [h.source_eq] using hf0_mem
    rw [h_symm_coe]
    calc
      (h : OpenPartialHomeomorph ℂ ℂ).symm (f 0) =
          (h : OpenPartialHomeomorph ℂ ℂ).symm (h (f 0)) := by rw [hfix.eq]
      _ = f 0 := by simpa using (h : OpenPartialHomeomorph ℂ ℂ).left_inv hf0_source
  have hfix_symm : (h_symm : ℂ → ℂ).IsFixedPt (f 0) := hfix_symm_eq
  have h_symm_subset : (h_symm : ℂ → ℂ) '' D_[r] ⊆ D_[r] := h_preserves_subset h_symm hfix_symm
  refine Subset.antisymm h_subset ?_
  intro w hw
  have hw_target : w ∈ D_[1] := by
    rcases (mem_discImage).mp hw with ⟨z, hz, rfl⟩
    exact (mem_discImage).mpr
      ⟨z, mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hr1), rfl⟩
  have hpre_mem : (h_symm : ℂ → ℂ) w ∈ D_[r] := h_symm_subset ⟨w, hw, rfl⟩
  -- Apply the already-proved inverse inclusion and then push forward by `h`.
  refine ⟨(h_symm : ℂ → ℂ) w, hpre_mem, ?_⟩
  have hw_target' : w ∈ (h : OpenPartialHomeomorph ℂ ℂ).target := by
    simpa [h.target_eq] using hw_target
  rw [h_symm_coe]
  simpa using (h : OpenPartialHomeomorph ℂ ℂ).right_inv hw_target'

/-- Exercise 3 (2): if `D = f(B)` is star-convex with respect to `f(0)`, then each
`D_r = f(B_r)` is also star-convex with respect to `f(0)` for `r < 1`. For `r ≤ 0`, the source
disc is empty. -/
theorem starConvex_discImage
    {r : ℝ}
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hD_star : StarConvex ℝ (f 0) D_[1])
    (hr1 : r < 1) :
    StarConvex ℝ (f 0) D_[r] := by
  by_cases hr_nonpos : r ≤ 0
  · -- Nonpositive radii give the empty source disc, which is automatically star-convex.
    have h_empty : D_[r] = ∅ := by
      ext w
      constructor
      · intro hw
        rcases (mem_discImage).mp hw with ⟨z, hz, _⟩
        have hz_lt : ‖z‖ < r := mem_ball_zero_iff.mp hz
        exact False.elim ((not_lt_of_ge (le_trans hr_nonpos (norm_nonneg z))) hz_lt)
      · intro hw
        exact False.elim hw
    simpa [h_empty] using (starConvex_empty (𝕜 := ℝ) (x := f 0))
  · have hf_maps : MapsTo f (Metric.ball (0 : ℂ) 1) D_[1] := by
      -- Again, `f` lands in its own image by definition.
      intro z hz
      exact (mem_discImage).mpr ⟨z, hz, rfl⟩
    intro y hy a b ha hb hab
    rcases (mem_discImage).mp hy with ⟨z, hz, rfl⟩
    let g : ℂ → ℂ := fun w ↦ a • f 0 + b • f w
    have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
      -- The star-probe map is an affine combination of a constant and the holomorphic map `f`.
      simpa [g] using (hf_analytic.differentiableOn.const_smul b).const_add (a • f 0)
    have hg_maps : MapsTo g (Metric.ball (0 : ℂ) 1) D_[1] := by
      intro w hw
      have hfw : f w ∈ D_[1] := hf_maps hw
      exact hD_star hfw ha hb hab
    have hg0 : g 0 = f 0 := by
      -- The affine combination collapses to the center because `a + b = 1`.
      calc
        g 0 = a • f 0 + b • f 0 := by rfl
        _ = (a + b) • f 0 := by rw [add_smul]
        _ = f 0 := by simpa [hab]
    have hsub :
        g '' Metric.ball (0 : ℂ) r ⊆ D_[r] :=
      subordinate_discImage_subset hf_analytic hf_inj hg_diff hg_maps hg0 hr1
    -- Evaluate the subordinate inclusion at the chosen preimage of the boundary point.
    exact hsub ⟨z, hz, rfl⟩

/-- Helper for Exercise 3: scaling by `z₁ / z₂` keeps the unit disc inside itself when the norm of
`z₁` is bounded by the norm of `z₂`. -/
private theorem scaled_precomp_mapsTo_unit_ball
    {z₁ z₂ : ℂ} (hnorm : ‖z₁‖ ≤ ‖z₂‖) (_hz₂ : z₂ ≠ 0) :
    MapsTo (fun z : ℂ ↦ z * (z₁ / z₂)) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hz_lt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hratio_le : ‖z₁‖ / ‖z₂‖ ≤ 1 := by
    exact div_le_one_of_le₀ hnorm (norm_nonneg _)
  have hmul_le : ‖z‖ * (‖z₁‖ / ‖z₂‖) ≤ ‖z‖ := by
    exact mul_le_of_le_one_right (norm_nonneg z) hratio_le
  have hscaled_lt : ‖z‖ * (‖z₁‖ / ‖z₂‖) < 1 := lt_of_le_of_lt hmul_le hz_lt
  -- Rewrite the scaled norm into the one-dimensional estimate above.
  exact mem_ball_zero_iff.mpr (by simpa [norm_mul, norm_div] using hscaled_lt)

/-- Helper for Exercise 3: in the ordered nonzero case, the textbook probe map sends `z₂` to the
segment point between `f z₁` and `f z₂`, and Schwarz's lemma forces that segment point back into
`D_r`. -/
private theorem lineMap_mem_discImage_of_norm_order
    {r : ℝ} {z₁ z₂ : ℂ} {t : ℝ}
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hD_convex : Convex ℝ D_[1])
    (hr1 : r < 1)
    (_hz₁ : z₁ ∈ Metric.ball (0 : ℂ) r)
    (hz₂ : z₂ ∈ Metric.ball (0 : ℂ) r)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hnorm : ‖z₁‖ ≤ ‖z₂‖)
    (hz₂_ne : z₂ ≠ 0) :
    AffineMap.lineMap (f z₁) (f z₂) t ∈ D_[r] := by
  let scale : ℂ → ℂ := fun z ↦ z * (z₁ / z₂)
  let g : ℂ → ℂ := fun z ↦ (1 - t) • f (scale z) + t • f z
  have hf_maps : MapsTo f (Metric.ball (0 : ℂ) 1) D_[1] := by
    -- The unit disc maps into its image by definition.
    intro z hz
    exact (mem_discImage).mpr ⟨z, hz, rfl⟩
  have hscale_maps : MapsTo scale (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) :=
    scaled_precomp_mapsTo_unit_ball hnorm hz₂_ne
  have hscale_diff : DifferentiableOn ℂ scale (Metric.ball (0 : ℂ) 1) := by
    -- The source probe is just multiplication by the constant `z₁ / z₂`.
    intro z hz
    simpa [scale] using (differentiableAt_id.mul_const (z₁ / z₂)).differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    have hcomp_diff : DifferentiableOn ℂ (fun z ↦ f (scale z)) (Metric.ball (0 : ℂ) 1) :=
      hf_analytic.differentiableOn.comp hscale_diff hscale_maps
    -- Differentiate the two probe terms separately and add them.
    intro z hz
    exact ((hcomp_diff z hz).const_smul (1 - t)).add ((hf_analytic.differentiableOn z hz).const_smul t)
  have hg_maps : MapsTo g (Metric.ball (0 : ℂ) 1) D_[1] := by
    intro z hz
    have hscale_mem : f (scale z) ∈ D_[1] := hf_maps (hscale_maps hz)
    have hfz_mem : f z ∈ D_[1] := hf_maps hz
    -- Convexity of `D_[1]` keeps the affine combination inside the full image.
    exact hD_convex hscale_mem hfz_mem (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hg0 : g 0 = f 0 := by
    -- The probe map fixes the origin because both summands evaluate at `f 0`.
    calc
      g 0 = (1 - t) • f 0 + t • f 0 := by simp [g, scale]
      _ = ((1 - t) + t) • f 0 := by rw [add_smul]
      _ = f 0 := by simp
  have hsub :
      g '' Metric.ball (0 : ℂ) r ⊆ D_[r] :=
    subordinate_discImage_subset hf_analytic hf_inj hg_diff hg_maps hg0 hr1
  have hcancel : scale z₂ = z₁ := by
    -- Evaluate the source probe at `z₂` and cancel the nonzero denominator.
    calc
      scale z₂ = z₂ * (z₁ / z₂) := rfl
      _ = z₂ * (z₁ * z₂⁻¹) := by rw [div_eq_mul_inv]
      _ = z₁ * (z₂ * z₂⁻¹) := by ring
      _ = z₁ := by simp [hz₂_ne]
  have hgz₂ : g z₂ = AffineMap.lineMap (f z₁) (f z₂) t := by
    -- After the cancellation, the probe value is exactly the segment point.
    simp [g, scale, hcancel, AffineMap.lineMap_apply_module]
  have hmem : g z₂ ∈ D_[r] := hsub ⟨z₂, hz₂, rfl⟩
  simpa [hgz₂] using hmem

/-- Exercise 3 (3): if `D = f(B)` is convex, then each `D_r = f(B_r)` is also convex for
`r < 1`. For `r ≤ 0`, the source disc is empty. -/
theorem convex_discImage
    {r : ℝ}
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hD_convex : Convex ℝ D_[1])
    (hr1 : r < 1) :
    Convex ℝ D_[r] := by
  by_cases hr_nonpos : r ≤ 0
  · -- Nonpositive radii again give the empty image set.
    have h_empty : D_[r] = ∅ := by
      ext w
      constructor
      · intro hw
        rcases (mem_discImage).mp hw with ⟨z, hz, _⟩
        have hz_lt : ‖z‖ < r := mem_ball_zero_iff.mp hz
        exact False.elim ((not_lt_of_ge (le_trans hr_nonpos (norm_nonneg z))) hz_lt)
      · intro hw
        exact False.elim hw
    simpa [h_empty] using (convex_empty : Convex ℝ (∅ : Set ℂ))
  · have hr_pos : 0 < r := lt_of_not_ge hr_nonpos
    rw [convex_iff_segment_subset]
    intro x hx y hy u hu
    rw [segment_eq_image_lineMap] at hu
    rcases hu with ⟨t, ht, rfl⟩
    rcases (mem_discImage).mp hx with ⟨z₁, hz₁, rfl⟩
    rcases (mem_discImage).mp hy with ⟨z₂, hz₂, rfl⟩
    -- Route correction: the proof now isolates the ordered nonzero segment case and handles the
    -- symmetric/degenerate cases separately instead of bundling all algebra into one probe helper.
    by_cases hnorm : ‖z₁‖ ≤ ‖z₂‖
    · by_cases hz₂_zero : z₂ = 0
      · have hz₁_zero_norm : ‖z₁‖ = 0 := by
          apply le_antisymm
          · simpa [hz₂_zero] using hnorm
          · exact norm_nonneg z₁
        have hz₁_zero : z₁ = 0 := norm_eq_zero.mp hz₁_zero_norm
        -- If the larger-norm endpoint is `0`, both endpoints are `0`, so the whole segment is.
        exact (mem_discImage).mpr ⟨0, mem_ball_zero_iff.mpr (by simpa using hr_pos), by
          simp [hz₁_zero, hz₂_zero]⟩
      · exact lineMap_mem_discImage_of_norm_order hf_analytic hf_inj hD_convex hr1
          hz₁ hz₂ ht hnorm hz₂_zero
    · have hnorm' : ‖z₂‖ ≤ ‖z₁‖ := le_of_not_ge hnorm
      by_cases hz₁_zero : z₁ = 0
      · have hz₂_zero_norm : ‖z₂‖ = 0 := by
          apply le_antisymm
          · simpa [hz₁_zero] using hnorm'
          · exact norm_nonneg z₂
        have hz₂_zero : z₂ = 0 := norm_eq_zero.mp hz₂_zero_norm
        -- The swapped degenerate case is the same: both endpoints collapse to `f 0`.
        exact (mem_discImage).mpr ⟨0, mem_ball_zero_iff.mpr (by simpa using hr_pos), by
          simp [hz₁_zero, hz₂_zero]⟩
      · have ht' : 1 - t ∈ Set.Icc (0 : ℝ) 1 := by
          constructor <;> linarith [ht.1, ht.2]
        have hswap :
            AffineMap.lineMap (f z₂) (f z₁) (1 - t) ∈ D_[r] :=
          lineMap_mem_discImage_of_norm_order hf_analytic hf_inj hD_convex hr1
            hz₂ hz₁ ht' hnorm' hz₁_zero
        -- Swap the endpoints back using the symmetry of the affine parameterization.
        simpa [AffineMap.lineMap_apply_one_sub] using hswap

-- Exercise 3 (4): the remaining proof reduces arbitrary subdiscs to a strict interior case by
-- shrinking around the two chosen preimages.
/-- Helper for Exercise 3: if `ball c ρ` lies in the unit disc, then its radius cannot protrude
past the unit boundary. -/
private theorem norm_add_radius_le_one_of_ball_subset_unit
    {c : ℂ} {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hdisc_subset : Metric.ball c ρ ⊆ Metric.ball (0 : ℂ) 1) :
    ‖c‖ + ρ ≤ 1 := by
  by_cases hc_zero : c = 0
  · -- At the origin, the condition reduces to the scalar radius bound `ρ ≤ 1`.
    subst hc_zero
    by_contra hρ
    have hρ' : ¬ρ ≤ 1 := by
      simpa using hρ
    have hρ_gt : 1 < ρ := lt_of_not_ge hρ'
    let t : ℝ := (1 + ρ) / 2
    have ht1 : 1 < t := by
      dsimp [t]
      linarith
    have ht2 : t < ρ := by
      dsimp [t]
      linarith
    have ht_pos : 0 < t := by
      linarith
    have ht_ball : (t : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
      simpa [Metric.mem_ball, dist_eq_norm, Complex.norm_real, abs_of_pos ht_pos] using ht2
    have ht_unit : (t : ℂ) ∈ Metric.ball (0 : ℂ) 1 := hdisc_subset ht_ball
    have ht_lt_one : t < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm, Complex.norm_real, abs_of_pos ht_pos] using ht_unit
    linarith
  · -- If `c ≠ 0`, move a radial point of distance `t` from `c` toward the boundary.
    by_contra hbound
    have hbound_lt : 1 < ‖c‖ + ρ := lt_of_not_ge hbound
    have hρ_gt : max 0 (1 - ‖c‖) < ρ := by
      rw [max_lt_iff]
      constructor
      · exact hρ_pos
      · linarith
    have hnorm_ne : ‖c‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hc_zero
    let t : ℝ := (max 0 (1 - ‖c‖) + ρ) / 2
    have ht_pos : 0 < t := by
      have hmax_nonneg : 0 ≤ max 0 (1 - ‖c‖) := le_max_left _ _
      dsimp [t]
      linarith
    have ht1 : 1 - ‖c‖ < t := by
      have hbound_le : 1 - ‖c‖ ≤ max 0 (1 - ‖c‖) := le_max_right _ _
      dsimp [t]
      linarith
    have ht2 : t < ρ := by
      dsimp [t]
      linarith
    let z : ℂ := c + ((((t / ‖c‖ : ℝ) : ℂ)) * c)
    have hz_ball : z ∈ Metric.ball c ρ := by
      have hdist_eq : dist z c = t := by
        have hcalc : ‖z - c‖ = t := by
          have hscale :
              ‖((((t / ‖c‖ : ℝ) : ℂ)) * c)‖ = t := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
              (div_nonneg ht_pos.le (norm_nonneg _))]
            field_simp [hnorm_ne]
          calc
            ‖z - c‖ = ‖((((t / ‖c‖ : ℝ) : ℂ)) * c)‖ := by
              simp [z]
            _ = t := hscale
        simpa [dist_eq_norm] using hcalc
      simpa [Metric.mem_ball, hdist_eq] using ht2
    have hz_unit : z ∈ Metric.ball (0 : ℂ) 1 := hdisc_subset hz_ball
    have hz_norm_lt : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz_unit
    have hz_norm_eq : ‖z‖ = ‖c‖ + t := by
      have hz_eq : z = ((((1 + t / ‖c‖ : ℝ) : ℂ)) * c) := by
        simp [z]
        ring
      rw [hz_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg]
      · field_simp [hnorm_ne]
      · have hfactor_nonneg : 0 ≤ 1 + t / ‖c‖ := by
          positivity
        exact hfactor_nonneg
    have hz_norm_gt : 1 < ‖z‖ := by
      rw [hz_norm_eq]
      linarith
    linarith

/-- Helper for Exercise 3: multiplication by a unit-modulus scalar carries an open disc to the
corresponding rotated open disc with the same radius. -/
private theorem unit_scalar_image_ball
    {u c : ℂ} {ρ : ℝ} (hu : ‖u‖ = 1) :
    (fun z : ℂ ↦ u * z) '' Metric.ball c ρ = Metric.ball (u * c) ρ := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz_norm : ‖z - c‖ < ρ := by
      -- Rewrite membership in the source ball to the norm form used by the scalar estimate.
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hw_norm : ‖u * (z - c)‖ < ρ := by
      -- Unit-modulus multiplication preserves the norm of the displacement vector.
      simpa [norm_mul, hu] using hz_norm
    simpa [Metric.mem_ball, dist_eq_norm, mul_sub_left_distrib] using hw_norm
  · intro hw
    have hu_ne : u ≠ 0 := by
      intro hu_zero
      simpa [hu_zero] using hu
    refine ⟨u⁻¹ * w, ?_, ?_⟩
    · have hw_norm : ‖w - u * c‖ < ρ := by
        -- Rewrite the rotated-ball membership to the same norm inequality.
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hu_inv : ‖u⁻¹‖ = 1 := by
        rw [norm_inv, hu, inv_one]
      have hpre_norm : ‖u⁻¹ * (w - u * c)‖ < ρ := by
        -- Multiplication by the inverse scalar preserves the radius as well.
        simpa [norm_mul, hu_inv] using hw_norm
      have hrew : u⁻¹ * w - c = u⁻¹ * (w - u * c) := by
        -- Normalize the translated preimage point into a single scalar multiple.
        calc
          u⁻¹ * w - c = u⁻¹ * w - ((u⁻¹ * u) * c) := by
            rw [inv_mul_cancel₀ hu_ne, one_mul]
          _ = u⁻¹ * w - u⁻¹ * (u * c) := by rw [mul_assoc]
          _ = u⁻¹ * (w - u * c) := by ring
      simpa [Metric.mem_ball, dist_eq_norm, hrew] using hpre_norm
    · -- Apply the inverse scalar and then cancel it to recover the prescribed target point.
      simpa [mul_assoc, hu_ne]

/-- Helper for Exercise 3: multiplication by a unit-modulus scalar packages to a holomorphic
automorphism of the open unit disc. -/
private theorem unit_scalar_automorphism_local {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1),
      EqOn φ (fun z : ℂ ↦ u * z) (Metric.ball (0 : ℂ) 1) := by
  have hu_ne : u ≠ 0 := by
    intro hu_zero
    simpa [hu_zero] using hu
  have hu_inv : ‖u⁻¹‖ = 1 := by
    rw [norm_inv, hu, inv_one]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine
        { toFun := fun z ↦ u * z
          invFun := fun z ↦ u⁻¹ * z
          source := Metric.ball (0 : ℂ) 1
          target := Metric.ball (0 : ℂ) 1
          map_source' := by
            intro z hz
            simpa [mem_ball_zero_iff, norm_mul, hu] using hz
          map_target' := by
            intro z hz
            simpa [mem_ball_zero_iff, norm_mul, hu_inv] using hz
          left_inv' := by
            intro z hz
            simp [mul_assoc, hu_ne]
          right_inv' := by
            intro z hz
            simp [mul_assoc, hu_ne]
          open_source := Metric.isOpen_ball
          open_target := Metric.isOpen_ball
          continuousOn_toFun := by
            exact continuousOn_const.mul continuousOn_id
          continuousOn_invFun := by
            exact continuousOn_const.mul continuousOn_id }
    · refine
        { source_eq := rfl
          target_eq := rfl
          analyticOn_toFun := by
            -- The forward branch is the linear map `z ↦ u z`.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 (by
              intro z hz
              simpa using
                ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul u).differentiableWithinAt)
          analyticOn_symm := by
            -- The inverse branch is the corresponding linear map by `u⁻¹`.
            exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 (by
              intro z hz
              simpa using
                ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul u⁻¹).differentiableWithinAt) }
  · intro z hz
    rfl

/-- Helper for Exercise 3: once a disc automorphism carries `ball c ρ` onto a centered subdisc,
precomposing `f` with its inverse identifies the corresponding image sets. -/
private theorem discImage_precompose_symm_eq_image_ball
    {c : ℂ} {ρ s : ℝ}
    (φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1))
    (hsub : Metric.ball c ρ ⊆ Metric.ball (0 : ℂ) 1)
    (hφ : (φ : ℂ → ℂ) '' Metric.ball c ρ = Metric.ball (0 : ℂ) s) :
    discImage (f ∘ holomorphicIsomorph_symm φ) 1 = D_[1] ∧
      discImage (f ∘ holomorphicIsomorph_symm φ) s = f '' Metric.ball c ρ := by
  constructor
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(holomorphicIsomorph_symm φ) z,
        holomorphicIsomorph_mapsTo (holomorphicIsomorph_symm φ) hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨φ z, holomorphicIsomorph_mapsTo φ hz, ?_⟩
      have hz_source : z ∈ (φ : OpenPartialHomeomorph ℂ ℂ).source := by
        simpa [φ.source_eq] using hz
      -- Evaluate the precomposition on the full unit disc and collapse the inverse pair.
      simpa [Function.comp, holomorphicIsomorph_symm] using
        congrArg f ((φ : OpenPartialHomeomorph ℂ ℂ).left_inv hz_source)
  · have hsymm_image :
        ((holomorphicIsomorph_symm φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1)
            (Metric.ball (0 : ℂ) 1)) : ℂ → ℂ) '' Metric.ball (0 : ℂ) s = Metric.ball c ρ := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw_image : w ∈ (φ : ℂ → ℂ) '' Metric.ball c ρ := by
          simpa [hφ] using hw
        rcases hw_image with ⟨x, hx, rfl⟩
        have hx_source : x ∈ (φ : OpenPartialHomeomorph ℂ ℂ).source := by
          simpa [φ.source_eq] using hsub hx
        have hx_cancel : (holomorphicIsomorph_symm φ) (φ x) = x := by
          -- Pull the centered point back through the inverse branch on the genuine source.
          simpa [holomorphicIsomorph_symm] using
            (φ : OpenPartialHomeomorph ℂ ℂ).left_inv hx_source
        simpa [hx_cancel] using hx
      · intro hz
        have hz_source : z ∈ (φ : OpenPartialHomeomorph ℂ ℂ).source := by
          simpa [φ.source_eq] using hsub hz
        have hz_image : φ z ∈ Metric.ball (0 : ℂ) s := by
          have : φ z ∈ (φ : ℂ → ℂ) '' Metric.ball c ρ := ⟨z, hz, rfl⟩
          simpa [hφ] using this
        refine ⟨φ z, hz_image, ?_⟩
        -- Push the source point forward and then cancel with the inverse branch.
        simpa [holomorphicIsomorph_symm] using
          (φ : OpenPartialHomeomorph ℂ ℂ).left_inv hz_source
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz_preimage : (holomorphicIsomorph_symm φ) z ∈ Metric.ball c ρ := by
        have : (holomorphicIsomorph_symm φ) z ∈
            ((holomorphicIsomorph_symm φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1)
              (Metric.ball (0 : ℂ) 1)) : ℂ → ℂ) '' Metric.ball (0 : ℂ) s := ⟨z, hz, rfl⟩
        simpa [hsymm_image] using this
      exact ⟨(holomorphicIsomorph_symm φ) z, hz_preimage, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hz_preimage : z ∈
          ((holomorphicIsomorph_symm φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1)
            (Metric.ball (0 : ℂ) 1)) : ℂ → ℂ) '' Metric.ball (0 : ℂ) s := by
        simpa [hsymm_image] using hz
      rcases hz_preimage with ⟨w, hw, hwz⟩
      -- Rewrite the witness through the inverse-image equality furnished above.
      exact ⟨w, hw, by simpa [Function.comp, hwz]⟩

/-- Helper for Exercise 3: a proper Euclidean subdisc of the unit disc is itself contained in the
unit disc. -/
private theorem proper_subdisc_subset_unit
    {c : ℂ} {ρ : ℝ} (hproper : ‖c‖ + ρ < 1) :
    Metric.ball c ρ ⊆ Metric.ball (0 : ℂ) 1 := by
  intro z hz
  have hzρ : ‖z - c‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz_le : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_add_le (z - c) c
  have hz_lt : ‖z‖ < 1 := by
    linarith
  simpa [mem_ball_zero_iff] using hz_lt

/-- Helper for Exercise 3: the real-axis centering parameter is the smaller root of the quadratic
forcing the two real endpoints `d ± ρ` to map to opposite points under a disc automorphism. -/
private theorem real_axis_center_parameter_exists
    {d ρ : ℝ} (hd_pos : 0 < d) (hρ_pos : 0 < ρ) (hproper : d + ρ < 1) :
    ∃ a, 0 < a ∧ a < d + ρ ∧ d * a ^ 2 - (1 + d ^ 2 - ρ ^ 2) * a + d = 0 := by
  let q : ℝ → ℝ := fun a ↦ d * a ^ 2 - (1 + d ^ 2 - ρ ^ 2) * a + d
  have hq_cont : Continuous q := by
    -- The parameter equation is polynomial, so the interval root comes from the IVT.
    continuity
  have hq_zero_pos : 0 < q 0 := by
    -- At `0` the quadratic equals `d`, which is positive.
    simp [q, hd_pos]
  have hsum_pos : 0 < d + ρ := by
    linarith
  have hq_right_neg : q (d + ρ) < 0 := by
    -- At the outer endpoint `d + ρ`, the quadratic becomes `-ρ * (1 - (d + ρ)^2)`.
    have hunit_gap : 0 < 1 - (d + ρ) ^ 2 := by
      nlinarith
    have hq_right :
        q (d + ρ) = -ρ * (1 - (d + ρ) ^ 2) := by
      dsimp [q]
      ring
    rw [hq_right]
    nlinarith
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (q (d + ρ)) (q 0) := by
    constructor <;> linarith
  rcases (intermediate_value_Icc' (a := 0) (b := d + ρ) hsum_pos.le hq_cont.continuousOn)
      hzero_mem with ⟨a, ha_mem, hqa⟩
  have ha_ne_zero : a ≠ 0 := by
    intro ha_zero
    subst ha_zero
    have : d = 0 := by
      simpa [q] using hqa
    linarith
  have ha_ne_right : a ≠ d + ρ := by
    intro ha_right
    subst ha_right
    linarith
  refine ⟨a, ?_, ?_, hqa⟩
  · -- The root is strict because the left endpoint was not a root.
    exact lt_of_le_of_ne ha_mem.1 (Ne.symm ha_ne_zero)
  · -- The same endpoint exclusion places the chosen root strictly before `d + ρ`.
    exact lt_of_le_of_ne ha_mem.2 ha_ne_right

/-- Helper for Exercise 3: after clearing the canonical denominator, the real Möbius inequality
for `discCenter (a : ℂ)` is exactly the Euclidean ball inequality for the standard center/radius
parameters. -/
private theorem disc_center_real_standard_gap_identity (a s : ℝ) (z : ℂ) :
    let N : ℝ := 1 - s ^ 2 * a ^ 2
    let c : ℝ := ((1 - s ^ 2) * a) / N
    let r : ℝ := s * (1 - a ^ 2) / N
    N ^ 2 * (Complex.normSq (z - (c : ℂ)) - r ^ 2) =
      N * (Complex.normSq (z - (a : ℂ)) - s ^ 2 * Complex.normSq (1 - (a : ℂ) * z)) := by
  -- Route correction: split first on the canonical denominator `N` before clearing it, so the
  -- algebra only runs in the genuine nonzero-denominator branch.
  dsimp
  by_cases hN : 1 - s ^ 2 * a ^ 2 = 0
  · -- When `N = 0`, both standard parameters are zero by definition, so the identity collapses.
    simp [hN]
  · -- In the nonzero branch, expand `normSq`, clear the real denominator, and normalize.
    rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.normSq_apply, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
    field_simp [hN]
    ring_nf

/-- Helper for Exercise 3: for a real center parameter, belonging to the centered image ball is
equivalent to belonging to the Euclidean ball with the canonical center/radius formulas. -/
private theorem disc_center_mem_ball_iff_real_standard_parameters
    {a s : ℝ} (ha_nonneg : 0 ≤ a) (ha_lt : a < 1) (hs_pos : 0 < s) (hs_lt : s < 1)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    discCenter (a : ℂ) z ∈ Metric.ball (0 : ℂ) s ↔
      z ∈ Metric.ball ((((1 - s ^ 2) * a) / (1 - s ^ 2 * a ^ 2) : ℝ) : ℂ)
        (s * (1 - a ^ 2) / (1 - s ^ 2 * a ^ 2)) := by
  let N : ℝ := 1 - s ^ 2 * a ^ 2
  let c : ℝ := ((1 - s ^ 2) * a) / N
  let r : ℝ := s * (1 - a ^ 2) / N
  have ha_ball : (a : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    -- The real centering parameter lies in the unit disc.
    simpa [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ha_nonneg] using ha_lt
  have hden_ne : 1 - conj (a : ℂ) * z ≠ 0 := disc_center_denom_ne_zero ha_ball hz
  have hN_pos : 0 < N := by
    -- The standard denominator stays positive because both real parameters lie in `(0, 1)`.
    have ha_sq_lt : a ^ 2 < 1 := by
      nlinarith [ha_nonneg, ha_lt]
    have hs_sq_lt : s ^ 2 < 1 := by
      nlinarith [hs_pos, hs_lt]
    have hprod_lt : s ^ 2 * a ^ 2 < 1 := by
      nlinarith [ha_sq_lt, hs_sq_lt, sq_nonneg a, sq_nonneg s]
    dsimp [N]
    linarith
  have hr_pos : 0 < r := by
    -- The Euclidean radius is positive once both the numerator and denominator are.
    dsimp [r, N]
    have ha_sq_pos : 0 < 1 - a ^ 2 := by
      nlinarith [ha_nonneg, ha_lt]
    exact div_pos (mul_pos hs_pos ha_sq_pos) hN_pos
  have hcenter_sq :
      discCenter (a : ℂ) z ∈ Metric.ball (0 : ℂ) s ↔
        Complex.normSq (z - (a : ℂ)) < s ^ 2 * Complex.normSq (1 - (a : ℂ) * z) := by
    constructor
    · intro h
      have hnorm_lt : ‖discCenter (a : ℂ) z‖ < s := by
        simpa [Metric.mem_ball, dist_eq_norm] using h
      have hnormSq_lt : Complex.normSq (discCenter (a : ℂ) z) < s ^ 2 := by
        have hsq_lt : ‖discCenter (a : ℂ) z‖ ^ 2 < s ^ 2 := by
          nlinarith [norm_nonneg (discCenter (a : ℂ) z), hs_pos, hnorm_lt]
        simpa [Complex.normSq_eq_norm_sq] using hsq_lt
      rw [discCenter, Complex.normSq_div] at hnormSq_lt
      have hden_pos : 0 < Complex.normSq (1 - conj (a : ℂ) * z) := Complex.normSq_pos.mpr hden_ne
      have hnum_lt :
          Complex.normSq (z - (a : ℂ)) <
            s ^ 2 * Complex.normSq (1 - conj (a : ℂ) * z) := by
        rw [div_lt_iff₀ hden_pos] at hnormSq_lt
        exact hnormSq_lt
      simpa [Complex.conj_ofReal] using hnum_lt
    · intro h
      have hden_pos : 0 < Complex.normSq (1 - conj (a : ℂ) * z) := Complex.normSq_pos.mpr hden_ne
      have hnormSq_lt : Complex.normSq (discCenter (a : ℂ) z) < s ^ 2 := by
        rw [discCenter, Complex.normSq_div]
        rw [div_lt_iff₀ hden_pos]
        simpa [Complex.conj_ofReal] using h
      have hnorm_lt : ‖discCenter (a : ℂ) z‖ < s := by
        have hsq_lt : ‖discCenter (a : ℂ) z‖ ^ 2 < s ^ 2 := by
          simpa [Complex.normSq_eq_norm_sq] using hnormSq_lt
        nlinarith [norm_nonneg (discCenter (a : ℂ) z), hs_pos]
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt
  have hball_sq :
      z ∈ Metric.ball (c : ℂ) r ↔ Complex.normSq (z - (c : ℂ)) < r ^ 2 := by
    constructor
    · intro h
      have hnorm_lt : ‖z - (c : ℂ)‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using h
      have hsq_lt : ‖z - (c : ℂ)‖ ^ 2 < r ^ 2 := by
        nlinarith [norm_nonneg (z - (c : ℂ)), hr_pos, hnorm_lt]
      simpa [Complex.normSq_eq_norm_sq] using hsq_lt
    · intro h
      have hnorm_lt : ‖z - (c : ℂ)‖ < r := by
        have hsq_lt : ‖z - (c : ℂ)‖ ^ 2 < r ^ 2 := by
          simpa [Complex.normSq_eq_norm_sq] using h
        nlinarith [norm_nonneg (z - (c : ℂ)), hr_pos]
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt
  have hgap := disc_center_real_standard_gap_identity a s z
  have hbridge :
      Complex.normSq (z - (a : ℂ)) < s ^ 2 * Complex.normSq (1 - (a : ℂ) * z) ↔
        Complex.normSq (z - (c : ℂ)) < r ^ 2 := by
    constructor
    · intro h
      have hleft :
          N * (Complex.normSq (z - (a : ℂ)) - s ^ 2 * Complex.normSq (1 - (a : ℂ) * z)) < 0 := by
        nlinarith [hN_pos, h]
      rw [← hgap] at hleft
      have : Complex.normSq (z - (c : ℂ)) - r ^ 2 < 0 := by
        nlinarith [hleft, hN_pos]
      nlinarith
    · intro h
      have hN_sq_pos : 0 < N ^ 2 := sq_pos_of_pos hN_pos
      have hleft : N ^ 2 * (Complex.normSq (z - (c : ℂ)) - r ^ 2) < 0 := by
        nlinarith [hN_sq_pos, h]
      rw [hgap] at hleft
      have : Complex.normSq (z - (a : ℂ)) - s ^ 2 * Complex.normSq (1 - (a : ℂ) * z) < 0 := by
        nlinarith [hleft, hN_pos]
      nlinarith
  -- Normalize both membership statements to squared inequalities, then transport them across the
  -- canonical denominator-cleared Möbius identity.
  rw [hcenter_sq, hball_sq]
  exact hbridge

/-- Helper for Exercise 3: the endpoint equalities for the centered real-axis disc determine the
two normalized endpoints `d ± ρ` explicitly. -/
private theorem real_axis_endpoint_values_of_centering
    {a d ρ s : ℝ}
    (ha_pos : 0 < a) (ha_lt : a < 1) (hs_pos : 0 < s) (hs_lt : s < 1)
    (hplus : discCenter (a : ℂ) ((d + ρ) : ℂ) = (s : ℂ))
    (hminus : discCenter (a : ℂ) ((d - ρ) : ℂ) = (-s : ℂ)) :
    d + ρ = (a + s) / (1 + a * s) ∧
      d - ρ = (a - s) / (1 - a * s) := by
  have hplus_real : (d + ρ - a) / (1 - a * (d + ρ)) = s := by
    apply Complex.ofReal_injective
    simpa [discCenter, Complex.conj_ofReal] using hplus
  have hminus_real : (d - ρ - a) / (1 - a * (d - ρ)) = -s := by
    apply Complex.ofReal_injective
    simpa [discCenter, Complex.conj_ofReal] using hminus
  have hden_plus_ne : 1 - a * (d + ρ) ≠ 0 := by
    intro hzero
    have hzero_complex : 1 - (a : ℂ) * ((d : ℂ) + (ρ : ℂ)) = 0 := by
      exact_mod_cast hzero
    have hs_zero : (s : ℂ) = 0 := by
      calc
        (s : ℂ) = discCenter (a : ℂ) ((d + ρ) : ℂ) := hplus.symm
        _ = (((d : ℂ) + (ρ : ℂ) - (a : ℂ)) / 0) := by
          rw [discCenter, Complex.conj_ofReal, hzero_complex]
        _ = (((d + ρ - a : ℝ) : ℂ) / 0) := by norm_num
        _ = 0 := by simp
    exact hs_pos.ne' (Complex.ofReal_injective hs_zero)
  have hden_minus_ne : 1 - a * (d - ρ) ≠ 0 := by
    intro hzero
    have hzero_complex : 1 - (a : ℂ) * ((d : ℂ) - (ρ : ℂ)) = 0 := by
      exact_mod_cast hzero
    have hs_zero : (-s : ℂ) = 0 := by
      calc
        (-s : ℂ) = discCenter (a : ℂ) ((d - ρ) : ℂ) := by simpa using hminus.symm
        _ = (((d : ℂ) - (ρ : ℂ) - (a : ℂ)) / 0) := by
          rw [discCenter, Complex.conj_ofReal, hzero_complex]
        _ = (((d - ρ - a : ℝ) : ℂ) / 0) := by norm_num
        _ = 0 := by simp
    have : s = 0 := by
      have : (-s : ℝ) = 0 := by
        exact_mod_cast hs_zero
      linarith
    exact hs_pos.ne' this
  have hplus_value : d + ρ = (a + s) / (1 + a * s) := by
    have hden_pos : 0 < 1 + a * s := by
      nlinarith [ha_pos, hs_pos]
    apply (eq_div_iff hden_pos.ne').2
    have hcross : d + ρ - a = s * (1 - a * (d + ρ)) := by
      exact (div_eq_iff hden_plus_ne).mp hplus_real
    nlinarith
  have hminus_value : d - ρ = (a - s) / (1 - a * s) := by
    have hden_pos : 0 < 1 - a * s := by
      nlinarith [ha_pos, ha_lt, hs_pos, hs_lt]
    apply (eq_div_iff hden_pos.ne').2
    have hcross : d - ρ - a = -s * (1 - a * (d - ρ)) := by
      exact (div_eq_iff hden_minus_ne).mp hminus_real
    nlinarith
  exact ⟨hplus_value, hminus_value⟩

/-- Helper for Exercise 3: the endpoint normalization determines the canonical Euclidean center
and radius parameters. -/
private theorem real_axis_parameters_of_endpoint_normalization
    {a d ρ s : ℝ}
    (ha_pos : 0 < a) (ha_lt : a < 1) (hs_pos : 0 < s) (hs_lt : s < 1)
    (hplus : discCenter (a : ℂ) ((d + ρ) : ℂ) = (s : ℂ))
    (hminus : discCenter (a : ℂ) ((d - ρ) : ℂ) = (-s : ℂ)) :
    d = ((1 - s ^ 2) * a) / (1 - s ^ 2 * a ^ 2) ∧
      ρ = s * (1 - a ^ 2) / (1 - s ^ 2 * a ^ 2) := by
  rcases real_axis_endpoint_values_of_centering ha_pos ha_lt hs_pos hs_lt hplus hminus with
    ⟨hplus_value, hminus_value⟩
  have hden_plus_pos : 0 < 1 + a * s := by
    nlinarith [ha_pos, hs_pos]
  have hden_minus_pos : 0 < 1 - a * s := by
    nlinarith [ha_pos, ha_lt, hs_pos, hs_lt]
  have hN_pos : 0 < 1 - s ^ 2 * a ^ 2 := by
    nlinarith [ha_pos, ha_lt, hs_pos, hs_lt]
  have hN'_pos : 0 < 1 - a ^ 2 * s ^ 2 := by
    nlinarith [ha_pos, ha_lt, hs_pos, hs_lt]
  constructor
  · -- Average the two endpoint formulas to recover the Euclidean center.
    calc
      d = ((d + ρ) + (d - ρ)) / 2 := by ring
      _ = (((a + s) / (1 + a * s)) + ((a - s) / (1 - a * s))) / 2 := by
        rw [hplus_value, hminus_value]
      _ = ((1 - s ^ 2) * a) / (1 - s ^ 2 * a ^ 2) := by
        field_simp [hden_plus_pos.ne', hden_minus_pos.ne', hN_pos.ne', hN'_pos.ne']
        ring
  · -- Subtract the two endpoint formulas to recover the Euclidean radius.
    calc
      ρ = ((d + ρ) - (d - ρ)) / 2 := by ring
      _ = (((a + s) / (1 + a * s)) - ((a - s) / (1 - a * s))) / 2 := by
        rw [hplus_value, hminus_value]
      _ = s * (1 - a ^ 2) / (1 - s ^ 2 * a ^ 2) := by
        field_simp [hden_plus_pos.ne', hden_minus_pos.ne', hN_pos.ne', hN'_pos.ne']
        ring

/-- Helper for Exercise 3: the inverse real disc automorphism sends the centered disc `ball 0 s`
onto the Euclidean disc with the canonical center/radius formulas. -/
private theorem disc_uncenter_image_centered_ball_real_standard
    {a s : ℝ} (ha_nonneg : 0 ≤ a) (ha_lt : a < 1) (hs_pos : 0 < s) (hs_lt : s < 1) :
    discUncenter (a : ℂ) '' Metric.ball (0 : ℂ) s =
      Metric.ball ((((1 - s ^ 2) * a) / (1 - s ^ 2 * a ^ 2) : ℝ) : ℂ)
        (s * (1 - a ^ 2) / (1 - s ^ 2 * a ^ 2)) := by
  let c : ℝ := ((1 - s ^ 2) * a) / (1 - s ^ 2 * a ^ 2)
  let r : ℝ := s * (1 - a ^ 2) / (1 - s ^ 2 * a ^ 2)
  have hN_pos : 0 < 1 - s ^ 2 * a ^ 2 := by
    -- The canonical denominator remains positive throughout the real-axis normalization.
    have ha_sq_lt : a ^ 2 < 1 := by
      nlinarith [ha_nonneg, ha_lt]
    have hs_sq_lt : s ^ 2 < 1 := by
      nlinarith [hs_pos, hs_lt]
    have hprod_lt : s ^ 2 * a ^ 2 < 1 := by
      nlinarith [ha_sq_lt, hs_sq_lt, sq_nonneg a, sq_nonneg s]
    linarith
  have ha_ball : (a : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    -- The real Möbius parameter lies in the unit disc.
    simpa [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ha_nonneg] using ha_lt
  have hneg_ball : ((-a : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    -- The opposite parameter is still in the unit disc.
    simpa [mem_ball_zero_iff, norm_neg] using ha_ball
  have hs_subset : Metric.ball (0 : ℂ) s ⊆ Metric.ball (0 : ℂ) 1 := by
    -- The smaller centered disc sits inside the unit disc.
    intro z hz
    exact mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hs_lt)
  have hright : Set.LeftInvOn (discCenter (a : ℂ)) (discUncenter (a : ℂ)) (Metric.ball (0 : ℂ) 1) := by
    -- `discCenter a` is the inverse branch of `discUncenter a` on the unit disc.
    intro z hz
    simpa [discUncenter] using (disc_uncenter_leftInvOn_disc_center hneg_ball hz)
  have hproper_std : ‖(c : ℂ)‖ + r < 1 := by
    -- The canonical center/radius recover the outer endpoint `(a + s) / (1 + a s)`, which stays
    -- inside the unit disc.
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      have hs_sq_nonneg : 0 ≤ 1 - s ^ 2 := by
        nlinarith [hs_pos, hs_lt]
      exact div_nonneg (mul_nonneg hs_sq_nonneg ha_nonneg) hN_pos.le
    have hsum :
        c + r = (a + s) / (1 + s * a) := by
      dsimp [c, r]
      field_simp [hN_pos.ne']
      ring
    have hden_pos : 0 < 1 + s * a := by
      nlinarith [ha_nonneg, hs_pos]
    have hlt : (a + s) / (1 + s * a) < 1 := by
      exact (div_lt_one hden_pos).2 (by nlinarith [ha_lt, hs_lt, ha_nonneg, hs_pos])
    rw [Complex.norm_real, Real.norm_of_nonneg hc_nonneg, hsum]
    exact hlt
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw_unit : w ∈ Metric.ball (0 : ℂ) 1 := hs_subset hw
    have hz_unit : discUncenter (a : ℂ) w ∈ Metric.ball (0 : ℂ) 1 :=
      disc_uncenter_mapsTo_unit_ball ha_ball hw_unit
    have hcenter_mem : discCenter (a : ℂ) (discUncenter (a : ℂ) w) ∈ Metric.ball (0 : ℂ) s := by
      have hright_eq : discCenter (a : ℂ) (discUncenter (a : ℂ) w) = w := hright hw_unit
      simpa [hright_eq] using hw
    exact (disc_center_mem_ball_iff_real_standard_parameters
      ha_nonneg ha_lt hs_pos hs_lt hz_unit).mp hcenter_mem
  · intro hz
    have hz_unit : z ∈ Metric.ball (0 : ℂ) 1 := proper_subdisc_subset_unit hproper_std hz
    have hcenter_mem : discCenter (a : ℂ) z ∈ Metric.ball (0 : ℂ) s :=
      (disc_center_mem_ball_iff_real_standard_parameters
        ha_nonneg ha_lt hs_pos hs_lt hz_unit).mpr hz
    refine ⟨discCenter (a : ℂ) z, hcenter_mem, ?_⟩
    exact disc_uncenter_leftInvOn_disc_center ha_ball hz_unit

/-- Helper for Exercise 3: once the off-center disc has been rotated onto the positive real axis,
the remaining geometric step is to center that real-axis subdisc by a disc automorphism. -/
private theorem real_axis_subdisc_has_centering_automorphism
    {d ρ : ℝ} (hd_pos : 0 < d) (hρ_pos : 0 < ρ) (hproper : d + ρ < 1) :
    ∃ s : ℝ,
      0 < s ∧ s < 1 ∧
      ∃ φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1),
        (φ : ℂ → ℂ) '' Metric.ball (d : ℂ) ρ = Metric.ball (0 : ℂ) s := by
  rcases real_axis_center_parameter_exists hd_pos hρ_pos hproper with
    ⟨a, ha_pos, ha_lt_right, hquad⟩
  let s : ℝ := (d + ρ - a) / (1 - a * (d + ρ))
  have ha_lt_one : a < 1 := by
    linarith
  have hmul_lt_sq : a * (d + ρ) < (d + ρ) ^ 2 := by
    -- The smaller root lies strictly inside the outer endpoint, so its product is bounded by the
    -- endpoint square.
    nlinarith [ha_pos, ha_lt_right]
  have hsq_lt_one : (d + ρ) ^ 2 < 1 := by
    nlinarith [hd_pos, hρ_pos, hproper]
  have hden_pos : 0 < 1 - a * (d + ρ) := by
    -- This denominator is positive because both real parameters lie in `(0, 1)`.
    linarith
  have hden_minus_pos : 0 < 1 - a * (d - ρ) := by
    -- The second endpoint denominator is even larger than the outer one.
    have hmul_lt : a * (d - ρ) < a * (d + ρ) := by
      nlinarith [ha_pos, hρ_pos]
    linarith
  have hs_pos : 0 < s := by
    -- The chosen `a` lies before the outer endpoint, so the centered radius is positive.
    have hnum_pos : 0 < d + ρ - a := by
      linarith
    dsimp [s]
    exact div_pos hnum_pos hden_pos
  have hs_lt : s < 1 := by
    -- Comparing numerator and denominator gives the strict unit-disc radius bound.
    have hgap_pos : 0 < (1 - a * (d + ρ)) - (d + ρ - a) := by
      have hproper_gap : 0 < 1 - d - ρ := by
        linarith
      have hplus_pos : 0 < 1 + a := by
        linarith
      have hgap :
          (1 - a * (d + ρ)) - (d + ρ - a) = (1 - d - ρ) * (1 + a) := by
        ring
      rw [hgap]
      exact mul_pos hproper_gap hplus_pos
    have hnum_lt : d + ρ - a < 1 - a * (d + ρ) := by
      linarith
    dsimp [s]
    exact (div_lt_one hden_pos).2 hnum_lt
  have ha_ball : (a : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    -- The real parameter belongs to the unit disc, so the Möbius map is a disc automorphism.
    simpa [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ha_pos.le] using ha_lt_one
  have h_endpoint_plus_real : (d + ρ - a) / (1 - a * (d + ρ)) = s := by
    -- Keep the real endpoint normalization in scalar form for the later parameter rewrite.
    rfl
  have h_endpoint_minus_real : (d - ρ - a) / (1 - a * (d - ρ)) = -s := by
    -- The quadratic relation is exactly the cross-multiplied symmetry of the two endpoints.
    change (d - ρ - a) / (1 - a * (d - ρ)) =
      -((d + ρ - a) / (1 - a * (d + ρ)))
    rw [← neg_div]
    apply (div_eq_iff hden_minus_pos.ne').2
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden_pos.ne').2
    nlinarith [hquad]
  have h_endpoint_plus : discCenter (a : ℂ) ((d + ρ) : ℂ) = (s : ℂ) := by
    -- The outer endpoint defines `s` by construction.
    simpa [discCenter, s, Complex.conj_ofReal] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) h_endpoint_plus_real
  have h_endpoint_minus : discCenter (a : ℂ) ((d - ρ) : ℂ) = (-s : ℂ) := by
    -- The lower endpoint is the symmetric counterpart of the upper endpoint.
    simpa [discCenter, Complex.conj_ofReal] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) h_endpoint_minus_real
  have hparams := real_axis_parameters_of_endpoint_normalization
    ha_pos ha_lt_one hs_pos hs_lt h_endpoint_plus h_endpoint_minus
  rcases hparams with ⟨hd_formula, hρ_formula⟩
  have hneg_ball : ((-a : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    -- The automorphism package uses `discUncenter (-a) = discCenter a`.
    simpa [mem_ball_zero_iff, norm_neg] using ha_ball
  have hproper_complex : ‖((d : ℝ) : ℂ)‖ + ρ < 1 := by
    -- The real-axis disc is a proper subdisc of the unit disc.
    simpa [Complex.norm_real, Real.norm_of_nonneg hd_pos.le] using hproper
  have hstd_image :
      discUncenter (a : ℂ) '' Metric.ball (0 : ℂ) s = Metric.ball (d : ℂ) ρ := by
    -- Route correction: use the canonical `(a,s)` image theorem first, then rewrite it back to
    -- the source coordinates `d, ρ` using the endpoint normalization formulas above.
    rw [disc_uncenter_image_centered_ball_real_standard ha_pos.le ha_lt_one hs_pos hs_lt,
      hd_formula, hρ_formula]
  rcases disc_uncenter_automorphism_local hneg_ball with ⟨φ, hφ⟩
  have hs_subset : Metric.ball (0 : ℂ) s ⊆ Metric.ball (0 : ℂ) 1 := by
    -- The centered radius is strictly smaller than `1`.
    intro z hz
    exact mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hz) hs_lt)
  have hright : Set.LeftInvOn (discCenter (a : ℂ)) (discUncenter (a : ℂ)) (Metric.ball (0 : ℂ) 1) := by
    -- `discCenter a` is the inverse branch of `discUncenter a` on the unit disc.
    intro z hz
    simpa [discUncenter] using (disc_uncenter_leftInvOn_disc_center hneg_ball hz)
  refine ⟨s, hs_pos, hs_lt, φ, ?_⟩
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw_image : w ∈ discUncenter (a : ℂ) '' Metric.ball (0 : ℂ) s := by
      simpa [hstd_image] using hw
    rcases hw_image with ⟨u, hu, rfl⟩
    have hw_ball : discUncenter (a : ℂ) u ∈ Metric.ball (d : ℂ) ρ := by
      have : discUncenter (a : ℂ) u ∈ discUncenter (a : ℂ) '' Metric.ball (0 : ℂ) s := ⟨u, hu, rfl⟩
      simpa [hstd_image] using this
    have hw_unit : discUncenter (a : ℂ) u ∈ Metric.ball (0 : ℂ) 1 := by
      exact proper_subdisc_subset_unit hproper_complex hw_ball
    have hu_unit : u ∈ Metric.ball (0 : ℂ) 1 := hs_subset hu
    have hφ_eq : φ (discUncenter (a : ℂ) u) = discCenter (a : ℂ) (discUncenter (a : ℂ) u) := by
      simpa [discUncenter] using hφ hw_unit
    have hright_eq : discCenter (a : ℂ) (discUncenter (a : ℂ) u) = u := hright hu_unit
    simpa [hφ_eq, hright_eq] using hu
  · intro hz
    have hw : discUncenter (a : ℂ) z ∈ Metric.ball (d : ℂ) ρ := by
      have : discUncenter (a : ℂ) z ∈ discUncenter (a : ℂ) '' Metric.ball (0 : ℂ) s := ⟨z, hz, rfl⟩
      simpa [hstd_image] using this
    have hw_unit : discUncenter (a : ℂ) z ∈ Metric.ball (0 : ℂ) 1 :=
      proper_subdisc_subset_unit hproper_complex hw
    have hz_unit : z ∈ Metric.ball (0 : ℂ) 1 := hs_subset hz
    refine ⟨discUncenter (a : ℂ) z, hw, ?_⟩
    have hφ_eq : φ (discUncenter (a : ℂ) z) = discCenter (a : ℂ) (discUncenter (a : ℂ) z) := by
      simpa [discUncenter] using hφ hw_unit
    have hright_eq : discCenter (a : ℂ) (discUncenter (a : ℂ) z) = z := hright hz_unit
    simpa [hφ_eq, hright_eq]

/-- Helper for Exercise 3: every proper off-center subdisc of the unit disc can be carried to a
centered subdisc by a holomorphic automorphism of the unit disc. -/
private theorem proper_subdisc_has_centering_automorphism
    {c : ℂ} {ρ : ℝ} (hc : c ≠ 0) (hρ_pos : 0 < ρ) (hproper : ‖c‖ + ρ < 1) :
    ∃ s : ℝ,
      0 < s ∧ s < 1 ∧
      ∃ φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1),
        (φ : ℂ → ℂ) '' Metric.ball c ρ = Metric.ball (0 : ℂ) s := by
  let u : ℂ := conj c / ‖c‖
  have hnorm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hu : ‖u‖ = 1 := by
    -- The scalar `conj c / ‖c‖` has unit norm, so it rotates `c` onto the positive real axis.
    dsimp [u]
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg c)]
    field_simp [norm_ne_zero_iff.mpr hc]
  have huc : u * c = (‖c‖ : ℂ) := by
    -- Multiplying by `conj c / ‖c‖` collapses the argument of `c`.
    dsimp [u]
    have hnorm_ne : ‖c‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hc
    have hnorm_ne_complex : (‖c‖ : ℂ) ≠ 0 := by
      exact_mod_cast hnorm_ne
    apply (mul_right_injective₀ hnorm_ne_complex)
    field_simp [hnorm_ne]
    rw [Complex.conj_mul']
  rcases real_axis_subdisc_has_centering_automorphism hnorm_pos hρ_pos hproper with
    ⟨s, hs_pos, hs_lt, ψ, hψ⟩
  rcases unit_scalar_automorphism_local hu with ⟨χ, hχ⟩
  have hsub : Metric.ball c ρ ⊆ Metric.ball (0 : ℂ) 1 :=
    proper_subdisc_subset_unit hproper
  have hχ_image :
      (χ : ℂ → ℂ) '' Metric.ball c ρ = Metric.ball ((‖c‖ : ℂ)) ρ := by
    -- Replace the packaged automorphism by the raw rotation on the proper source disc.
    calc
      (χ : ℂ → ℂ) '' Metric.ball c ρ = (fun z : ℂ ↦ u * z) '' Metric.ball c ρ := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨w, hw, (hχ (hsub hw)).symm⟩
        · rintro ⟨w, hw, rfl⟩
          exact ⟨w, hw, hχ (hsub hw)⟩
      _ = Metric.ball (u * c) ρ := unit_scalar_image_ball hu
      _ = Metric.ball ((‖c‖ : ℂ)) ρ := by rw [huc]
  let φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := χ.trans ψ
  refine ⟨s, hs_pos, hs_lt, φ, ?_⟩
  -- Route correction: the off-center case now factors through an explicit rotation to the real
  -- axis, so only the real-axis centering geometry remains isolated in the helper above.
  calc
    (φ : ℂ → ℂ) '' Metric.ball c ρ = (ψ : ℂ → ℂ) '' ((χ : ℂ → ℂ) '' Metric.ball c ρ) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨χ w, ⟨w, hw, rfl⟩, ?_⟩
        simp [φ, HolomorphicIsomorph.trans, OpenPartialHomeomorph.trans_apply, Function.comp_def]
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨v, hv, ?_⟩
        simp [φ, HolomorphicIsomorph.trans, OpenPartialHomeomorph.trans_apply, Function.comp_def]
    _ = (ψ : ℂ → ℂ) '' Metric.ball ((‖c‖ : ℂ)) ρ := by rw [hχ_image]
    _ = Metric.ball (0 : ℂ) s := hψ

/-- Helper for Exercise 3: once the geometric centering automorphism is available, convexity of a
proper subdisc image follows by precomposing with its inverse and applying the centered case. -/
private theorem convex_image_of_open_disc_of_centering_automorphism
    {c : ℂ} {ρ s : ℝ}
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hD_convex : Convex ℝ D_[1])
    (φ : HolomorphicIsomorph (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1))
    (hs_lt : s < 1)
    (hsub : Metric.ball c ρ ⊆ Metric.ball (0 : ℂ) 1)
    (hφ : (φ : ℂ → ℂ) '' Metric.ball c ρ = Metric.ball (0 : ℂ) s) :
    Convex ℝ (f '' Metric.ball c ρ) := by
  let g : ℂ → ℂ := f ∘ holomorphicIsomorph_symm φ
  have hg_diff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1) := by
    -- Differentiate the precomposed map by composing `f` with the inverse automorphism.
    simpa [g] using
      hf_analytic.differentiableOn.comp
        (holomorphicIsomorph_symm φ).analyticOn_toFun.differentiableOn
        (holomorphicIsomorph_mapsTo (holomorphicIsomorph_symm φ))
  have hg_analytic : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) 1) := by
    -- Convert the differentiability-on-ball owner back into the analytic-on-neighborhood owner.
    exact (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 hg_diff
  have hleft_symm :
      Set.LeftInvOn (φ : ℂ → ℂ) (holomorphicIsomorph_symm φ) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz_source :
        z ∈ ((holomorphicIsomorph_symm φ : OpenPartialHomeomorph ℂ ℂ).source) := by
      simpa [(holomorphicIsomorph_symm φ).source_eq] using hz
    simpa [holomorphicIsomorph_symm] using
      ((holomorphicIsomorph_symm φ : OpenPartialHomeomorph ℂ ℂ).left_inv hz_source)
  have hsymm_inj : Set.InjOn (holomorphicIsomorph_symm φ) (Metric.ball (0 : ℂ) 1) :=
    hleft_symm.injOn
  have hg_inj : Set.InjOn g (Metric.ball (0 : ℂ) 1) := by
    intro z hz w hw hzw
    apply hsymm_inj hz hw
    apply hf_inj
    · exact holomorphicIsomorph_mapsTo (holomorphicIsomorph_symm φ) hz
    · exact holomorphicIsomorph_mapsTo (holomorphicIsomorph_symm φ) hw
    simpa [g] using hzw
  have hdiscImage :
      discImage g 1 = D_[1] ∧ discImage g s = f '' Metric.ball c ρ :=
    discImage_precompose_symm_eq_image_ball (f := f) φ hsub hφ
  rcases hdiscImage with ⟨hg_one, hg_s⟩
  have hg_convex : Convex ℝ (discImage g 1) := by
    -- Rewrite the full image of `g` back to the original convex owner `D_[1]`.
    simpa [hg_one] using hD_convex
  have hg_small_convex : Convex ℝ (discImage g s) :=
    convex_discImage (f := g) hg_analytic hg_inj hg_convex hs_lt
  -- The centered-radius convexity statement is exactly the original image after rewriting.
  simpa [hg_s] using hg_small_convex

/-- Helper for Exercise 3: the source-faithful automorphism reduction proves convexity first for
proper subdiscs strictly contained in the unit disc. -/
private theorem convex_image_of_open_disc_strict
    {c : ℂ} {ρ : ℝ}
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hD_convex : Convex ℝ D_[1])
    (hρ_pos : 0 < ρ)
    (hproper : ‖c‖ + ρ < 1) :
    Convex ℝ (f '' Metric.ball c ρ) := by
  -- Route correction: the global automorphism claim is false on tangent discs, so the source
  -- proof must first be carried out only for proper subdiscs `‖c‖ + ρ < 1`.
  by_cases hc_zero : c = 0
  · subst hc_zero
    have hρ_lt : ρ < 1 := by
      simpa using hproper
    -- In the centered case the target set is exactly the textbook family `D_[ρ]`.
    simpa [discImage] using convex_discImage hf_analytic hf_inj hD_convex hρ_lt
  · have hsub : Metric.ball c ρ ⊆ Metric.ball (0 : ℂ) 1 :=
      proper_subdisc_subset_unit hproper
    rcases proper_subdisc_has_centering_automorphism hc_zero hρ_pos hproper with
      ⟨s, hs_pos, hs_lt, φ, hφ⟩
    -- Once the proper subdisc has been centered by an automorphism, the convexity proof is the
    -- already-verified centered case applied to the precomposed map.
    exact convex_image_of_open_disc_of_centering_automorphism
      hf_analytic hf_inj hD_convex φ hs_lt hsub hφ

/-- Exercise 3 (4): if `D = f(B)` is convex, then the image of every open disc contained in `B`
is convex as well; for `ρ ≤ 0`, the source disc is empty. -/
theorem convex_image_of_open_disc
    {c : ℂ} {ρ : ℝ}
    (hf_analytic : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_inj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (hD_convex : Convex ℝ D_[1])
    (hdisc_subset : Metric.ball c ρ ⊆ Metric.ball (0 : ℂ) 1) :
    Convex ℝ (f '' Metric.ball c ρ) := by
  by_cases hρ_nonpos : ρ ≤ 0
  · -- Nonpositive radii again give the empty source disc.
    have h_empty : f '' Metric.ball c ρ = ∅ := by
      ext w
      constructor
      · intro hw
        rcases hw with ⟨z, hz, rfl⟩
        have hz_lt : dist z c < ρ := by
          simpa [Metric.mem_ball] using hz
        have hρ_dist : ρ ≤ dist z c := by
          have hdist_nonneg : 0 ≤ dist z c := dist_nonneg
          linarith
        exact False.elim ((not_lt_of_ge hρ_dist) hz_lt)
      · intro hw
        exact False.elim hw
    simpa [h_empty] using (convex_empty : Convex ℝ (∅ : Set ℂ))
  · have hρ_pos : 0 < ρ := lt_of_not_ge hρ_nonpos
    rw [convex_iff_segment_subset]
    intro x hx y hy u hu
    rw [segment_eq_image_lineMap] at hu
    rcases hu with ⟨t, ht, rfl⟩
    rcases hx with ⟨z₁, hz₁, rfl⟩
    rcases hy with ⟨z₂, hz₂, rfl⟩
    have hz₁_lt : dist z₁ c < ρ := by
      simpa [Metric.mem_ball] using hz₁
    have hz₂_lt : dist z₂ c < ρ := by
      simpa [Metric.mem_ball] using hz₂
    have hnormρ : ‖c‖ + ρ ≤ 1 :=
      norm_add_radius_le_one_of_ball_subset_unit hρ_pos hdisc_subset
    let ρ' : ℝ := (max (dist z₁ c) (dist z₂ c) + ρ) / 2
    have hmax_lt_ρ : max (dist z₁ c) (dist z₂ c) < ρ := by
      rw [max_lt_iff]
      exact ⟨hz₁_lt, hz₂_lt⟩
    have hρ'_gt_max : max (dist z₁ c) (dist z₂ c) < ρ' := by
      dsimp [ρ']
      linarith
    have hρ'_lt : ρ' < ρ := by
      dsimp [ρ']
      linarith
    have hρ'_pos : 0 < ρ' := by
      have hdist1_nonneg : 0 ≤ dist z₁ c := dist_nonneg
      have hdist2_nonneg : 0 ≤ dist z₂ c := dist_nonneg
      have hmax_nonneg : 0 ≤ max (dist z₁ c) (dist z₂ c) := by
        exact le_trans hdist1_nonneg (le_max_left _ _)
      dsimp [ρ']
      nlinarith
    have hz₁' : z₁ ∈ Metric.ball c ρ' := by
      have hz₁_lt' : dist z₁ c < ρ' := lt_of_le_of_lt (le_max_left _ _) hρ'_gt_max
      simpa [Metric.mem_ball] using hz₁_lt'
    have hz₂' : z₂ ∈ Metric.ball c ρ' := by
      have hz₂_lt' : dist z₂ c < ρ' := lt_of_le_of_lt (le_max_right _ _) hρ'_gt_max
      simpa [Metric.mem_ball] using hz₂_lt'
    have hproper : ‖c‖ + ρ' < 1 := by
      have hlt : ‖c‖ + ρ' < ‖c‖ + ρ := by
        nlinarith
      exact lt_of_lt_of_le hlt hnormρ
    have hconvex' :
        Convex ℝ (f '' Metric.ball c ρ') :=
      convex_image_of_open_disc_strict hf_analytic hf_inj hD_convex hρ'_pos hproper
    have hx' : f z₁ ∈ f '' Metric.ball c ρ' := ⟨z₁, hz₁', rfl⟩
    have hy' : f z₂ ∈ f '' Metric.ball c ρ' := ⟨z₂, hz₂', rfl⟩
    have hsegment' :
        AffineMap.lineMap (f z₁) (f z₂) t ∈ f '' Metric.ball c ρ' :=
      by
        simpa [AffineMap.lineMap_apply_module] using
          hconvex' hx' hy' (sub_nonneg.mpr ht.2) ht.1 (by ring)
    -- Shrinking to a proper subdisc keeps the two chosen preimages while fitting the strict case.
    exact (Set.image_mono (Metric.ball_subset_ball hρ'_lt.le)) hsegment'

end

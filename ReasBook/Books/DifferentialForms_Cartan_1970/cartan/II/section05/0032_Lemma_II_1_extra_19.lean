import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace OpenPartialHomeomorph

/-- The parameter values whose horizontal-axis points lie in the source of a planar chart. -/
def horizontalAxisDomain (δ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) : Set ℝ :=
  {t | (t, 0) ∈ δ.source}

end OpenPartialHomeomorph

/-- A local `C^1` straightening chart for a planar curve near the parameter value `t₀`. -/
class IsLocalCurveStraighteningAt
    (γ : ℝ → ℝ × ℝ) (a b t₀ : ℝ)
    (δ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) : Prop where
  basePoint_mem_source : (t₀, 0) ∈ δ.source
  source_subset : δ.source ⊆ Set.Ioo a b ×ˢ (Set.univ : Set ℝ)
  contDiffOn : ContDiffOn ℝ 1 δ δ.source
  contDiffOn_symm : ContDiffOn ℝ 1 δ.symm δ.target
  map_horizontal_axis {t : ℝ} (ht : t ∈ δ.horizontalAxisDomain) : δ (t, 0) = γ t
  isImage_horizontalAxis :
    δ.IsImage {p : ℝ × ℝ | p.2 = 0} (γ '' δ.horizontalAxisDomain)

namespace IsLocalCurveStraighteningAt

variable {γ : ℝ → ℝ × ℝ} {a b t₀ : ℝ}
variable {δ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}

theorem basePoint_mem_horizontalAxisDomain (h : IsLocalCurveStraighteningAt γ a b t₀ δ) :
    t₀ ∈ δ.horizontalAxisDomain := by
  simpa [OpenPartialHomeomorph.horizontalAxisDomain] using h.basePoint_mem_source

theorem horizontalAxisDomain_subset (h : IsLocalCurveStraighteningAt γ a b t₀ δ) :
    δ.horizontalAxisDomain ⊆ Set.Ioo a b := by
  intro t ht
  exact (h.source_subset ht).1

theorem image_basePoint_mem_target (h : IsLocalCurveStraighteningAt γ a b t₀ δ) :
    γ t₀ ∈ δ.target := by
  rw [← h.map_horizontal_axis h.basePoint_mem_horizontalAxisDomain]
  exact δ.map_source h.basePoint_mem_source

theorem image_mem_curve_iff_second_eq_zero (h : IsLocalCurveStraighteningAt γ a b t₀ δ)
    {p : ℝ × ℝ} (hp : p ∈ δ.source) :
    δ p ∈ γ '' δ.horizontalAxisDomain ↔ p.2 = 0 := by
  simpa [OpenPartialHomeomorph.horizontalAxisDomain] using
    h.isImage_horizontalAxis.apply_mem_iff hp

end IsLocalCurveStraighteningAt

/-- Helper for Lemma II.1-extra-19: rotate a planar vector by a positive quarter-turn. -/
def rot90 (v : ℝ × ℝ) : ℝ × ℝ :=
  (-v.2, v.1)

/-- Helper for Lemma II.1-extra-19: an interior regular point of a `C^1` curve on `[a, b]`
is an ordinary `C^1` point with the same nonvanishing derivative. -/
lemma regular_curve_local_data
    {γ : ℝ → ℝ × ℝ} {a b t₀ : ℝ}
    (hγ : ContDiffWithinAt ℝ 1 γ (Set.Icc a b) t₀)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hγ'₀ : derivWithin γ (Set.Icc a b) t₀ ≠ 0) :
    let v := derivWithin γ (Set.Icc a b) t₀
    ContDiffAt ℝ 1 γ t₀ ∧ HasDerivAt γ v t₀ ∧ v ≠ 0 := by
  dsimp
  constructor
  · -- Move from the interval-local hypotheses to an ordinary `C^1` neighborhood of `t₀`.
    exact hγ.contDiffAt (Icc_mem_nhds ht₀.1 ht₀.2)
  constructor
  · -- The derivative within `[a, b]` agrees with the ordinary derivative at an interior point.
    exact (hγ.differentiableWithinAt one_ne_zero).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds ht₀.1 ht₀.2)
  · -- The nonvanishing assumption is part of the regularity input.
    exact hγ'₀

/-- Helper for Lemma II.1-extra-19: the tangent vector together with its quarter-turn
forms a basis of the plane whenever the tangent vector is nonzero. -/
lemma rot90_frame_equiv_of_ne_zero (v : ℝ × ℝ) (hv : v ≠ 0) :
    ∃ e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (rot90 v) := by
  let d : ℝ := v.1 ^ 2 + v.2 ^ 2
  have hd : d ≠ 0 := by
    -- A nonzero vector has positive squared norm, so its determinant cannot vanish.
    intro hd0
    have hv1sq : v.1 ^ 2 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg v.2, hd0]
    have hv2sq : v.2 ^ 2 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg v.2, hd0]
    have hv1 : v.1 = 0 := by
      nlinarith [hv1sq]
    have hv2 : v.2 = 0 := by
      nlinarith [hv2sq]
    exact hv <| by
      ext <;> simp [hv1, hv2]
  let fwd : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (v.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + (-v.2) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (v.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + v.1 • ContinuousLinearMap.snd ℝ ℝ ℝ)
  let inv : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    ((v.1 / d) • ContinuousLinearMap.fst ℝ ℝ ℝ + (v.2 / d) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      ((-v.2 / d) • ContinuousLinearMap.fst ℝ ℝ ℝ + (v.1 / d) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  refine ⟨ContinuousLinearEquiv.equivOfInverse' fwd inv ?_ ?_, ?_⟩
  · -- The explicit inverse matrix is the normalized adjugate.
    ext <;> simp [fwd, inv, d]
    · calc
        v.1 * (v.1 / (v.1 ^ 2 + v.2 ^ 2)) + -(v.2 * (-v.2 / (v.1 ^ 2 + v.2 ^ 2))) =
            (v.1 ^ 2 + v.2 ^ 2) * (v.1 ^ 2 + v.2 ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ hd
    · ring
    · ring
    · calc
        v.2 * (v.2 / (v.1 ^ 2 + v.2 ^ 2)) + v.1 * (v.1 / (v.1 ^ 2 + v.2 ^ 2)) =
            (v.2 ^ 2 + v.1 ^ 2) * (v.2 ^ 2 + v.1 ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ (by simpa [add_comm] using hd)
  · -- The same computation works in the opposite composition order.
    ext <;> simp [fwd, inv, d]
    · calc
        v.1 / (v.1 ^ 2 + v.2 ^ 2) * v.1 + v.2 / (v.1 ^ 2 + v.2 ^ 2) * v.2 =
            (v.1 ^ 2 + v.2 ^ 2) * (v.1 ^ 2 + v.2 ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ hd
    · ring
    · ring
    · calc
        -(-v.2 / (v.1 ^ 2 + v.2 ^ 2) * v.2) + v.1 / (v.1 ^ 2 + v.2 ^ 2) * v.1 =
            (v.2 ^ 2 + v.1 ^ 2) * (v.2 ^ 2 + v.1 ^ 2)⁻¹ := by ring
        _ = 1 := mul_inv_cancel₀ (by simpa [add_comm] using hd)
  · -- Rewrite the forward map as `(s, u) ↦ s • v + u • rot90 v`.
    ext <;> simp [fwd, rot90, ContinuousLinearMap.smulRight_apply]

/-- Helper for Lemma II.1-extra-19: the straightening candidate has the expected `C^1`
regularity and derivative at the base point. -/
lemma straightening_candidate_hasFDerivAt
    {γ : ℝ → ℝ × ℝ} {t₀ : ℝ} {v : ℝ × ℝ}
    (hγCont : ContDiffAt ℝ 1 γ t₀)
    (hγDeriv : HasDerivAt γ v t₀) :
    let n := rot90 v
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ ↦ γ p.1 + p.2 • n) (t₀, 0) ∧
      HasFDerivAt (fun p : ℝ × ℝ ↦ γ p.1 + p.2 • n)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight n)
        (t₀, 0) := by
  dsimp [rot90]
  constructor
  · -- The candidate is the sum of the pulled-back curve and a fixed linear transverse term.
    have hfst : ContDiffAt ℝ 1 (fun p : ℝ × ℝ ↦ γ p.1) (t₀, 0) := by
      simpa using hγCont.comp (x := (t₀, 0)) contDiffAt_fst
    have hsnd : ContDiffAt ℝ 1 (fun p : ℝ × ℝ ↦ p.2 • (-v.2, v.1)) (t₀, 0) := by
      fun_prop
    simpa using hfst.add hsnd
  · -- Its derivative has tangent column `v` and transverse column `rot90 v`.
    simpa [ContinuousLinearMap.smulRight_apply] using
      (hγDeriv.hasFDerivAt.comp (t₀, 0) hasFDerivAt_fst).add
        ((hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)).smul_const (-v.2, v.1))

/-- Helper for Lemma II.1-extra-19: once a chart sends the horizontal axis to the curve,
its source identifies the axis exactly with the corresponding branch of the curve image. -/
lemma curve_image_is_horizontal_axis
    {γ : ℝ → ℝ × ℝ} {δ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (haxis : ∀ {t}, t ∈ δ.horizontalAxisDomain → δ (t, 0) = γ t) :
    δ.IsImage {p : ℝ × ℝ | p.2 = 0} (γ '' δ.horizontalAxisDomain) := by
  rintro ⟨x, y⟩ hp
  constructor
  · intro himage
    rcases himage with ⟨t, ht, hEq⟩
    have hsource : (t, 0) ∈ δ.source := ht
    -- Any point of the restricted curve branch has the same chart-image as a horizontal-axis point.
    have hmap : δ (x, y) = δ (t, 0) := by
      calc
        δ (x, y) = γ t := hEq.symm
        _ = δ (t, 0) := (haxis ht).symm
    have hxy : (x, y) = (t, 0) := by
      -- Injectivity on the source follows by applying the partial inverse.
      have := congrArg δ.symm hmap
      simp [δ.left_inv hp, δ.left_inv hsource] at this
      exact Prod.ext this.1 this.2
    simp [hxy]
  · intro hy
    have hy0 : y = 0 := by
      simpa using hy
    have hp0 : (x, (0 : ℝ)) ∈ δ.source := by
      simpa [hy0] using hp
    have hdomain : x ∈ δ.horizontalAxisDomain := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain] using hp0
    -- Conversely, every horizontal-axis point maps onto the corresponding curve point.
    refine ⟨x, hdomain, ?_⟩
    calc
      γ x = δ (x, 0) := (haxis hdomain).symm
      _ = δ (x, y) := by simp [hy0]

-- Proof sketch: apply the inverse function theorem to a local straightening map around
-- `(t₀, 0)` whose differential has first column `γ'(t₀)` and second column transverse to it;
-- the resulting open partial homeomorphism identifies the chosen local branch of the path with
-- the horizontal axis.
/-- Lemma II.1-extra-19: at an interior parameter value where the derivative of a `C^1` plane path
does not vanish, the path admits a local `C^1` straightening chart whose horizontal axis
corresponds exactly to the chosen local branch of the path. -/
theorem exists_local_straightening_at_regular_curve_point
    {γ : ℝ → ℝ × ℝ} {a b t₀ : ℝ}
    (hγ : ContDiffWithinAt ℝ 1 γ (Set.Icc a b) t₀)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hγ'₀ : derivWithin γ (Set.Icc a b) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      IsLocalCurveStraighteningAt γ a b t₀ δ := by
  let v := derivWithin γ (Set.Icc a b) t₀
  obtain ⟨hγCont, hγDeriv, hv⟩ := regular_curve_local_data hγ ht₀ hγ'₀
  obtain ⟨e, he⟩ := rot90_frame_equiv_of_ne_zero v hv
  obtain ⟨hΦcont, hΦderiv⟩ := straightening_candidate_hasFDerivAt
    (γ := γ) (t₀ := t₀) (v := v) hγCont hγDeriv
  let Φ : ℝ × ℝ → ℝ × ℝ := fun p ↦ γ p.1 + p.2 • rot90 v
  have hΦderiv' : HasFDerivAt Φ (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (t₀, 0) := by
    -- This matches the candidate derivative with the explicit frame equivalence.
    simpa [Φ, he] using hΦderiv
  let δ₀ : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    hΦcont.toOpenPartialHomeomorph Φ hΦderiv' one_ne_zero
  let δ₁ := δ₀.restrContDiff ℝ 1 (by norm_num)
  let strip : Set (ℝ × ℝ) := Set.Ioo a b ×ˢ (Set.univ : Set ℝ)
  let δ := δ₁.restrOpen strip (isOpen_Ioo.prod isOpen_univ)
  have hδ₀_source : (t₀, 0) ∈ δ₀.source := by
    -- The inverse function theorem keeps the base point in the source chart.
    exact hΦcont.mem_toOpenPartialHomeomorph_source hΦderiv' one_ne_zero
  have hδ₀_symm : ContDiffAt ℝ 1 δ₀.symm (γ t₀) := by
    -- The local inverse is `C^1` at the image of the base point.
    simpa [δ₀, Φ] using hΦcont.to_localInverse hΦderiv' one_ne_zero
  have hδ₁_source : (t₀, 0) ∈ δ₁.source := by
    -- Restrict to the `C^1` locus while keeping the base point.
    simp [δ₁, δ₀, Φ, hδ₀_source, hΦcont, hδ₀_symm]
  have hsource_subset : δ.source ⊆ δ₁.source := by
    intro p hp
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp
    exact hp'.1
  have htarget_subset : δ.target ⊆ δ₁.target := by
    intro q hq
    have hq' : q ∈ δ₁.target ∩ δ₁.symm ⁻¹' strip := by
      simpa [δ, strip] using hq
    exact hq'.1
  refine ⟨δ, ?_⟩
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_ }
  · -- After both restrictions, the base point still lies in the chart source.
    have hstrip : (t₀, 0) ∈ strip := by
      simp [strip, ht₀]
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · -- The final source is explicitly confined to the interval strip.
    intro p hp
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp
    exact hp'.2
  · -- Restricting the source preserves the `C^1` regularity obtained from `restrContDiff`.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_source (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono hsource_subset
  · -- The same restriction argument applies to the local inverse.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono htarget_subset
  · intro t ht
    -- Route correction: the final chart is only a restriction, so its forward map is still `Φ`.
    have ht' : (t, (0 : ℝ)) ∈ δ.source := ht
    simp [δ, δ₁, δ₀, Φ, rot90]
  · -- On the restricted source, belonging to the curve image is equivalent to lying on the axis.
    apply curve_image_is_horizontal_axis
    intro t ht
    have ht' : (t, (0 : ℝ)) ∈ δ.source := ht
    simp [δ, δ₁, δ₀, Φ, rot90]

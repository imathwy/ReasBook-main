import Mathlib

/-!
# Generic derivative-to-convexity bridges

This file isolates the order/convex part of the derivative criteria over an arbitrary ordered
normed field with enough order completeness for the one-dimensional mean value theorem.
-/

open Set Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]

namespace ConvexAnalysis

/-- Generic Fermat theorem for a scalar local minimum. -/
theorem IsLocalMin.hasDerivAt_eq_zero {f : 𝕜 → 𝕜} {a f' : 𝕜}
    (h : _root_.IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  have hmin_nhds : ∀ᶠ y in 𝓝 a, f a ≤ f y := h
  have hmap : Tendsto (fun t : 𝕜 => a + t) (𝓝 (0 : 𝕜)) (𝓝 a) := by
    simpa [add_zero] using
      (tendsto_const_nhds.add
        (Filter.tendsto_id : Tendsto (fun t : 𝕜 => t) (𝓝 (0 : 𝕜)) (𝓝 (0 : 𝕜))))
  have hloc : ∀ᶠ t in 𝓝 (0 : 𝕜), f a ≤ f (a + t) :=
    hmap.eventually hmin_nhds
  have h_nonneg : 0 ≤ f' := by
    refine ge_of_tendsto hf.tendsto_slope_zero_right ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hloc] with t hmin htpos
    have hdiff : 0 ≤ f (a + t) - f a := sub_nonneg.mpr hmin
    have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr htpos.le
    simpa [smul_eq_mul] using mul_nonneg htinv hdiff
  have h_nonpos : f' ≤ 0 := by
    refine le_of_tendsto hf.tendsto_slope_zero_left ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hloc] with t hmin htneg
    have hdiff : 0 ≤ f (a + t) - f a := sub_nonneg.mpr hmin
    have htinv : t⁻¹ ≤ 0 := inv_nonpos.mpr htneg.le
    simpa [smul_eq_mul] using mul_nonpos_of_nonpos_of_nonneg htinv hdiff
  exact le_antisymm h_nonpos h_nonneg

/-- Generic Fermat theorem for a scalar local maximum. -/
theorem IsLocalMax.hasDerivAt_eq_zero {f : 𝕜 → 𝕜} {a f' : 𝕜}
    (h : _root_.IsLocalMax f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  have hneg : -f' = 0 := IsLocalMin.hasDerivAt_eq_zero h.neg hf.neg
  exact neg_eq_zero.mp hneg

/-- Generic Fermat theorem for a scalar local extremum. -/
theorem IsLocalExtr.hasDerivAt_eq_zero {f : 𝕜 → 𝕜} {a f' : 𝕜}
    (h : _root_.IsLocalExtr f a) : HasDerivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.hasDerivAt_eq_zero IsLocalMax.hasDerivAt_eq_zero

/-- Generic Rolle theorem, `HasDerivAt` version. -/
theorem exists_hasDerivAt_eq_zero {f f' : 𝕜 → 𝕜} {a b : 𝕜}
    [DenselyOrdered 𝕜]
    (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = 0 := by
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  exact ⟨c, cmem, IsLocalExtr.hasDerivAt_eq_zero hc <| hff' c cmem⟩

/-- Generic Lagrange mean value theorem, `HasDerivAt` version. -/
theorem exists_hasDerivAt_eq_slope (f f' : 𝕜 → 𝕜) {a b : 𝕜}
    [DenselyOrdered 𝕜]
    (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  let m : 𝕜 := (f b - f a) / (b - a)
  let h : 𝕜 → 𝕜 := fun x => f x - m * x
  have hcont : ContinuousOn h (Icc a b) :=
    hfc.sub (continuousOn_const.mul continuousOn_id)
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt h (f' x - m) x := by
    intro x hx
    have hm : HasDerivAt (fun x => m * x) m x := by
      simpa [one_mul] using (hasDerivAt_id x).const_mul m
    exact (hff' x hx).sub hm
  have hsame : h a = h b := by
    have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    dsimp [h, m]
    field_simp [hden]
    ring
  rcases exists_hasDerivAt_eq_zero hab hcont hsame hderiv with ⟨c, hc, hzero⟩
  exact ⟨c, hc, sub_eq_zero.mp hzero⟩

/-- Generic Lagrange mean value theorem, `deriv` version. -/
theorem exists_deriv_eq_slope (f : 𝕜 → 𝕜) {a b : 𝕜}
    [DenselyOrdered 𝕜]
    (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn 𝕜 f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx =>
    ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

/- Mean-value slope witness on a convex set, derived from differentiability on that set. -/
theorem exists_deriv_eq_slope_of_differentiableOn {D : Set 𝕜} {f : 𝕜 → 𝕜}
    [DenselyOrdered 𝕜]
    (hD : Convex 𝕜 D) (hf : DifferentiableOn 𝕜 f D)
    ⦃x y : 𝕜⦄ (hx : x ∈ D) (hy : y ∈ D) (hxy : x < y) :
    ∃ c ∈ Ioo x y, deriv f c = (f y - f x) / (y - x) := by
  have hIcc : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hIoo : Ioo x y ⊆ D := Ioo_subset_Icc_self.trans hIcc
  exact exists_deriv_eq_slope f hxy (hf.continuousOn.mono hIcc) (hf.mono hIoo)

/-- Generic replacement for the order-theoretic core of `monotoneOn_of_deriv_nonneg`.

If every secant slope on `D` is attained by the derivative at an interior point, then
nonnegativity of the derivative on `interior D` implies monotonicity on `D`. -/
theorem monotoneOn_of_deriv_nonneg_of_exists_deriv_eq_slope {D : Set 𝕜} {f : 𝕜 → 𝕜}
    (hD : Convex 𝕜 D)
    (h_slope : ∀ ⦃x y : 𝕜⦄, x ∈ D → y ∈ D → x < y →
      ∃ c ∈ Ioo x y, deriv f c = (f y - f x) / (y - x))
    (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) :
    MonotoneOn f D := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  rcases h_slope hx hy hxy' with ⟨c, hc, hderiv⟩
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxy_int : Ioo x y ⊆ interior D :=
    isOpen_Ioo.subset_interior_iff.mpr (Ioo_subset_Icc_self.trans hxyD)
  have hc_int : c ∈ interior D := hxy_int hc
  have hslope_nonneg : 0 ≤ (f y - f x) / (y - x) := by
    rw [← hderiv]
    exact hf'_nonneg c hc_int
  have hden_pos : 0 < y - x := sub_pos.mpr hxy'
  have hdiff_nonneg : 0 ≤ f y - f x := by
    have hmul : 0 ≤ (f y - f x) / (y - x) * (y - x) :=
      mul_nonneg hslope_nonneg hden_pos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hden_pos)] at hmul
  exact sub_nonneg.mp hdiff_nonneg

/-- Generic replacement for the order-theoretic core of `MonotoneOn.convexOn_of_deriv`.

If the derivative is monotone on `interior D` and every secant slope is attained by an interior
derivative, then `f` is convex on `D`. -/
theorem MonotoneOn.convexOn_of_deriv_of_exists_deriv_eq_slope {D : Set 𝕜} {f : 𝕜 → 𝕜}
    (hD : Convex 𝕜 D)
    (hf'_mono : MonotoneOn (deriv f) (interior D))
    (h_slope : ∀ ⦃x y : 𝕜⦄, x ∈ D → y ∈ D → x < y →
      ∃ c ∈ Ioo x y, deriv f c = (f y - f x) / (y - x)) :
    ConvexOn 𝕜 D f := by
  refine convexOn_of_slope_mono_adjacent hD ?_
  intro x y z hx hz hxy hyz
  have hy : y ∈ D := hD.ordConnected.out hx hz ⟨hxy.le, hyz.le⟩
  have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
  have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
  have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
  have hxy_int : Ioo x y ⊆ interior D :=
    isOpen_Ioo.subset_interior_iff.mpr (Ioo_subset_Icc_self.trans hxyD)
  have hyz_int : Ioo y z ⊆ interior D :=
    isOpen_Ioo.subset_interior_iff.mpr (Ioo_subset_Icc_self.trans hyzD)
  rcases h_slope hx hy hxy with ⟨a, ha, ha_deriv⟩
  rcases h_slope hy hz hyz with ⟨b, hb, hb_deriv⟩
  rw [← ha_deriv, ← hb_deriv]
  exact hf'_mono (hxy_int ha) (hyz_int hb) (ha.2.trans hb.1).le

/-- Generic replacement for the order-theoretic core of `convexOn_of_deriv2_nonneg'`.

There are two explicit MVT hypotheses: one for `f` on `D`, and one for `deriv f` on
`interior D`.  These are supplied by `exists_deriv_eq_slope_of_differentiableOn` in the
source-facing bridge below. -/
theorem convexOn_of_deriv2_nonneg_of_exists_deriv_eq_slope {D : Set 𝕜} {f : 𝕜 → 𝕜}
    (hD : Convex 𝕜 D)
    (h_slope_f : ∀ ⦃x y : 𝕜⦄, x ∈ D → y ∈ D → x < y →
      ∃ c ∈ Ioo x y, deriv f c = (f y - f x) / (y - x))
    (h_slope_deriv : ∀ ⦃x y : 𝕜⦄, x ∈ interior D → y ∈ interior D → x < y →
      ∃ c ∈ Ioo x y,
        deriv (deriv f) c = (deriv f y - deriv f x) / (y - x))
    (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) :
    ConvexOn 𝕜 D f := by
  have hf'_mono : MonotoneOn (deriv f) (interior D) := by
    refine monotoneOn_of_deriv_nonneg_of_exists_deriv_eq_slope
      (𝕜 := 𝕜) (D := interior D) (f := deriv f) hD.interior h_slope_deriv ?_
    intro x hx
    have hxD : x ∈ interior D := by
      simpa [interior_interior] using hx
    simpa [Function.iterate_succ_apply'] using hf''_nonneg x hxD
  exact MonotoneOn.convexOn_of_deriv_of_exists_deriv_eq_slope hD hf'_mono h_slope_f

/-- Generic replacement for `convexOn_of_deriv2_nonneg'`.

This keeps the source-facing `DifferentiableOn` hypotheses for both `f` and `deriv f`, and keeps
the second-derivative nonnegativity hypothesis on `D`; the mean-value witnesses are derived from
the generic Lagrange theorem above. -/
theorem convexOn_of_deriv2_nonneg' {D : Set 𝕜} {f : 𝕜 → 𝕜}
    [DenselyOrdered 𝕜]
    (hD : Convex 𝕜 D)
    (hf' : DifferentiableOn 𝕜 f D)
    (hf'' : DifferentiableOn 𝕜 (deriv f) D)
    (hf''_nonneg : ∀ x ∈ D, 0 ≤ deriv^[2] f x) :
    ConvexOn 𝕜 D f := by
  refine convexOn_of_deriv2_nonneg_of_exists_deriv_eq_slope hD ?_ ?_ ?_
  · exact exists_deriv_eq_slope_of_differentiableOn hD hf'
  · exact exists_deriv_eq_slope_of_differentiableOn hD.interior (hf''.mono interior_subset)
  · intro x hx
    exact hf''_nonneg x (interior_subset hx)

end ConvexAnalysis

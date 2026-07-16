import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section06.«0007_Theorem_I»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0012_Theorem_4»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ComplexConjugate Topology

/-- The Schwarz reflection of a function on the upper half-plane uses the original values for
`0 ≤ im z` and the reflected conjugate values for `im z < 0`. -/
noncomputable def schwarzReflection (f : ℂ → ℂ) : ℂ → ℂ :=
  {z : ℂ | 0 ≤ z.im}.piecewise f (conj ∘ f ∘ conj)

/-- On the closed upper half-plane, Schwarz reflection agrees with the original function. -/
-- Proof sketch: unfold `schwarzReflection` and evaluate the defining `piecewise` expression on a
-- point satisfying `0 ≤ im z`.
@[simp] theorem schwarzReflection_apply_of_nonneg_im {f : ℂ → ℂ} {z : ℂ} (hz : 0 ≤ z.im) :
    schwarzReflection f z = f z := by
  simp [schwarzReflection, hz]

/-- On the open lower half-plane, Schwarz reflection is given by the reflected conjugate formula. -/
-- Proof sketch: unfold `schwarzReflection` and evaluate the defining `piecewise` expression on a
-- point satisfying `im z < 0`.
@[simp] theorem schwarzReflection_apply_of_neg_im {f : ℂ → ℂ} {z : ℂ} (hz : z.im < 0) :
    schwarzReflection f z = conj (f (conj z)) := by
  simp [schwarzReflection, hz, Function.comp]

/-- Helper for Remark II.2-extra-6: on the real-axis slice of `D`, the reflected branch
`z ↦ conj (f (conj z))` agrees with `f`. -/
lemma conj_comp_conj_eq_on_zero_im {D : Set ℂ} {f : ℂ → ℂ}
    (hf_real : ∀ z ∈ D, z.im = 0 → conj (f z) = f z) :
    Set.EqOn (conj ∘ f ∘ conj) f (D ∩ {z : ℂ | z.im = 0}) := by
  intro z hz
  -- On the real axis, conjugation fixes the input, so the boundary hypothesis rewrites the value.
  have hz_zero : z.im = 0 := by
    simpa using hz.2
  have hz_conj : conj z = z := by
    apply Complex.ext
    · simp
    · simp [Complex.conj_im, hz_zero]
  simpa [Function.comp, hz_conj] using hf_real z hz.1 hz_zero

/-- Helper for Remark II.2-extra-6: Schwarz reflection is continuous on the symmetric domain `D`
because the upper and reflected lower branches glue on the real axis. -/
lemma schwarzReflection_continuousOn {D : Set ℂ} {f : ℂ → ℂ} (hD_symm : Set.MapsTo conj D D)
    (hf_cont : ContinuousOn f (D ∩ {z : ℂ | 0 ≤ z.im}))
    (hf_real : ∀ z ∈ D, z.im = 0 → conj (f z) = f z) :
    ContinuousOn (schwarzReflection f) D := by
  have hboundary_zero : Set.EqOn (conj ∘ f ∘ conj) f (D ∩ {z : ℂ | z.im = 0}) :=
    conj_comp_conj_eq_on_zero_im hf_real
  have hmaps_closed_lower :
      Set.MapsTo conj (D ∩ {z : ℂ | z.im ≤ 0}) (D ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz
    refine ⟨hD_symm hz.1, ?_⟩
    simpa [Complex.conj_im] using neg_nonneg.mpr (show z.im ≤ 0 from hz.2)
  have hlower_cont : ContinuousOn (conj ∘ f ∘ conj) (D ∩ {z : ℂ | z.im ≤ 0}) := by
    -- First pull `hf_cont` back across the domain conjugation, then conjugate the values.
    have hcomp_cont : ContinuousOn (f ∘ conj) (D ∩ {z : ℂ | z.im ≤ 0}) :=
      hf_cont.comp Complex.continuous_conj.continuousOn hmaps_closed_lower
    exact Complex.continuous_conj.comp_continuousOn hcomp_cont
  have hfrontier :
      ∀ z ∈ D ∩ frontier {z : ℂ | 0 ≤ z.im}, f z = (conj ∘ f ∘ conj) z := by
    intro z hz
    -- The frontier of the closed upper half-plane is exactly the real axis.
    have hz_zero : z.im = 0 := by
      simpa [Complex.frontier_setOf_le_im] using hz.2
    exact (hboundary_zero ⟨hz.1, hz_zero⟩).symm
  have hf_cont_closure : ContinuousOn f (D ∩ closure {z : ℂ | 0 ≤ z.im}) := by
    simpa [(isClosed_le continuous_const Complex.continuous_im).closure_eq] using hf_cont
  have hlower_cont_closure :
      ContinuousOn (conj ∘ f ∘ conj) (D ∩ closure {z : ℂ | ¬0 ≤ z.im}) := by
    simpa [show ({z : ℂ | ¬0 ≤ z.im} : Set ℂ) = {z : ℂ | z.im < 0} by
        ext z
        simp [not_le], Complex.closure_setOf_im_lt] using hlower_cont
  -- Apply the standard piecewise continuity theorem with the upper half-plane cut.
  simpa [schwarzReflection, Function.comp] using
    (ContinuousOn.piecewise (s := D) (t := {z : ℂ | 0 ≤ z.im}) hfrontier hf_cont_closure
      hlower_cont_closure)

/-- Helper for Remark II.2-extra-6: reflecting a holomorphic function across the real axis keeps it
holomorphic on the open lower slice. -/
lemma conj_comp_conj_differentiableOn_neg_im {D : Set ℂ} {f : ℂ → ℂ} (hD_open : IsOpen D)
    (hD_symm : Set.MapsTo conj D D)
    (hf_diff : DifferentiableOn ℂ f (D ∩ {z : ℂ | 0 < z.im})) :
    DifferentiableOn ℂ (conj ∘ f ∘ conj) (D ∩ {z : ℂ | z.im < 0}) := by
  have hupper_open : IsOpen (D ∩ {z : ℂ | 0 < z.im}) :=
    hD_open.inter (isOpen_lt continuous_const Complex.continuous_im)
  intro z hz
  -- The reflected point lies in the open upper slice, so holomorphy transfers by `conj_conj`.
  have hz_conj : conj z ∈ D ∩ {z : ℂ | 0 < z.im} := by
    refine ⟨hD_symm hz.1, ?_⟩
    simpa [Complex.conj_im] using neg_pos.mpr (show z.im < 0 from hz.2)
  have hf_at : DifferentiableAt ℂ f (conj z) := by
    exact (hf_diff (conj z) hz_conj).differentiableAt (hupper_open.mem_nhds hz_conj)
  have hreflect : DifferentiableAt ℂ (conj ∘ f ∘ conj) z := by
    simpa [Function.comp, Complex.conj_conj] using hf_at.conj_conj
  exact hreflect.differentiableWithinAt

/-- Helper for Remark II.2-extra-6: Schwarz reflection is holomorphic away from the real axis on
`D`. -/
lemma schwarzReflection_differentiableOn_off_real_axis {D : Set ℂ} {f : ℂ → ℂ}
    (hD_open : IsOpen D) (hD_symm : Set.MapsTo conj D D)
    (hf_diff : DifferentiableOn ℂ f (D ∩ {z : ℂ | 0 < z.im})) :
    DifferentiableOn ℂ (schwarzReflection f) (D \ {z : ℂ | z.im = 0}) := by
  have hupper_open : IsOpen (D ∩ {z : ℂ | 0 < z.im}) :=
    hD_open.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hlower_open : IsOpen (D ∩ {z : ℂ | z.im < 0}) :=
    hD_open.inter (isOpen_lt Complex.continuous_im continuous_const)
  have hlower_diff :
      DifferentiableOn ℂ (conj ∘ f ∘ conj) (D ∩ {z : ℂ | z.im < 0}) :=
    conj_comp_conj_differentiableOn_neg_im hD_open hD_symm hf_diff
  intro z hz
  rcases hz with ⟨hzD, hz_ne_zero⟩
  by_cases hz_pos : 0 < z.im
  · -- Above the axis, the reflected function agrees with `f` on a neighborhood.
    have hz_upper : z ∈ D ∩ {z : ℂ | 0 < z.im} := ⟨hzD, hz_pos⟩
    have hf_at : DifferentiableAt ℂ f z := by
      exact (hf_diff z hz_upper).differentiableAt (hupper_open.mem_nhds hz_upper)
    have heq : schwarzReflection f =ᶠ[𝓝 z] f := by
      filter_upwards [hupper_open.mem_nhds hz_upper] with w hw
      simp [schwarzReflection_apply_of_nonneg_im (f := f) (z := w) hw.2.le]
    exact (hf_at.congr_of_eventuallyEq heq).differentiableWithinAt
  · have hz_neg : z.im < 0 := by
      refine lt_of_le_of_ne (le_of_not_gt hz_pos) ?_
      exact fun hz_zero ↦ hz_ne_zero (by simpa using hz_zero)
    -- Below the axis, the reflected function agrees with the conjugated lower branch on a
    -- neighborhood.
    have hz_lower : z ∈ D ∩ {z : ℂ | z.im < 0} := ⟨hzD, hz_neg⟩
    have hbranch_at : DifferentiableAt ℂ (conj ∘ f ∘ conj) z := by
      exact (hlower_diff z hz_lower).differentiableAt (hlower_open.mem_nhds hz_lower)
    have heq : schwarzReflection f =ᶠ[𝓝 z] (conj ∘ f ∘ conj) := by
      filter_upwards [hlower_open.mem_nhds hz_lower] with w hw
      simp [schwarzReflection_apply_of_neg_im (f := f) (z := w) hw.2, Function.comp]
    exact (hbranch_at.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Helper for Remark II.2-extra-6: a nonempty open domain symmetric under conjugation contains a
point strictly above the real axis. -/
lemma exists_mem_with_pos_im {D : Set ℂ} (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hD_symm : Set.MapsTo conj D D) :
    ∃ z ∈ D, 0 < z.im := by
  rcases hD_connected.nonempty with ⟨z, hzD⟩
  by_cases hz_pos : 0 < z.im
  · exact ⟨z, hzD, hz_pos⟩
  by_cases hz_zero : z.im = 0
  · -- A boundary point on the real axis is a closure point of the open upper half-plane.
    have hz_closure : z ∈ closure {w : ℂ | 0 < w.im} := by
      rw [Complex.closure_setOf_lt_im]
      simp [hz_zero]
    have hupper_nonempty : (D ∩ {w : ℂ | 0 < w.im}).Nonempty := by
      exact (mem_closure_iff_nhds.mp hz_closure) D (hD_open.mem_nhds hzD)
    rcases hupper_nonempty with ⟨w, hwD, hwim⟩
    exact ⟨w, hwD, hwim⟩
  · -- Otherwise the chosen point lies below the axis, so its conjugate lies above it.
    have hz_neg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hz_pos) hz_zero
    refine ⟨conj z, hD_symm hzD, ?_⟩
    simpa [Complex.conj_im] using neg_pos.mpr hz_neg

/-- Remark II.2-extra-6: if `D` is open and symmetric with respect to the real axis, and `f` is
continuous on the closed upper slice `D ∩ {z | 0 ≤ im z}`, holomorphic on the open upper slice
`D ∩ {z | 0 < im z}`, and real-valued on `D ∩ ℝ`, then its Schwarz reflection is holomorphic on
`D`. -/
-- Proof sketch: the reflected formula is continuous on the lower slice because conjugation is
-- continuous, and it is holomorphic away from the real axis by the conjugation rules for
-- differentiability. The real-valued boundary hypothesis makes the two formulas agree on
-- `D ∩ ℝ`, so the piecewise function is continuous on `D`; then apply the earlier removable-line
-- principle to conclude holomorphicity on all of `D`.
theorem schwarzReflection_differentiableOn {D : Set ℂ} {f : ℂ → ℂ} (hD_open : IsOpen D)
    (hD_symm : Set.MapsTo conj D D)
    (hf_cont : ContinuousOn f (D ∩ {z : ℂ | 0 ≤ z.im}))
    (hf_diff : DifferentiableOn ℂ f (D ∩ {z : ℂ | 0 < z.im}))
    (hf_real : ∀ z ∈ D, z.im = 0 → conj (f z) = f z) :
    DifferentiableOn ℂ (schwarzReflection f) D := by
  -- Package the two parts of the textbook argument into continuity on `D` and holomorphy off the
  -- real axis.
  have hcont : ContinuousOn (schwarzReflection f) D :=
    schwarzReflection_continuousOn hD_symm hf_cont hf_real
  have hoff :
      DifferentiableOn ℂ (schwarzReflection f) (D \ {z : ℂ | z.im = 0}) :=
    schwarzReflection_differentiableOn_off_real_axis hD_open hD_symm hf_diff
  -- The earlier removable-horizontal-line theorem upgrades this to a conservative form on `D`.
  have hconservative : Complex.IsConservativeOn (schwarzReflection f) D :=
    continuous_holomorphic_off_horizontal_line_isConservativeOn hcont hoff
  -- Theorem 4 then turns conservativity plus continuity into holomorphy on all of `D`.
  exact differentiableOn_of_isConservativeOn_of_continuousOn hD_open hcont hconservative

/-- Schwarz reflection extends `f` on the closed upper half-plane. -/
theorem schwarzReflection_eqOn_nonneg_im (f : ℂ → ℂ) :
    Set.EqOn (schwarzReflection f) f {z : ℂ | 0 ≤ z.im} := by
  simpa [schwarzReflection] using
    ({z : ℂ | 0 ≤ z.im}.piecewise_eqOn f (conj ∘ f ∘ conj))

/-- Helper for Remark II.2-extra-6: any holomorphic extension `h` of `f` over the closed upper
slice agrees there with the Schwarz reflection. -/
lemma extension_eqOn_upper_slice {D : Set ℂ} {f h : ℂ → ℂ}
    (hh_eq : Set.EqOn h f (D ∩ {z : ℂ | 0 ≤ z.im})) :
    Set.EqOn h (schwarzReflection f) (D ∩ {z : ℂ | 0 < z.im}) := by
  intro z hz
  -- On the strict upper slice, both functions reduce to `f`.
  calc
    h z = f z := hh_eq ⟨hz.1, show 0 ≤ z.im from hz.2.le⟩
    _ = schwarzReflection f z := by
      symm
      exact schwarzReflection_apply_of_nonneg_im (f := f) (z := z) hz.2.le

/-- On a connected symmetric domain, any holomorphic extension of `f` from the closed upper slice
must agree with the Schwarz reflection extension on the whole domain. -/
-- Proof sketch: first apply `schwarzReflection_differentiableOn` to see that the reflected
-- function is holomorphic on `D`. Both `h` and `schwarzReflection f` agree with `f` on the upper
-- slice, so they agree on the nonempty open upper slice `D ∩ {z | 0 < im z}`; then the identity
-- theorem yields equality on all of the connected domain `D`.
theorem eqOn_schwarzReflection_of_differentiableOn {D : Set ℂ} {f h : ℂ → ℂ}
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hD_symm : Set.MapsTo conj D D)
    (hf_cont : ContinuousOn f (D ∩ {z : ℂ | 0 ≤ z.im}))
    (hf_diff : DifferentiableOn ℂ f (D ∩ {z : ℂ | 0 < z.im}))
    (hf_real : ∀ z ∈ D, z.im = 0 → conj (f z) = f z)
    (hh_diff : DifferentiableOn ℂ h D)
    (hh_eq : Set.EqOn h f (D ∩ {z : ℂ | 0 ≤ z.im})) :
    Set.EqOn h (schwarzReflection f) D := by
  have hupper_open : IsOpen (D ∩ {z : ℂ | 0 < z.im}) :=
    hD_open.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hreflect_diff : DifferentiableOn ℂ (schwarzReflection f) D :=
    schwarzReflection_differentiableOn hD_open hD_symm hf_cont hf_diff hf_real
  have hh_analytic : AnalyticOnNhd ℂ h D := hh_diff.analyticOnNhd hD_open
  have hreflect_analytic : AnalyticOnNhd ℂ (schwarzReflection f) D :=
    hreflect_diff.analyticOnNhd hD_open
  have hupper_eq : Set.EqOn h (schwarzReflection f) (D ∩ {z : ℂ | 0 < z.im}) :=
    extension_eqOn_upper_slice hh_eq
  rcases exists_mem_with_pos_im hD_open hD_connected hD_symm with ⟨z₀, hz₀D, hz₀pos⟩
  have heventually : h =ᶠ[𝓝 z₀] schwarzReflection f := by
    -- The two analytic functions agree on the open upper slice around the chosen point.
    filter_upwards [hupper_open.mem_nhds ⟨hz₀D, hz₀pos⟩] with z hz
    exact hupper_eq hz
  -- Apply analytic continuation from the nonempty upper slice to all of the connected domain.
  exact hh_analytic.eqOn_of_preconnected_of_eventuallyEq hreflect_analytic
    hD_connected.isPreconnected hz₀D heventually

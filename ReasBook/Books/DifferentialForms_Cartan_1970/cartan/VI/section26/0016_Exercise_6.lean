import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section06.«0013_Corollary_II_2_extra_5»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0015_Remark_II_2_extra_6»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0009_Proposition_4_2»
import DifferentialForms_Cartan_1970.cartan.VI.section22.«0005_Corollary_VI_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.VI.section22.«0006_Definition_VI_1_extra_4»
import DifferentialForms_Cartan_1970.cartan.VI.section26.«0016_Exercise_6».Index

-- Declarations for this item will be appended below by the statement pipeline.

open Set Filter
open scoped ComplexConjugate Topology
open EuclideanGeometry

noncomputable section

/-- Helper for Exercise 6: membership in the reflection line is equivalent to being a real multiple
of its distinguished direction after translating by the chosen base point. -/
theorem reflectionLineVsubBasepoint_iff_realSmulDirection
    {c w : ℂ} {t : ℝ} (hc : c ≠ 0) :
    let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
    w ∈ reflection_line c t hc ↔ ∃ s : ℝ, w - u = s • (Complex.I * star c) := by
  dsimp
  -- Unfold the packaged affine line into the explicit base point and direction used later.
  rw [show reflection_line c t hc =
      line[ℝ, ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c,
        ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c + Complex.I * star c] by
      simp [reflection_line]]
  rw [← vsub_vadd w (((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c),
    vadd_left_mem_affineSpan_pair]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, by simpa using hs.symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, by simpa using hs.symm⟩

/-- Helper for Exercise 6: the homogeneous reflection-line equation cuts out the real span of the
direction vector `I * conj c`. -/
theorem reflectionLineEquationZero_iff_realSmulDirection
    {c d : ℂ} (hc : c ≠ 0) :
    c * d + star c * star d = 0 ↔ ∃ s : ℝ, d = s • (Complex.I * star c) := by
  constructor
  · intro hzero
    let q : ℂ := d / (Complex.I * star c)
    have hstarc : star c ≠ 0 := by
      intro hstar
      apply hc
      simpa using congrArg star hstar
    have hden : Complex.I * star c ≠ 0 := mul_ne_zero Complex.I_ne_zero hstarc
    have hfactor :
        c * d + star c * star d = (Complex.I * (Complex.normSq c : ℂ)) * (q - star q) := by
      -- Normalize the displacement by the nonzero line direction.
      have hd : d = q * (Complex.I * star c) := by
        exact (div_mul_cancel₀ d hden).symm
      rw [hd]
      simp [q, Complex.normSq_eq_conj_mul_self]
      ring
    have hnorm : (Complex.normSq c : ℂ) ≠ 0 := by
      exact_mod_cast (show Complex.normSq c ≠ 0 by simpa [Complex.normSq_eq_zero] using hc)
    have hmulzero : (Complex.I * (Complex.normSq c : ℂ)) * (q - star q) = 0 := by
      rw [← hfactor]
      exact hzero
    have hq_eq : q = star q := by
      apply sub_eq_zero.mp
      exact (mul_eq_zero.mp hmulzero).resolve_left (mul_ne_zero Complex.I_ne_zero hnorm)
    have hq_real : q = (Complex.re q : ℂ) := by
      have him : Complex.im q = 0 := Complex.conj_eq_iff_im.mp hq_eq.symm
      calc
        q = (Complex.re q : ℂ) + (Complex.im q : ℂ) * Complex.I := by
          symm
          exact Complex.re_add_im q
        _ = (Complex.re q : ℂ) := by simp [him]
    refine ⟨Complex.re q, ?_⟩
    -- Replace the normalized scalar by its real part.
    calc
      d = q * (Complex.I * star c) := by
        exact (div_mul_cancel₀ d hden).symm
      _ = (Complex.re q : ℂ) * (Complex.I * star c) := by
        exact congrArg (fun z : ℂ ↦ z * (Complex.I * star c)) hq_real
      _ = Complex.re q • (Complex.I * star c) := by simp
  · rintro ⟨s, rfl⟩
    -- A genuine direction vector annihilates the homogeneous line equation.
    simp
    ring

/-- Helper for Exercise 6: the concrete affine line `reflection_line c t hc` is exactly the locus
where the textbook equation `c * w + conj c * conj w = t` holds. -/
theorem mem_reflectionLine_iff {c w : ℂ} {t : ℝ} (hc : c ≠ 0) :
    w ∈ reflection_line c t hc ↔ c * w + star c * star w = (t : ℂ) := by
  let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
  have hnorm : Complex.normSq c ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hc
  have hbase : c * u + star c * star u = (t : ℂ) := by
    -- Evaluate the defining equation at the distinguished base point of the line.
    dsimp [u]
    calc
      c * (((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c) +
            star c * star ((((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c))
          = (((t / (2 * Complex.normSq c)) * Complex.normSq c +
                (t / (2 * Complex.normSq c)) * Complex.normSq c : ℝ) : ℂ) := by
              simp [Complex.normSq_eq_conj_mul_self, mul_assoc, mul_left_comm, mul_comm]
      _ = (t : ℂ) := by
        have hreal :
            (t / (2 * Complex.normSq c)) * Complex.normSq c +
              (t / (2 * Complex.normSq c)) * Complex.normSq c = t := by
          field_simp [hnorm]
          ring
        exact_mod_cast hreal
  have hshift :
      c * (w - u) + star c * star (w - u) =
        (c * w + star c * star w) - (c * u + star c * star u) := by
    -- Translate the affine equation from `w` to the chosen base point `u`.
    simp [sub_eq_add_neg, mul_add]
    ring
  constructor
  · intro hw
    have hdir : ∃ s : ℝ, w - u = s • (Complex.I * star c) :=
      (reflectionLineVsubBasepoint_iff_realSmulDirection (c := c) (w := w) (t := t) hc).1 hw
    have hzero : c * (w - u) + star c * star (w - u) = 0 :=
      (reflectionLineEquationZero_iff_realSmulDirection (c := c) (d := w - u) hc).2 hdir
    calc
      c * w + star c * star w
          = (c * (w - u) + star c * star (w - u)) + (c * u + star c * star u) := by
              rw [hshift]
              ring
      _ = (0 : ℂ) + (t : ℂ) := by rw [hzero, hbase]
      _ = (t : ℂ) := by simp
  · intro hw
    have hzero : c * (w - u) + star c * star (w - u) = 0 := by
      rw [hshift, hw, hbase]
      ring
    have hdir : ∃ s : ℝ, w - u = s • (Complex.I * star c) :=
      (reflectionLineEquationZero_iff_realSmulDirection (c := c) (d := w - u) hc).1 hzero
    exact (reflectionLineVsubBasepoint_iff_realSmulDirection
      (c := c) (w := w) (t := t) hc).2 hdir

/-- Helper for Exercise 6: the normal vector `conj c` is orthogonal to the direction space of the
reflection line. -/
theorem star_mem_reflectionLine_directionOrthogonal {c : ℂ} {t : ℝ} (hc : c ≠ 0) :
    star c ∈ (reflection_line c t hc).directionᗮ := by
  let u : ℂ := ((t / (2 * Complex.normSq c) : ℝ) : ℂ) * star c
  let v : ℂ := u + Complex.I * star c
  have hvsub : v - u = Complex.I * star c := by
    -- The affine direction is exactly `I * conj c`.
    simp [u, v]
  have hline : reflection_line c t hc = line[ℝ, u, v] := by
    -- Replace the packaged line by its explicit affine-span model.
    simp [reflection_line, u, v]
  simpa [hline] using
    (by
      rw [direction_affineSpan, vectorSpan_pair_rev,
        Submodule.mem_orthogonal_singleton_iff_inner_left]
      simpa [hvsub, smul_eq_mul, mul_comm] using
        (real_inner_I_smul_self (𝕜 := ℂ) (E := ℂ) (x := star c)) :
      star c ∈ (line[ℝ, u, v] : AffineSubspace ℝ ℂ).directionᗮ)

/-- Helper for Exercise 6: the antisymmetric line equation cuts out the real span of `conj c`. -/
theorem mulSubStar_eq_zero_iff_realSmulStar {c d : ℂ} (hc : c ≠ 0) :
    c * d - star c * star d = 0 ↔ ∃ s : ℝ, d = s • star c := by
  constructor
  · intro hzero
    let q : ℂ := d / star c
    have hstarc : star c ≠ 0 := by
      intro hstar
      apply hc
      simpa using congrArg star hstar
    have hd : d = q * star c := by
      dsimp [q]
      exact (div_mul_cancel₀ d hstarc).symm
    have hfactor :
        c * d - star c * star d = (Complex.normSq c : ℂ) * (q - star q) := by
      -- Normalize by the nonzero normal vector instead of the direction vector.
      rw [hd]
      simp [q, Complex.normSq_eq_conj_mul_self]
      ring
    have hnorm : (Complex.normSq c : ℂ) ≠ 0 := by
      exact_mod_cast (show Complex.normSq c ≠ 0 by simpa [Complex.normSq_eq_zero] using hc)
    have hq_eq : q = star q := by
      have hmulzero : (Complex.normSq c : ℂ) * (q - star q) = 0 := by
        rwa [hfactor] at hzero
      apply sub_eq_zero.mp
      exact (mul_eq_zero.mp hmulzero).resolve_left hnorm
    have hq_real : q = (Complex.re q : ℂ) := by
      have him : Complex.im q = 0 := Complex.conj_eq_iff_im.mp hq_eq.symm
      calc
        q = (Complex.re q : ℂ) + (Complex.im q : ℂ) * Complex.I := by
          symm
          exact Complex.re_add_im q
        _ = (Complex.re q : ℂ) := by simp [him]
    refine ⟨Complex.re q, ?_⟩
    calc
      d = q * star c := hd
      _ = (Complex.re q : ℂ) * star c := by
        exact congrArg (fun z : ℂ ↦ z * star c) hq_real
      _ = Complex.re q • star c := by simp
  · rintro ⟨s, rfl⟩
    -- A real multiple of the normal vector makes the antisymmetric expression vanish.
    simp [mul_assoc, mul_comm]

/-- Helper for Exercise 6: on the explicit pole-chart domain, a point that is neither already in
the transported exterior nor on the transported boundary line must come from the source interior,
so reflecting it across that line lands in the transported exterior. -/
theorem reflection_mem_explicitPoleExterior_of_not_mem_exterior_not_line
    {a p w : ℂ} {r : ℝ} {D : Set ℂ}
    (hr : 0 < r) (hp : p ∈ Metric.sphere a r) (ha_not_mem : a ∉ D) (hp_not_mem : p ∉ D)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hw0 : w ≠ 0) (hwD : invPoleChart p w ∈ D)
    (hw_not_ext : invPoleChart p w ∉ circleExterior a r D)
    (hw_not_line :
      w ∉ reflection_line (a - p) (-1) (sub_ne_zero.mpr <| by
        intro hpa
        have hpdist : ‖p - a‖ = r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hp
        exact hr.ne' <| by simpa [hpa] using hpdist.symm)) :
    let L := reflection_line (a - p) (-1) (sub_ne_zero.mpr <| by
      intro hpa
      have hpdist : ‖p - a‖ = r := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hp
      exact hr.ne' <| by simpa [hpa] using hpdist.symm)
    reflection L w ≠ 0 ∧ invPoleChart p (reflection L w) ∈ circleExterior a r D := by
  let L := reflection_line (a - p) (-1) (sub_ne_zero.mpr <| by
    intro hpa
    have hpdist : ‖p - a‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hp
    exact hr.ne' <| by simpa [hpa] using hpdist.symm)
  let z : ℂ := invPoleChart p w
  have hz_ne_p : z ≠ p := by
    simpa [z] using invPoleChart_ne_base (p := p) hw0
  have hz_int : z ∈ circleInterior a r D := by
    -- The source point lies in `D`; excluding the exterior and the boundary leaves only the
    -- interior side.
    rw [mem_circleInterior]
    refine ⟨hwD, ?_⟩
    by_contra hz_not_lt
    have hz_ge : r ≤ ‖z - a‖ := le_of_not_gt hz_not_lt
    rcases lt_or_eq_of_le hz_ge with hz_gt | hz_eq
    · exact hw_not_ext ((mem_circleExterior).2 ⟨hwD, hz_gt⟩)
    · apply hw_not_line
      have hz_boundary : z ∈ circleBoundaryArc a r D := by
        refine (mem_circleBoundaryArc).2 ?_
        refine ⟨hwD, ?_⟩
        simpa [Metric.mem_sphere, dist_eq_norm] using hz_eq.symm
      have hz_sphere : z ∈ Metric.sphere a r := (mem_circleBoundaryArc.mp hz_boundary).2
      simpa [L, z, poleChart_invPoleChart (p := p) hw0] using
        (poleChart_memReflectionLine_of_mem_sphere (a := a) (p := p) (z := z) hr hp hz_sphere
          hz_ne_p)
  have hreflect_eq :
      invPoleChart p (reflection L w) = inversion a r z :=
    invPoleChart_reflection_eq_inversion (a := a) (p := p) (w := w) (r := r) (D := D)
      hr hp ha_not_mem hw0 hwD
  have hreflect_ext : invPoleChart p (reflection L w) ∈ circleExterior a r D := by
    -- After transport back to the source, the reflected point is the inversion of an interior
    -- point, hence exterior by the textbook symmetry hypothesis.
    rw [hreflect_eq]
    exact inversion_mapsTo_circleExterior hD_reflect hz_int
  have hreflect_ne_zero : reflection L w ≠ 0 := by
    -- Otherwise the reflected source point would be the pole `p`, which is outside `D`.
    intro hzero
    have hp_ext : p ∈ circleExterior a r D := by
      simpa [L, hzero, invPoleChart] using hreflect_ext
    exact hp_not_mem (mem_circleExterior.mp hp_ext).1
  exact ⟨hreflect_ne_zero, hreflect_ext⟩

/-- Cartan section26 0016_Exercise_6 (Exercise 6 (1)): the inversion-defined reflected map is
holomorphic on the full reflected domain. -/
theorem circle_reflection_extension
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hΔ_open : IsOpen Δ) (hΔ_connected : IsConnected Δ)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D))
    (hΓ₀ : IsOpenArcOnCircle α ρ (circleBoundaryArc α ρ Δ))
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (hf_holo : AnalyticOnNhd ℂ f (circleExterior a r D))
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (hf_boundary :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ)) :
    AnalyticOnNhd ℂ (circleReflection a α r ρ D f) D := by
  have ha_not_mem : a ∉ D :=
    center_not_mem_of_circleExterior_eq_inversion_image_circleInterior hr hD_reflect
  have hα_not_mem : α ∉ Δ :=
    center_not_mem_of_circleExterior_eq_inversion_image_circleInterior hρ hΔ_reflect
  rcases exists_sphere_point_not_mem_of_open_arc hC₀ with ⟨pS, hpS_sphere, hpS_not_mem⟩
  rcases exists_sphere_point_not_mem_of_open_arc hΓ₀ with ⟨pT, hpT_sphere, hpT_not_mem⟩
  let mS : ℂ → ℂ := poleChart pS
  let mT : ℂ → ℂ := poleChart pT
  have hpS_ne : pS ≠ a := by
    have hpSdist : ‖pS - a‖ = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hpS_sphere
    exact fun hpS_eq ↦ hr.ne' <| by simpa [hpS_eq] using hpSdist.symm
  have hpT_ne : pT ≠ α := by
    have hpTdist : ‖pT - α‖ = ρ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hpT_sphere
    exact fun hpT_eq ↦ hρ.ne' <| by simpa [hpT_eq] using hpTdist.symm
  have hmS_reflect :
      ∀ ⦃z : ℂ⦄, z ∈ D → z ≠ pS →
        reflection (reflection_line (a - pS) (-1) (sub_ne_zero.mpr (Ne.symm hpS_ne))) (mS z) =
          mS (inversion a r z) := by
    intro z hzD hzp
    have hza : z ≠ a := by
      intro hza
      exact ha_not_mem (hza ▸ hzD)
    simpa [mS] using
      poleChart_reflects_inversion (a := a) (p := pS) (z := z) hr hpS_sphere hza hzp
  have hmT_reflect :
      ∀ ⦃w : ℂ⦄, w ∈ Δ → w ≠ pT →
        reflection (reflection_line (α - pT) (-1) (sub_ne_zero.mpr (Ne.symm hpT_ne))) (mT w) =
          mT (inversion α ρ w) := by
    intro w hwΔ hwp
    have hwα : w ≠ α := by
      intro hwα
      exact hα_not_mem (hwα ▸ hwΔ)
    simpa [mT] using
      poleChart_reflects_inversion (a := α) (p := pT) (z := w) hρ hpT_sphere hwα hwp
  have hmS_boundary :
      ∀ ⦃z : ℂ⦄, z ∈ circleBoundaryArc a r D → z ≠ pS →
        mS z ∈ reflection_line (a - pS) (-1) (sub_ne_zero.mpr (Ne.symm hpS_ne)) := by
    intro z hz hzp
    have hzSphere : z ∈ Metric.sphere a r := (mem_circleBoundaryArc.mp hz).2
    simpa [mS] using
      poleChart_memReflectionLine_of_mem_sphere (a := a) (p := pS) (z := z) hr hpS_sphere hzSphere
        hzp
  have hmT_boundary :
      ∀ ⦃w : ℂ⦄, w ∈ circleBoundaryArc α ρ Δ → w ≠ pT →
        mT w ∈ reflection_line (α - pT) (-1) (sub_ne_zero.mpr (Ne.symm hpT_ne)) := by
    intro w hw hwp
    have hwSphere : w ∈ Metric.sphere α ρ := (mem_circleBoundaryArc.mp hw).2
    simpa [mT] using
      poleChart_memReflectionLine_of_mem_sphere (a := α) (p := pT) (z := w) hρ hpT_sphere hwSphere
        hwp
  -- Route correction: the source-side swap needed for the reflected branch is now available via
  -- `reflection_mem_explicitPoleExterior_of_not_mem_exterior_not_line`, so the remaining gap is no
  -- longer the global exterior/interior classification. What is still missing is a compile-stable
  -- affine-conjugation adapter for `w ↦ reflection LT (F (reflection LS w))`, together with the
  -- pointwise differentiability package that lets `continuous_holomorphic_off_line_differentiableOn`
  -- glue the transported exterior and reflected branches.
  classical
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  let LS : AffineSubspace ℝ ℂ :=
    reflection_line (a - pS) (-1) (sub_ne_zero.mpr (Ne.symm hpS_ne))
  let LT : AffineSubspace ℝ ℂ :=
    reflection_line (α - pT) (-1) (sub_ne_zero.mpr (Ne.symm hpT_ne))
  let Omega : Set ℂ := {w : ℂ | w ≠ 0 ∧ invPoleChart pS w ∈ D}
  let OmegaExt : Set ℂ := {w : ℂ | w ≠ 0 ∧ invPoleChart pS w ∈ circleExterior a r D}
  let OmegaPlus : Set ℂ :=
    {w : ℂ | w ≠ 0 ∧ invPoleChart pS w ∈ circleExterior a r D ∪ circleBoundaryArc a r D}
  let boundarySlice : Set ℂ :=
    {w : ℂ | w ≠ 0 ∧ invPoleChart pS w ∈ circleBoundaryArc a r D}
  let F : ℂ → ℂ := fun w ↦ mT (f (invPoleChart pS w))
  let G : ℂ → ℂ := fun w ↦ reflection LT (F (reflection LS w))
  let H : ℂ → ℂ := Set.piecewise OmegaExt F G
  let uS : ℂ := (((-1 : ℝ) / (2 * Complex.normSq (a - pS)) : ℝ) : ℂ) * star (a - pS)
  let vS : ℂ := uS + Complex.I * star (a - pS)
  let AS : ℂ → ℂ := fun ζ ↦ uS + (vS - uS) * ζ
  let psiS : ℂ → ℂ := fun w ↦ (w - uS) / (vS - uS)
  let uT : ℂ := (((-1 : ℝ) / (2 * Complex.normSq (α - pT)) : ℝ) : ℂ) * star (α - pT)
  let vT : ℂ := uT + Complex.I * star (α - pT)
  let AT : ℂ → ℂ := fun ζ ↦ uT + (vT - uT) * ζ
  let psiT : ℂ → ℂ := fun w ↦ (w - uT) / (vT - uT)
  let FTilde : ℂ → ℂ := fun ζ ↦ psiT (F (AS ζ))
  let K : ℂ → ℂ := fun ζ ↦ psiT (G (AS ζ))
  have hOmega_open : IsOpen Omega := by
    -- The transported source domain stays open under the inverse pole chart.
    simpa [Omega] using isOpen_explicitPoleChartDomain (p := pS) hD_open
  have hOmegaExt_open : IsOpen OmegaExt := by
    -- The explicit exterior pullback is open for the same reason.
    simpa [OmegaExt] using
      isOpen_explicitPoleChartDomain (p := pS) (isOpen_circleExterior hD_open)
  have hOmegaPlus_subset_punctured : OmegaPlus ⊆ {w : ℂ | w ≠ 0} := by
    intro w hw
    exact hw.1
  have hBoundarySlice_subset_plus : boundarySlice ⊆ OmegaPlus := by
    intro w hw
    exact ⟨hw.1, Or.inr hw.2⟩
  have hBoundarySlice_subset_line : boundarySlice ⊆ LS := by
    intro w hw
    have hw_line :
        mS (invPoleChart pS w) ∈ LS := by
      have hw_ne_base : invPoleChart pS w ≠ pS := invPoleChart_ne_base hw.1
      simpa [LS] using hmS_boundary hw.2 hw_ne_base
    simpa [mS, poleChart_invPoleChart (p := pS) hw.1] using hw_line
  have hFrontier_subset_boundarySlice :
      Omega ∩ frontier OmegaExt ⊆ boundarySlice := by
    simpa [Omega, OmegaExt, boundarySlice] using
      explicitPoleExteriorFrontier_subset_boundarySlice (a := a) (p := pS) (r := r)
        (D := D) hD_open hpS_not_mem
  have hFrontier_subset_line : Omega ∩ frontier OmegaExt ⊆ LS := by
    intro w hw
    exact hBoundarySlice_subset_line (hFrontier_subset_boundarySlice hw)
  have hDomain_trichotomy :
      ∀ ⦃z : ℂ⦄, z ∈ D →
        z ∈ circleExterior a r D ∨ z ∈ circleBoundaryArc a r D ∨ z ∈ circleInterior a r D := by
    intro z hzD
    -- Compare the radius of `z` with `r` to split `D` into the textbook exterior/boundary/interior
    -- pieces.
    rcases lt_trichotomy ‖z - a‖ r with hz_lt | hz_eq | hz_gt
    · exact Or.inr <| Or.inr <| (mem_circleInterior.2 ⟨hzD, hz_lt⟩)
    · refine Or.inr <| Or.inl <| mem_circleBoundaryArc.2 ?_
      refine ⟨hzD, ?_⟩
      simpa [Metric.mem_sphere, dist_eq_norm] using hz_eq
    · exact Or.inl <| (mem_circleExterior.2 ⟨hzD, hz_gt⟩)
  have hcircle_maps_target : Set.MapsTo g D Δ := by
    intro z hzD
    rcases hDomain_trichotomy hzD with
      hz_ext | hz_boundary | hz_int
    · -- On the exterior branch, `g` is just `f`.
      rw [show g z = f z by
        simpa [g] using circleReflection_apply_of_mem_exterior_boundary
          (a := a) (α := α) (r := r) (ρ := ρ) (D := D) (f := f) (z := z) (Or.inl hz_ext)]
      exact (hf_maps hz_ext).1
    · -- On the boundary arc, `g` still agrees with `f`.
      rw [show g z = f z by
        simpa [g] using circleReflection_apply_of_mem_exterior_boundary
          (a := a) (α := α) (r := r) (ρ := ρ) (D := D) (f := f) (z := z) (Or.inr hz_boundary)]
      exact (hf_boundary hz_boundary).1
    · -- On the interior side, the reflected inversion lands in the target interior.
      have hz_not_mem :
          z ∉ circleExterior a r D ∪ circleBoundaryArc a r D := by
        rw [mem_circleInterior] at hz_int
        intro hz'
        rcases hz' with hz_ext' | hz_boundary'
        · rw [mem_circleExterior] at hz_ext'
          exact (not_lt_of_ge hz_int.2.le) hz_ext'.2
        · rw [mem_circleBoundaryArc] at hz_boundary'
          have hz_not_sphere : z ∉ Metric.sphere a r := by
            simpa [Metric.mem_sphere, dist_eq_norm] using (ne_of_lt hz_int.2)
          exact hz_not_sphere hz_boundary'.2
      have hzInv_ext : inversion a r z ∈ circleExterior a r D :=
        inversion_mapsTo_circleExterior hD_reflect hz_int
      have htarget_int :
          inversion α ρ (f (inversion a r z)) ∈ circleInterior α ρ Δ :=
        inversion_mapsTo_circleInterior hρ hΔ_reflect (hf_maps hzInv_ext)
      simpa [g, circleReflection_apply_of_not_mem_exterior_boundary hz_not_mem] using
        (mem_circleInterior.mp htarget_int).1
  have hg_ne_pT : ∀ z ∈ D, g z ≠ pT := by
    intro z hzD hEq
    exact hpT_not_mem (hEq ▸ hcircle_maps_target hzD)
  have hstarS_ne_zero : star (a - pS) ≠ 0 := by
    intro hzero
    apply sub_ne_zero.mpr (Ne.symm hpS_ne)
    exact by simpa using congrArg star hzero
  have hstarT_ne_zero : star (α - pT) ≠ 0 := by
    intro hzero
    apply sub_ne_zero.mpr (Ne.symm hpT_ne)
    exact by simpa using congrArg star hzero
  have hSlopeS_ne : vS - uS ≠ 0 := by
    -- The source affine straightener has nonzero slope because the reflected line is genuine.
    rw [show vS - uS = Complex.I * star (a - pS) by simp [uS, vS]]
    exact mul_ne_zero Complex.I_ne_zero hstarS_ne_zero
  have hSlopeT_ne : vT - uT ≠ 0 := by
    -- The target straightener is equally nondegenerate.
    rw [show vT - uT = Complex.I * star (α - pT) by simp [uT, vT]]
    exact mul_ne_zero Complex.I_ne_zero hstarT_ne_zero
  have hAS_diff : Differentiable ℂ AS := by
    -- The straightening chart is affine.
    simpa [AS, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using ((differentiable_id.const_mul (vS - uS)).const_add uS)
  have hAT_diff : Differentiable ℂ AT := by
    -- The target straightening chart is also affine.
    simpa [AT, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using ((differentiable_id.const_mul (vT - uT)).const_add uT)
  have hpsiS_diff : Differentiable ℂ psiS := by
    -- The inverse affine chart divides by the nonzero source slope.
    simpa [psiS, div_eq_mul_inv, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc,
      mul_left_comm, mul_comm] using ((differentiable_id.sub_const uS).mul_const ((vS - uS)⁻¹))
  have hpsiT_diff : Differentiable ℂ psiT := by
    -- The target inverse affine chart is affine as well.
    simpa [psiT, div_eq_mul_inv, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc,
      mul_left_comm, mul_comm] using ((differentiable_id.sub_const uT).mul_const ((vT - uT)⁻¹))
  have hAS_cont : Continuous AS := hAS_diff.continuous
  have hAT_cont : Continuous AT := hAT_diff.continuous
  have hAS_psiS : ∀ w : ℂ, AS (psiS w) = w := by
    intro w
    -- The source affine chart and its inverse cancel exactly.
    dsimp [AS, psiS]
    field_simp [hSlopeS_ne]
    ring
  have hpsiS_AS : ∀ ζ : ℂ, psiS (AS ζ) = ζ := by
    intro ζ
    -- The same cancellation holds in the other order.
    dsimp [AS, psiS]
    field_simp [hSlopeS_ne]
    ring
  have hAT_psiT : ∀ w : ℂ, AT (psiT w) = w := by
    intro w
    -- The target affine chart cancels its inverse as well.
    dsimp [AT, psiT]
    field_simp [hSlopeT_ne]
    ring
  have hpsiT_AT : ∀ ζ : ℂ, psiT (AT ζ) = ζ := by
    intro ζ
    -- This normalization is what lets us compare the reflected branch in one spelling world.
    dsimp [AT, psiT]
    field_simp [hSlopeT_ne]
    ring
  have hAS_conj :
      ∀ ζ : ℂ, AS (conj ζ) = reflection LS (AS ζ) := by
    -- Straightening the source reflection line turns reflection into complex conjugation.
    simpa [LS, AS, uS, vS] using
      reflection_line_straightening_intertwines_conj
        (c := a - pS) (t := (-1 : ℝ)) (hc := sub_ne_zero.mpr (Ne.symm hpS_ne))
  have hAT_conj :
      ∀ ζ : ℂ, AT (conj ζ) = reflection LT (AT ζ) := by
    -- The target line enjoys the same straightening identity.
    simpa [LT, AT, uT, vT] using
      reflection_line_straightening_intertwines_conj
        (c := α - pT) (t := (-1 : ℝ)) (hc := sub_ne_zero.mpr (Ne.symm hpT_ne))
  have hPreLS :
      AS ⁻¹' LS = {ζ : ℂ | ζ.im = 0} := by
    -- After source straightening, the exceptional reflection line is the real axis.
    simpa [LS, AS, uS, vS] using
      preimage_reflection_line_eq_real_axis
        (c := a - pS) (t := (-1 : ℝ)) (hc := sub_ne_zero.mpr (Ne.symm hpS_ne))
  have hpsiReflection_eq_conjPsi :
      ∀ w : ℂ, psiT (reflection LT w) = conj (psiT w) := by
    intro w
    -- Normalize the target reflection only after moving through the affine straightener.
    have hstraight := hAT_conj (psiT w)
    rw [hAT_psiT w] at hstraight
    calc
      psiT (reflection LT w) = psiT (AT (conj (psiT w))) := by rw [← hstraight]
      _ = conj (psiT w) := hpsiT_AT (conj (psiT w))
  have hInvPole_diffOn : DifferentiableOn ℂ (invPoleChart pS) {w : ℂ | w ≠ 0} := by
    intro w hw
    -- The inverse pole chart is holomorphic on the punctured plane.
    simpa [invPoleChart, sub_eq_add_neg] using
      ((differentiableAt_const (𝕜 := ℂ) pS).sub (differentiableAt_inv hw)).differentiableWithinAt
  have hPole_diffOn : DifferentiableOn ℂ (poleChart pT) {w : ℂ | w ≠ pT} := by
    intro w hw
    -- The pole chart is the usual Möbius inversion away from the target pole.
    change DifferentiableWithinAt ℂ (fun z : ℂ ↦ -((z - pT)⁻¹)) {w : ℂ | w ≠ pT} w
    simpa [poleChart] using
      (((differentiableAt_inv (sub_ne_zero.mpr hw)).comp w
          (differentiableAt_id.sub_const pT)).neg).differentiableWithinAt
  have hInvPole_contOn : ContinuousOn (invPoleChart pS) {w : ℂ | w ≠ 0} := by
    intro w hw
    -- Continuity on the punctured plane is immediate from continuity of inversion.
    simpa [invPoleChart, sub_eq_add_neg] using
      ((continuousAt_const.sub (continuousAt_inv₀ hw))).continuousWithinAt
  have hPole_contOn : ContinuousOn (poleChart pT) {w : ℂ | w ≠ pT} := by
    intro w hw
    -- The target pole chart is continuous away from the pole.
    exact (hPole_diffOn w hw).continuousWithinAt
  have hF_contPlus : ContinuousOn F OmegaPlus := by
    -- First pull the source continuity through the inverse pole chart, then apply the target pole
    -- chart on the punctured target.
    have hInv_on_plus : ContinuousOn (invPoleChart pS) OmegaPlus :=
      hInvPole_contOn.mono hOmegaPlus_subset_punctured
    have hSource_maps :
        Set.MapsTo (invPoleChart pS) OmegaPlus
          (circleExterior a r D ∪ circleBoundaryArc a r D) := by
      intro w hw
      exact hw.2
    have hSource_cont :
        ContinuousOn (fun w ↦ f (invPoleChart pS w)) OmegaPlus :=
      hf_cont.comp hInv_on_plus hSource_maps
    have hTarget_maps :
        Set.MapsTo (fun w ↦ f (invPoleChart pS w)) OmegaPlus {u : ℂ | u ≠ pT} := by
      intro w hw
      rcases hw.2 with hw_ext | hw_boundary
      · exact fun hEq ↦ hpT_not_mem <| hEq ▸ (hf_maps hw_ext).1
      · exact fun hEq ↦ hpT_not_mem <| hEq ▸ (hf_boundary hw_boundary).1
    simpa [F, mT] using hPole_contOn.comp hSource_cont hTarget_maps
  have hF_diff : DifferentiableOn ℂ F OmegaExt := by
    -- The transported exterior branch is holomorphic because `f` is holomorphic there and the two
    -- pole charts are holomorphic away from their poles.
    have hInv_on_ext : DifferentiableOn ℂ (invPoleChart pS) OmegaExt :=
      hInvPole_diffOn.mono (by intro w hw; exact hw.1)
    have hSource_maps :
        Set.MapsTo (invPoleChart pS) OmegaExt (circleExterior a r D) := by
      intro w hw
      exact hw.2
    have hSource_diff :
        DifferentiableOn ℂ (fun w ↦ f (invPoleChart pS w)) OmegaExt :=
      hf_holo.differentiableOn.comp hInv_on_ext hSource_maps
    have hTarget_maps :
        Set.MapsTo (fun w ↦ f (invPoleChart pS w)) OmegaExt {u : ℂ | u ≠ pT} := by
      intro w hw
      exact fun hEq ↦ hpT_not_mem <| hEq ▸ (hf_maps hw.2).1
    simpa [F, mT] using hPole_diffOn.comp hSource_diff hTarget_maps
  have hboundary_value_on_target_line : ∀ ⦃w : ℂ⦄, w ∈ boundarySlice → F w ∈ LT := by
    intro w hw
    have hw_ne_base : invPoleChart pS w ≠ pS := invPoleChart_ne_base hw.1
    have hsource_boundary : f (invPoleChart pS w) ∈ circleBoundaryArc α ρ Δ :=
      hf_boundary hw.2
    have htarget_ne : f (invPoleChart pS w) ≠ pT := by
      exact fun hEq ↦ hpT_not_mem (hEq ▸ (mem_circleBoundaryArc.mp hsource_boundary).1)
    simpa [F, LT, mT, poleChart_invPoleChart (p := pS) hw.1] using
      hmT_boundary hsource_boundary htarget_ne
  have hF_eq_G_on_boundarySlice : ∀ ⦃w : ℂ⦄, w ∈ boundarySlice → F w = G w := by
    intro w hw
    -- On the pulled-back boundary slice, source reflection fixes the input and target reflection
    -- fixes the boundary value.
    have hw_line : w ∈ LS := hBoundarySlice_subset_line hw
    have hw_fix : reflection LS w = w :=
      (EuclideanGeometry.reflection_eq_self_iff (s := LS) (p := w)).2 hw_line
    have hF_line : F w ∈ LT := hboundary_value_on_target_line hw
    have htarget_fix : reflection LT (F w) = F w :=
      (EuclideanGeometry.reflection_eq_self_iff (s := LT) (p := F w)).2 hF_line
    simp [G, hw_fix, htarget_fix]
  have hReflection_maps_minus_to_plus :
      Set.MapsTo (reflection LS) (Omega ∩ OmegaExtᶜ) OmegaPlus := by
    intro w hw
    rcases hw with ⟨hwOmega, hwNotExt⟩
    rcases hwOmega with ⟨hw0, hwD⟩
    by_cases hwLine : w ∈ LS
    · -- Boundary points on the source line stay on that line and correspond to the boundary arc.
      have hw_boundary :
          invPoleChart pS w ∈ circleBoundaryArc a r D := by
        simpa [LS] using
          invPoleChart_mem_circleBoundaryArc_of_mem_reflectionLine (a := a) (p := pS) (w := w)
            (r := r) (D := D) hr hpS_sphere ha_not_mem hw0 hwD hwLine
      have hw_fix : reflection LS w = w :=
        (EuclideanGeometry.reflection_eq_self_iff (s := LS) (p := w)).2 hwLine
      simpa [OmegaPlus, hw_fix] using ⟨hw0, Or.inr hw_boundary⟩
    · -- Off the source line, the source-side helper moves the point into the explicit exterior.
      have hw_not_ext' : invPoleChart pS w ∉ circleExterior a r D := by
        intro hwExt
        exact hwNotExt ⟨hw0, hwExt⟩
      have hreflect :=
        reflection_mem_explicitPoleExterior_of_not_mem_exterior_not_line (a := a) (p := pS)
          (w := w) (r := r) (D := D) hr hpS_sphere ha_not_mem hpS_not_mem hD_reflect hw0 hwD
          hw_not_ext' hwLine
      simpa [OmegaPlus, LS] using ⟨hreflect.1, Or.inl hreflect.2⟩
  have hG_contMinus : ContinuousOn G (Omega ∩ OmegaExtᶜ) := by
    -- The reflected branch is continuous because source reflection lands in the already-continuous
    -- exterior-plus-boundary branch of `F`.
    have hmid :
        ContinuousOn (F ∘ reflection LS) (Omega ∩ OmegaExtᶜ) :=
      hF_contPlus.comp (reflection LS).continuous.continuousOn hReflection_maps_minus_to_plus
    have hReflT_on : ContinuousOn (reflection LT) (Set.univ : Set ℂ) :=
      (reflection LT).continuous.continuousOn
    change ContinuousOn ((fun z : ℂ ↦ reflection LT z) ∘ (F ∘ reflection LS))
      (Omega ∩ OmegaExtᶜ)
    simpa [Function.comp] using hReflT_on.comp hmid (by intro w hw; simp)
  have hPreOmegaExt_open : IsOpen (AS ⁻¹' OmegaExt) := hOmegaExt_open.preimage hAS_cont
  have hFTilde_diff : DifferentiableOn ℂ FTilde (AS ⁻¹' OmegaExt) := by
    -- After straightening the source line, the transported exterior branch remains holomorphic.
    have hAS_on_ext : DifferentiableOn ℂ AS (AS ⁻¹' OmegaExt) := hAS_diff.differentiableOn
    have hSource_diff :
        DifferentiableOn ℂ (F ∘ AS) (AS ⁻¹' OmegaExt) :=
      hF_diff.comp hAS_on_ext (by intro ζ hζ; exact hζ)
    have hpsiT_on : DifferentiableOn ℂ psiT Set.univ := hpsiT_diff.differentiableOn
    simpa [FTilde, Function.comp] using
      hpsiT_on.comp hSource_diff (by intro ζ hζ; simp)
  have hK_eq_fun : K = conj ∘ FTilde ∘ conj := by
    funext ζ
    -- Stay in the straightened coordinates until all reflections have been normalized.
    calc
      K ζ = psiT (reflection LT (F (reflection LS (AS ζ)))) := by rfl
      _ = psiT (reflection LT (F (AS (conj ζ)))) := by rw [hAS_conj ζ]
      _ = conj (psiT (F (AS (conj ζ)))) := hpsiReflection_eq_conjPsi (F (AS (conj ζ)))
      _ = (conj ∘ FTilde ∘ conj) ζ := by rfl
  have hconj_mem_preimage_ext :
      Set.MapsTo conj (((AS ⁻¹' Omega) ∩ (AS ⁻¹' OmegaExt)ᶜ) \ {ζ : ℂ | ζ.im = 0})
        (AS ⁻¹' OmegaExt) := by
    intro ζ hζ
    rcases hζ with ⟨⟨hζOmega, hζNotExt⟩, hζNotReal⟩
    have hASOmega : AS ζ ∈ Omega := hζOmega
    have hAS0 : AS ζ ≠ 0 := hASOmega.1
    have hASD : invPoleChart pS (AS ζ) ∈ D := hASOmega.2
    have hASNotExt : invPoleChart pS (AS ζ) ∉ circleExterior a r D := by
      intro hExt
      exact hζNotExt ⟨hAS0, hExt⟩
    have hASNotLine : AS ζ ∉ LS := by
      have hpre : ζ ∉ AS ⁻¹' LS := by
        intro hmem
        exact hζNotReal (by simpa [hPreLS] using hmem)
      simpa [Set.mem_preimage] using hpre
    have hreflect :=
      reflection_mem_explicitPoleExterior_of_not_mem_exterior_not_line (a := a) (p := pS)
        (w := AS ζ) (r := r) (D := D) hr hpS_sphere ha_not_mem hpS_not_mem hD_reflect hAS0 hASD
        hASNotExt hASNotLine
    have hASconj : AS (conj ζ) = reflection LS (AS ζ) := hAS_conj ζ
    simpa [OmegaExt, hASconj] using hreflect
  have hK_diff :
      DifferentiableOn ℂ K (((AS ⁻¹' Omega) ∩ (AS ⁻¹' OmegaExt)ᶜ) \ {ζ : ℂ | ζ.im = 0}) := by
    intro ζ hζ
    -- Once the reflected branch is rewritten as `conj ∘ FTilde ∘ conj`, differentiability follows
    -- from `DifferentiableAt.conj_conj` at the reflected exterior point.
    have hconjExt : conj ζ ∈ AS ⁻¹' OmegaExt := hconj_mem_preimage_ext hζ
    have hFTilde_at : DifferentiableAt ℂ FTilde (conj ζ) :=
      (hFTilde_diff (conj ζ) hconjExt).differentiableAt (hPreOmegaExt_open.mem_nhds hconjExt)
    have hK_at : DifferentiableAt ℂ K ζ := by
      simpa [hK_eq_fun, Function.comp, Complex.conj_conj] using hFTilde_at.conj_conj
    exact hK_at.differentiableWithinAt
  have hG_eq_fun : G = AT ∘ K ∘ psiS := by
    funext w
    -- Transport the straightened reflected branch back to the original pole-chart coordinates.
    calc
      G w = G (AS (psiS w)) := by rw [hAS_psiS w]
      _ = AT (K (psiS w)) := by simp [K, hAT_psiT]
      _ = (AT ∘ K ∘ psiS) w := by rfl
  have hG_diff :
      DifferentiableOn ℂ G ((Omega ∩ OmegaExtᶜ) \ LS) := by
    -- The only non-holomorphic step was source reflection; after straightening, it has already
    -- been absorbed into the `conj ∘ _ ∘ conj` formula for `K`.
    have hpsiS_on :
        DifferentiableOn ℂ psiS ((Omega ∩ OmegaExtᶜ) \ LS) := hpsiS_diff.differentiableOn
    have hpsiS_maps :
        Set.MapsTo psiS ((Omega ∩ OmegaExtᶜ) \ LS)
          (((AS ⁻¹' Omega) ∩ (AS ⁻¹' OmegaExt)ᶜ) \ {ζ : ℂ | ζ.im = 0}) := by
      intro w hw
      rcases hw with ⟨⟨hwOmega, hwNotExt⟩, hwNotLine⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [Set.mem_preimage, hAS_psiS w] using hwOmega
      · simpa [Set.mem_preimage, hAS_psiS w] using hwNotExt
      · have hnot_pre : psiS w ∉ AS ⁻¹' LS := by
          simpa [Set.mem_preimage, hAS_psiS w] using hwNotLine
        simpa [hPreLS] using hnot_pre
    have hKpsi_diff :
        DifferentiableOn ℂ (K ∘ psiS) ((Omega ∩ OmegaExtᶜ) \ LS) :=
      hK_diff.comp hpsiS_on hpsiS_maps
    have hAT_on : DifferentiableOn ℂ AT Set.univ := hAT_diff.differentiableOn
    simpa [hG_eq_fun, Function.comp] using
      hAT_on.comp hKpsi_diff (by intro w hw; simp)
  have hH_cont : ContinuousOn H Omega := by
    -- The two transported branches glue continuously along the pulled-back boundary arc.
    refine ContinuousOn.piecewise' ?_ ?_ ?_ ?_
    · intro w hw
      have hwSlice : w ∈ boundarySlice := hFrontier_subset_boundarySlice hw
      have hwNotExt : w ∉ OmegaExt := by
        intro hwExt
        exact hw.2.2 <|
          mem_interior_iff_mem_nhds.2 (hOmegaExt_open.mem_nhds hwExt)
      have hcont :
          ContinuousWithinAt F OmegaPlus w := hF_contPlus w (hBoundarySlice_subset_plus hwSlice)
      have hcont' :
          ContinuousWithinAt F (Omega ∩ OmegaExt) w := by
        refine hcont.mono ?_
        intro z hz
        exact ⟨hz.2.1, Or.inl hz.2.2⟩
      have hwEq : F w = G w := hF_eq_G_on_boundarySlice hwSlice
      have hwEq' : G w = F w := hwEq.symm
      simpa [H, hwNotExt, hwEq'] using hcont'
    · intro w hw
      have hwSlice : w ∈ boundarySlice := hFrontier_subset_boundarySlice hw
      have hwNotExt : w ∉ OmegaExt := by
        intro hwExt
        exact hw.2.2 <|
          mem_interior_iff_mem_nhds.2 (hOmegaExt_open.mem_nhds hwExt)
      have hcont : ContinuousWithinAt G (Omega ∩ OmegaExtᶜ) w :=
        hG_contMinus w ⟨hw.1, hwNotExt⟩
      simpa [H, hwNotExt] using hcont
    · simpa [H] using hF_contPlus.mono (by
        intro w hw
        rcases hw with ⟨hwOmega, hwExt⟩
        exact ⟨hwExt.1, Or.inl hwExt.2⟩)
    · simpa [H] using hG_contMinus
  have hBoundary_nhds : ∀ {w : ℂ}, w ∈ boundarySlice → w ∈ LS := by
    intro w hw
    exact hBoundarySlice_subset_line hw
  have hH_diffOff : DifferentiableOn ℂ H (Omega \ LS) := by
    intro w hw
    rcases hw with ⟨hwOmega, hwNotLine⟩
    by_cases hwExt : w ∈ OmegaExt
    · -- On the open exterior pullback, the piecewise function is locally just `F`.
      have hF_at : DifferentiableAt ℂ F w :=
        (hF_diff w hwExt).differentiableAt (hOmegaExt_open.mem_nhds hwExt)
      have hEq : H =ᶠ[nhdsWithin w (Omega \ LS)] F := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hOmegaExt_open.mem_nhds hwExt)] with z hz
        simp [H, hz]
      exact hF_at.differentiableWithinAt.congr_of_eventuallyEq hEq (by simp [H, hwExt])
    · -- Away from both the exterior pullback and the source line, the frontier subset lemma gives
      -- a neighborhood on which the piecewise function is just `G`.
      have hwNotFront : w ∉ frontier OmegaExt := by
        intro hwFront
        exact hwNotLine (hFrontier_subset_line ⟨hwOmega, hwFront⟩)
      have hwNotClosure : w ∉ closure OmegaExt := by
        intro hwClosure
        apply hwNotFront
        refine ⟨hwClosure, ?_⟩
        intro hwInterior
        exact hwExt (interior_subset hwInterior)
      have hG_at : DifferentiableAt ℂ G w := by
        have hNhds :
            ((Omega ∩ OmegaExtᶜ) \ (LS : Set ℂ)) ∈ nhds w := by
          have hOmega_mem : Omega ∈ nhds w := hOmega_open.mem_nhds hwOmega
          have hNotClosure_mem : (closure OmegaExt)ᶜ ∈ nhds w :=
            isClosed_closure.isOpen_compl.mem_nhds hwNotClosure
          have hNotLine_mem : (LS : Set ℂ)ᶜ ∈ nhds w :=
            (LS.closed_of_finiteDimensional.isOpen_compl).mem_nhds hwNotLine
          refine mem_of_superset (inter_mem (inter_mem hOmega_mem hNotClosure_mem) hNotLine_mem) ?_
          intro z hz
          rcases hz with ⟨hzLeft, hzNotLine⟩
          rcases hzLeft with ⟨hzOmega, hzNotClosure⟩
          refine ⟨⟨hzOmega, ?_⟩, hzNotLine⟩
          intro hzExt
          exact hzNotClosure (subset_closure hzExt)
        exact (hG_diff w ⟨⟨hwOmega, hwExt⟩, hwNotLine⟩).differentiableAt hNhds
      have hEq : H =ᶠ[nhdsWithin w (Omega \ LS)] G := by
        have hNhds :
            Omega ∩ (closure OmegaExt)ᶜ ∩ (LS : Set ℂ)ᶜ ∈ nhds w := by
          exact inter_mem
            (inter_mem (hOmega_open.mem_nhds hwOmega)
              (isClosed_closure.isOpen_compl.mem_nhds hwNotClosure))
            ((LS.closed_of_finiteDimensional.isOpen_compl).mem_nhds hwNotLine)
        filter_upwards [mem_nhdsWithin_of_mem_nhds hNhds] with z hz
        have hzNotExt : z ∉ OmegaExt := by
          intro hzExt
          exact hz.1.2 (subset_closure hzExt)
        simp [H, hzNotExt]
      exact hG_at.differentiableWithinAt.congr_of_eventuallyEq hEq (by simp [H, hwExt])
  have hLS_line : LS = line[ℝ, uS, vS] := by
    -- Expose the source reflection line in the explicit affine form needed by the removable-line
    -- theorem.
    simp [LS, reflection_line, uS, vS]
  have hH_diff : DifferentiableOn ℂ H Omega := by
    -- Apply the earlier removable-line theorem once the transported map is continuous and
    -- holomorphic off the source reflection line.
    simpa [hLS_line] using
      continuous_holomorphic_off_line_differentiableOn
        (D := Omega) (f := H) (z₀ := uS) (z₁ := vS) hOmega_open hH_cont hH_diffOff
  have hPoleS_diffOn : DifferentiableOn ℂ mS D := by
    intro z hzD
    have hz_ne : z ≠ pS := by
      intro hEq
      exact hpS_not_mem (hEq ▸ hzD)
    -- The source pole chart is holomorphic on `D` because the chosen pole lies outside `D`.
    change DifferentiableWithinAt ℂ (fun w : ℂ ↦ -((w - pS)⁻¹)) D z
    simpa [mS, poleChart] using
      (((differentiableAt_inv (sub_ne_zero.mpr hz_ne)).comp z
          (differentiableAt_id.sub_const pS)).neg).differentiableWithinAt
  have hmS_maps : Set.MapsTo mS D Omega := by
    intro z hzD
    have hz_ne : z ≠ pS := by
      intro hEq
      exact hpS_not_mem (hEq ▸ hzD)
    change mS z ≠ 0 ∧ invPoleChart pS (mS z) ∈ D
    refine ⟨poleChart_ne_zero (p := pS) hz_ne, ?_⟩
    simpa [mS, hz_ne] using hzD
  have htransport_model :
      Set.EqOn (fun z ↦ H (mS z)) (fun z ↦ mT (g z)) D := by
    intro z hzD
    have hz_ne : z ≠ pS := by
      intro hEq
      exact hpS_not_mem (hEq ▸ hzD)
    rcases hDomain_trichotomy hzD with
      hzExt | hzBoundary | hzInt
    · -- On the exterior branch, all transported formulas collapse to `f`.
      have hmSz_ext : mS z ∈ OmegaExt := by
        change mS z ≠ 0 ∧ invPoleChart pS (mS z) ∈ circleExterior a r D
        refine ⟨poleChart_ne_zero (p := pS) hz_ne, ?_⟩
        simpa [mS, hz_ne] using hzExt
      calc
        H (mS z) = F (mS z) := by simp [H, hmSz_ext]
        _ = mT (f z) := by simp [F, mS, hz_ne]
        _ = mT (g z) := by
          have hgEq : g z = f z := by
            simpa [g] using circleReflection_apply_of_mem_exterior_boundary
              (a := a) (α := α) (r := r) (ρ := ρ) (D := D) (f := f) (z := z) (Or.inl hzExt)
          rw [hgEq]
    · -- On the boundary slice, source and target reflections both fix the transported value.
      have hmSz_not_ext : mS z ∉ OmegaExt := by
        intro hmSz_ext
        have hzExt' : z ∈ circleExterior a r D := by
          simpa [OmegaExt, mS, hz_ne] using hmSz_ext
        have hzNorm : ‖z - a‖ = r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using (mem_circleBoundaryArc.mp hzBoundary).2
        exact (not_lt_of_ge hzNorm.le) (mem_circleExterior.mp hzExt').2
      have hmSz_slice : mS z ∈ boundarySlice := by
        change mS z ≠ 0 ∧ invPoleChart pS (mS z) ∈ circleBoundaryArc a r D
        refine ⟨poleChart_ne_zero (p := pS) hz_ne, ?_⟩
        simpa [mS, hz_ne] using hzBoundary
      calc
        H (mS z) = G (mS z) := by simp [H, hmSz_not_ext]
        _ = F (mS z) := (hF_eq_G_on_boundarySlice hmSz_slice).symm
        _ = mT (f z) := by simp [F, mS, hz_ne]
        _ = mT (g z) := by
          have hgEq : g z = f z := by
            simpa [g] using circleReflection_apply_of_mem_exterior_boundary
              (a := a) (α := α) (r := r) (ρ := ρ) (D := D) (f := f) (z := z)
                (Or.inr hzBoundary)
          rw [hgEq]
    · -- On the interior branch, the reflected pole-chart formula reproduces the defining inversion
      -- branch of `circleReflection`.
      have hz_not_mem :
          z ∉ circleExterior a r D ∪ circleBoundaryArc a r D :=
        by
          rw [mem_circleInterior] at hzInt
          intro hz'
          rcases hz' with hzExt' | hzBoundary'
          · rw [mem_circleExterior] at hzExt'
            exact (not_lt_of_ge hzInt.2.le) hzExt'.2
          · rw [mem_circleBoundaryArc] at hzBoundary'
            have hz_not_sphere : z ∉ Metric.sphere a r := by
              simpa [Metric.mem_sphere, dist_eq_norm] using (ne_of_lt hzInt.2)
            exact hz_not_sphere hzBoundary'.2
      have hmSz_not_ext : mS z ∉ OmegaExt := by
        intro hmSz_ext
        exact hz_not_mem (Or.inl <| by simpa [OmegaExt, mS, hz_ne] using hmSz_ext)
      have hzInv_ext : inversion a r z ∈ circleExterior a r D :=
        inversion_mapsTo_circleExterior hD_reflect hzInt
      have hzInv_ne : inversion a r z ≠ pS := by
        intro hEq
        exact hpS_not_mem (hEq ▸ (mem_circleExterior.mp hzInv_ext).1)
      have hsource_reflect :
          reflection LS (mS z) = mS (inversion a r z) := hmS_reflect hzD hz_ne
      have htarget_ext :
          f (inversion a r z) ∈ circleExterior α ρ Δ := hf_maps hzInv_ext
      have htarget_reflect :
          reflection LT (mT (f (inversion a r z))) =
            mT (inversion α ρ (f (inversion a r z))) := by
        have htarget_ne : f (inversion a r z) ≠ pT := by
          intro hEq
          exact hpT_not_mem (hEq ▸ htarget_ext.1)
        simpa [mT, LT] using hmT_reflect htarget_ext.1 htarget_ne
      calc
        H (mS z) = G (mS z) := by simp [H, hmSz_not_ext]
        _ = reflection LT (F (mS (inversion a r z))) := by simp [G, hsource_reflect]
        _ = reflection LT (mT (f (inversion a r z))) := by simp [F, mS, hzInv_ne]
        _ = mT (inversion α ρ (f (inversion a r z))) := htarget_reflect
        _ = mT (g z) := by
          have hgEq : g z = inversion α ρ (f (inversion a r z)) := by
            simpa [g] using circleReflection_apply_of_not_mem_exterior_boundary
              (a := a) (α := α) (r := r) (ρ := ρ) (D := D) (f := f) (z := z) hz_not_mem
          rw [hgEq]
  have hH_nonzero : ∀ z ∈ D, H (mS z) ≠ 0 := by
    intro z hzD
    have hEq : H (mS z) = mT (g z) := htransport_model hzD
    rw [hEq]
    exact poleChart_ne_zero (p := pT) (hg_ne_pT z hzD)
  have htransport_diff :
      DifferentiableOn ℂ (fun z ↦ invPoleChart pT (H (mS z))) D := by
    -- Compose the transported holomorphic model with the two pole charts.
    have hHmS_diff : DifferentiableOn ℂ (H ∘ mS) D :=
      hH_diff.comp hPoleS_diffOn hmS_maps
    have hInvPoleT_diff : DifferentiableOn ℂ (invPoleChart pT) {w : ℂ | w ≠ 0} := by
      intro w hw
      simpa [invPoleChart, sub_eq_add_neg] using
        ((differentiableAt_const (𝕜 := ℂ) pT).sub (differentiableAt_inv hw)).differentiableWithinAt
    have hMaps : Set.MapsTo (H ∘ mS) D {w : ℂ | w ≠ 0} := by
      intro z hzD
      exact hH_nonzero z hzD
    simpa [Function.comp] using hInvPoleT_diff.comp hHmS_diff hMaps
  have htransport_analytic :
      AnalyticOnNhd ℂ (fun z ↦ invPoleChart pT (H (mS z))) D :=
    htransport_diff.analyticOnNhd hD_open
  have htransport_eq :
      Set.EqOn (fun z ↦ invPoleChart pT (H (mS z))) g D := by
    intro z hzD
    have hEq : H (mS z) = mT (g z) := htransport_model hzD
    simpa [mT, hEq] using invPoleChart_poleChart (p := pT) (z := g z) (hg_ne_pT z hzD)
  -- Pull the transported holomorphic model back to the original domain and identify it with the
  -- textbook reflected extension.
  exact AnalyticOnNhd.congr hD_open htransport_analytic htransport_eq

/-- Exercise 6 (1): the inversion-defined reflected map carries the interior side into the target
interior side. -/
theorem circleReflection_mapsTo_interior
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hρ : 0 < ρ)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ)) :
    Set.MapsTo (circleReflection a α r ρ D f) (circleInterior a r D) (circleInterior α ρ Δ) :=
  by
    intro z hz
    have hz_not_mem :
        z ∉ circleExterior a r D ∪ circleBoundaryArc a r D := by
      rw [mem_circleInterior] at hz
      intro hz'
      rcases hz' with hz_ext | hz_boundary
      · rw [mem_circleExterior] at hz_ext
        exact (not_lt_of_ge hz.2.le) hz_ext.2
      · rw [mem_circleBoundaryArc] at hz_boundary
        have hz_not_sphere : z ∉ Metric.sphere a r := by
          simpa [Metric.mem_sphere, dist_eq_norm] using (ne_of_lt hz.2)
        exact hz_not_sphere hz_boundary.2
    have hz_exterior : inversion a r z ∈ circleExterior a r D :=
      inversion_mapsTo_circleExterior hD_reflect hz
    have hfz_exterior : f (inversion a r z) ∈ circleExterior α ρ Δ :=
      hf_maps hz_exterior
    have hfz_interior : inversion α ρ (f (inversion a r z)) ∈ circleInterior α ρ Δ :=
      inversion_mapsTo_circleInterior hρ hΔ_reflect hfz_exterior
    simpa [circleReflection_apply_of_not_mem_exterior_boundary hz_not_mem] using hfz_interior

/-- Helper for Exercise 6: every point of the ambient domain lies in exactly one of the exterior,
boundary, or interior circle cuts. -/
theorem mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior
    {a z : ℂ} {r : ℝ} {D : Set ℂ} (hzD : z ∈ D) :
    z ∈ circleExterior a r D ∨ z ∈ circleBoundaryArc a r D ∨ z ∈ circleInterior a r D := by
  -- Compare the radius `‖z - a‖` with `r` to place `z` in the textbook trichotomy.
  rcases lt_trichotomy ‖z - a‖ r with hz_lt | hz_eq | hz_gt
  · exact Or.inr <| Or.inr <| (mem_circleInterior.2 ⟨hzD, hz_lt⟩)
  · refine Or.inr <| Or.inl <| mem_circleBoundaryArc.2 ?_
    refine ⟨hzD, ?_⟩
    simpa [Metric.mem_sphere, dist_eq_norm] using hz_eq
  · exact Or.inl <| (mem_circleExterior.2 ⟨hzD, hz_gt⟩)

/-- Helper for Exercise 6: under the reflected-extension hypotheses, a point of `D` whose image
lies in the strict target exterior must already lie in the strict source exterior. -/
theorem circleReflection_preimage_targetExterior_subset_sourceExterior
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hρ : 0 < ρ)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    {z : ℂ} (hzD : z ∈ D)
    (hz_target : circleReflection a α r ρ D f z ∈ circleExterior α ρ Δ) :
    z ∈ circleExterior a r D := by
  rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hzD with
    hz_ext | hz_boundary | hz_int
  · exact hz_ext
  · exfalso
    have hz_boundary_image : circleReflection a α r ρ D f z ∈ circleBoundaryArc α ρ Δ := by
      -- On the boundary arc, the reflected extension still agrees with the boundary trace `f`.
      rw [circleReflection_apply_of_mem_exterior_boundary (Or.inr hz_boundary)]
      exact hf_boundary_maps hz_boundary
    rw [mem_circleExterior] at hz_target
    rcases mem_circleBoundaryArc.mp hz_boundary_image with ⟨_, hz_sphere⟩
    have hz_norm : ‖circleReflection a α r ρ D f z - α‖ = ρ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz_sphere
    exact (not_lt_of_ge hz_norm.le) hz_target.2
  · exfalso
    have hz_int_image :
        circleReflection a α r ρ D f z ∈ circleInterior α ρ Δ :=
      circleReflection_mapsTo_interior hρ hD_reflect hΔ_reflect hf_maps hz_int
    rw [mem_circleExterior] at hz_target
    rw [mem_circleInterior] at hz_int_image
    exact (not_lt_of_ge hz_int_image.2.le) hz_target.2

/-- Helper for Exercise 6: interior points lie outside the exterior-or-boundary cut that controls
the `piecewise` definition of `circleReflection`. -/
theorem not_mem_circleExterior_union_circleBoundaryArc_of_mem_circleInterior
    {a z : ℂ} {r : ℝ} {D : Set ℂ} (hz : z ∈ circleInterior a r D) :
    z ∉ circleExterior a r D ∪ circleBoundaryArc a r D := by
  -- The interior inequality excludes both the strict exterior branch and the boundary circle.
  rw [mem_circleInterior] at hz
  intro hz'
  rcases hz' with hz_ext | hz_boundary
  · rw [mem_circleExterior] at hz_ext
    exact (not_lt_of_ge hz.2.le) hz_ext.2
  · rw [mem_circleBoundaryArc] at hz_boundary
    have hz_not_sphere : z ∉ Metric.sphere a r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using (ne_of_lt hz.2)
    exact hz_not_sphere hz_boundary.2

/-- Exercise 6 (1): any other holomorphic extension from the same exterior and boundary data agrees
with the inversion-defined reflected map on all of `D`. -/
theorem eqOn_circleReflection_of_analyticOnNhd
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f G : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hΔ_open : IsOpen Δ) (hΔ_connected : IsConnected Δ)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D))
    (hΓ₀ : IsOpenArcOnCircle α ρ (circleBoundaryArc α ρ Δ))
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (hf_holo : AnalyticOnNhd ℂ f (circleExterior a r D))
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (hf_boundary :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    (hG_holo : AnalyticOnNhd ℂ G D)
    (hG_eq : Set.EqOn G f (circleExterior a r D ∪ circleBoundaryArc a r D)) :
    Set.EqOn G (circleReflection a α r ρ D f) D := by
  -- Route correction: once the reflected extension is known to be analytic on `D`, uniqueness no
  -- longer needs the straightening charts. The identity principle on the connected domain `D`
  -- applies directly because `G` and `circleReflection` already agree on the nonempty open
  -- exterior slice.
  have hReflection_holo : AnalyticOnNhd ℂ (circleReflection a α r ρ D f) D :=
    circle_reflection_extension hr hρ hD_open hD_connected hΔ_open hΔ_connected
      hC₀ hΓ₀ hD_reflect hΔ_reflect hf_cont hf_holo hf_maps hf_boundary
  have hEqExterior : Set.EqOn G (circleReflection a α r ρ D f) (circleExterior a r D) := by
    intro z hz
    calc
      G z = f z := hG_eq (Or.inl hz)
      _ = circleReflection a α r ρ D f z := by
        symm
        exact circleReflection_apply_of_mem_exterior_boundary (Or.inl hz)
  rcases circleExterior_nonempty_of_open_arc hr hD_open hC₀ with ⟨z₀, hz₀Ext⟩
  have hz₀D : z₀ ∈ D := (mem_circleExterior.mp hz₀Ext).1
  have heventually : G =ᶠ[nhds z₀] circleReflection a α r ρ D f := by
    -- The exterior slice is open, so the pointwise equality on that slice upgrades to a local
    -- eventual equality at any exterior point.
    filter_upwards [(isOpen_circleExterior hD_open).mem_nhds hz₀Ext] with z hz
    exact hEqExterior hz
  exact hG_holo.eqOn_of_preconnected_of_eventuallyEq
    hReflection_holo hD_connected.isPreconnected hz₀D heventually

/-- Helper for Exercise 6: once the boundary branch is known to be injective, the reflected map is
injective on the whole domain. -/
theorem circleReflection_injOn_domain_of_boundary_inj
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    (hboundary_inj :
      Set.InjOn (circleReflection a α r ρ D f) (circleBoundaryArc a r D)) :
    Set.InjOn (circleReflection a α r ρ D f) D := by
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  have hExterior_inj : Set.InjOn g (circleExterior a r D) := by
    -- On the exterior branch, `g` agrees with the given holomorphic isomorphism `e₀`.
    have he₀_inj : Set.InjOn (e₀ : ℂ → ℂ) (circleExterior a r D) := by
      simpa [e₀.source_eq] using (e₀ : OpenPartialHomeomorph ℂ ℂ).injOn
    intro z hz w hw hEq
    apply he₀_inj hz hw
    calc
      e₀ z = f z := he₀ hz
      _ = g z := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := z) (Or.inl hz))
      _ = g w := hEq
      _ = f w := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w) (Or.inl hw))
      _ = e₀ w := (he₀ hw).symm
  have hInterior_maps :
      Set.MapsTo g (circleInterior a r D) (circleInterior α ρ Δ) :=
    circleReflection_mapsTo_interior hρ hD_reflect hΔ_reflect hf_maps
  intro z hzD w hwD hEq
  have hEqg : g z = g w := by
    simpa [g] using hEq
  rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hzD with
    hz_ext | hz_boundary | hz_int
  · rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hwD with
      hw_ext | hw_boundary | hw_int
    · exact hExterior_inj hz_ext hw_ext hEq
    · exfalso
      have hgz_eq : g z = f z := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := z) (Or.inl hz_ext))
      have hgz_ext : g z ∈ circleExterior α ρ Δ := by
        rw [hgz_eq]
        exact hf_maps hz_ext
      have hgw_boundary : g w ∈ circleBoundaryArc α ρ Δ := by
        have hgw_eq : g w = f w := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := w) (Or.inr hw_boundary))
        rw [hgw_eq]
        exact hf_boundary_maps hw_boundary
      rw [mem_circleExterior] at hgz_ext
      rcases mem_circleBoundaryArc.mp hgw_boundary with ⟨_, hgw_sphere⟩
      have hgw_norm : ‖g w - α‖ = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hgw_sphere
      have hgw_gt : ρ < ‖g w - α‖ := by
        rw [← hEqg]
        exact hgz_ext.2
      exact (not_lt_of_ge hgw_norm.le) hgw_gt
    · exfalso
      have hgz_eq : g z = f z := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := z) (Or.inl hz_ext))
      have hgz_ext : g z ∈ circleExterior α ρ Δ := by
        rw [hgz_eq]
        exact hf_maps hz_ext
      have hgw_int : g w ∈ circleInterior α ρ Δ := hInterior_maps hw_int
      rw [mem_circleExterior] at hgz_ext
      rw [mem_circleInterior] at hgw_int
      have hgw_gt : ρ < ‖g w - α‖ := by
        rw [← hEqg]
        exact hgz_ext.2
      exact (not_lt_of_ge hgw_int.2.le) hgw_gt
  · rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hwD with
      hw_ext | hw_boundary | hw_int
    · exfalso
      have hgz_boundary : g z ∈ circleBoundaryArc α ρ Δ := by
        have hgz_eq : g z = f z := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := z) (Or.inr hz_boundary))
        rw [hgz_eq]
        exact hf_boundary_maps hz_boundary
      have hgw_eq : g w = f w := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w) (Or.inl hw_ext))
      have hgw_ext : g w ∈ circleExterior α ρ Δ := by
        rw [hgw_eq]
        exact hf_maps hw_ext
      rw [mem_circleExterior] at hgw_ext
      rcases mem_circleBoundaryArc.mp hgz_boundary with ⟨_, hgz_sphere⟩
      have hgz_norm : ‖g z - α‖ = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hgz_sphere
      have hgz_gt : ρ < ‖g z - α‖ := by
        rw [hEqg]
        exact hgw_ext.2
      exact (not_lt_of_ge hgz_norm.le) hgz_gt
    · exact hboundary_inj hz_boundary hw_boundary hEq
    · exfalso
      have hgz_boundary : g z ∈ circleBoundaryArc α ρ Δ := by
        have hgz_eq : g z = f z := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := z) (Or.inr hz_boundary))
        rw [hgz_eq]
        exact hf_boundary_maps hz_boundary
      have hgw_int : g w ∈ circleInterior α ρ Δ := hInterior_maps hw_int
      rw [mem_circleInterior] at hgw_int
      rcases mem_circleBoundaryArc.mp hgz_boundary with ⟨_, hgz_sphere⟩
      have hgz_norm : ‖g z - α‖ = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hgz_sphere
      have hgz_lt : ‖g z - α‖ < ρ := by
        rw [hEqg]
        exact hgw_int.2
      exact (ne_of_lt hgz_lt) hgz_norm
  · rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hwD with
      hw_ext | hw_boundary | hw_int
    · exfalso
      have hgz_int : g z ∈ circleInterior α ρ Δ := hInterior_maps hz_int
      have hgw_eq : g w = f w := by
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w) (Or.inl hw_ext))
      have hgw_ext : g w ∈ circleExterior α ρ Δ := by
        rw [hgw_eq]
        exact hf_maps hw_ext
      rw [mem_circleExterior] at hgw_ext
      rw [mem_circleInterior] at hgz_int
      have hgz_gt : ρ < ‖g z - α‖ := by
        rw [hEqg]
        exact hgw_ext.2
      exact (not_lt_of_ge hgz_int.2.le) hgz_gt
    · exfalso
      have hgz_int : g z ∈ circleInterior α ρ Δ := hInterior_maps hz_int
      have hgw_boundary : g w ∈ circleBoundaryArc α ρ Δ := by
        have hgw_eq : g w = f w := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := w) (Or.inr hw_boundary))
        rw [hgw_eq]
        exact hf_boundary_maps hw_boundary
      rw [mem_circleInterior] at hgz_int
      rcases mem_circleBoundaryArc.mp hgw_boundary with ⟨_, hgw_sphere⟩
      have hgw_norm : ‖g w - α‖ = ρ := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hgw_sphere
      have hgw_lt : ‖g w - α‖ < ρ := by
        rw [← hEqg]
        exact hgz_int.2
      exact (ne_of_lt hgw_lt) hgw_norm
    · have hz_not_mem :
          z ∉ circleExterior a r D ∪ circleBoundaryArc a r D :=
        not_mem_circleExterior_union_circleBoundaryArc_of_mem_circleInterior hz_int
      have hw_not_mem :
          w ∉ circleExterior a r D ∪ circleBoundaryArc a r D :=
        not_mem_circleExterior_union_circleBoundaryArc_of_mem_circleInterior hw_int
      have hz_pre_ext : inversion a r z ∈ circleExterior a r D :=
        inversion_mapsTo_circleExterior hD_reflect hz_int
      have hw_pre_ext : inversion a r w ∈ circleExterior a r D :=
        inversion_mapsTo_circleExterior hD_reflect hw_int
      have hpre_eq :
          g (inversion a r z) = g (inversion a r w) := by
        have hz_formula : g z = inversion α ρ (f (inversion a r z)) := by
          simpa [g] using
            (circleReflection_apply_of_not_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := z) hz_not_mem)
        have hw_formula : g w = inversion α ρ (f (inversion a r w)) := by
          simpa [g] using
            (circleReflection_apply_of_not_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := w) hw_not_mem)
        have hinv_eq :
            inversion α ρ (f (inversion a r z)) =
              inversion α ρ (f (inversion a r w)) := by
          calc
            inversion α ρ (f (inversion a r z)) = g z := hz_formula.symm
            _ = g w := hEq
            _ = inversion α ρ (f (inversion a r w)) := hw_formula
        have hvalue_eq : f (inversion a r z) = f (inversion a r w) :=
          (inversion_injective α hρ.ne') hinv_eq
        calc
          g (inversion a r z) = f (inversion a r z) := by
            simpa [g] using
              (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
                (ρ := ρ) (D := D) (f := f) (z := inversion a r z) (Or.inl hz_pre_ext))
          _ = f (inversion a r w) := hvalue_eq
          _ = g (inversion a r w) := by
            symm
            simpa [g] using
              (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
                (ρ := ρ) (D := D) (f := f) (z := inversion a r w) (Or.inl hw_pre_ext))
      have hinv_eq : inversion a r z = inversion a r w :=
        hExterior_inj hz_pre_ext hw_pre_ext hpre_eq
      exact (inversion_injective a hr.ne') hinv_eq

/-- Helper for Exercise 6: the reflected map is surjective onto the target once the exterior branch
and the boundary arc are already surjective. -/
theorem circleReflection_image_eq_target
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_maps :
      Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    (hf_boundary_surj :
      Set.SurjOn f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ)) :
    (circleReflection a α r ρ D f) '' D = Δ := by
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  have hInterior_maps :
      Set.MapsTo g (circleInterior a r D) (circleInterior α ρ Δ) :=
    circleReflection_mapsTo_interior hρ hD_reflect hΔ_reflect hf_maps
  apply Set.Subset.antisymm
  · rintro y ⟨z, hzD, rfl⟩
    rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hzD with
      hz_ext | hz_boundary | hz_int
    · have hgz_eq :
          circleReflection a α r ρ D f z = f z := by
        exact circleReflection_apply_of_mem_exterior_boundary (Or.inl hz_ext)
      rw [hgz_eq]
      exact (hf_maps hz_ext).1
    · have hboundary : g z ∈ circleBoundaryArc α ρ Δ := by
        have hgz_eq : g z = f z := by
          simpa [g] using
            (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := z) (Or.inr hz_boundary))
        rw [hgz_eq]
        exact hf_boundary_maps hz_boundary
      exact (mem_circleBoundaryArc.mp hboundary).1
    · exact (mem_circleInterior.mp (hInterior_maps hz_int)).1
  · intro y hyΔ
    rcases mem_circleExterior_or_mem_circleBoundaryArc_or_mem_circleInterior hyΔ with
      hy_ext | hy_boundary | hy_int
    · have hy_target : y ∈ (e₀ : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e₀.target_eq] using hy_ext
      refine ⟨((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y), ?_, ?_⟩
      · have hx_ext :
            ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y) ∈ circleExterior a r D := by
          simpa [e₀.source_eq] using
            (e₀ : OpenPartialHomeomorph ℂ ℂ).map_target hy_target
        exact (mem_circleExterior.mp hx_ext).1
      · have hx_ext :
            ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y) ∈ circleExterior a r D := by
          simpa [e₀.source_eq] using
            (e₀ : OpenPartialHomeomorph ℂ ℂ).map_target hy_target
        calc
          g ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y)
              = f ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y) := by
                  simpa [g] using
                    (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
                      (ρ := ρ) (D := D) (f := f)
                      (z := ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y)) (Or.inl hx_ext))
          _ = e₀ ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm y) := (he₀ hx_ext).symm
          _ = y := (e₀ : OpenPartialHomeomorph ℂ ℂ).right_inv hy_target
    · rcases hf_boundary_surj hy_boundary with ⟨x, hx_boundary, hxy⟩
      exact ⟨x, (mem_circleBoundaryArc.mp hx_boundary).1, by
        calc
          g x = f x := by
            simpa [g] using
              (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
                (ρ := ρ) (D := D) (f := f) (z := x) (Or.inr hx_boundary))
          _ = y := hxy⟩
    · have hy_ext : inversion α ρ y ∈ circleExterior α ρ Δ :=
        inversion_mapsTo_circleExterior hΔ_reflect hy_int
      have hy_ext_target : inversion α ρ y ∈ (e₀ : OpenPartialHomeomorph ℂ ℂ).target := by
        simpa [e₀.target_eq] using hy_ext
      let xPlus : ℂ := ((e₀ : OpenPartialHomeomorph ℂ ℂ).symm) (inversion α ρ y)
      have hxPlus_ext : xPlus ∈ circleExterior a r D := by
        simpa [xPlus, e₀.source_eq] using
          (e₀ : OpenPartialHomeomorph ℂ ℂ).map_target hy_ext_target
      let x : ℂ := inversion a r xPlus
      have hx_int : x ∈ circleInterior a r D := by
        simpa [x] using inversion_mapsTo_circleInterior hr hD_reflect hxPlus_ext
      have hx_not_mem :
          x ∉ circleExterior a r D ∪ circleBoundaryArc a r D :=
        not_mem_circleExterior_union_circleBoundaryArc_of_mem_circleInterior hx_int
      refine ⟨x, (mem_circleInterior.mp hx_int).1, ?_⟩
      have hx_inv : inversion a r x = xPlus := by
        simpa [x] using (inversion_involutive a hr.ne' xPlus)
      have hx_image : e₀ xPlus = inversion α ρ y := by
        simpa [xPlus] using (e₀ : OpenPartialHomeomorph ℂ ℂ).right_inv hy_ext_target
      calc
        g x = inversion α ρ (f (inversion a r x)) := by
          simpa [g] using
            (circleReflection_apply_of_not_mem_exterior_boundary (a := a) (α := α) (r := r)
              (ρ := ρ) (D := D) (f := f) (z := x) hx_not_mem)
        _ = inversion α ρ (f xPlus) := by rw [hx_inv]
        _ = inversion α ρ (e₀ xPlus) := by rw [(he₀ hxPlus_ext).symm]
        _ = inversion α ρ (inversion α ρ y) := by rw [hx_image]
        _ = y := by simpa using (inversion_involutive α hρ.ne' y)

/-- Helper for Exercise 6: an analytic injective map on an open set with image exactly `Δ`
packages into the chapter's `HolomorphicIsomorph` owner. -/
theorem isHolomorphicIsomorphOn_of_analyticOnNhd_of_injOn_image_eq
    {D Δ : Set ℂ} {g : ℂ → ℂ}
    (hD_open : IsOpen D) (hΔ_open : IsOpen Δ)
    (hg_holo : AnalyticOnNhd ℂ g D)
    (hg_inj : Set.InjOn g D)
    (himage : g '' D = Δ) :
    g.IsHolomorphicIsomorphOn D Δ := by
  have hsurj : Set.SurjOn g D Δ := by
    intro y hy
    rw [← himage] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hmaps : Set.MapsTo g D Δ := by
    intro z hz
    rw [← himage]
    exact ⟨z, hz, rfl⟩
  have hmaps_inv : Set.MapsTo (Function.invFunOn g D) Δ D :=
    hsurj.mapsTo_invFunOn
  have hleft_inv : Set.LeftInvOn (Function.invFunOn g D) g D :=
    hg_inj.leftInvOn_invFunOn
  have hright_inv : Set.RightInvOn (Function.invFunOn g D) g Δ :=
    hsurj.rightInvOn_invFunOn
  have hInv_holo : AnalyticOnNhd ℂ (Function.invFunOn g D) Δ := by
    simpa [himage] using
      corollary_VI_1_extra_3_invFunOn_analyticOnNhd hg_holo hg_inj hD_open
  have hInv_cont : ContinuousOn (Function.invFunOn g D) Δ := hInv_holo.continuousOn
  refine ⟨?_, ?_⟩
  · exact ⟨{
      toFun := g
      invFun := Function.invFunOn g D
      source := D
      target := Δ
      map_source' := hmaps
      map_target' := hmaps_inv
      left_inv' := hleft_inv
      right_inv' := hright_inv
      open_source := hD_open
      open_target := hΔ_open
      continuousOn_toFun := hg_holo.continuousOn
      continuousOn_invFun := hInv_cont
    }, {
      source_eq := rfl
      target_eq := rfl
      analyticOn_toFun := hg_holo
      analyticOn_symm := hInv_holo
    }⟩
  · intro z hz
    rfl

/-- Helper for Exercise 6: near a source boundary point, the reflected extension cannot be
eventually constant because its exterior trace agrees with an injective biholomorphism. -/
theorem circleReflection_not_eventuallyConst_at_boundary_of_exterior_isomorphism
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ} (hr : 0 < r)
    (hD_open : IsOpen D)
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    {z : ℂ} (hz : z ∈ circleBoundaryArc a r D) :
    ¬ Filter.EventuallyConst (circleReflection a α r ρ D f) (nhds z) := by
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  have hExterior_open : IsOpen (circleExterior a r D) := isOpen_circleExterior hD_open
  have he₀_inj : Set.InjOn (e₀ : ℂ → ℂ) (circleExterior a r D) := by
    simpa [e₀.source_eq] using (e₀ : OpenPartialHomeomorph ℂ ℂ).injOn
  intro hconst
  rcases hconst.eventuallyEq_const with ⟨c, hc⟩
  have hzD : z ∈ D := (mem_circleBoundaryArc.mp hz).1
  rcases Metric.mem_nhds_iff.mp (hD_open.mem_nhds hzD) with ⟨εD, hεD_pos, _hεD_subD⟩
  have hconst_set : {w : ℂ | g w = c} ∈ nhds z := by
    simpa using hc
  rcases Metric.mem_nhds_iff.mp hconst_set with ⟨εc, hεc_pos, hεc_sub⟩
  let ε : ℝ := min εD εc
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min hεD_pos hεc_pos
  rcases exists_mem_circleExterior_mem_ball_of_mem_circleBoundaryArc
      (a := a) (z := z) (r := r) (ε := ε / 2) hr (half_pos hε_pos) hD_open hz with
    ⟨w₁, hw₁_ext, hw₁_ball⟩
  have hw₁_eq : g w₁ = c := by
    apply hεc_sub
    have hw₁_lt_half : dist w₁ z < ε / 2 := by
      simpa [Metric.mem_ball] using hw₁_ball
    have hhalf_le : ε / 2 ≤ εc := by
      dsimp [ε]
      linarith [min_le_right εD εc]
    simpa [Metric.mem_ball, dist_comm] using lt_of_lt_of_le hw₁_lt_half hhalf_le
  rcases Metric.mem_nhds_iff.mp (hExterior_open.mem_nhds hw₁_ext) with ⟨δext, hδext_pos, hδext_sub⟩
  have hw₁_ball_nhds : Metric.ball z (ε / 2) ∈ nhds w₁ :=
    Metric.isOpen_ball.mem_nhds hw₁_ball
  rcases Metric.mem_nhds_iff.mp hw₁_ball_nhds with ⟨δball, hδball_pos, hδball_sub⟩
  let δ : ℝ := min δext δball
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδext_pos hδball_pos
  let w₂ : ℂ := w₁ + (((δ / 2 : ℝ) : ℂ))
  have hw₂_ball_w₁ : w₂ ∈ Metric.ball w₁ δ := by
    have hw₂_dist : dist w₂ w₁ = δ / 2 := by
      calc
        dist w₂ w₁ = ‖w₂ - w₁‖ := by rw [dist_eq_norm]
        _ = ‖(((δ / 2 : ℝ) : ℂ))‖ := by simp [w₂]
        _ = δ / 2 := by
          simp [Complex.norm_real, le_of_lt hδ_pos]
    have hw₂_lt : dist w₂ w₁ < δ := by
      rw [hw₂_dist]
      linarith
    simpa [Metric.mem_ball] using hw₂_lt
  have hw₂_ext : w₂ ∈ circleExterior a r D := by
    apply hδext_sub
    have hw₂_lt : dist w₂ w₁ < δ := by
      simpa [Metric.mem_ball] using hw₂_ball_w₁
    have hδ_le : δ ≤ δext := by
      dsimp [δ]
      exact min_le_left _ _
    simpa [Metric.mem_ball] using lt_of_lt_of_le hw₂_lt hδ_le
  have hw₂_ball : w₂ ∈ Metric.ball z (ε / 2) := by
    apply hδball_sub
    have hw₂_lt : dist w₂ w₁ < δ := by
      simpa [Metric.mem_ball] using hw₂_ball_w₁
    have hδ_le : δ ≤ δball := by
      dsimp [δ]
      exact min_le_right _ _
    simpa [Metric.mem_ball] using lt_of_lt_of_le hw₂_lt hδ_le
  have hw₂_eq : g w₂ = c := by
    apply hεc_sub
    have hw₂_lt_half : dist w₂ z < ε / 2 := by
      simpa [Metric.mem_ball] using hw₂_ball
    have hhalf_le : ε / 2 ≤ εc := by
      dsimp [ε]
      linarith [min_le_right εD εc]
    simpa [Metric.mem_ball, dist_comm] using lt_of_lt_of_le hw₂_lt_half hhalf_le
  have hw₁_value : e₀ w₁ = c := by
    calc
      e₀ w₁ = f w₁ := he₀ hw₁_ext
      _ = g w₁ := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w₁) (Or.inl hw₁_ext))
      _ = c := hw₁_eq
  have hw₂_value : e₀ w₂ = c := by
    calc
      e₀ w₂ = f w₂ := he₀ hw₂_ext
      _ = g w₂ := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r)
            (ρ := ρ) (D := D) (f := f) (z := w₂) (Or.inl hw₂_ext))
      _ = c := hw₂_eq
  have hw_eq : w₁ = w₂ := he₀_inj hw₁_ext hw₂_ext (hw₁_value.trans hw₂_value.symm)
  have hw_ne : w₁ ≠ w₂ := by
    intro hw
    have hzero : (((δ / 2 : ℝ) : ℂ)) = 0 := by
      have hsum : w₁ + (((δ / 2 : ℝ) : ℂ)) = w₁ + 0 := by
        simpa [w₂] using hw.symm
      exact add_left_cancel hsum
    have hhalf_ne : (((δ / 2 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt (half_pos hδ_pos))
    exact hhalf_ne hzero
  exact hw_ne hw_eq

/-- Helper for Exercise 6: under the exterior-isomorphism hypotheses, Proposition 4.2 supplies
injectivity of the reflected map on the boundary arc. -/
theorem circleReflection_injOn_boundaryArc_of_exterior_isomorphism
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hΔ_open : IsOpen Δ) (hΔ_connected : IsConnected Δ)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D))
    (hΓ₀ : IsOpenArcOnCircle α ρ (circleBoundaryArc α ρ Δ))
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ)) :
    Set.InjOn (circleReflection a α r ρ D f) (circleBoundaryArc a r D) := by
  let g : ℂ → ℂ := circleReflection a α r ρ D f
  have hf_holo : AnalyticOnNhd ℂ f (circleExterior a r D) :=
    analyticOnNhd_of_eqOn_holomorphicIsomorph e₀ he₀
  have hf_maps : Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ) :=
    mapsTo_target_of_eqOn_holomorphicIsomorph e₀ he₀
  have hg_holo : AnalyticOnNhd ℂ g D :=
    circle_reflection_extension hr hρ hD_open hD_connected hΔ_open hΔ_connected
      hC₀ hΓ₀ hD_reflect hΔ_reflect hf_cont hf_holo hf_maps hf_boundary_maps
  have he₀_inj : Set.InjOn (e₀ : ℂ → ℂ) (circleExterior a r D) := by
    -- The exterior branch is already a biholomorphism, hence injective on its source.
    simpa [e₀.source_eq] using (e₀ : OpenPartialHomeomorph ℂ ℂ).injOn
  intro z₁ hz₁ z₂ hz₂ hzEq
  by_contra hz_ne
  have hz₁D : z₁ ∈ D := (mem_circleBoundaryArc.mp hz₁).1
  have hz₂D : z₂ ∈ D := (mem_circleBoundaryArc.mp hz₂).1
  have hz₁_value : g z₁ = f z₁ := by
    simpa [g] using
      (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r) (ρ := ρ)
        (D := D) (f := f) (z := z₁) (Or.inr hz₁))
  have hz₂_value : g z₂ = f z₂ := by
    simpa [g] using
      (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r) (ρ := ρ)
        (D := D) (f := f) (z := z₂) (Or.inr hz₂))
  let c : ℂ := g z₁
  have hc_eq₂ : g z₂ = c := by
    simpa [c] using hzEq.symm
  have hc_boundary : c ∈ circleBoundaryArc α ρ Δ := by
    -- On the boundary arc, `g` agrees with `f`, so the common value lies on the target boundary
    -- arc.
    have hc_eq₁ : c = f z₁ := by
      simpa [c] using hz₁_value
    simpa [hc_eq₁] using hf_boundary_maps hz₁
  have hnot_const₁ :
      ¬ Filter.EventuallyConst g (nhds z₁) :=
    circleReflection_not_eventuallyConst_at_boundary_of_exterior_isomorphism hr hD_open e₀ he₀ hz₁
  have hnot_const₂ :
      ¬ Filter.EventuallyConst g (nhds z₂) :=
    circleReflection_not_eventuallyConst_at_boundary_of_exterior_isomorphism hr hD_open e₀ he₀ hz₂
  have horder₁_ne_top : analyticOrderAt (fun w ↦ g w - c) z₁ ≠ ⊤ := by
    -- Route correction: convert the "not eventually constant" statement into finiteness of the
    -- vanishing order of `g - c` at the first boundary point.
    intro htop
    apply hnot_const₁
    refine Filter.eventuallyConst_iff_exists_eventuallyEq.mpr ?_
    refine ⟨c, ?_⟩
    simpa [sub_eq_zero] using (analyticOrderAt_eq_top.mp htop)
  have horder₂_ne_top : analyticOrderAt (fun w ↦ g w - c) z₂ ≠ ⊤ := by
    -- The same finiteness argument applies at the second boundary point.
    intro htop
    apply hnot_const₂
    refine Filter.eventuallyConst_iff_exists_eventuallyEq.mpr ?_
    refine ⟨c, ?_⟩
    simpa [sub_eq_zero] using (analyticOrderAt_eq_top.mp htop)
  have horder₁_ne_zero : analyticOrderAt (fun w ↦ g w - c) z₁ ≠ 0 := by
    -- Since `g z₁ = c`, the shifted function vanishes at `z₁`, so its order is positive.
    rw [analyticOrderAt_ne_zero]
    refine ⟨(hg_holo z₁ hz₁D).sub analyticAt_const, ?_⟩
    simp [c]
  have horder₂_ne_zero : analyticOrderAt (fun w ↦ g w - c) z₂ ≠ 0 := by
    -- Since `g z₂ = c`, the shifted function also vanishes at the second boundary point.
    rw [analyticOrderAt_ne_zero]
    refine ⟨(hg_holo z₂ hz₂D).sub analyticAt_const, ?_⟩
    simp [c, hc_eq₂]
  let k₁ : ℕ := analyticOrderNatAt (fun w ↦ g w - c) z₁
  let k₂ : ℕ := analyticOrderNatAt (fun w ↦ g w - c) z₂
  have hk₁ : analyticOrderAt (fun w ↦ g w - c) z₁ = k₁ := by
    rw [← Nat.cast_analyticOrderNatAt horder₁_ne_top]
  have hk₂ : analyticOrderAt (fun w ↦ g w - c) z₂ = k₂ := by
    rw [← Nat.cast_analyticOrderNatAt horder₂_ne_top]
  have hk₁_pos : 0 < k₁ := by
    have hk₁_ne : k₁ ≠ 0 := by
      intro hk₁_zero
      exact horder₁_ne_zero <| by simpa [k₁, hk₁_zero] using hk₁
    omega
  have hk₂_pos : 0 < k₂ := by
    have hk₂_ne : k₂ ≠ 0 := by
      intro hk₂_zero
      exact horder₂_ne_zero <| by simpa [k₂, hk₂_zero] using hk₂
    omega
  obtain ⟨r₀₁, hr₀₁_pos, hr₀₁⟩ :=
    nearby_level_set_has_k_simple_roots (f := g) (z₀ := z₁) (a := c) (k := k₁) hk₁_pos hk₁
  obtain ⟨r₀₂, hr₀₂_pos, hr₀₂⟩ :=
    nearby_level_set_has_k_simple_roots (f := g) (z₀ := z₂) (a := c) (k := k₂) hk₂_pos hk₂
  obtain ⟨rD₁, hrD₁_pos, hrD₁_subset⟩ := Metric.mem_nhds_iff.mp (hD_open.mem_nhds hz₁D)
  obtain ⟨rD₂, hrD₂_pos, hrD₂_subset⟩ := Metric.mem_nhds_iff.mp (hD_open.mem_nhds hz₂D)
  have hdist_pos : 0 < dist z₁ z₂ := dist_pos.mpr hz_ne
  let r₀ : ℝ := min r₀₁ r₀₂
  let rD : ℝ := min rD₁ rD₂
  let s : ℝ := dist z₁ z₂ / 3
  let r' : ℝ := min rD s
  let rloc : ℝ := min r₀ r'
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hr₀_pos : 0 < r₀ := by
    dsimp [r₀]
    exact lt_min hr₀₁_pos hr₀₂_pos
  have hr'_pos : 0 < r' := by
    dsimp [r']
    exact lt_min (by dsimp [rD]; exact lt_min hrD₁_pos hrD₂_pos) hs_pos
  have hrloc_pos : 0 < rloc := by
    dsimp [rloc]
    exact lt_min hr₀_pos hr'_pos
  have hrloc_le_r₀₁ : rloc ≤ r₀₁ := by
    exact le_trans (by dsimp [rloc]; exact min_le_left _ _) (by dsimp [r₀]; exact min_le_left _ _)
  have hrloc_le_r₀₂ : rloc ≤ r₀₂ := by
    exact le_trans (by dsimp [rloc]; exact min_le_left _ _) (by dsimp [r₀]; exact min_le_right _ _)
  have hrloc_le_rD₁ : rloc ≤ rD₁ := by
    exact le_trans
      (by dsimp [rloc]; exact min_le_right _ _)
      (le_trans (by dsimp [r']; exact min_le_left _ _) (by dsimp [rD]; exact min_le_left _ _))
  have hrloc_le_rD₂ : rloc ≤ rD₂ := by
    exact le_trans
      (by dsimp [rloc]; exact min_le_right _ _)
      (le_trans (by dsimp [r']; exact min_le_left _ _) (by dsimp [rD]; exact min_le_right _ _))
  have hrloc_le_s : rloc ≤ s := by
    exact le_trans (by dsimp [rloc]; exact min_le_right _ _) (by dsimp [r']; exact min_le_right _ _)
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hr₀₁ rloc hrloc_pos hrloc_le_r₀₁
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hr₀₂ rloc hrloc_pos hrloc_le_r₀₂
  let ε : ℝ := min δ₁ δ₂
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min hδ₁_pos hδ₂_pos
  obtain ⟨b, hb_ext, hb_ball⟩ :=
    exists_mem_circleExterior_mem_ball_of_mem_circleBoundaryArc
      (a := α) (z := c) (r := ρ) (ε := ε) hρ hε_pos hΔ_open hc_boundary
  have hb_dist₁ : ‖b - c‖ < δ₁ := by
    have hb_dist : dist b c < ε := by
      simpa [Metric.mem_ball] using hb_ball
    exact lt_of_lt_of_le (by simpa [dist_eq_norm] using hb_dist) (by dsimp [ε]; exact min_le_left _ _)
  have hb_dist₂ : ‖b - c‖ < δ₂ := by
    have hb_dist : dist b c < ε := by
      simpa [Metric.mem_ball] using hb_ball
    exact lt_of_lt_of_le (by simpa [dist_eq_norm] using hb_dist) (by dsimp [ε]; exact min_le_right _ _)
  have hb_ne_c : b ≠ c := by
    intro hb_eq
    have hc_ext : c ∈ circleExterior α ρ Δ := by
      simpa [hb_eq] using hb_ext
    rcases mem_circleBoundaryArc.mp hc_boundary with ⟨_, hc_sphere⟩
    rw [mem_circleExterior] at hc_ext
    have hc_norm : ‖c - α‖ = ρ := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hc_sphere
    exact (not_lt_of_ge hc_norm.le) hc_ext.2
  obtain ⟨hroot₁_count, _⟩ := hδ₁ b hb_dist₁ hb_ne_c
  obtain ⟨hroot₂_count, _⟩ := hδ₂ b hb_dist₂ hb_ne_c
  have hroot₁_nonempty :
      ({z : ℂ | z ∈ Metric.ball z₁ rloc ∧ g z = b} : Set ℂ).Nonempty := by
    apply Set.nonempty_of_encard_ne_zero
    rw [hroot₁_count]
    exact_mod_cast hk₁_pos.ne'
  have hroot₂_nonempty :
      ({z : ℂ | z ∈ Metric.ball z₂ rloc ∧ g z = b} : Set ℂ).Nonempty := by
    apply Set.nonempty_of_encard_ne_zero
    rw [hroot₂_count]
    exact_mod_cast hk₂_pos.ne'
  rcases hroot₁_nonempty with ⟨x₁, hx₁_ball, hx₁_value⟩
  rcases hroot₂_nonempty with ⟨x₂, hx₂_ball, hx₂_value⟩
  have hx₁D : x₁ ∈ D := by
    apply hrD₁_subset
    have hx₁_lt : dist x₁ z₁ < rloc := by
      simpa [Metric.mem_ball] using hx₁_ball
    have : dist x₁ z₁ < rD₁ := lt_of_lt_of_le hx₁_lt hrloc_le_rD₁
    simpa [Metric.mem_ball] using this
  have hx₂D : x₂ ∈ D := by
    apply hrD₂_subset
    have hx₂_lt : dist x₂ z₂ < rloc := by
      simpa [Metric.mem_ball] using hx₂_ball
    have : dist x₂ z₂ < rD₂ := lt_of_lt_of_le hx₂_lt hrloc_le_rD₂
    simpa [Metric.mem_ball] using this
  have hx₁_ext : x₁ ∈ circleExterior a r D :=
    circleReflection_preimage_targetExterior_subset_sourceExterior hρ hD_reflect hΔ_reflect hf_maps
      hf_boundary_maps hx₁D <| by simpa [g, hx₁_value] using hb_ext
  have hx₂_ext : x₂ ∈ circleExterior a r D :=
    circleReflection_preimage_targetExterior_subset_sourceExterior hρ hD_reflect hΔ_reflect hf_maps
      hf_boundary_maps hx₂D <| by simpa [g, hx₂_value] using hb_ext
  have hx₁_eval : e₀ x₁ = b := by
    -- On the exterior, the reflected map collapses back to the original biholomorphic branch.
    calc
      e₀ x₁ = f x₁ := he₀ hx₁_ext
      _ = g x₁ := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r) (ρ := ρ)
            (D := D) (f := f) (z := x₁) (Or.inl hx₁_ext))
      _ = b := hx₁_value
  have hx₂_eval : e₀ x₂ = b := by
    calc
      e₀ x₂ = f x₂ := he₀ hx₂_ext
      _ = g x₂ := by
        symm
        simpa [g] using
          (circleReflection_apply_of_mem_exterior_boundary (a := a) (α := α) (r := r) (ρ := ρ)
            (D := D) (f := f) (z := x₂) (Or.inl hx₂_ext))
      _ = b := hx₂_value
  have hx_eq : x₁ = x₂ := he₀_inj hx₁_ext hx₂_ext (hx₁_eval.trans hx₂_eval.symm)
  have hballs_disjoint : Disjoint (Metric.ball z₁ rloc) (Metric.ball z₂ rloc) := by
    -- The two root-counting balls were chosen much smaller than the distance between the boundary
    -- points.
    apply Metric.ball_disjoint_ball
    have hsum : rloc + rloc ≤ dist z₁ z₂ := by
      dsimp [s] at hrloc_le_s
      linarith [hrloc_le_s, hdist_pos]
    exact hsum
  have hx₁_in₂ : x₁ ∈ Metric.ball z₂ rloc := by
    simpa [hx_eq] using hx₂_ball
  exact (Set.disjoint_left.mp hballs_disjoint hx₁_ball hx₁_in₂).elim

/-- Exercise 6 (2): if the exterior map is already a holomorphic isomorphism onto the exterior
target and the boundary arc is mapped onto the target arc, then the inversion-defined reflected map
is biholomorphic from `D` onto `Δ`. -/
theorem circle_reflection_extension_isomorphism
    {a α : ℂ} {r ρ : ℝ} {D Δ : Set ℂ} {f : ℂ → ℂ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hD_open : IsOpen D) (hD_connected : IsConnected D)
    (hΔ_open : IsOpen Δ) (hΔ_connected : IsConnected Δ)
    (hC₀ : IsOpenArcOnCircle a r (circleBoundaryArc a r D))
    (hΓ₀ : IsOpenArcOnCircle α ρ (circleBoundaryArc α ρ Δ))
    (hD_reflect :
      circleExterior a r D = inversion a r '' circleInterior a r D)
    (hΔ_reflect :
      circleExterior α ρ Δ = inversion α ρ '' circleInterior α ρ Δ)
    (hf_cont :
      ContinuousOn f (circleExterior a r D ∪ circleBoundaryArc a r D))
    (e₀ : HolomorphicIsomorph (circleExterior a r D) (circleExterior α ρ Δ))
    (he₀ : Set.EqOn e₀ f (circleExterior a r D))
    (hf_boundary_maps :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ))
    (hf_boundary_surj :
      Set.SurjOn f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ)) :
    (circleReflection a α r ρ D f).IsHolomorphicIsomorphOn D Δ := by
  -- Route correction: reduce the biholomorphic case to part (1) first, so the remaining blocker is
  -- exactly the source-faithful boundary-simplicity and inverse-extension stage.
  have hf_holo : AnalyticOnNhd ℂ f (circleExterior a r D) :=
    analyticOnNhd_of_eqOn_holomorphicIsomorph e₀ he₀
  have hf_maps : Set.MapsTo f (circleExterior a r D) (circleExterior α ρ Δ) :=
    mapsTo_target_of_eqOn_holomorphicIsomorph e₀ he₀
  have hf_boundary_closure :
      Set.MapsTo f (circleBoundaryArc a r D) (closure (circleExterior α ρ Δ)) := by
    intro z hz
    -- Boundary values are limits of exterior values because the source boundary arc is the
    -- frontier of the source exterior cut.
    exact image_mem_closure_circleExterior_of_boundary_point hD_open hf_cont hf_maps hz
  have hf_boundary_not_exterior :
      Set.MapsTo f (circleBoundaryArc a r D) (circleExterior α ρ Δ)ᶜ :=
    boundary_value_not_mem_target_exterior_of_exterior_isomorphism hD_open hf_cont e₀ he₀
  have hf_boundary_of_target_nonexterior :
      Set.MapsTo f (circleBoundaryArc a r D) Δ →
        Set.MapsTo f (circleBoundaryArc a r D) (circleExterior α ρ Δ)ᶜ →
        Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ) := by
    intro hf_target hf_not_exterior z hz
    -- Route correction: the remaining issue is not the closure/frontier transport anymore; it is
    -- exactly the missing target-side membership and non-exteriority of the boundary values.
    exact mem_circleBoundaryArc_of_not_mem_circleExterior_of_mem_closure_circleExterior
      hΔ_open (hf_target hz) (hf_not_exterior hz) (hf_boundary_closure hz)
  have hf_boundary :
      Set.MapsTo f (circleBoundaryArc a r D) (circleBoundaryArc α ρ Δ) :=
    hf_boundary_maps
  -- The first half of the exercise now gives the analytic extension `g`.
  have hg_holo : AnalyticOnNhd ℂ (circleReflection a α r ρ D f) D :=
    circle_reflection_extension hr hρ hD_open hD_connected hΔ_open hΔ_connected
      hC₀ hΓ₀ hD_reflect hΔ_reflect hf_cont hf_holo hf_maps hf_boundary
  have hboundary_inj :
      Set.InjOn (circleReflection a α r ρ D f) (circleBoundaryArc a r D) :=
    circleReflection_injOn_boundaryArc_of_exterior_isomorphism hr hρ hD_open hD_connected
      hΔ_open hΔ_connected hC₀ hΓ₀ hD_reflect hΔ_reflect hf_cont e₀ he₀ hf_boundary_maps
  have hg_inj : Set.InjOn (circleReflection a α r ρ D f) D :=
    circleReflection_injOn_domain_of_boundary_inj hr hρ hD_reflect hΔ_reflect hf_maps
      e₀ he₀ hf_boundary_maps hboundary_inj
  have himage : (circleReflection a α r ρ D f) '' D = Δ :=
    circleReflection_image_eq_target hr hρ hD_reflect hΔ_reflect hf_maps e₀ he₀
      hf_boundary_maps hf_boundary_surj
  -- Package the analytic bijection and its analytic inverse into the chapter owner.
  exact isHolomorphicIsomorphOn_of_analyticOnNhd_of_injOn_image_eq
    hD_open hΔ_open hg_holo hg_inj himage

/-- Two holomorphic isomorphisms with the same source and target that realize the same function on
the source are unique up to `OpenPartialHomeomorph.EqOnSource`. -/
theorem eqOnSource_of_eqOn_holomorphicIsomorph
    {D Δ : Set ℂ} {g : ℂ → ℂ} {e e' : HolomorphicIsomorph D Δ}
    (he : Set.EqOn e g D) (he' : Set.EqOn e' g D) :
    OpenPartialHomeomorph.EqOnSource
      (e : OpenPartialHomeomorph ℂ ℂ) (e' : OpenPartialHomeomorph ℂ ℂ) := by
  refine ⟨?_, ?_⟩
  · simp [HolomorphicIsomorph.source_eq]
  · intro z hz
    have hzD : z ∈ D := by
      simpa [HolomorphicIsomorph.source_eq] using hz
    exact (he hzD).trans (he' hzD).symm

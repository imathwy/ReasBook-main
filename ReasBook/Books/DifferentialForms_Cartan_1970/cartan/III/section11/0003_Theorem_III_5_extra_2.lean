import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0001_Definition_II_1_extra_1»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2».Index

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology unitInterval

noncomputable section

universe u

-- Semantic recall note: no `lean_leansearch` MCP tool was exposed in this session, so the
-- statement shape below follows local oriented-boundary precedent and the available Mathlib
-- contour-integral API.

/-- Theorem III.5-extra-2 (1): if the singular points of `f` in `D` are isolated in the
source-text sense, namely the singular set has no accumulation point in `D`, then only finitely
many of them can lie in a fixed compact subset `K ⊆ D`. The separate punctured-holomorphic
hypothesis records that these locally discrete singular points are genuine isolated singularities
of `f`. -/
theorem finite_nondifferentiable_points_in_compact_of_isolated
    {K D : Set ℂ} {f : ℂ → ℂ} (hK : IsCompact K) (hKD : K ⊆ D)
    (hdiscrete :
      ∀ z ∈ D, ∃ r > 0,
        Metric.ball z r ∩ {w | w ∈ D ∧ ¬ DifferentiableAt ℂ f w} ⊆ {z})
    (hisolated :
      ∀ z ∈ D, ¬ DifferentiableAt ℂ f z →
        ∃ r > 0,
          Metric.closedBall z r ⊆ D ∧
          DifferentiableOn ℂ f (Metric.ball z r \ ({z} : Set ℂ))) :
    Set.Finite (K ∩ {z | ¬ DifferentiableAt ℂ f z}) := by
  let _ := hisolated
  let S : Set ℂ := {z | DifferentiableAt ℂ f z}
  have hS_codiscrete : S ∈ Filter.codiscreteWithin D := by
    rw [codiscreteWithin_iff_locallyEmptyComplementWithin]
    intro z hz
    rcases hdiscrete z hz with ⟨r, hr, hball⟩
    refine ⟨Metric.ball z r \ ({z} : Set ℂ), ?_, ?_⟩
    · simpa [Set.diff_eq, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
        (inter_mem_nhdsWithin ({z} : Set ℂ)ᶜ
          (Metric.ball_mem_nhds z hr))
    ext w
    constructor
    · intro hw
      have hwSing : w ∈ {w | w ∈ D ∧ ¬ DifferentiableAt ℂ f w} := by
        exact ⟨hw.2.1, hw.2.2⟩
      have hwEq : w = z := by
        exact hball ⟨hw.1.1, hwSing⟩
      exact hw.1.2 hwEq
    · intro hw
      exact False.elim hw
  have hKfinite : (K \ S).Finite :=
    hK.finite_diff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hKD hS_codiscrete)
  -- Rewrite the compact difference against the differentiability locus as the singular subset.
  simpa [S, Set.diff_eq, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hKfinite

/-- Helper for Theorem III.5-extra-2: the explicit source restriction set for an open ambient
subset is the original chart source intersected with the preimage of that ambient subset in plane
coordinates. -/
private def boundaryStraighteningRestrictionSource
    (δ : OpenPartialHomeomorph Plane Plane) (C : Set ℂ) : Set Plane :=
  δ.source ∩ δ ⁻¹' (Complex.equivRealProdCLM '' C)

/-- Helper for Theorem III.5-extra-2: the restriction source used to cut a chart down to an open
ambient subset is itself open. -/
private theorem boundaryStraighteningRestrictionSource_isOpen
    {δ : OpenPartialHomeomorph Plane Plane} {C : Set ℂ} (hC_open : IsOpen C) :
    IsOpen (boundaryStraighteningRestrictionSource δ C) := by
  let Cplane : Set Plane := Complex.equivRealProdCLM '' C
  have hCplane_open : IsOpen Cplane := by
    exact Complex.equivRealProdCLM.isOpenMap _ hC_open
  have hs_target_open : IsOpen (Cplane ∩ δ.target) := hCplane_open.inter δ.open_target
  have hs_target_subset : Cplane ∩ δ.target ⊆ δ.target := Set.inter_subset_right
  have hs_open_image : IsOpen (δ.symm '' (Cplane ∩ δ.target)) :=
    δ.symm.isOpen_image_of_subset_source hs_target_open hs_target_subset
  have hs_eq :
      δ.symm '' (Cplane ∩ δ.target) = boundaryStraighteningRestrictionSource δ C := by
    rw [δ.symm.image_eq_target_inter_inv_preimage hs_target_subset]
    ext p
    constructor
    · rintro ⟨hp_source, hpCplane_target⟩
      exact ⟨hp_source, hpCplane_target.1⟩
    · intro hp
      exact ⟨hp.1, hp.2, δ.map_source hp.1⟩
  -- Rewrite the image-side openness statement back to the explicit restricted source.
  rw [← hs_eq]
  exact hs_open_image

/-- Helper for Theorem III.5-extra-2: restricting a boundary-straightening chart to an open
ambient subset containing the base point preserves the boundary straightening data. -/
private theorem IsBoundaryStraighteningAt.interOpen
    {K C : Set ℂ} {γ : ℝ → Plane} {t₀ : ℝ}
    {δ : OpenPartialHomeomorph Plane Plane}
    (hδ : IsBoundaryStraighteningAt K γ t₀ δ)
    (hC_open : IsOpen C)
    (hγC : Complex.equivRealProdCLM.symm (γ t₀) ∈ C)
    (hs_open : IsOpen (boundaryStraighteningRestrictionSource δ C)) :
    IsBoundaryStraighteningAt (K ∩ C) γ t₀
      (δ.restrOpen (boundaryStraighteningRestrictionSource δ C) hs_open) := by
  let Cplane : Set Plane := Complex.equivRealProdCLM '' C
  let δ' := δ.restrOpen (boundaryStraighteningRestrictionSource δ C) hs_open
  have hbase_mem : (t₀, 0) ∈ boundaryStraighteningRestrictionSource δ C := by
    refine ⟨hδ.basePoint_mem_source, ?_⟩
    refine ⟨Complex.equivRealProdCLM.symm (γ t₀), hγC, ?_⟩
    exact (hδ.map_horizontal_axis hδ.basePoint_mem_horizontalAxisDomain).symm
  have hlocal : IsLocalCurveStraighteningAt γ 0 1 t₀ δ' :=
    hδ.toIsLocalCurveStraighteningAt.restrOpen hs_open hbase_mem
  refine
    { toIsLocalCurveStraighteningAt := hlocal
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The restricted chart uses fewer right-side points, so the old exterior condition still
    -- rules out membership in `K ∩ C`.
    apply Set.not_nonempty_iff_eq_empty.1
    rintro ⟨z, hz⟩
    rcases hz with ⟨hz_image, hzKC⟩
    have hzK : z ∈ K := hzKC.1
    have hz_old :
        z ∈ Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p : Plane | p.2 < 0})) := by
      rcases hz_image with ⟨q, hq, rfl⟩
      rcases hq with ⟨p, hp, rfl⟩
      refine ⟨δ p, ?_, rfl⟩
      exact ⟨p, ⟨hp.1.1, hp.2⟩, rfl⟩
    have hz_oldK :
        z ∈ (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {p : Plane | p.2 < 0}))) ∩ K :=
      ⟨hz_old, hzK⟩
    have : False := by
      simp [hδ.exterior_on_right] at hz_oldK
    exact this
  · -- On the left side, the restricted chart stays in `interior K`, and the target restriction
    -- also keeps it inside the ambient open set `C`.
    intro z hz
    rcases hz with ⟨q, hq, rfl⟩
    rcases hq with ⟨p, hp, rfl⟩
    have hp' :
        p ∈ boundaryStraighteningRestrictionSource δ C ∩ {p : Plane | 0 < p.2} := by
      simpa [δ', boundaryStraighteningRestrictionSource] using hp
    have hzInteriorK :
        Complex.equivRealProdCLM.symm (δ p) ∈ interior K := by
      exact hδ.interior_on_left ⟨δ p, ⟨p, ⟨hp'.1.1, hp'.2⟩, rfl⟩, rfl⟩
    have hzCplane : δ p ∈ Cplane := hp'.1.2
    rcases hzCplane with ⟨w, hwC, hwEq⟩
    have hzC : Complex.equivRealProdCLM.symm (δ p) ∈ C := by
      rw [← hwEq]
      simpa using hwC
    rw [interior_inter, hC_open.interior_eq]
    exact ⟨hzInteriorK, hzC⟩

/-- Helper for Theorem III.5-extra-2: quarter-turning a complex tangent in plane coordinates is
the same as multiplying by `I` before converting back to `Plane`. -/
private lemma rot90_equivRealProd_eq_equivRealProd_mul_I (z : ℂ) :
    rot90 (Complex.equivRealProd z) = Complex.equivRealProd (z * Complex.I) := by
  -- `Complex.equivRealProd` identifies multiplication by `I` with the standard quarter-turn.
  ext <;> simp [rot90, Complex.equivRealProd]

/-- Helper for Theorem III.5-extra-2: a radial tube around a `C¹` complex curve has derivative
columns given by the tangent and the chosen transverse direction. -/
private lemma radial_tube_hasFDerivAt {γ n : ℝ → ℂ} {t₀ : ℝ} {v : ℂ}
    (hγCont : ContDiffAt ℝ 1 γ t₀) (hγDeriv : HasDerivAt γ v t₀)
    (hnCont : ContDiffAt ℝ 1 n t₀) :
    ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1 + p.2 • n p.1) (t₀, 0) ∧
      HasFDerivAt (fun p : Plane ↦ γ p.1 + p.2 • n p.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))
        (t₀, 0) := by
  constructor
  · -- The tube map is the sum of the curve branch and the varying transverse branch.
    have hγfst : ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1) (t₀, 0) := by
      simpa using hγCont.comp (x := (t₀, 0)) contDiffAt_fst
    have hnfst : ContDiffAt ℝ 1 (fun p : Plane ↦ n p.1) (t₀, 0) := by
      simpa using hnCont.comp (x := (t₀, 0)) contDiffAt_fst
    simpa using hγfst.add (contDiffAt_snd.smul hnfst)
  · -- At the base point, the transverse derivative contributes only the actual normal vector.
    have hγfst :
        HasFDerivAt (fun p : Plane ↦ γ p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        hγDeriv.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hnfst :
        HasFDerivAt (fun p : Plane ↦ n p.1)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (deriv n t₀)) (t₀, (0 : ℝ)) := by
      simpa [ContinuousLinearMap.smulRight_apply] using
        (hnCont.differentiableAt one_ne_zero).hasDerivAt.hasFDerivAt.comp (t₀, (0 : ℝ))
          (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    have hsnd :
        HasFDerivAt (fun p : Plane ↦ p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (t₀, (0 : ℝ)) := by
      simpa using
        (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (t₀, (0 : ℝ))))
    simpa [ContinuousLinearMap.smulRight_apply] using hγfst.add (hsnd.smul hnfst)

/-- Helper for Theorem III.5-extra-2: rescaling the second plane coordinate by a nonzero real
factor is a continuous linear automorphism. -/
private noncomputable def plane_second_rescale (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
  { toLinearEquiv :=
      { toFun := fun p ↦ (p.1, p.2 / c)
        invFun := fun p ↦ (p.1, c * p.2)
        left_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        right_inv := by
          intro p
          ext
          · rfl
          · field_simp [hc]
        map_add' := by
          intro p q
          ext <;> simp [div_eq_mul_inv, add_mul]
        map_smul' := by
          intro s p
          ext <;> simp [div_eq_mul_inv, mul_assoc] }
    continuous_toFun := by
      fun_prop
    continuous_invFun := by
      fun_prop }

/-- Helper for Theorem III.5-extra-2: the distance to the circle center along a radial exponential
ray is the absolute value of the real radial coefficient. -/
private lemma dist_add_real_mul_exp_eq_abs {a : ℂ} {s θ : ℝ} :
    dist (a + (s : ℂ) * Complex.exp (θ * Complex.I)) a = |s| := by
  -- The exponential factor has norm `1`, so only the real radius contributes to the distance.
  rw [dist_eq_norm]
  calc
    ‖a + (s : ℂ) * Complex.exp (θ * Complex.I) - a‖ =
        ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ := by
          ring_nf
    _ = ‖(s : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := norm_mul _ _
    _ = |s| := by simp [Complex.norm_exp]

/-- Helper for Theorem III.5-extra-2: the reversed boundary-circle parameter has constant
derivative `-2π`. -/
private lemma clockwise_boundary_circle_arg_hasDerivAt (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ 2 * Real.pi * (1 - t)) (-(2 * Real.pi)) t₀ := by
  -- The angular variable is the affine function `t ↦ 2π (1 - t)`.
  simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using
    ((hasDerivAt_id t₀).const_sub (1 : ℝ)).const_mul (2 * Real.pi)

/-- Helper for Theorem III.5-extra-2: on the reversed circle, quarter-turning the tangent yields
the outward radial direction scaled by `2πr`. -/
private lemma clockwise_boundary_circle_rot90_tangent_eq_scaled_outward {r : ℝ} {t₀ : ℝ} :
    rot90
      (Complex.equivRealProd
        (((((-(2 * Real.pi * r : ℝ))) : ℂ) * Complex.I) *
          Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I))) =
      (2 * Real.pi * r) •
        Complex.equivRealProd (Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I)) := by
  -- Multiplication by `I` turns the clockwise tangent into the outward radial direction.
  rw [rot90_equivRealProd_eq_equivRealProd_mul_I]
  have hz :
      (((((((-(2 * Real.pi * r : ℝ))) : ℂ) * Complex.I) *
            Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I))) * Complex.I) =
        ((2 * Real.pi * r) : ℝ) •
          Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I) := by
    calc
      (((((((-(2 * Real.pi * r : ℝ))) : ℂ) * Complex.I) *
            Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I))) * Complex.I) =
          ((((-(2 * Real.pi * r : ℝ)) : ℂ) *
              Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I)) *
            (Complex.I * Complex.I)) := by
              ring
      _ = ((((-(2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I)) * (-1)) := by
            simp
      _ = -(((-(2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I)) := by
            ring
      _ = ((2 * Real.pi * r) : ℝ) •
            Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
  calc
    Complex.equivRealProd
        (((((((-(2 * Real.pi * r : ℝ))) : ℂ) * Complex.I) *
              Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I))) * Complex.I) =
        Complex.equivRealProd
          (((2 * Real.pi * r) : ℝ) • Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I)) :=
      congrArg Complex.equivRealProd hz
    _ = (2 * Real.pi * r) •
          Complex.equivRealProd (Complex.exp ((2 * Real.pi * (1 - t₀)) * Complex.I)) := by
      simp

/-- Helper for Theorem III.5-extra-2: the reversed boundary circle has the explicit
`circleMap a r (2π(1-t))` parametrization on the unit interval. -/
private lemma boundary_circle_path_symm_extend_eq_circleMap {a : ℂ} {r t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((boundary_circle_path a r).symm).extend t = circleMap a r (2 * Real.pi * (1 - t)) := by
  -- Reversing the loop just replaces `t` by `1 - t` in the explicit circle formula.
  rw [Path.extend_apply ((boundary_circle_path a r).symm) ht]
  simp [boundary_circle_path, Path.symm, unitInterval.symm, sub_eq_add_neg, add_comm, mul_comm,
    mul_left_comm]

/-- Helper for Theorem III.5-extra-2: the clockwise closed-path real curve is the explicit
clockwise `circleMap` after converting back from `Plane` coordinates. -/
private lemma clockwiseBoundaryCircle_realCurve_eq_circleMap {a : ℂ} {r t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Complex.equivRealProdCLM.symm ((((boundary_circle_path a r).symm).toClosedPath.realCurve) t) =
      circleMap a r (2 * Real.pi * (1 - t)) := by
  -- Route correction: normalize the clockwise branch once so the chart proof stays in one
  -- `circleMap` spelling world.
  rw [toClosedPath_realCurve_eq, Function.comp_apply]
  rw [Complex.equivRealProdCLM_symm_apply]
  rw [boundary_circle_path_symm_extend_eq_circleMap ht]
  exact Complex.re_add_im _

/-- Helper for Theorem III.5-extra-2: on the inward side of the clockwise radial tube, the
explicit tube point lies strictly inside the deleted ball. -/
private lemma clockwiseBoundaryCircleTube_mem_ball {a : ℂ} {r : ℝ}
    {p : Plane} (hp_lower : -r < p.2) (hp_upper : p.2 < 0) :
    a + (((r + p.2 : ℝ)) : ℂ) * Complex.exp ((2 * Real.pi * (1 - p.1)) * Complex.I) ∈
      Metric.ball a r := by
  -- The explicit tube radius is `r + p.2`, which lies in `(0, r)` on the inward side.
  have hrad_nonneg : 0 ≤ r + p.2 := by
    linarith
  rw [Metric.mem_ball]
  have hdist :
      dist
          (a + (((r + p.2 : ℝ)) : ℂ) * Complex.exp (2 * Real.pi * (1 - p.1) * Complex.I))
          a =
        |r + p.2| :=
    by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (dist_add_real_mul_exp_eq_abs
          (a := a) (s := r + p.2) (θ := 2 * Real.pi * (1 - p.1)))
  rw [hdist, abs_of_nonneg hrad_nonneg]
  linarith

/-- Helper for Theorem III.5-extra-2: on the outward side of the clockwise radial tube, the
explicit tube point lies in the interior of the complement of the deleted ball. -/
private lemma clockwiseBoundaryCircleTube_mem_ballComplInterior {a : ℂ} {r : ℝ} (hr : 0 < r)
    {p : Plane} (hp : 0 < p.2) :
    a + (((r + p.2 : ℝ)) : ℂ) * Complex.exp ((2 * Real.pi * (1 - p.1)) * Complex.I) ∈
      interior ((Metric.ball a r)ᶜ : Set ℂ) := by
  -- The explicit tube radius is now strictly larger than `r`, so the point misses the closed ball.
  rw [interior_compl, closure_ball a hr.ne', Set.mem_compl_iff, Metric.mem_closedBall]
  have hdist :
      dist
          (a + (((r + p.2 : ℝ)) : ℂ) * Complex.exp (2 * Real.pi * (1 - p.1) * Complex.I))
          a =
        |r + p.2| := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (dist_add_real_mul_exp_eq_abs
          (a := a) (s := r + p.2) (θ := 2 * Real.pi * (1 - p.1)))
  have hrad_nonneg : 0 ≤ r + p.2 := by
    linarith
  rw [hdist, abs_of_nonneg hrad_nonneg]
  linarith

/-- Helper for Theorem III.5-extra-2: every regular point of the clockwise circle admits an
explicit boundary-straightening chart for the complement of the enclosed open disc. -/
private lemma clockwise_boundary_circle_exists_boundary_chart_ball_compl
    {a : ℂ} {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ (((boundary_circle_path a r).symm).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin (((boundary_circle_path a r).symm).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt ((Metric.ball a r)ᶜ : Set ℂ)
        (((boundary_circle_path a r).symm).toClosedPath.realCurve) t₀ δ := by
  let θ : ℝ → ℝ := fun t ↦ 2 * Real.pi * (1 - t)
  let γ : ℝ → ℂ := fun t ↦ circleMap a r (θ t)
  let n : ℝ → ℂ := fun t ↦ Complex.exp (θ t * Complex.I)
  let tangent : ℂ := (-(2 * Real.pi : ℝ)) • (circleMap 0 r (θ t₀) * Complex.I)
  let Ψ : Plane → ℂ := fun p ↦ γ p.1 + p.2 • n p.1
  let Φ : Plane → Plane := fun p ↦ Complex.equivRealProd (Ψ p)
  have _hkeep_regular :
      DifferentiableWithinAt ℝ (((boundary_circle_path a r).symm).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ := hdiff
  have _hkeep_nonzero :
      derivWithin (((boundary_circle_path a r).symm).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0 := hderiv
  have hθCont : ContDiffAt ℝ 1 θ t₀ := by
    -- The reversed angular parameter is still affine.
    have hθ : ContDiff ℝ 1 θ := by
      have hconst : ContDiff ℝ 1 (fun _ : ℝ ↦ (2 * Real.pi : ℝ)) := contDiff_const
      have hrev : ContDiff ℝ 1 (fun t : ℝ ↦ 1 - t) := by
        simpa [sub_eq_add_neg] using
          (contDiff_const.sub (contDiff_id : ContDiff ℝ 1 (fun t : ℝ ↦ t)))
      simpa [θ, mul_comm] using hconst.mul hrev
    exact hθ.contDiffAt
  have hγCont : ContDiffAt ℝ 1 γ t₀ := by
    -- The clockwise circle branch is smooth after composing `circleMap` with the affine angle.
    simpa [γ] using (contDiff_circleMap a r).contDiffAt.comp t₀ hθCont
  have hnCont : ContDiffAt ℝ 1 n t₀ := by
    -- The outward radial unit field varies smoothly along the clockwise circle.
    have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
      simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
    have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
      simpa [one_mul] using hθComplex.mul contDiffAt_const
    simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner)
  have hγDeriv : HasDerivAt γ tangent t₀ := by
    -- Differentiate the clockwise circle explicitly by the chain rule.
    simpa [γ, tangent] using
      ((hasDerivAt_circleMap a r (θ t₀)).scomp t₀ (clockwise_boundary_circle_arg_hasDerivAt t₀))
  have htangent_formula :
      tangent = ((((-(2 * Real.pi * r : ℝ))) : ℂ) * Complex.I) *
        Complex.exp (θ t₀ * Complex.I) := by
    -- Rewrite the chain-rule derivative into the explicit tangent form used by the frame lemma.
    calc
      tangent = ((-(2 * Real.pi : ℝ)) : ℂ) * (circleMap 0 r (θ t₀) * Complex.I) := by
        simp [tangent]
      _ = ((((-(2 * Real.pi * r : ℝ))) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I) := by
        rw [circleMap, zero_add]
        simp [mul_assoc, mul_left_comm, mul_comm]
  obtain ⟨hΨcont, hΨderiv⟩ := radial_tube_hasFDerivAt
    (γ := γ) (n := n) (t₀ := t₀) (v := tangent) hγCont hγDeriv hnCont
  have hΦcont : ContDiffAt ℝ 1 Φ (t₀, 0) := by
    -- Converting the complex tube to real-plane coordinates preserves `C¹`.
    simpa [Φ] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_contDiffAt_iff).2 hΨcont
  let v : Plane := Complex.equivRealProd tangent
  let radial : Plane := Complex.equivRealProd (n t₀)
  have hv : v ≠ 0 := by
    -- A positive-radius circle has nonvanishing clockwise tangent.
    intro hv0
    have htangent : tangent = 0 := by
      exact Complex.equivRealProd.injective (by simpa [v] using hv0)
    have hscale : ((((-(2 * Real.pi * r : ℝ))) : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hr.ne')
    have hmul :
        ((((-(2 * Real.pi * r : ℝ))) : ℂ) * Complex.I) * Complex.exp (θ t₀ * Complex.I) = 0 := by
      simpa [htangent_formula] using htangent
    exact Complex.exp_ne_zero (θ t₀ * Complex.I) ((mul_eq_zero.mp hmul).resolve_left hscale)
  have hrot : rot90 v = (2 * Real.pi * r) • radial := by
    -- Quarter-turning the clockwise tangent now gives the outward radial direction.
    simpa [v, radial, n, θ, htangent_formula, mul_assoc, mul_left_comm, mul_comm] using
      clockwise_boundary_circle_rot90_tangent_eq_scaled_outward (r := r) (t₀ := t₀)
  obtain ⟨e₀, he₀⟩ := rot90_frame_equiv_of_ne_zero v hv
  let c : ℝ := 2 * Real.pi * r
  have hc : c ≠ 0 := by
    positivity
  let e : Plane ≃L[ℝ] Plane := (plane_second_rescale c hc).trans e₀
  have hderiv_map :
      ((Complex.equivRealProdCLM : ℂ →L[ℝ] Plane).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight tangent +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))) =
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Convert the complex derivative columns into the real-plane tangent and radial columns.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    simp [ContinuousLinearMap.comp_apply, v, radial, ContinuousLinearMap.smulRight_apply]
  have hΦderiv :
      HasFDerivAt Φ
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial)
        (t₀, 0) := by
    -- The real-plane tube has tangent column `v` and outward radial column `radial`.
    simpa [Φ, hderiv_map] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_hasFDerivAt_iff).2 hΨderiv
  have he : (e : Plane →L[ℝ] Plane) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Rescaling the second frame coordinate turns the `rot90` column into the actual outward
    -- normal column.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    change e₀ (x, y / c) = x • v + y • radial
    calc
      e₀ (x, y / c) = x • v + (y / c) • rot90 v := by
        simpa [ContinuousLinearMap.smulRight_apply] using
          congrArg (fun f : Plane →L[ℝ] Plane => f (x, y / c)) he₀
      _ = x • v + (y / c) • (c • radial) := by rw [hrot]
      _ = x • v + (((y / c) * c) • radial) := by rw [smul_smul]
      _ = x • v + y • radial := by
        have hyc : y * c⁻¹ * c = y := by
          calc
            y * c⁻¹ * c = y * (c⁻¹ * c) := by ring
            _ = y := by simp [hc]
        simp [div_eq_mul_inv, hyc]
  have hΦderiv' : HasFDerivAt Φ (e : Plane →L[ℝ] Plane) (t₀, 0) := by
    -- This is the invertible derivative required by the inverse function theorem.
    simpa [he] using hΦderiv
  let δ₀ : OpenPartialHomeomorph Plane Plane :=
    hΦcont.toOpenPartialHomeomorph Φ hΦderiv' one_ne_zero
  let δ₁ : OpenPartialHomeomorph Plane Plane := δ₀.restrContDiff ℝ 1 (by norm_num)
  let strip : Set Plane := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-r) r
  let δ : OpenPartialHomeomorph Plane Plane := δ₁.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
  have hδ₀_source : (t₀, 0) ∈ δ₀.source := by
    -- The inverse function theorem keeps the base point in the source.
    exact hΦcont.mem_toOpenPartialHomeomorph_source hΦderiv' one_ne_zero
  have hδ₀_symm : ContDiffAt ℝ 1 δ₀.symm (Φ (t₀, 0)) := by
    -- The local inverse is again `C¹` at the image of the base point.
    simpa [δ₀, Φ] using hΦcont.to_localInverse hΦderiv' one_ne_zero
  have hδ₁_source : (t₀, 0) ∈ δ₁.source := by
    -- Restricting to the `C¹` locus still keeps the base point in the source.
    simpa [δ₁, δ₀, Φ] using And.intro hδ₀_source (And.intro hΦcont hδ₀_symm)
  have hsource_subset : δ.source ⊆ δ₁.source := by
    intro p hp
    exact (show p ∈ δ₁.source ∩ strip by simpa [δ, strip] using hp).1
  have htarget_subset : δ.target ⊆ δ₁.target := by
    intro q hq
    exact (show q ∈ δ₁.target ∩ δ₁.symm ⁻¹' strip by simpa [δ, strip] using hq).1
  refine ⟨δ, ?_⟩
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The base point lies in the open strip because `t₀ ∈ (0, 1)` and `0 ∈ (-r, r)`.
    have hstrip : (t₀, 0) ∈ strip := by
      refine ⟨ht₀, ?_⟩
      constructor <;> linarith
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · -- Any source point still lies over the standard parameter strip around the circle.
    intro p hp
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp
    exact ⟨hp'.2.1, Set.mem_univ _⟩
  · -- Restricting the inverse-function chart preserves `C¹` regularity on the smaller source.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_source (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono hsource_subset
  · -- The same inheritance applies to the local inverse on the restricted target.
    exact
      (OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) (f := δ₀)
        (n := 1) (by norm_num)).mono htarget_subset
  · intro t ht
    -- Along the horizontal axis, the chart reproduces the clockwise boundary circle.
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htStrip.1.1.le, htStrip.1.2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd (circleMap a r (2 * Real.pi * (1 - t))) := by
        simp [γ, θ]
      _ = (((boundary_circle_path a r).symm).toClosedPath.realCurve) t := by
        exact congrArg Complex.equivRealProd
          (clockwiseBoundaryCircle_realCurve_eq_circleMap (a := a) (r := r) htIcc).symm
  · -- The chart image of the clockwise boundary branch is exactly the horizontal axis.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htStrip.1.1.le, htStrip.1.2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd (circleMap a r (2 * Real.pi * (1 - t))) := by
        simp [γ, θ]
      _ = (((boundary_circle_path a r).symm).toClosedPath.realCurve) t := by
        exact congrArg Complex.equivRealProd
          (clockwiseBoundaryCircle_realCurve_eq_circleMap (a := a) (r := r) htIcc).symm
  · -- Negative transverse parameters move into the deleted open ball, hence outside the owner.
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp.1
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          a + (((r + p.2 : ℝ)) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
          rw [Complex.equivRealProdCLM_symm_apply]
          exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
          simp [Ψ]
        _ = a + (((r + p.2 : ℝ)) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
          simp [γ, n, θ, circleMap]
          ring
    have hball :
        Complex.equivRealProdCLM.symm (δ p) ∈ Metric.ball a r := by
      rw [hformula]
      simpa [θ] using
        clockwiseBoundaryCircleTube_mem_ball (a := a) (r := r) hp'.2.2.1 hp.2
    have hnotOwner : Complex.equivRealProdCLM.symm (δ p) ∉ ((Metric.ball a r)ᶜ : Set ℂ) := by
      simpa using hball
    exact hnotOwner hx.2
  · intro x hx
    -- Positive transverse parameters move outside the closed ball, hence into the interior of the
    -- complement owner.
    rcases hx with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          a + (((r + p.2 : ℝ)) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
          rw [Complex.equivRealProdCLM_symm_apply]
          exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
          simp [Ψ]
        _ = a + (((r + p.2 : ℝ)) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
          simp [γ, n, θ, circleMap]
          ring
    have hinside :
        Complex.equivRealProdCLM.symm (δ p) ∈ interior ((Metric.ball a r)ᶜ : Set ℂ) := by
      rw [hformula]
      simpa [θ] using
        clockwiseBoundaryCircleTube_mem_ballComplInterior (a := a) (r := r) hr hp.2
    simpa using hinside

/-- Helper for Theorem III.5-extra-2: an outer boundary chart for `K` can be restricted away from
the finite excision discs, yielding a boundary chart for the punctured owner. -/
lemma outer_boundary_chart_restrict_away_from_excised_balls
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {s : Finset ℂ} {ρ : ℂ → ℝ} (hΓ : IsOrientedBoundaryOf K Γ)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    {i : ι} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff : DifferentiableWithinAt ℝ (Γ i).realCurve (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv : derivWithin (Γ i).realCurve (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z))
        (Γ i).realCurve t₀ δ := by
  obtain ⟨δ, hδ⟩ := hΓ.exists_boundary_chart_at_regular_point i ht₀ hdiff hderiv
  let C : Set ℂ := (⋃ z ∈ (↑s : Set ℂ), Metric.closedBall z (ρ z))ᶜ
  have hC_open : IsOpen C := by
    classical
    have hClosed :
        IsClosed (⋃ z ∈ s, Metric.closedBall z (ρ z)) :=
      isClosed_biUnion_finset fun z hz ↦ Metric.isClosed_closedBall
    simpa [C] using hClosed.isOpen_compl
  have hpoint_range :
      Complex.equivRealProdCLM.symm ((Γ i).realCurve t₀) ∈ Set.range (Γ i).toPath := by
    let u : Set.Icc (0 : ℝ) 1 := ⟨t₀, ht₀.1.le, ht₀.2.le⟩
    refine ⟨u, ?_⟩
    rw [ClosedPath.realCurve, Function.comp_apply, Complex.equivRealProdCLM_symm_apply,
      Path.extend_apply (Γ i).toPath u.2]
    exact (Complex.re_add_im ((Γ i).toPath u)).symm
  have hpointC : Complex.equivRealProdCLM.symm ((Γ i).realCurve t₀) ∈ C := by
    -- The outer boundary lies on `frontier K`, so it misses every closed ball contained in
    -- `interior K`.
    rw [Set.mem_compl_iff]
    intro hUnion
    rcases Set.mem_iUnion.1 hUnion with ⟨z, hzUnion⟩
    rcases Set.mem_iUnion.1 hzUnion with ⟨hzs, hzBall⟩
    have hdisj :
        Disjoint (Set.range (Γ i).toPath) (Metric.closedBall z (ρ z)) :=
      boundary_path_disjoint_of_closedBall_subset_interior
        (Γ := Γ) hΓ (z := z) (r := ρ z) (hρK z hzs) i
    exact (Set.disjoint_left.1 hdisj) hpoint_range hzBall
  have hs_open : IsOpen (boundaryStraighteningRestrictionSource δ C) :=
    boundaryStraighteningRestrictionSource_isOpen (δ := δ) hC_open
  let δ' : OpenPartialHomeomorph Plane Plane :=
    δ.restrOpen (boundaryStraighteningRestrictionSource δ C) hs_open
  have hδ' :
      IsBoundaryStraighteningAt (K ∩ C) (Γ i).realCurve t₀ δ' := by
    simpa [δ'] using
      IsBoundaryStraighteningAt.interOpen
        (K := K) (C := C) (γ := (Γ i).realCurve) (t₀ := t₀) hδ hC_open hpointC hs_open
  have hsubset : K ∩ C ⊆ K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxUnion
    apply hx.2
    rcases Set.mem_iUnion.1 hxUnion with ⟨z, hzUnion⟩
    rcases Set.mem_iUnion.1 hzUnion with ⟨hzs, hzBall⟩
    exact Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzs, Metric.ball_subset_closedBall hzBall⟩⟩
  refine ⟨δ', ?_⟩
  refine
    { toIsLocalCurveStraighteningAt := hδ'.toIsLocalCurveStraighteningAt
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The restricted right side stays in the closed-ball complement, so the old exterior
    -- condition for `K ∩ C` rules out the punctured owner as well.
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx.1 with ⟨q, hq, rfl⟩
    rcases hq with ⟨p, hp, rfl⟩
    have hp' :
        p ∈ boundaryStraighteningRestrictionSource δ C ∩ {p : Plane | p.2 < 0} := by
      simpa [δ', boundaryStraighteningRestrictionSource] using hp
    have hxCplane : δ p ∈ Complex.equivRealProdCLM '' C := hp'.1.2
    have hxC : Complex.equivRealProdCLM.symm (δ' p) ∈ C := by
      rw [show δ' p = δ p by simp [δ']]
      rcases hxCplane with ⟨w, hwC, hwEq⟩
      rw [← hwEq]
      simpa using hwC
    have hxRestricted :
        Complex.equivRealProdCLM.symm (δ' p) ∈
          (Complex.equivRealProdCLM.symm '' (δ' '' (δ'.source ∩ {q : Plane | q.2 < 0}))) ∩
            (K ∩ C) := by
      refine ⟨⟨δ' p, ⟨p, hp, rfl⟩, rfl⟩, ?_⟩
      exact ⟨hx.2.1, hxC⟩
    simp [hδ'.exterior_on_right] at hxRestricted
  · -- Any point on the restricted left side already lies in `interior (K ∩ C)`, hence in the
    -- interior of the larger punctured owner.
    intro x hx
    exact (interior_mono hsubset) (hδ'.interior_on_left hx)

/-- Helper for Theorem III.5-extra-2: every regular point of a clockwise excision circle admits a
local boundary straightening chart for the punctured owner. -/
lemma clockwise_boundary_circle_exists_boundary_chart_punctured_owner
    {K : Set ℂ} {s : Finset ℂ} {ρ : ℂ → ℝ} (z : s.attach)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)))
    {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ
        (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin
          (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve)
          (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt
        (K \ ⋃ w ∈ (↑s : Set ℂ), Metric.ball w (ρ w))
        (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve)
        t₀ δ := by
  let ballCompl : Set ℂ := ((Metric.ball z.1.1 (ρ z.1.1))ᶜ : Set ℂ)
  obtain ⟨δ, hδ⟩ :=
    clockwise_boundary_circle_exists_boundary_chart_ball_compl
      (a := z.1.1) (r := ρ z.1.1) (hρpos z.1.1 z.1.2) ht₀ hdiff hderiv
  let others : Finset ℂ := s.erase z.1.1
  let C : Set ℂ := interior K ∩ (⋃ w ∈ (↑others : Set ℂ), Metric.closedBall w (ρ w))ᶜ
  have hC_open : IsOpen C := by
    -- The restriction neighborhood is open: stay inside `interior K` and away from the other
    -- excision closed balls.
    have hClosed :
        IsClosed (⋃ w ∈ others, Metric.closedBall w (ρ w)) :=
      isClosed_biUnion_finset fun w hw ↦ Metric.isClosed_closedBall
    exact isOpen_interior.inter hClosed.isOpen_compl
  have htIcc : t₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨ht₀.1.le, ht₀.2.le⟩
  have hbase_sphere :
      Complex.equivRealProdCLM.symm
          ((((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve) t₀) ∈
        Metric.sphere z.1.1 (ρ z.1.1) := by
    rw [clockwiseBoundaryCircle_realCurve_eq_circleMap (a := z.1.1) (r := ρ z.1.1) htIcc]
    convert circleMap_mem_sphere' z.1.1 (ρ z.1.1) (2 * Real.pi * (1 - t₀)) using 1
    simp [abs_of_pos (hρpos z.1.1 z.1.2)]
  have hbase_closed :
      Complex.equivRealProdCLM.symm
          ((((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve) t₀) ∈
        Metric.closedBall z.1.1 (ρ z.1.1) :=
    Metric.sphere_subset_closedBall hbase_sphere
  have hpointC :
      Complex.equivRealProdCLM.symm
          ((((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve) t₀) ∈ C := by
    constructor
    · -- The base point lies on the excision sphere, hence inside `interior K`.
      exact hρK z.1.1 z.1.2 hbase_closed
    · -- Pairwise disjointness keeps the same boundary point away from every other excision disc.
      rw [Set.mem_compl_iff]
      intro hUnion
      rcases Set.mem_iUnion.1 hUnion with ⟨w, hwUnion⟩
      rcases Set.mem_iUnion.1 hwUnion with ⟨hwOthers, hwBall⟩
      have hwInS : w ∈ s := (Finset.mem_erase.mp hwOthers).2
      have hzw : z.1.1 ≠ w := by
        intro hEq
        exact (Finset.mem_erase.mp hwOthers).1 hEq.symm
      have hdisj :=
        hpair z.1.1 z.1.2 w hwInS hzw
      exact (Set.disjoint_left.1 hdisj) hbase_closed hwBall
  have hs_open : IsOpen (boundaryStraighteningRestrictionSource δ C) :=
    boundaryStraighteningRestrictionSource_isOpen (δ := δ) hC_open
  let δ' : OpenPartialHomeomorph Plane Plane :=
    δ.restrOpen (boundaryStraighteningRestrictionSource δ C) hs_open
  have hδ' :
      IsBoundaryStraighteningAt (ballCompl ∩ C)
        (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve) t₀ δ' := by
    -- Restrict the single-disc complement chart to the open neighborhood that stays inside
    -- `interior K` and avoids the other excision discs.
    simpa [ballCompl, δ'] using
      IsBoundaryStraighteningAt.interOpen
        (K := ballCompl)
        (C := C)
        (γ := (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.realCurve))
        (t₀ := t₀) hδ hC_open hpointC hs_open
  have howner_subset_ballCompl :
      (K \ ⋃ w ∈ (↑s : Set ℂ), Metric.ball w (ρ w)) ⊆ ballCompl := by
    intro x hx
    have hxNotBall : x ∉ Metric.ball z.1.1 (ρ z.1.1) := by
      intro hxBall
      exact hx.2 (Set.mem_iUnion.2 ⟨z.1.1, Set.mem_iUnion.2 ⟨z.1.2, hxBall⟩⟩)
    simpa [ballCompl] using hxNotBall
  have hsubset_owner :
      ballCompl ∩ C ⊆ K \ ⋃ w ∈ (↑s : Set ℂ), Metric.ball w (ρ w) := by
    intro x hx
    refine ⟨interior_subset hx.2.1, ?_⟩
    intro hUnion
    rcases Set.mem_iUnion.1 hUnion with ⟨w, hwUnion⟩
    rcases Set.mem_iUnion.1 hwUnion with ⟨hwInS, hwBall⟩
    by_cases hwz : w = z.1.1
    · have hxNotBall : x ∉ Metric.ball z.1.1 (ρ z.1.1) := by
        simpa [ballCompl] using hx.1
      exact hxNotBall (by simpa [hwz] using hwBall)
    · apply hx.2.2
      have hwOthers : w ∈ others := Finset.mem_erase.mpr ⟨hwz, hwInS⟩
      exact Set.mem_iUnion.2
        ⟨w, Set.mem_iUnion.2 ⟨hwOthers, Metric.ball_subset_closedBall hwBall⟩⟩
  refine ⟨δ', ?_⟩
  refine
    { toIsLocalCurveStraighteningAt := hδ'.toIsLocalCurveStraighteningAt
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- On the right side, the restricted chart still lands in the deleted `z`-ball, so it cannot
    -- meet the punctured owner.
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hx.1 with ⟨q, hq, rfl⟩
    rcases hq with ⟨p, hp, rfl⟩
    have hp' :
        p ∈ boundaryStraighteningRestrictionSource δ C ∩ {p : Plane | p.2 < 0} := by
      simpa [δ', boundaryStraighteningRestrictionSource] using hp
    have hxOld :
        Complex.equivRealProdCLM.symm (δ' p) ∈
          (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {q : Plane | q.2 < 0}))) ∩
            ballCompl := by
      refine ⟨?_, howner_subset_ballCompl hx.2⟩
      rw [show δ' p = δ p by simp [δ']]
      exact ⟨δ p, ⟨p, ⟨hp'.1.1, hp'.2⟩, rfl⟩, rfl⟩
    simp [ballCompl, hδ.exterior_on_right] at hxOld
  · -- On the left side, the restricted chart already lands in `interior (ballCompl ∩ C)`, which
    -- sits inside the interior of the punctured owner.
    intro x hx
    exact (interior_mono hsubset_owner) (hδ'.interior_on_left hx)

/-- Helper for Theorem III.5-extra-2: the explicit excision boundary family has image equal to the
frontier of the punctured owner once the finite frontier decomposition is known. -/
lemma range_iUnion_finite_excision_boundary_family_eq_frontier
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {s : Finset ℂ} {ρ : ℂ → ℝ} (hΓ : IsOrientedBoundaryOf K Γ)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w))) :
    (⋃ j, Set.range ((finite_excision_boundary_family Γ s ρ j).toPath)) =
      frontier (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) := by
  have hfrontier :=
    frontier_diff_iUnion_ball_eq_of_pairwise_disjoint_closedBall_subset_interior
      (K := K) (s := s) (ρ := ρ) hΓ.isCompact.isClosed hρpos hρK hpair
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
    cases j with
    | inl i =>
        have hxFrontier : x ∈ frontier K := by
          rw [← hΓ.iUnion_range_eq_frontier]
          exact Set.mem_iUnion.2 ⟨i, by simpa [finite_excision_boundary_family] using hj⟩
        rw [hfrontier]
        exact Or.inl hxFrontier
    | inr z =>
        have hjCircle :
            x ∈ Set.range
              ((((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath).toPath) := by
          simpa [finite_excision_boundary_family] using hj
        have hxSphere : x ∈ Metric.sphere z.1.1 (ρ z.1.1) := by
          rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos z.1.1 z.1.2)] at hjCircle
          exact hjCircle
        rw [hfrontier]
        exact Or.inr <| Set.mem_iUnion.2 ⟨z.1.1, Set.mem_iUnion.2 ⟨z.1.2, hxSphere⟩⟩
  · intro hx
    rw [hfrontier] at hx
    rcases hx with hxFrontier | hxSphere
    · rw [← hΓ.iUnion_range_eq_frontier] at hxFrontier
      rcases Set.mem_iUnion.1 hxFrontier with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨Sum.inl i, by simpa [finite_excision_boundary_family] using hi⟩
    · rcases Set.mem_iUnion.1 hxSphere with ⟨z, hzSphere⟩
      rcases Set.mem_iUnion.1 hzSphere with ⟨hz, hxSphere⟩
      let zz : s.attach := ⟨⟨z, hz⟩, by simp⟩
      have hxCircle :
          x ∈ Set.range
            ((((boundary_circle_path zz.1.1 (ρ zz.1.1)).symm).toClosedPath).toPath) := by
        rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos zz.1.1 zz.1.2)]
        exact hxSphere
      exact Set.mem_iUnion.2 ⟨Sum.inr zz, by simpa [finite_excision_boundary_family] using hxCircle⟩

/-- Helper for Theorem III.5-extra-2: source-faithful finite excision should identify the punctured
owner with the original outer boundary plus the clockwise inner circles. -/
lemma finite_excision_isOrientedBoundaryOf
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (s : Finset ℂ) (ρ : ℂ → ℝ)
    (hΓ : IsOrientedBoundaryOf K Γ)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w))) :
    IsOrientedBoundaryOf (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z))
      (finite_excision_boundary_family Γ s ρ) := by
  let _ := hΓ
  let _ := hρpos
  let _ := hρK
  let _ := hpair
  have hholesOpen : IsOpen (⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) := by
    refine isOpen_biUnion ?_
    intro (z : ℂ) hz
    exact Metric.isOpen_ball
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The punctured owner is the compact owner intersected with the complement of the open holes.
    simpa [Set.diff_eq] using hΓ.isCompact.inter_right hholesOpen.isClosed_compl
  · intro j
    cases j with
    | inl i =>
        -- Outer boundary components are unchanged.
        simpa [finite_excision_boundary_family] using hΓ.piecewiseDifferentiable i
    | inr z =>
        -- Each inner component is the reversed explicit circle.
        simpa [finite_excision_boundary_family] using
          boundary_circle_path_symm_isPiecewiseDifferentiable z.1.1 (ρ z.1.1)
  · intro j s₀ t₀ hst
    cases j with
    | inl i =>
        -- Outer simple loops are inherited from the original oriented boundary.
        simpa [finite_excision_boundary_family] using hΓ.simple_loops i hst
    | inr z =>
        -- The clockwise circles reduce to the reversed-circle simplicity lemma.
        simpa [finite_excision_boundary_family] using
          clockwise_boundary_circle_simple_eq_or_endpoints
            (a := z.1.1) (r := ρ z.1.1) (hρpos z.1.1 z.1.2).ne' hst
  · -- Pairwise disjointness was proved once and for all from the disc geometry.
    exact pairwiseDisjoint_ranges_finite_excision_boundary_family
      (Γ := Γ) hΓ hρpos hρK hpair
  · -- Rewrite the image of the explicit boundary family to the frontier of the punctured owner.
    exact range_iUnion_finite_excision_boundary_family_eq_frontier
      (Γ := Γ) hΓ hρpos hρK hpair
  · intro j t₀ ht₀ hdiff hderiv
    -- Route correction: the global excision geometry is finished, so only the two local chart
    -- constructions remain: restriction for outer branches and an explicit radial tube for the
    -- clockwise inner circles.
    cases j with
    | inl i =>
        simpa [finite_excision_boundary_family] using
          outer_boundary_chart_restrict_away_from_excised_balls
            (Γ := Γ) (s := s) (ρ := ρ) hΓ hρK ht₀ hdiff hderiv
    | inr z =>
        simpa [finite_excision_boundary_family] using
          clockwise_boundary_circle_exists_boundary_chart_punctured_owner
            (K := K) (s := s) (ρ := ρ) z hρpos hρK hpair ht₀ hdiff hderiv

/-- Helper for Theorem III.5-extra-2: after excising finitely many pairwise disjoint interior
discs, the outer oriented-boundary integral equals the sum of the positively oriented inner circle
integrals. -/
-- TODO: re-prove the Chapter II punctured-boundary construction for a finite family of disjoint
-- interior discs, then apply `orientedBoundary_sum_curveIntegral_eq_zero` to the punctured region.
lemma orientedBoundary_sum_curveIntegral_eq_sum_small_circle_integrals
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ}
    (s : Finset ℂ) (ρ : ℂ → ℝ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hρD : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ D)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)))
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ))) :
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
      Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
  classical
  have hboundary_disjoint :
      ∀ i, Disjoint (Set.range (Γ i).toPath) (↑s : Set ℂ) :=
    boundary_path_disjoint_of_centers_closedBall_subset_interior
      (Γ := Γ) hΓ hρpos hρK
  have hpunctured_subset :
      K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) ⊆ D \ (↑s : Set ℂ) :=
    punctured_owner_subset_punctured_domain_of_excised_balls hKD hρpos
  have hω_closed :
      IsClosedOn (Complex.realScalarOneForm f) (D \ (↑s : Set ℂ)) :=
    realScalarOneForm_isClosedOn_punctured_domain hD hhol
  let _ := hD
  let _ := hρD
  let _ := hpair
  let _ := hhol
  let _ := hboundary_disjoint
  let _ := hpunctured_subset
  let _ := hω_closed
  let Δ := finite_excision_boundary_family Γ s ρ
  have hΔ :
      IsOrientedBoundaryOf (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) Δ := by
    -- This is now the only structural gap: the punctured owner needs the source-faithful
    -- oriented-boundary witness with outer components `Γ` and clockwise inner circles.
    simpa [Δ] using finite_excision_isOrientedBoundaryOf
      (Γ := Γ) (s := s) (ρ := ρ) hΓ hρpos hρK hpair
  have hzero :
      ∑ j, ∫ᶜ z in (Δ j).toPath, (f dz) z = 0 := by
    -- Once the punctured boundary family exists, the closed-form zero theorem applies directly.
    have hzero' :
        ∑ j, ∫ᶜ z in (Δ j).toPath, Complex.realScalarOneForm f z = 0 :=
      orientedBoundary_integral_eq_zero_of_isClosedOn
        (Γ := Δ) hΔ hpunctured_subset hω_closed
    calc
      ∑ j, ∫ᶜ z in (Δ j).toPath, (f dz) z =
          ∑ j, ∫ᶜ z in (Δ j).toPath, Complex.realScalarOneForm f z := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [Complex.realScalarOneForm] using
              (curveIntegral_restrictScalars
                (γ := (Δ j).toPath) (ω := fun z ↦ (f dz) z) (𝕜 := ℂ) (𝕝 := ℝ)).symm
      _ = 0 := hzero'
  have hsplit :
      ∑ j, ∫ᶜ z in (Δ j).toPath, (f dz) z =
        (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) -
          Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
    -- The explicit boundary family has the outer pieces with positive sign and the inner circles
    -- with reversed orientation.
    simpa [Δ] using sum_curveIntegral_finite_excision_boundary_family
      (Γ := Γ) (f := f) (s := s) (ρ := ρ)
  -- After rewriting the punctured boundary sum, the zero theorem gives the desired comparison.
  rw [hsplit] at hzero
  exact sub_eq_zero.mp hzero

/-- Cartan section11 0003_Theorem_III_5_extra_2.
Theorem III.5-extra-2 (2): source-form residue theorem for an oriented boundary, stated with
explicit isolated local residue data at the finitely many interior singularities enclosed by the
boundary. -/
theorem orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
    {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ}
    (s : Finset ℂ) (residue : ℂ → ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D)
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ)))
    (hres : ∀ z ∈ s, IsolatedLocalResidueCircle K D s f z (residue z)) :
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
      (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
  classical
  let _ := hKD
  choose ρ₀ hρ₀pos hρ₀K hρ₀D hρ₀avoid hρ₀diff hρ₀sep hρ₀circle using
    fun z : s ↦
      exists_half_radius_isolated_local_residue_circle hD hhol z.2 (hres z.1 z.2)
  let ρ : ℂ → ℝ := fun z ↦ if hz : z ∈ s then ρ₀ ⟨z, hz⟩ else 0
  have hρpos : ∀ z ∈ s, 0 < ρ z := by
    intro z hz
    simp [ρ, hz, hρ₀pos]
  have hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K := by
    intro z hz
    simpa [ρ, hz] using hρ₀K ⟨z, hz⟩
  have hρD : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ D := by
    intro z hz
    simpa [ρ, hz] using hρ₀D ⟨z, hz⟩
  have hρsep :
      ∀ z ∈ s, ∀ w ∈ s, w ≠ z → ρ z + ρ w < dist z w := by
    intro z hz w hw hwz
    have hzlt : 2 * ρ z < dist z w := by
      simpa [ρ, hz] using hρ₀sep ⟨z, hz⟩ w hw hwz
    have hwlt : 2 * ρ w < dist z w := by
      have hwlt' : 2 * ρ₀ ⟨w, hw⟩ < dist w z :=
        hρ₀sep ⟨w, hw⟩ z hz hwz.symm
      simpa [ρ, hw, dist_comm] using hwlt'
    linarith
  have hpair :
      ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
        Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)) :=
    pairwise_disjoint_closedBall_of_radius_separation
      (fun z hz ↦ (hρpos z hz).le) hρsep
  have hboundary :
      ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
        Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) :=
    orientedBoundary_sum_curveIntegral_eq_sum_small_circle_integrals
      Γ s ρ hΓ hKD hD hρpos hρK hρD hpair hhol
  -- Route correction: the local residue circles are now normalized first; only the finite-excision
  -- geometry remains hidden behind the structural comparison lemma above.
  calc
    ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z = Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := hboundary
    _ = Finset.sum s (fun z ↦ (2 * Real.pi * Complex.I : ℂ) * residue z) := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      simpa [ρ, hz] using hρ₀circle ⟨z, hz⟩
    _ = (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
      simpa using (Finset.mul_sum s residue (2 * Real.pi * Complex.I : ℂ)).symm

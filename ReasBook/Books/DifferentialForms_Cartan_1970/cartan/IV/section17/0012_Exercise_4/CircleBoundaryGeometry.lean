import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»

open Filter InnerProductSpace Laplacian Metric Real Set Topology
open scoped BigOperators InnerProductSpace
/-- Helper for Exercise 4: varying the radius in `circleMap` differentiates to the fixed unit
complex direction at angle `θ`. -/
lemma hasDerivAt_circleMap_radius (a : ℂ) (θ s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ circleMap a t θ) (Complex.exp (θ * Complex.I)) s := by
  -- Freeze the angle and differentiate the affine radius parameterization directly.
  simpa [circleMap, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using
    (HasDerivAt.comp_ofReal
      (((hasDerivAt_id (x := (s : ℂ))).mul_const (Complex.exp (θ * Complex.I))).const_add a))

/-- Helper for Exercise 4: the derivative of the radius-parameter circle map is the fixed unit
complex direction. -/
lemma deriv_circleMap_radius (a : ℂ) (θ s : ℝ) :
    deriv (fun t : ℝ ↦ circleMap a t θ) s = Complex.exp (θ * Complex.I) := by
  -- This is the derivative extracted from the explicit affine radius parametrization.
  exact (hasDerivAt_circleMap_radius a θ s).deriv

/-- Helper for Exercise 4: the real part of `circleMap a r θ` is the expected polar-coordinate
expression. -/
lemma circleMap_re_radius (a : ℂ) (r θ : ℝ) :
    (circleMap a r θ).re = a.re + r * Real.cos θ := by
  -- Expand the circle map and read off its real part.
  rw [circleMap, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  simp [Complex.exp_ofReal_mul_I_re]

/-- Helper for Exercise 4: the imaginary part of `circleMap a r θ` is the expected
polar-coordinate expression. -/
lemma circleMap_im_radius (a : ℂ) (r θ : ℝ) :
    (circleMap a r θ).im = a.im + r * Real.sin θ := by
  -- Expand the circle map and read off its imaginary part.
  rw [circleMap, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  simp [Complex.exp_ofReal_mul_I_im]

/-- Helper for Exercise 4: the positive boundary circle of the closed disc centered at `a` with
radius `r`, parametrized on the unit interval. -/
noncomputable def positive_circle_path (a : ℂ) (r : ℝ) : Path (a + r) (a + r) :=
  Path.mk
    ⟨fun t ↦ circleMap a r (2 * Real.pi * (t : ℝ)), by
      fun_prop⟩
    (by
      -- At `t = 0`, the boundary path starts at the positive real boundary point.
      simp [circleMap])
    (by
      -- At `t = 1`, the angle is `2π`, so the path closes up again.
      simp [circleMap, Complex.exp_two_pi_mul_I])

/-- Helper for Exercise 4: the positive boundary circle has image exactly the geometric sphere
`Metric.sphere a r`. -/
lemma range_positive_circle_path_eq_sphere {a : ℂ} {r : ℝ} (hr : 0 < r) :
    Set.range (positive_circle_path a r) = Metric.sphere a r := by
  -- Every path value lies on the circle, and every circle point occurs at some angle in `(0, 2π]`.
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simpa [positive_circle_path, abs_of_pos hr] using
      circleMap_mem_sphere' a r (2 * Real.pi * (t : ℝ))
  · intro hz
    have hz' : z ∈ Metric.sphere a |r| := by
      simpa [abs_of_pos hr] using hz
    rw [← image_circleMap_Ioc a r] at hz'
    rcases hz' with ⟨θ, hθ, rfl⟩
    refine ⟨⟨θ / (2 * Real.pi), ?_, ?_⟩, ?_⟩
    · exact div_nonneg hθ.1.le (by positivity)
    · exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by simpa using hθ.2)
    · have hscale : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
        field_simp [Real.pi_ne_zero]
      simp [positive_circle_path, hscale]

/-- Helper for Exercise 4: on the unit interval, the positive boundary loop is the standard
counterclockwise `circleMap`. -/
lemma positive_circle_path_extend_eq_circleMap {a : ℂ} {r t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (positive_circle_path a r).extend t = circleMap a r (2 * Real.pi * t) := by
  -- Inside the unit interval, `Path.extend` is evaluation of the original circle path.
  simpa [positive_circle_path] using
    (Path.extend_apply (γ := positive_circle_path a r) ht)

/-- Helper for Exercise 4: converting a loop path to a closed path and back only inserts the
endpoint cast forced by the oriented-boundary API. -/
lemma toClosedPath_toPath_eq_cast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath =
      γ.cast (by simpa [Path.toClosedPath] using γ.source)
        (by simpa [Path.toClosedPath] using γ.source) := by
  -- After destructing the loop, the closed-path wrapper and its unpacking are definitionally the
  -- same path up to the endpoint cast.
  cases γ
  rfl

/-- Helper for Exercise 4: the real-curve parametrization of a loop closed path is the original
path extension in real coordinates. -/
lemma toClosedPath_realCurve_eq {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.realCurve = Complex.equivRealProd ∘ γ.extend := by
  -- `ClosedPath.realCurve` only differs from the original loop by the harmless endpoint cast.
  cases γ
  rfl

/-- Helper for Exercise 4: the positive boundary circle is globally `C¹`, hence piecewise
differentiable. -/
lemma positive_circle_path_isPiecewiseDifferentiable (a : ℂ) (r : ℝ) :
    (positive_circle_path a r).IsPiecewiseDifferentiable := by
  -- The counterclockwise circle is a single smooth parametrized arc on the whole unit interval.
  have hdiff : (positive_circle_path a r).IsDifferentiable := by
    rw [Path.IsDifferentiable]
    let g : ℝ → ℂ := fun t ↦ circleMap a r (2 * Real.pi * t)
    have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ 2 * Real.pi * t) := by
      simpa [one_mul] using (contDiff_const.mul contDiff_id)
    have hg : ContDiff ℝ 1 g := by
      simpa [g] using (contDiff_circleMap a r).comp hlin
    refine hg.contDiffOn.congr ?_
    intro t ht
    simpa [g] using positive_circle_path_extend_eq_circleMap (a := a) (r := r) (t := t) ht
  exact hdiff.isPiecewiseDifferentiable

/-- Helper for Exercise 4: the positive circle only identifies equal parameters or the two
endpoints of the unit interval. -/
lemma positive_circle_path_simple_eq_or_endpoints {a : ℂ} {r : ℝ} (hr : r ≠ 0)
    {s t : Set.Icc (0 : ℝ) 1} (h : positive_circle_path a r s = positive_circle_path a r t) :
    s = t ∨ ((s : ℝ) = 0 ∧ (t : ℝ) = 1) ∨ ((s : ℝ) = 1 ∧ (t : ℝ) = 0) := by
  let α : ℝ := 2 * Real.pi * (s : ℝ)
  let β : ℝ := 2 * Real.pi * (t : ℝ)
  have hcircle : circleMap a r α = circleMap a r β := by
    simpa [positive_circle_path, α, β] using h
  have hlen : |(0 : ℝ) - 2 * Real.pi| ≤ 2 * Real.pi := by
    simpa [abs_of_nonneg Real.two_pi_pos.le]
  have hinj :=
    injOn_circleMap_of_abs_sub_le (c := a) (R := r) (a := (0 : ℝ)) (b := 2 * Real.pi) hr hlen
  by_cases hs0 : (s : ℝ) = 0
  · by_cases ht0 : (t : ℝ) = 0
    · exact Or.inl (Subtype.ext (hs0.trans ht0.symm))
    · have htpos : 0 < (t : ℝ) := by
        exact lt_of_le_of_ne t.2.1 (by
          intro htEq
          exact ht0 htEq.symm)
      have hβmem : β ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [β]
          nlinarith [Real.two_pi_pos, htpos]
        · dsimp [β]
          nlinarith [Real.two_pi_pos, t.2.2]
      have h2πmem : (2 * Real.pi : ℝ) ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · nlinarith [Real.pi_pos]
        · exact le_rfl
      have hβ2π : circleMap a r β = circleMap a r (2 * Real.pi) := by
        calc
          circleMap a r β = circleMap a r 0 := by
            simpa [α, hs0] using hcircle.symm
          _ = circleMap a r (2 * Real.pi) := by
            simp [circleMap, Complex.exp_two_pi_mul_I]
      have hβeq : β = 2 * Real.pi := hinj hβmem h2πmem hβ2π
      have ht1 : (t : ℝ) = 1 := by
        dsimp [β] at hβeq
        nlinarith [Real.two_pi_pos, hβeq]
      right
      left
      exact ⟨hs0, ht1⟩
  · by_cases ht0 : (t : ℝ) = 0
    · have hspos : 0 < (s : ℝ) := by
        exact lt_of_le_of_ne s.2.1 (by
          intro hsEq
          exact hs0 hsEq.symm)
      have hαmem : α ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [α]
          nlinarith [Real.two_pi_pos, hspos]
        · dsimp [α]
          nlinarith [Real.two_pi_pos, s.2.2]
      have h2πmem : (2 * Real.pi : ℝ) ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · nlinarith [Real.pi_pos]
        · exact le_rfl
      have hα2π : circleMap a r α = circleMap a r (2 * Real.pi) := by
        calc
          circleMap a r α = circleMap a r 0 := by
            simpa [β, ht0] using hcircle
          _ = circleMap a r (2 * Real.pi) := by
            simp [circleMap, Complex.exp_two_pi_mul_I]
      have hαeq : α = 2 * Real.pi := hinj hαmem h2πmem hα2π
      have hs1 : (s : ℝ) = 1 := by
        dsimp [α] at hαeq
        nlinarith [Real.two_pi_pos, hαeq]
      right
      right
      exact ⟨hs1, ht0⟩
    · have hspos : 0 < (s : ℝ) := by
        exact lt_of_le_of_ne s.2.1 (by
          intro hsEq
          exact hs0 hsEq.symm)
      have htpos : 0 < (t : ℝ) := by
        exact lt_of_le_of_ne t.2.1 (by
          intro htEq
          exact ht0 htEq.symm)
      have hαmem : α ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [α]
          nlinarith [Real.two_pi_pos, hspos]
        · dsimp [α]
          nlinarith [Real.two_pi_pos, s.2.2]
      have hβmem : β ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le Real.two_pi_pos.le]
        constructor
        · dsimp [β]
          nlinarith [Real.two_pi_pos, htpos]
        · dsimp [β]
          nlinarith [Real.two_pi_pos, t.2.2]
      have hαeqβ : α = β := hinj hαmem hβmem hcircle
      have hst : (s : ℝ) = (t : ℝ) := by
        dsimp [α, β] at hαeqβ
        nlinarith [Real.two_pi_pos, hαeqβ]
      exact Or.inl (Subtype.ext hst)

/-- Helper for Exercise 4: quarter-turning a complex tangent in real coordinates is multiplication
by `I` before converting back to `Plane`. -/
lemma rot90_equivRealProd_eq_equivRealProd_mul_I (z : ℂ) :
    rot90 (Complex.equivRealProd z) = Complex.equivRealProd (z * Complex.I) := by
  -- `Complex.equivRealProd` identifies multiplication by `I` with the standard quarter-turn.
  ext <;> simp [rot90, Complex.equivRealProd]

/-- Helper for Exercise 4: a radial tube around a `C¹` curve has the expected derivative columns. -/
lemma radial_tube_hasFDerivAt {γ n : ℝ → ℂ} {t₀ : ℝ} {v : ℂ}
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

/-- Helper for Exercise 4: rescaling the second plane coordinate by a nonzero real factor is a
continuous linear automorphism. -/
noncomputable def plane_second_rescale (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
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
          intro x p
          ext <;> simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] }
    continuous_toFun := by
      exact continuous_fst.prodMk (continuous_snd.div_const c)
    continuous_invFun := by
      exact continuous_fst.prodMk (continuous_const.mul continuous_snd) }

/-- Helper for Exercise 4: the distance from `a` to a radial exponential point is the absolute
value of its real radial coefficient. -/
lemma dist_add_real_mul_exp_eq_abs {a : ℂ} {s θ : ℝ} :
    dist (a + (s : ℂ) * Complex.exp (θ * Complex.I)) a = |s| := by
  -- The exponential factor has norm `1`, so only the real radius contributes to the distance.
  rw [dist_eq_norm]
  calc
    ‖a + (s : ℂ) * Complex.exp (θ * Complex.I) - a‖ =
        ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ := by
          ring_nf
    _ = ‖(s : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := norm_mul _ _
    _ = |s| := by simp [Complex.norm_exp]

/-- Helper for Exercise 4: the positive angular parameter has constant derivative `2π`. -/
lemma positive_circle_arg_hasDerivAt (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ 2 * Real.pi * t) (2 * Real.pi) t₀ := by
  -- The angular variable is the affine function `t ↦ 2π t`.
  simpa [one_mul] using (hasDerivAt_id t₀).const_mul (2 * Real.pi)

/-- Helper for Exercise 4: quarter-turning the positive circle tangent yields the inward radial
direction scaled by `2πr`. -/
lemma positive_circle_rot90_tangent_eq_scaled_inward {r : ℝ} {t₀ : ℝ} :
    rot90
      (Complex.equivRealProd
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I *
          Complex.exp ((2 * Real.pi * t₀) * Complex.I))) =
      (2 * Real.pi * r) •
        Complex.equivRealProd (-Complex.exp ((2 * Real.pi * t₀) * Complex.I)) := by
  -- Multiplication by `I` turns the tangent into the inward radial direction.
  rw [rot90_equivRealProd_eq_equivRealProd_mul_I]
  have hz :
      (((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) * Complex.I =
        ((2 * Real.pi * r) : ℝ) • (-Complex.exp ((2 * Real.pi * t₀) * Complex.I)) := by
    calc
      (((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) * Complex.I =
          ((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) * (Complex.I * Complex.I) := by
              ring
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) * (-1) := by
            simp
      _ = -((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((2 * Real.pi * t₀) * Complex.I)) := by
            ring
      _ = ((2 * Real.pi * r) : ℝ) • (-Complex.exp ((2 * Real.pi * t₀) * Complex.I)) := by
            simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  simpa using congrArg Complex.equivRealProd hz

/-- Helper for Exercise 4: the positive circle admits a local boundary straightening chart for the
closed disc it bounds. -/
lemma positive_circle_exists_boundary_chart_closedBall {a : ℂ} {r : ℝ} (hr : 0 < r)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((positive_circle_path a r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (hderiv :
      derivWithin ((positive_circle_path a r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (Metric.closedBall a r)
        ((positive_circle_path a r).toClosedPath.realCurve) t₀ δ := by
  let θ : ℝ → ℝ := fun t ↦ 2 * Real.pi * t
  let γ : ℝ → ℂ := fun t ↦ circleMap a r (θ t)
  let n : ℝ → ℂ := fun t ↦ -Complex.exp (θ t * Complex.I)
  let tangent : ℂ := (2 * Real.pi : ℝ) • (circleMap 0 r (θ t₀) * Complex.I)
  let Ψ : Plane → ℂ := fun p ↦ γ p.1 + p.2 • n p.1
  let Φ : Plane → Plane := fun p ↦ Complex.equivRealProd (Ψ p)
  have _hkeep_regular :
      DifferentiableWithinAt ℝ ((positive_circle_path a r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ := hdiff
  have _hkeep_nonzero :
      derivWithin ((positive_circle_path a r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0 := hderiv
  have hθCont : ContDiffAt ℝ 1 θ t₀ := by
    -- The angular parameter is affine.
    have hθ : ContDiff ℝ 1 θ := by
      simpa [θ, one_mul] using (contDiff_const.mul contDiff_id)
    exact hθ.contDiffAt
  have hγCont : ContDiffAt ℝ 1 γ t₀ := by
    -- The boundary branch is smooth after composing `circleMap` with the affine angle.
    simpa [γ] using (contDiff_circleMap a r).contDiffAt.comp t₀ hθCont
  have hnCont : ContDiffAt ℝ 1 n t₀ := by
    -- The inward radial unit field is also smooth along the circle.
    have hθComplex : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ)) t₀ := by
      simpa using (Complex.ofRealCLM.contDiff.contDiffAt.comp t₀ hθCont)
    have hinner : ContDiffAt ℝ 1 (fun t : ℝ ↦ (θ t : ℂ) * Complex.I) t₀ := by
      simpa [one_mul] using hθComplex.mul contDiffAt_const
    simpa [n] using (Complex.contDiff_exp.contDiffAt.comp t₀ hinner).neg
  have hγDeriv : HasDerivAt γ tangent t₀ := by
    -- Differentiate the counterclockwise circle explicitly by the chain rule.
    simpa [γ, tangent] using
      ((hasDerivAt_circleMap a r (θ t₀)).scomp t₀ (positive_circle_arg_hasDerivAt t₀))
  have htangent_formula :
      tangent = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
        Complex.exp (θ t₀ * Complex.I) := by
    -- Rewrite the chain-rule derivative into the explicit tangent form used by the frame lemma.
    calc
      tangent = ((2 * Real.pi : ℝ) : ℂ) * (circleMap 0 r (θ t₀) * Complex.I) := by
        simp [tangent, smul_eq_mul]
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
          Complex.exp (θ t₀ * Complex.I) := by
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
    -- The circle tangent never vanishes when the radius is positive.
    intro hv0
    have htangent : tangent = 0 := by
      exact Complex.equivRealProd.injective (by simpa [v] using hv0)
    have hscale : ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      exact_mod_cast mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hr.ne'
    have hmul :
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
          Complex.exp (θ t₀ * Complex.I) = 0 := by
      simpa [htangent_formula] using htangent
    exact Complex.exp_ne_zero (θ t₀ * Complex.I) ((mul_eq_zero.mp hmul).resolve_left hscale)
  have hrot : rot90 v = (2 * Real.pi * r) • radial := by
    -- Quarter-turning the tangent gives the inward normal because the orientation is positive.
    simpa [v, radial, n, θ, htangent_formula, mul_assoc, mul_left_comm, mul_comm] using
      positive_circle_rot90_tangent_eq_scaled_inward (r := r) (t₀ := t₀)
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
    -- Convert the complex derivative columns into the corresponding real-plane columns.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨x, y⟩
    simp [ContinuousLinearMap.comp_apply, v, radial, ContinuousLinearMap.smulRight_apply]
  have hΦderiv :
      HasFDerivAt Φ
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial)
        (t₀, 0) := by
    -- The real-plane tube has tangent column `v` and inward normal column `radial`.
    simpa [Φ, hderiv_map] using
      ((Complex.equivRealProdCLM : ℂ ≃L[ℝ] Plane).comp_hasFDerivAt_iff).2 hΨderiv
  have he : (e : Plane →L[ℝ] Plane) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight radial := by
    -- Rescaling the second frame coordinate turns the `rot90` column into the actual inward normal.
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
    -- This is the invertible derivative needed by the inverse function theorem.
    simpa [he] using hΦderiv
  let δ₀ : OpenPartialHomeomorph Plane Plane :=
    hΦcont.toOpenPartialHomeomorph Φ hΦderiv' one_ne_zero
  let δ₁ : OpenPartialHomeomorph Plane Plane := δ₀.restrContDiff ℝ 1 (by norm_num)
  let strip : Set Plane := Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-r) r
  let δ : OpenPartialHomeomorph Plane Plane := δ₁.restrOpen strip (isOpen_Ioo.prod isOpen_Ioo)
  have hδ₀_source : (t₀, 0) ∈ δ₀.source := by
    -- The inverse function theorem keeps the base point in the chart source.
    exact hΦcont.mem_toOpenPartialHomeomorph_source hΦderiv' one_ne_zero
  have hδ₀_symm : ContDiffAt ℝ 1 δ₀.symm (Φ (t₀, 0)) := by
    -- The local inverse is `C¹` at the image of the base point.
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
  · -- The base point lies in the strip because `t₀ ∈ (0,1)` and `0 ∈ (-r, r)`.
    have hstrip : (t₀, 0) ∈ strip := by
      refine ⟨ht₀, ?_⟩
      constructor <;> linarith
    simpa [δ, strip] using And.intro hδ₁_source hstrip
  · -- Any point of the chart source lies over the open parameter strip around the circle.
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
    -- Along the horizontal axis, the chart reproduces the positive boundary circle.
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htStrip.1.1.le, htStrip.1.2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd ((positive_circle_path a r).extend t) := by
        congr 1
        simpa [γ, θ] using
          (positive_circle_path_extend_eq_circleMap (a := a) (r := r) (t := t) htIcc).symm
      _ = ((positive_circle_path a r).toClosedPath).realCurve t := by
        simpa [toClosedPath_realCurve_eq]
  · -- The chart image of the boundary branch is exactly the horizontal axis.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htSource : (t, 0) ∈ δ.source := ht
    have htStrip : (t, 0) ∈ strip := by
      exact (show (t, 0) ∈ δ₁.source ∩ strip by simpa [δ, strip] using htSource).2
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htStrip.1.1.le, htStrip.1.2.le⟩
    calc
      δ (t, 0) = Complex.equivRealProd (γ t) := by
        simp [δ, δ₁, δ₀, Φ, Ψ]
      _ = Complex.equivRealProd ((positive_circle_path a r).extend t) := by
        congr 1
        simpa [γ, θ] using
          (positive_circle_path_extend_eq_circleMap (a := a) (r := r) (t := t) htIcc).symm
      _ = ((positive_circle_path a r).toClosedPath).realCurve t := by
        simpa [toClosedPath_realCurve_eq]
  · -- Negative transverse parameters move strictly outside the closed disc.
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp.1
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          a + ((r - p.2 : ℝ) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
          rw [Complex.equivRealProdCLM_symm_apply]
          exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
          simp [Ψ]
        _ = a + ((r - p.2 : ℝ) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
          simp [γ, n, θ, circleMap, smul_eq_mul]
          ring
    have houtside :
        Complex.equivRealProdCLM.symm (δ p) ∉ Metric.closedBall a r := by
      intro hzBall
      have hle : dist (Complex.equivRealProdCLM.symm (δ p)) a ≤ r := by
        simpa [Metric.mem_closedBall] using hzBall
      have hp_le_r : p.2 ≤ r := by
        exact le_of_lt (lt_trans hp.2 hr)
      have hrad_nonneg : 0 ≤ r - p.2 := by
        exact sub_nonneg.mpr hp_le_r
      rw [hformula, dist_add_real_mul_exp_eq_abs, abs_of_nonneg hrad_nonneg] at hle
      have hrad_gt : r < r - p.2 := by
        simpa [sub_eq_add_neg] using add_lt_add_left (neg_pos.mpr hp.2) r
      exact (not_lt_of_ge hle) hrad_gt
    exact houtside hz.2
  · intro z hz
    -- Positive transverse parameters move strictly inside the open disc, hence into the interior.
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hp' : p ∈ δ₁.source ∩ strip := by
      simpa [δ, strip] using hp.1
    have hformula :
        Complex.equivRealProdCLM.symm (δ p) =
          a + ((r - p.2 : ℝ) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
      calc
        Complex.equivRealProdCLM.symm (δ p) = Complex.equivRealProdCLM.symm (Φ p) := by
          simp [δ, δ₁, δ₀]
        _ = Ψ p := by
          rw [Complex.equivRealProdCLM_symm_apply]
          exact Complex.re_add_im (Ψ p)
        _ = γ p.1 + p.2 • n p.1 := by
          simp [Ψ]
        _ = a + ((r - p.2 : ℝ) : ℂ) * Complex.exp (θ p.1 * Complex.I) := by
          simp [γ, n, θ, circleMap, smul_eq_mul]
          ring
    have hrad_nonneg : 0 ≤ r - p.2 := by
      exact sub_nonneg.mpr (le_of_lt hp'.2.2.2)
    have hball :
        Complex.equivRealProdCLM.symm (δ p) ∈ Metric.ball a r := by
      rw [hformula, Metric.mem_ball, dist_add_real_mul_exp_eq_abs, abs_of_nonneg hrad_nonneg]
      have hrad_lt : r - p.2 < r := by
        exact sub_lt_self _ hp.2
      simpa using hrad_lt
    simpa [interior_closedBall a hr.ne'] using hball

/-- Helper for Exercise 4: the positive boundary circle is an oriented boundary of the closed disc
it bounds. -/
lemma closedBallBoundary_isOrientedBoundaryOf {a : ℂ} {r : ℝ} (hr : 0 < r) :
    IsOrientedBoundaryOf (Metric.closedBall a r)
      (fun _ : Unit ↦ (positive_circle_path a r).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (positive_circle_path a r).toClosedPath
  change IsOrientedBoundaryOf (Metric.closedBall a r) Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- The closed disc is compact.
    simpa using isCompact_closedBall a r
  · rintro ⟨⟩
    -- The singleton loop inherits piecewise differentiability from the explicit circle path.
    simpa [Γ, Path.toClosedPath] using positive_circle_path_isPiecewiseDifferentiable a r
  · rintro ⟨⟩ s t hst
    -- Simplicity reduces to injectivity of `circleMap` on `(0, 2π]`.
    let zeroI : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
    let oneI : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
    rcases positive_circle_path_simple_eq_or_endpoints (a := a) (r := r) hr.ne' hst with
      hEq | h01 | h10
    · exact Or.inl hEq
    · have hs0 : s = zeroI := Subtype.ext h01.1
      have ht1 : t = oneI := Subtype.ext h01.2
      right
      left
      simpa [zeroI, oneI, hs0, ht1]
    · have hs1 : s = oneI := Subtype.ext h10.1
      have ht0 : t = zeroI := Subtype.ext h10.2
      right
      right
      simpa [zeroI, oneI, hs1, ht0]
  · intro i j hij
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i, Set.range ((Γ i : ClosedPath ℂ) : C(Set.Icc (0 : ℝ) 1, ℂ))) =
          Set.range (positive_circle_path a r) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        cases i
        simpa [Γ, Path.toClosedPath] using hi
      · intro hx
        refine Set.mem_iUnion.mpr ?_
        refine ⟨(), ?_⟩
        simpa [Γ, Path.toClosedPath] using hx
    -- Rewrite the singleton union to the circle image, then identify it with the frontier sphere.
    simpa [ClosedPath.range_toPath, frontier_closedBall a hr.ne'] using
      hboundary.trans (range_positive_circle_path_eq_sphere (a := a) hr)
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- The explicit radial tube chart supplies the local oriented-boundary model.
    exact positive_circle_exists_boundary_chart_closedBall (a := a) (r := r) hr ht₀ hdiff hderiv

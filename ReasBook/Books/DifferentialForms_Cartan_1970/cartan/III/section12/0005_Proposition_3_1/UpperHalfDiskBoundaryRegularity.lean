import DifferentialForms_Cartan_1970.cartan.III.section12.«0005_Proposition_3_1».UpperHalfDiskBoundaryPath

noncomputable section

open Filter
open MeasureTheory
open UpperHalfPlane
open scoped BigOperators Interval Topology

section

variable {f : ℂ → ℂ} {s : Finset ℂ}

/-- Helper for Proposition 3.1: quarter-turning a complex tangent in real coordinates is
multiplication by `I` before converting back to `Plane`. -/
lemma upper_half_disk_rot90_equivRealProd_eq_equivRealProd_mul_I (z : ℂ) :
    rot90 (Complex.equivRealProd z) = Complex.equivRealProd (z * Complex.I) := by
  -- `Complex.equivRealProd` identifies multiplication by `I` with the standard quarter-turn.
  ext <;> simp [rot90, Complex.equivRealProd]

/-- Helper for Proposition 3.1: a tube map around a `C¹` branch has the expected tangent and
transverse derivative columns at the base point. -/
lemma upper_half_disk_radial_tube_hasFDerivAt {γ n : ℝ → ℂ} {t₀ : ℝ} {v : ℂ}
    (hγCont : ContDiffAt ℝ 1 γ t₀) (hγDeriv : HasDerivAt γ v t₀)
    (hnCont : ContDiffAt ℝ 1 n t₀) :
    ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1 + p.2 • n p.1) (t₀, 0) ∧
      HasFDerivAt (fun p : Plane ↦ γ p.1 + p.2 • n p.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (n t₀))
        (t₀, 0) := by
  constructor
  · -- The tube map is the sum of the branch and the varying transverse direction.
    have hγfst : ContDiffAt ℝ 1 (fun p : Plane ↦ γ p.1) (t₀, 0) := by
      simpa using hγCont.comp (x := (t₀, 0)) contDiffAt_fst
    have hnfst : ContDiffAt ℝ 1 (fun p : Plane ↦ n p.1) (t₀, 0) := by
      simpa using hnCont.comp (x := (t₀, 0)) contDiffAt_fst
    simpa using hγfst.add (contDiffAt_snd.smul hnfst)
  · -- At `p.2 = 0`, the transverse derivative contributes only the actual normal vector.
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

/-- Helper for Proposition 3.1: rescaling the second plane coordinate by a nonzero real factor is
a continuous linear automorphism. -/
noncomputable def upper_half_disk_plane_second_rescale (c : ℝ) (hc : c ≠ 0) : Plane ≃L[ℝ] Plane :=
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

/-- Helper for Proposition 3.1: the distance from `a` to a radial exponential point is the
absolute value of its real radial coefficient. -/
lemma upper_half_disk_dist_add_real_mul_exp_eq_abs {a : ℂ} {s θ : ℝ} :
    dist (a + (s : ℂ) * Complex.exp (θ * Complex.I)) a = |s| := by
  -- The exponential factor has norm `1`, so only the real radius contributes to the distance.
  rw [dist_eq_norm]
  calc
    ‖a + (s : ℂ) * Complex.exp (θ * Complex.I) - a‖ =
        ‖(s : ℂ) * Complex.exp (θ * Complex.I)‖ := by
          ring_nf
    _ = ‖(s : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := norm_mul _ _
    _ = |s| := by simp [Complex.norm_exp]

/-- Helper for Proposition 3.1: the affine angle parameter on the upper-semicircle branch has
constant derivative `2π`. -/
lemma upper_half_disk_arc_arg_hasDerivAt (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.pi * (2 * t - 1)) (2 * Real.pi) t₀ := by
  -- The branch angle is an affine reparametrization of the standard semicircle angle.
  simpa [sub_eq_add_neg, mul_add, add_mul, two_mul, mul_assoc, mul_left_comm, mul_comm] using
    ((((hasDerivAt_id t₀).const_mul 2).sub_const 1).const_mul Real.pi)

/-- Helper for Proposition 3.1: quarter-turning the upper-semicircle tangent yields the inward
radial direction scaled by `2πr`. -/
lemma upper_half_disk_arc_rot90_tangent_eq_scaled_inward {r t₀ : ℝ} :
    rot90
      (Complex.equivRealProd
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I *
          Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I))) =
      (2 * Real.pi * r) •
        Complex.equivRealProd (-Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) := by
  -- Multiplication by `I` turns the tangent into the inward radial direction.
  rw [upper_half_disk_rot90_equivRealProd_eq_equivRealProd_mul_I]
  have hz :
      (((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) * Complex.I =
        ((2 * Real.pi * r) : ℝ) • (-Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) := by
    calc
      (((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) * Complex.I =
          ((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) * (Complex.I * Complex.I) := by
              ring
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) * (-1) := by
            simp
      _ = -((((2 * Real.pi * r : ℝ)) : ℂ) *
            Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) := by
            ring
      _ = ((2 * Real.pi * r) : ℝ) •
            (-Complex.exp ((Real.pi * (2 * t₀ - 1)) * Complex.I)) := by
            simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  simpa using congrArg Complex.equivRealProd hz

/-- Helper for Proposition 3.1: the diameter model has tangent `4r` at the diameter/arc junction
parameter `1 / 2`. -/
lemma upper_half_disk_boundary_diameter_hasDerivWithinAt_half (r : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ ↦ ((((4 * r) * t - r : ℝ)) : ℂ))
      (((4 * r : ℝ)) : ℂ)
      (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  -- The diameter branch is an affine real-to-complex map.
  have hreal :
      HasDerivAt (fun t : ℝ ↦ (4 * r) * t - r) (4 * r) (1 / 2 : ℝ) := by
    simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id (1 / 2 : ℝ)).const_mul (4 * r)).sub_const r)
  have hmodel :
      HasDerivAt (fun t : ℝ ↦ ((((4 * r) * t - r : ℝ)) : ℂ))
        (((4 * r : ℝ)) : ℂ) (1 / 2 : ℝ) := by
    simpa using hreal.ofReal_comp
  exact hmodel.hasDerivWithinAt

/-- Helper for Proposition 3.1: the upper-semicircle model has tangent `2πri` at the
diameter/arc junction parameter `1 / 2`. -/
lemma upper_half_disk_boundary_arc_hasDerivWithinAt_half (r : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ ↦ circleMap 0 r (Real.pi * (2 * t - 1)))
      ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I)
      (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
  -- Compose `circleMap` with the affine angle and then simplify the angle value `θ(1/2) = 0`.
  have hderivComp :
      HasDerivAt
        ((circleMap 0 r) ∘ fun t : ℝ ↦ Real.pi * (2 * t - 1))
        ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) (1 / 2 : ℝ) := by
    simpa [circleMap_zero, mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_circleMap 0 r (Real.pi * (2 * (1 / 2 : ℝ) - 1))).scomp (1 / 2 : ℝ)
        (upper_half_disk_arc_arg_hasDerivAt (1 / 2 : ℝ)))
  -- The ordinary derivative immediately restricts to the branch interval.
  simpa [Function.comp] using hderivComp.hasDerivWithinAt

/-- Helper for Proposition 3.1: the midpoint parameter is a genuine corner of the semidisk
boundary, so the closed-path real curve is not differentiable there within `[0, 1]`. -/
lemma upper_half_disk_boundary_not_differentiable_at_half
    {r : ℝ} (hr : 0 < r) :
    ¬ DifferentiableWithinAt ℝ ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
  -- Route correction: compare the diameter and upper-semicircle tangents at the shared parameter,
  -- then use uniqueness of within-derivatives on the two closed branch intervals.
  intro hdiff
  let γ : ℝ → ℂ := (upperHalfDiskBoundaryPath r).extend
  let d : ℂ := derivWithin γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ)
  let diameter : ℝ → ℂ := fun t ↦ ((((4 * r) * t - r : ℝ)) : ℂ)
  let arc : ℝ → ℂ := fun t ↦ circleMap 0 r (Real.pi * (2 * t - 1))
  have hγdiff : DifferentiableWithinAt ℝ γ (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    -- Undo the `Complex.equivRealProd` wrapper so the tangent comparison happens in `ℂ`.
    simpa [γ, toClosedPath_realCurve_eq, Function.comp] using
      (Complex.equivRealProdCLM.comp_differentiableWithinAt_iff.mp hdiff)
  have hmain : HasDerivWithinAt γ d (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) := by
    simpa [d, γ] using hγdiff.hasDerivWithinAt
  have hdiamMain :
      HasDerivWithinAt γ d (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the ambient derivative to the diameter branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · exact ht.1
    · linarith [ht.2]
  have harcMain :
      HasDerivWithinAt γ d (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Restrict the same derivative to the semicircle branch interval.
    apply hmain.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · exact ht.2
  have hdiamγ :
      HasDerivWithinAt γ ((((4 * r : ℝ)) : ℂ))
        (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    -- Transfer the explicit affine derivative to the original contour on the diameter branch.
    exact (upper_half_disk_boundary_diameter_hasDerivWithinAt_half r).congr_of_mem
      (fun t ht ↦ by
        have hI : t ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · exact ht.1
          · linarith [ht.2]
        let tI : Set.Icc (0 : ℝ) 1 := ⟨t, hI⟩
        calc
          γ t = upperHalfDiskBoundaryPath r tI := by
            simpa [γ, tI] using (Path.extend_apply (γ := upperHalfDiskBoundaryPath r) hI)
          _ = diameter t := by
            simpa [diameter, tI] using
              upper_half_disk_boundary_eq_diameter_of_le_half r (t := tI) ht.2)
      (by constructor <;> norm_num)
  have harcγ :
      HasDerivWithinAt γ ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I)
        (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
    -- Transfer the explicit circular derivative to the original contour on the arc branch.
    exact (upper_half_disk_boundary_arc_hasDerivWithinAt_half r).congr_of_mem
      (fun t ht ↦ by
        have hI : t ∈ Set.Icc (0 : ℝ) 1 := by
          constructor
          · linarith [ht.1]
          · exact ht.2
        let tI : Set.Icc (0 : ℝ) 1 := ⟨t, hI⟩
        calc
          γ t = upperHalfDiskBoundaryPath r tI := by
            simpa [γ, tI] using (Path.extend_apply (γ := upperHalfDiskBoundaryPath r) hI)
          _ = arc t := by
            simpa [arc, tI] using
              upper_half_disk_boundary_eq_arc_of_half_le r (t := tI) ht.1)
      (by constructor <;> norm_num)
  have hdiamUD :
      UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 / 2 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have harcUD :
      UniqueDiffWithinAt ℝ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) :=
    (uniqueDiffOn_Icc (show (1 / 2 : ℝ) < 1 by norm_num)).uniqueDiffWithinAt
      (by constructor <;> norm_num)
  have hcompare :
      ((((4 * r : ℝ)) : ℂ)) = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) := by
    -- Uniqueness of within-derivatives forces the two branch tangents to agree.
    calc
      ((((4 * r : ℝ)) : ℂ))
          = derivWithin γ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
              symm
              exact hdiamγ.derivWithin hdiamUD
      _ = d := hdiamMain.derivWithin hdiamUD
      _ = derivWithin γ (Set.Icc (1 / 2 : ℝ) (1 : ℝ)) (1 / 2 : ℝ) := by
            symm
            exact harcMain.derivWithin harcUD
      _ = ((((2 * Real.pi * r : ℝ)) : ℂ) * Complex.I) := harcγ.derivWithin harcUD
  have him_eq : (0 : ℝ) = 2 * Real.pi * r := by
    simpa using congrArg Complex.im hcompare
  nlinarith [hr, Real.pi_pos]

/-- Helper for Proposition 3.1: every regular interior parameter of the semidisk boundary lies on
exactly one of the two smooth open branches. -/
lemma upper_half_disk_boundary_regular_parameter_mem_branch
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((upperHalfDiskBoundaryPath r).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨ t₀ ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  -- Exclude the corner parameter `1 / 2`, then dispatch by order on the interval.
  by_cases ht_half : t₀ < 1 / 2
  · exact Or.inl ⟨ht₀.1, ht_half⟩
  · have hne : t₀ ≠ 1 / 2 := by
      intro ht_eq
      exact (upper_half_disk_boundary_not_differentiable_at_half hr) (by simpa [ht_eq] using hdiff)
    have hgt : 1 / 2 < t₀ := lt_of_le_of_ne (le_of_not_gt ht_half) (Ne.symm hne)
    exact Or.inr ⟨hgt, ht₀.2⟩

/-- Helper for Proposition 3.1: an interior diameter parameter admits a quantitative strip
around the affine branch where positive height enters the semidisk interior and negative height
leaves the owner immediately through the lower half-plane. -/
lemma upper_half_disk_diameter_local_strip_data
    {r t₀ : ℝ} (hr : 0 < r) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ eps_t eps_u, 0 < eps_t ∧ 0 < eps_u ∧
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) ∧
      ∀ {t u : ℝ},
        t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        u ∈ Set.Ioo (-eps_u) eps_u →
        (u < 0 →
          ((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∉
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) ∧
        (0 < u →
          ((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I) ∈
            interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) := by
  let μ : ℝ := min t₀ (1 / 2 - t₀)
  have hμ_pos : 0 < μ := by
    -- The open diameter branch stays a positive distance away from both endpoints.
    exact lt_min ht₀.1 (by linarith [ht₀.2])
  refine ⟨μ / 4, r * μ, by positivity, by positivity, ?_, ?_⟩
  · intro t ht
    constructor
    · -- The chosen `t`-strip remains inside the open diameter parameter interval.
      have hμ_le : μ ≤ t₀ := min_le_left _ _
      have hleft : 0 < t₀ - μ / 4 := by
        nlinarith [hμ_pos, hμ_le]
      exact lt_trans hleft ht.1
    · have hμ_le : μ ≤ 1 / 2 - t₀ := min_le_right _ _
      have hright : t₀ + μ / 4 < 1 / 2 := by
        nlinarith [hμ_pos, hμ_le]
      exact lt_trans ht.2 hright
  · intro t u ht hu
    constructor
    · intro hu_neg hz
      -- Negative height forces a strictly negative imaginary part, so the point is outside.
      have hz_im : 0 ≤
          (((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)).im := hz.2
      exact (not_le_of_gt (by simpa using hu_neg)) (by simpa using hz_im)
    · intro hu_pos
      have ht_abs : |t - t₀| < μ / 4 := by
        -- Recenter the strip at `t₀` so the affine branch estimate can use absolute values.
        refine abs_lt.2 ?_
        constructor <;> linarith [ht.1, ht.2]
      have hu_abs : |u| < r * μ := by
        -- The vertical strip already records the exact height bound we need.
        exact abs_lt.2 ⟨hu.1, hu.2⟩
      have hμ_formula : |4 * t₀ - 1| = 1 - 4 * μ := by
        -- The distance from `t₀` to the midpoint `1 / 4` is exactly encoded by `μ`.
        by_cases hquarter : t₀ ≤ 1 / 4
        · have hquarter' : t₀ ≤ 1 / 2 - t₀ := by
            linarith
          have hμ_eq : μ = t₀ := min_eq_left hquarter'
          have hsign : 4 * t₀ - 1 ≤ 0 := by linarith
          rw [hμ_eq, abs_of_nonpos hsign]
          ring
        · have hquarter' : 1 / 4 < t₀ := lt_of_not_ge hquarter
          have hμ_eq : μ = 1 / 2 - t₀ := by
            apply min_eq_right
            linarith [ht₀.2, hquarter']
          have hsign : 0 ≤ 4 * t₀ - 1 := by linarith
          rw [hμ_eq, abs_of_nonneg hsign]
          ring
      have hx0_abs : |(4 * r) * t₀ - r| = r * (1 - 4 * μ) := by
        -- Rewrite the center point on the diameter as `r * (4 t₀ - 1)`.
        calc
          |(4 * r) * t₀ - r| = |r * (4 * t₀ - 1)| := by ring_nf
          _ = |r| * |4 * t₀ - 1| := by rw [abs_mul]
          _ = r * (1 - 4 * μ) := by rw [abs_of_pos hr, hμ_formula]
      have hxdiff :
          |((4 * r) * t - r) - ((4 * r) * t₀ - r)| < r * μ := by
        -- The diameter branch is affine, so the horizontal displacement is controlled directly by
        -- the `t`-strip width.
        calc
          |((4 * r) * t - r) - ((4 * r) * t₀ - r)| = |(4 * r) * (t - t₀)| := by ring_nf
          _ = |4 * r| * |t - t₀| := by rw [abs_mul]
          _ = (4 * r) * |t - t₀| := by
                rw [abs_of_nonneg (by positivity : 0 ≤ 4 * r)]
          _ < (4 * r) * (μ / 4) := by
                gcongr
          _ = r * μ := by ring
      have hx_abs : |(4 * r) * t - r| < r := by
        -- The horizontal coordinate stays away from the radius bound by a margin larger than the
        -- allowed vertical height.
        calc
          |(4 * r) * t - r|
              = |((4 * r) * t₀ - r) +
                  (((4 * r) * t - r) - ((4 * r) * t₀ - r))| := by ring_nf
          _ ≤ |(4 * r) * t₀ - r| +
                |((4 * r) * t - r) - ((4 * r) * t₀ - r)| := abs_add_le _ _
          _ < r * (1 - 4 * μ) + r * μ := by
                rw [hx0_abs]
                gcongr
          _ < r := by
                nlinarith [hr, hμ_pos]
      have hz_norm :
          ‖((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ < r := by
        have htriangle :
            ‖((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ≤
              |(4 * r) * t - r| + |u| := by
          -- The affine real part and the vertical displacement contribute additively to the norm.
          calc
            ‖((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖
                ≤ ‖(((4 * r) * t - r : ℝ) : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := norm_add_le _ _
            _ = |(4 * r) * t - r| + |u| := by
                  rw [Complex.norm_real, norm_mul]
                  simp
        refine lt_of_le_of_lt htriangle ?_
        calc
          |(4 * r) * t - r| + |u|
              < (r * (1 - 4 * μ) + r * μ) + r * μ := by
                have hx_bound : |(4 * r) * t - r| < r * (1 - 4 * μ) + r * μ := by
                  calc
                    |(4 * r) * t - r|
                        = |((4 * r) * t₀ - r) +
                            (((4 * r) * t - r) - ((4 * r) * t₀ - r))| := by ring_nf
                    _ ≤ |(4 * r) * t₀ - r| +
                          |((4 * r) * t - r) - ((4 * r) * t₀ - r)| := abs_add_le _ _
                    _ < r * (1 - 4 * μ) + r * μ := by
                          rw [hx0_abs]
                          gcongr
                gcongr
          _ < r := by
            nlinarith [hr, hμ_pos]
      have hz_im :
          0 < (((((4 * r) * t - r : ℝ) : ℂ) + (u : ℂ) * Complex.I)).im := by
        -- Positive height is exactly positive imaginary part on this affine strip.
        simpa using hu_pos
      exact mem_interior_upper_half_disk_of_norm_lt_im_pos hz_norm hz_im

/-- Helper for Proposition 3.1: moving a semicircle point by the inward unit normal only changes
the radius, replacing `r` by `r - u`. -/
lemma upper_half_disk_arc_add_real_mul_inward_eq_circleMap_radius_sub
    {r u θ : ℝ} :
    circleMap 0 r θ + (u : ℂ) * (-Complex.exp (θ * Complex.I)) =
      circleMap 0 (r - u) θ := by
  -- Route correction: normalize the radial tube to a pure `circleMap` radius change before any
  -- side-condition estimates.
  rw [circleMap_zero, circleMap_zero]
  calc
    (r : ℂ) * Complex.exp (θ * Complex.I) + (u : ℂ) * (-Complex.exp (θ * Complex.I))
        = (r : ℂ) * Complex.exp (θ * Complex.I) - (u : ℂ) * Complex.exp (θ * Complex.I) := by
            ring
    _ = ((r : ℂ) - (u : ℂ)) * Complex.exp (θ * Complex.I) := by
          ring
    _ = (((r - u : ℝ)) : ℂ) * Complex.exp (θ * Complex.I) := by
          simp

/-- Helper for Proposition 3.1: near any regular point of the upper-semicircle branch, decreasing
the radius exits the closed semidisk while increasing it enters the interior. -/
lemma upper_half_disk_arc_local_strip_data
    {r t₀ : ℝ} (hr : 0 < r) (ht₀ : t₀ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ eps_t eps_u, 0 < eps_t ∧ 0 < eps_u ∧ eps_u < r ∧
      Set.Ioo (t₀ - eps_t) (t₀ + eps_t) ⊆ Set.Ioo (1 / 2 : ℝ) 1 ∧
      ∀ {t u : ℝ},
        t ∈ Set.Ioo (t₀ - eps_t) (t₀ + eps_t) →
        u ∈ Set.Ioo (-eps_u) eps_u →
        (u < 0 →
          circleMap 0 (r - u) (Real.pi * (2 * t - 1)) ∉
            ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) ∧
        (0 < u →
          circleMap 0 (r - u) (Real.pi * (2 * t - 1)) ∈
            interior ({z : ℂ | ‖z‖ ≤ r ∧ 0 ≤ z.im} : Set ℂ)) := by
  let μ : ℝ := min (t₀ - 1 / 2) (1 - t₀)
  have hμ_pos : 0 < μ := by
    -- The regular arc parameter stays a positive distance away from both arc endpoints.
    exact lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  refine ⟨μ / 4, r / 2, by positivity, by positivity, ?_, ?_, ?_⟩
  · -- The chosen radial strip stays strictly inside the positive radius regime.
    nlinarith [hr]
  · intro t ht
    constructor
    · -- The `t`-strip remains on the open arc branch, away from the midpoint corner.
      have hμ_le : μ ≤ t₀ - 1 / 2 := min_le_left _ _
      have hleft : 1 / 2 < t₀ - μ / 4 := by
        nlinarith [hμ_pos, hμ_le]
      exact lt_trans hleft ht.1
    · have hμ_le : μ ≤ 1 - t₀ := min_le_right _ _
      have hright : t₀ + μ / 4 < 1 := by
        nlinarith [hμ_pos, hμ_le]
      exact lt_trans ht.2 hright
  · intro t u ht hu
    have htArc : t ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
      -- First move from the local strip back to the actual arc-branch parameter interval.
      have hstrip_param :
          Set.Ioo (t₀ - μ / 4) (t₀ + μ / 4) ⊆ Set.Ioo (1 / 2 : ℝ) 1 := by
        intro s hs
        constructor
        · have hμ_le : μ ≤ t₀ - 1 / 2 := min_le_left _ _
          have hleft : 1 / 2 < t₀ - μ / 4 := by
            nlinarith [hμ_pos, hμ_le]
          exact lt_trans hleft hs.1
        · have hμ_le : μ ≤ 1 - t₀ := min_le_right _ _
          have hright : t₀ + μ / 4 < 1 := by
            nlinarith [hμ_pos, hμ_le]
          exact lt_trans hs.2 hright
      exact hstrip_param ht
    have htheta :
        Real.pi * (2 * t - 1) ∈ Set.Ioo (0 : ℝ) Real.pi := by
      -- On the open arc branch, the normalized angle lies strictly between `0` and `π`.
      constructor
      · nlinarith [Real.pi_pos, htArc.1]
      · nlinarith [Real.pi_pos, htArc.2]
    constructor
    · intro hu_neg hz
      -- Negative transverse height increases the radius beyond `r`, so the point leaves the
      -- closed semidisk already by the norm bound.
      have hrad_nonneg : 0 ≤ r - u := by
        linarith
      have hrad_gt : r < r - u := by
        linarith
      have hz_norm :
          ‖circleMap 0 (r - u) (Real.pi * (2 * t - 1))‖ ≤ r := hz.1
      rw [norm_circleMap_upper_semicircle hrad_nonneg] at hz_norm
      exact (not_le_of_gt hrad_gt) hz_norm
    · intro hu_pos
      have hrad_nonneg : 0 ≤ r - u := by
        nlinarith [hr, hu.2]
      have hrad_pos : 0 < r - u := by
        nlinarith [hr, hu.2]
      have hz_norm :
          ‖circleMap 0 (r - u) (Real.pi * (2 * t - 1))‖ < r := by
        rw [norm_circleMap_upper_semicircle hrad_nonneg]
        nlinarith
      have hz_im :
          0 < (circleMap 0 (r - u) (Real.pi * (2 * t - 1))).im := by
        -- Positive radius together with `0 < θ < π` keeps the point strictly above the real axis.
        rw [circleMap_zero_im]
        exact mul_pos hrad_pos (Real.sin_pos_of_mem_Ioo htheta)
      exact mem_interior_upper_half_disk_of_norm_lt_im_pos hz_norm hz_im

end

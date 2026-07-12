import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContinuousMap unitInterval

open Metric
open Topology

noncomputable section

/-- The boundary of the closed unit disc, viewed as a subset of the closed unit disc subtype. -/
def closedUnitDiscBoundary : Set (closedBall (0 : ℂ) 1) :=
  (((↑) : closedBall (0 : ℂ) 1 → ℂ) ⁻¹' sphere (0 : ℂ) 1 : Set (closedBall (0 : ℂ) 1))

/-- Membership in `closedUnitDiscBoundary` means lying on the unit circle. -/
@[simp] theorem mem_closedUnitDiscBoundary (z : closedBall (0 : ℂ) 1) :
    z ∈ closedUnitDiscBoundary ↔ (z : ℂ) ∈ sphere (0 : ℂ) 1 :=
  Iff.rfl

/-- The boundary of the unit square, viewed as a subset of `I × I`. -/
def unitSquareBoundary : Set (I × I) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1}

/-- Membership in `unitSquareBoundary` means lying on one of the four edges of the square. -/
@[simp] theorem mem_unitSquareBoundary (p : I × I) :
    p ∈ unitSquareBoundary ↔ p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1 :=
  Iff.rfl

/-- Helper for Exercise II.1-extra-15: on a connected open subset of `ℂ`, simple connectedness of
the subtype is equivalent to the fixed-endpoint homotopy uniqueness of paths in that subtype. -/
lemma isSimplyConnected_iff_paths_homotopic_in_subtype (D : Set ℂ) (hD_open : IsOpen D)
    (hD_connected : IsConnected D) :
    IsSimplyConnected D ↔ ∀ ⦃x y : D⦄ (p q : Path x y), p.Homotopic q := by
  -- Replace connectedness of the open subset by the path-connectedness hypothesis used by
  -- `simply_connected_iff_paths_homotopic'`.
  have hD_pathConnected : IsPathConnected D :=
    (hD_open.isConnected_iff_isPathConnected).1 hD_connected
  have hD_pathConnectedSpace : PathConnectedSpace D := by
    rw [← isPathConnected_iff_pathConnectedSpace]
    exact hD_pathConnected
  -- Then the subtype version of clause `(d)` is exactly the second conjunct in mathlib's
  -- path-homotopy characterization of simple connectedness.
  rw [IsSimplyConnected, simply_connected_iff_paths_homotopic']
  constructor
  · intro h
    exact fun {x y} p q ↦ h.2 p q
  · intro hpaths
    exact ⟨hD_pathConnectedSpace, fun {x y} p q ↦ hpaths p q⟩

/-- Helper for Exercise II.1-extra-15: the angular coordinate on `I` that traverses the full unit
circle exactly once, with the only duplication at the endpoints `0` and `1`. -/
def disc_angle (t : I) : ℝ :=
  Real.pi * (2 * (t : ℝ) - 1)

/-- Helper for Exercise II.1-extra-15: the angular parametrization is continuous. -/
theorem continuous_disc_angle : Continuous disc_angle := by
  -- The angle is an affine function of the unit-interval parameter.
  simpa [disc_angle] using
    (continuous_const.mul ((continuous_const.mul continuous_subtype_val).sub continuous_const))

/-- Helper for Exercise II.1-extra-15: the closed-disc point on the boundary corresponding to the
angle `disc_angle t`. -/
def disc_boundary_carrier (t : I) : closedBall (0 : ℂ) 1 :=
  ⟨circleMap 0 1 (disc_angle t), circleMap_mem_closedBall 0 (by positivity) (disc_angle t)⟩

/-- Helper for Exercise II.1-extra-15: the parametrized boundary point really lies on the boundary
circle. -/
theorem disc_boundary_carrier_mem_boundary (t : I) :
    disc_boundary_carrier t ∈ closedUnitDiscBoundary := by
  rw [mem_closedUnitDiscBoundary]
  simpa [disc_boundary_carrier] using circleMap_mem_sphere' (0 : ℂ) (1 : ℝ) (disc_angle t)

/-- Helper for Exercise II.1-extra-15: the canonical boundary parametrization of the closed unit
disc. -/
def disc_boundary_point (t : I) : closedUnitDiscBoundary :=
  ⟨disc_boundary_carrier t, disc_boundary_carrier_mem_boundary t⟩

/-- Helper for Exercise II.1-extra-15: the boundary parametrization is continuous. -/
theorem continuous_disc_boundary_carrier : Continuous disc_boundary_carrier := by
  -- The parametrization is the explicit circle map viewed in the closed-disc subtype.
  have hArg : Continuous fun t : I ↦ (disc_angle t : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp continuous_disc_angle).mul continuous_const
  apply Continuous.subtype_mk
  simpa [disc_boundary_carrier, circleMap] using Complex.continuous_exp.comp hArg

/-- Helper for Exercise II.1-extra-15: the boundary parametrization into the boundary subtype is
continuous. -/
theorem continuous_disc_boundary_point : Continuous disc_boundary_point := by
  -- After the carrier map is continuous, continuity into the boundary subtype is automatic.
  exact Continuous.subtype_mk continuous_disc_boundary_carrier _

/-- Helper for Exercise II.1-extra-15: the bundled boundary parametrization used to turn boundary
maps into loops. -/
def disc_boundary_param : C(I, closedUnitDiscBoundary) :=
  ⟨disc_boundary_point, continuous_disc_boundary_point⟩

/-- Helper for Exercise II.1-extra-15: the distinguished basepoint on the boundary circle is the
leftmost point `-1`. -/
def disc_boundary_basepoint : closedUnitDiscBoundary :=
  disc_boundary_point 0

/-- Helper for Exercise II.1-extra-15: the boundary parametrization ends where it starts. -/
theorem disc_boundary_point_one_eq_basepoint :
    disc_boundary_point 1 = disc_boundary_basepoint := by
  -- The endpoint angle `π` represents the same boundary point as the starting angle `-π`.
  apply Subtype.ext
  apply Subtype.ext
  norm_num [disc_boundary_basepoint, disc_boundary_point, disc_boundary_carrier, disc_angle,
    circleMap, Complex.exp_mul_I]

/-- Helper for Exercise II.1-extra-15: the boundary parametrization as a loop in the boundary
space. -/
def disc_boundary_path : Path disc_boundary_basepoint disc_boundary_basepoint :=
  Path.mk disc_boundary_param rfl disc_boundary_point_one_eq_basepoint

/-- Helper for Exercise II.1-extra-15: the radial cone point indexed by a radius and an angle lies
in the closed unit disc. -/
def disc_cone_point (p : I × I) : closedBall (0 : ℂ) 1 :=
  ⟨circleMap 0 (p.1 : ℝ) (disc_angle p.2),
    by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_circleMap_zero]
      rw [abs_of_nonneg p.1.2.1]
      exact p.1.2.2⟩

/-- Helper for Exercise II.1-extra-15: the radial cone map is continuous. -/
theorem continuous_disc_cone_point : Continuous disc_cone_point := by
  -- The cone map is the explicit polar formula inside the closed-disc subtype.
  have hRadius : Continuous fun p : I × I ↦ (((p.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have hArg : Continuous fun p : I × I ↦ (disc_angle p.2 : ℂ) * Complex.I := by
    exact
      (Complex.continuous_ofReal.comp (continuous_disc_angle.comp continuous_snd)).mul
        continuous_const
  apply Continuous.subtype_mk
  simpa [disc_cone_point, circleMap] using hRadius.mul (Complex.continuous_exp.comp hArg)

/-- Helper for Exercise II.1-extra-15: the bundled cone map from the square to the closed disc. -/
def disc_cone_param : C(I × I, closedBall (0 : ℂ) 1) :=
  ⟨disc_cone_point, continuous_disc_cone_point⟩

/-- Helper for Exercise II.1-extra-15: the center of the closed unit disc as a subtype point. -/
def disc_center : closedBall (0 : ℂ) 1 :=
  ⟨0, by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_self]
    norm_num⟩

/-- Helper for Exercise II.1-extra-15: the top edge of the cone recovers the boundary
parametrization. -/
@[simp] theorem disc_cone_point_top (t : I) :
    disc_cone_point (1, t) = disc_boundary_carrier t := by
  -- Setting the radial coordinate to `1` gives the boundary circle itself.
  rfl

/-- Helper for Exercise II.1-extra-15: the bottom edge of the cone is the disc center. -/
@[simp] theorem disc_cone_point_bottom (t : I) :
    disc_cone_point (0, t) = disc_center := by
  -- Radius `0` collapses every angle to the center.
  apply Subtype.ext
  simp [disc_cone_point, disc_center, disc_angle, circleMap_zero]

/-- Helper for Exercise II.1-extra-15: the left and right edges of the cone agree. -/
theorem disc_cone_point_left_eq_right (s : I) :
    disc_cone_point (s, 0) = disc_cone_point (s, 1) := by
  -- The endpoint angles `-π` and `π` determine the same point on every intermediate circle.
  apply Subtype.ext
  norm_num [disc_cone_point, disc_angle, circleMap, Complex.exp_mul_I]

/-- Helper for Exercise II.1-extra-15: the `I`-coordinate corresponding to the principal argument
of `z`. -/
def disc_angle_param (z : ℂ) : I :=
  ⟨(Complex.arg z + Real.pi) / (2 * Real.pi),
    by
      -- The principal argument lies in `(-π, π]`, so the affine rescaling lands in `[0, 1]`.
      have harg : -Real.pi < Complex.arg z := Complex.neg_pi_lt_arg z
      have hnum : 0 ≤ Complex.arg z + Real.pi := by linarith
      have hden : 0 ≤ 2 * Real.pi := by positivity
      exact div_nonneg hnum hden,
    by
      -- The same principal-argument bounds give the upper endpoint of the interval.
      have harg : Complex.arg z ≤ Real.pi := Complex.arg_le_pi z
      have hden : 0 < 2 * Real.pi := by positivity
      refine (div_le_iff₀ hden).2 ?_
      linarith⟩

/-- Helper for Exercise II.1-extra-15: the chosen argument parameter really recovers the principal
argument. -/
theorem disc_angle_disc_angle_param (z : ℂ) :
    disc_angle (disc_angle_param z) = Complex.arg z := by
  -- Expanding the affine rescaling shows that `disc_angle_param` is the explicit inverse of
  -- `disc_angle` on the principal-argument interval.
  have hpi : Real.pi ≠ 0 := by positivity
  calc
    disc_angle (disc_angle_param z) =
        Real.pi * (2 * ((Complex.arg z + Real.pi) / (2 * Real.pi)) - 1) := by
          rfl
    _ = Complex.arg z := by
          field_simp [hpi]
          ring

/-- Helper for Exercise II.1-extra-15: boundary points have complex norm `1`. -/
theorem disc_boundary_norm (z : closedUnitDiscBoundary) :
    ‖((z : closedBall (0 : ℂ) 1) : ℂ)‖ = 1 := by
  -- Boundary membership is exactly membership in the unit sphere inside `ℂ`.
  have hz : (((z : closedBall (0 : ℂ) 1) : ℂ)) ∈ sphere (0 : ℂ) 1 := z.2
  simpa [mem_sphere_iff_norm] using hz

/-- Helper for Exercise II.1-extra-15: the boundary parametrization is surjective. -/
theorem disc_boundary_param_surjective : Function.Surjective disc_boundary_param := by
  intro z
  refine ⟨disc_angle_param (((z : closedBall (0 : ℂ) 1) : ℂ)), ?_⟩
  -- Reconstruct the boundary point from its norm-one polar decomposition.
  apply Subtype.ext
  apply Subtype.ext
  have hz : ‖(((z : closedBall (0 : ℂ) 1) : ℂ))‖ = 1 := disc_boundary_norm z
  -- After unfolding the explicit parametrization, the claim is exactly the polar form identity.
  simpa [disc_boundary_param, disc_boundary_point, disc_boundary_carrier, circleMap,
    disc_angle_disc_angle_param, hz] using
    Complex.norm_mul_exp_arg_mul_I (((z : closedBall (0 : ℂ) 1) : ℂ))

/-- Helper for Exercise II.1-extra-15: the boundary parametrization is a quotient map. -/
theorem disc_boundary_param_isQuotientMap :
    Topology.IsQuotientMap disc_boundary_param := by
  -- A surjective continuous map from compact `I` to the Hausdorff boundary subtype is quotient.
  exact IsQuotientMap.of_surjective_continuous disc_boundary_param_surjective
    disc_boundary_param.continuous

/-- Helper for Exercise II.1-extra-15: the radial cone map is surjective onto the closed unit
disc. -/
theorem disc_cone_param_surjective : Function.Surjective disc_cone_param := by
  intro z
  have hz_norm : ‖((z : closedBall (0 : ℂ) 1) : ℂ)‖ ≤ 1 := by
    simpa using (mem_closedBall_zero_iff.1 z.2)
  refine ⟨(⟨‖((z : closedBall (0 : ℂ) 1) : ℂ)‖, by
      constructor
      · exact norm_nonneg _
      · exact hz_norm⟩,
    disc_angle_param (((z : closedBall (0 : ℂ) 1) : ℂ))), ?_⟩
  -- The cone point with radius `‖z‖` and argument `arg z` is exactly `z`.
  apply Subtype.ext
  simpa [disc_cone_param, disc_cone_point, circleMap, disc_angle_disc_angle_param] using
    Complex.norm_mul_exp_arg_mul_I (((z : closedBall (0 : ℂ) 1) : ℂ))

/-- Helper for Exercise II.1-extra-15: the radial cone map is a quotient map. -/
theorem disc_cone_param_isQuotientMap :
    Topology.IsQuotientMap disc_cone_param := by
  -- Again, compact-to-Hausdorff surjective continuity yields a quotient map.
  exact IsQuotientMap.of_surjective_continuous disc_cone_param_surjective
    disc_cone_param.continuous

/-- Helper for Exercise II.1-extra-15: on any nondegenerate circle, the explicit `disc_angle`
parametrization only identifies the two endpoints of `I`. -/
theorem disc_angle_eq_cases_of_circleMap_eq {u v : I} {R : ℝ} (hR : R ≠ 0)
    (h : circleMap 0 R (disc_angle u) = circleMap 0 R (disc_angle v)) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  -- First convert equality on the circle to equality of angles modulo integer multiples of `2π`.
  rw [circleMap_eq_circleMap_iff (c := (0 : ℂ)) hR] at h
  obtain ⟨n, hn⟩ := h
  have hangle : disc_angle u = disc_angle v + n * (2 * Real.pi) := by
    -- Taking imaginary parts removes the common factor `I`.
    have him := congrArg Complex.im hn
    simpa [mul_add, add_mul, mul_assoc] using him
  have hu_lo : -Real.pi ≤ disc_angle u := by
    -- The affine angle map sends `I` into `[-π, π]`.
    unfold disc_angle
    nlinarith [u.2.1, Real.pi_pos]
  have hu_hi : disc_angle u ≤ Real.pi := by
    -- The upper endpoint is reached exactly at `u = 1`.
    unfold disc_angle
    nlinarith [u.2.2, Real.pi_pos]
  have hv_lo : -Real.pi ≤ disc_angle v := by
    -- The same range control holds for the second parameter.
    unfold disc_angle
    nlinarith [v.2.1, Real.pi_pos]
  have hv_hi : disc_angle v ≤ Real.pi := by
    -- Again the angle stays inside the principal interval.
    unfold disc_angle
    nlinarith [v.2.2, Real.pi_pos]
  have hn_le : n ≤ 1 := by
    have hupper : (n : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by
      linarith
    have hpi : 0 < 2 * Real.pi := by positivity
    have hn_le_real : (n : ℝ) ≤ 1 := by
      nlinarith
    exact_mod_cast hn_le_real
  have hn_ge : -1 ≤ n := by
    have hlower : -(2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) := by
      linarith
    have hpi : 0 < 2 * Real.pi := by positivity
    have hn_ge_real : (-1 : ℝ) ≤ n := by
      nlinarith
    exact_mod_cast hn_ge_real
  have hn_cases : n = -1 ∨ n = 0 ∨ n = 1 := by
    omega
  rcases hn_cases with hn_neg | hn_zero | hn_pos
  · -- The negative `2π` shift forces `u = 0` and `v = 1`.
    right
    left
    have hangle_neg : disc_angle u = disc_angle v - 2 * Real.pi := by
      simpa [hn_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hangle
    have hu_eq : disc_angle u = -Real.pi := by
      linarith [hangle_neg, hv_hi]
    have hv_eq : disc_angle v = Real.pi := by
      linarith [hangle_neg, hu_lo]
    constructor
    · have hu_zero : (u : ℝ) = 0 := by
        have hpi : 0 < Real.pi := Real.pi_pos
        unfold disc_angle at hu_eq
        nlinarith
      exact Subtype.ext hu_zero
    · have hv_one : (v : ℝ) = 1 := by
        have hpi : 0 < Real.pi := Real.pi_pos
        unfold disc_angle at hv_eq
        nlinarith
      exact Subtype.ext hv_one
  · -- Zero shift means the affine angle map is injective.
    left
    have hangle_zero : disc_angle u = disc_angle v := by
      simpa [hn_zero] using hangle
    have huv : (u : ℝ) = v := by
      have hpi : 0 < Real.pi := Real.pi_pos
      unfold disc_angle at hangle_zero
      nlinarith
    exact Subtype.ext huv
  · -- The positive `2π` shift forces `u = 1` and `v = 0`.
    right
    right
    have hangle_pos : disc_angle u = disc_angle v + 2 * Real.pi := by
      simpa [hn_pos] using hangle
    have hu_eq : disc_angle u = Real.pi := by
      linarith [hangle_pos, hv_lo]
    have hv_eq : disc_angle v = -Real.pi := by
      linarith [hangle_pos, hu_hi]
    constructor
    · have hu_one : (u : ℝ) = 1 := by
        have hpi : 0 < Real.pi := Real.pi_pos
        unfold disc_angle at hu_eq
        nlinarith
      exact Subtype.ext hu_one
    · have hv_zero : (v : ℝ) = 0 := by
        have hpi : 0 < Real.pi := Real.pi_pos
        unfold disc_angle at hv_eq
        nlinarith
      exact Subtype.ext hv_zero

/-- Helper for Exercise II.1-extra-15: equal boundary parameters differ only by the trivial
endpoint identification. -/
theorem disc_boundary_param_eq_cases {u v : I} (h : disc_boundary_param u = disc_boundary_param v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  -- Forgetting to the underlying complex points reduces the claim to the angle-fiber
  -- classification on the unit circle.
  have hcircle : circleMap 0 1 (disc_angle u) = circleMap 0 1 (disc_angle v) := by
    simpa [disc_boundary_param, disc_boundary_point, disc_boundary_carrier] using
      congrArg (fun z : closedUnitDiscBoundary => (((z : closedBall (0 : ℂ) 1) : ℂ))) h
  exact disc_angle_eq_cases_of_circleMap_eq one_ne_zero hcircle

/-- Helper for Exercise II.1-extra-15: a loop factors through the boundary parametrization because
that parametrization only identifies the two endpoints. -/
theorem disc_boundary_param_factors_through_loop {Y : Type*} [TopologicalSpace Y]
    {x : Y} (γ : Path x x) :
    Function.FactorsThrough γ.toContinuousMap disc_boundary_param := by
  intro u v huv
  -- The only nontrivial fibers are the endpoint pair `0 ~ 1`, and a loop already identifies them.
  rcases disc_boundary_param_eq_cases huv with rfl | h01 | h10
  · rfl
  · rcases h01 with ⟨hu, hv⟩
    rw [hu, hv]
    exact γ.source.trans γ.target.symm
  · rcases h10 with ⟨hu, hv⟩
    rw [hu, hv]
    exact γ.target.trans γ.source.symm

/-- Helper for Exercise II.1-extra-15: equal cone parameters are either both at the center or
share the same radius and the same angular class modulo the boundary endpoint identification. -/
theorem disc_cone_param_eq_cases {p q : I × I} (h : disc_cone_param p = disc_cone_param q) :
    (p.1 = 0 ∧ q.1 = 0) ∨
      (p.1 = q.1 ∧ p.2 = q.2) ∨
      (p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 1) ∨
      (p.1 = q.1 ∧ p.2 = 1 ∧ q.2 = 0) := by
  -- Equal points in polar form have equal radii, so only the angular endpoint identification
  -- remains to analyze.
  have hr_val : (p.1 : ℝ) = q.1 := by
    have hnorm := congrArg (fun z : closedBall (0 : ℂ) 1 => ‖(z : ℂ)‖) h
    simpa [disc_cone_param, disc_cone_point, norm_circleMap_zero, abs_of_nonneg p.1.2.1,
      abs_of_nonneg q.1.2.1] using hnorm
  have hr : p.1 = q.1 := Subtype.ext hr_val
  by_cases hp0 : p.1 = 0
  · -- Radius `0` collapses the whole angular fiber to the center.
    left
    constructor
    · exact hp0
    · rw [← hr]
      exact hp0
  · -- Away from the center, the circle fiber is the same as for the boundary parametrization.
    have hR : (p.1 : ℝ) ≠ 0 := by
      intro hzero
      apply hp0
      exact Subtype.ext hzero
    have hcircle : circleMap 0 (p.1 : ℝ) (disc_angle p.2) =
        circleMap 0 (p.1 : ℝ) (disc_angle q.2) := by
      have hcomplex := congrArg (fun z : closedBall (0 : ℂ) 1 => (z : ℂ)) h
      simpa [disc_cone_param, disc_cone_point, hr] using hcomplex
    rcases disc_angle_eq_cases_of_circleMap_eq hR hcircle with hpq | h01 | h10
    · right
      left
      exact ⟨hr, hpq⟩
    · right
      right
      left
      exact ⟨hr, h01.1, h01.2⟩
    · right
      right
      right
      exact ⟨hr, h10.1, h10.2⟩

/-- Helper for Exercise II.1-extra-15: the radial cone respects the endpoint conditions of a path
homotopy after the standard coordinate flip `r ↦ 1 - r`. -/
theorem disc_cone_param_factors_through_homotopy {Y : Type*} [TopologicalSpace Y]
    {x : Y} {γ : Path x x} (F : γ.Homotopy (Path.refl x)) :
    Function.FactorsThrough
      (fun p : I × I ↦ F (⟨1 - (p.1 : ℝ), by
        constructor
        · nlinarith [p.1.2.2]
        · nlinarith [p.1.2.1]⟩, p.2))
      disc_cone_param := by
  let flip : I → I := fun s ↦
    ⟨1 - (s : ℝ), by
      constructor
      · nlinarith [s.2.2]
      · nlinarith [s.2.1]⟩
  intro p q hpq
  change F (flip p.1, p.2) = F (flip q.1, q.2)
  -- The quotient fibers are exactly the center fiber and the two vertical boundary identifications.
  rcases disc_cone_param_eq_cases hpq with hzero | hsame | hleft | hright
  · rcases hzero with ⟨hp0, hq0⟩
    have hpflip : flip p.1 = 1 := by
      apply Subtype.ext
      simp [flip, hp0]
    have hqflip : flip q.1 = 1 := by
      apply Subtype.ext
      simp [flip, hq0]
    rw [hpflip, hqflip]
    -- At homotopy time `1`, both paths have collapsed to the constant loop.
    have hpconst : F (1, p.2) = x := by
      simpa using congrArg (fun g : Path x x => g p.2) F.eval_one
    have hqconst : F (1, q.2) = x := by
      simpa using congrArg (fun g : Path x x => g q.2) F.eval_one
    exact hpconst.trans hqconst.symm
  · rcases hsame with ⟨hr, hs⟩
    -- Equal radius and equal angle give the same point after the radial flip.
    have hflip : flip p.1 = flip q.1 := by
      apply Subtype.ext
      simpa [flip] using congrArg (fun s : I => (1 - (s : ℝ) : ℝ)) hr
    rw [hflip, hs]
  · rcases hleft with ⟨hr, hp2, hq2⟩
    -- The `0 ~ 1` angular identification is absorbed by the fixed-endpoint condition.
    have hflip : flip p.1 = flip q.1 := by
      apply Subtype.ext
      simpa [flip] using congrArg (fun s : I => (1 - (s : ℝ) : ℝ)) hr
    rw [hp2, hq2, hflip]
    exact (F.source _).trans (F.target _).symm
  · rcases hright with ⟨hr, hp2, hq2⟩
    -- The opposite endpoint identification is handled in the same way.
    have hflip : flip p.1 = flip q.1 := by
      apply Subtype.ext
      simpa [flip] using congrArg (fun s : I => (1 - (s : ℝ) : ℝ)) hr
    rw [hp2, hq2, hflip]
    exact (F.target _).trans (F.source _).symm

/-- Helper for Exercise II.1-extra-15: the affine reversal map `s ↦ 1 - s` preserves the unit
interval and is continuous. -/
theorem continuous_unitIntervalFlip :
    Continuous (fun s : I ↦
      (⟨1 - (s : ℝ), by
        constructor
        · nlinarith [s.2.2]
        · nlinarith [s.2.1]⟩ : I)) := by
  -- The reversal map is affine on the ambient real line, so continuity descends to the subtype.
  apply Continuous.subtype_mk
  simpa using continuous_const.sub continuous_subtype_val

/-- Helper for Exercise II.1-extra-15: the closed unit square viewed as the rectangle
`0 ≤ re z ≤ 1`, `0 ≤ im z ≤ 1` in `ℂ`. -/
def unitSquareSet : Set ℂ :=
  Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (0 : ℝ) 1

/-- Helper for Exercise II.1-extra-15: the evident identification of `I × I` with the square
subtype in `ℂ`. -/
def unitSquareSetHomeomorph : I × I ≃ₜ unitSquareSet := by
  let toProd : I × I ≃ₜ ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1)) :=
    (Homeomorph.Set.prod (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)).symm
  let toComplex :
      ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1)) ≃ₜ unitSquareSet :=
    (Complex.equivRealProdCLM.symm.toHomeomorph).sets
      (by
        ext x
        -- Rewrite the square predicate through the real/imaginary coordinate homeomorphism.
        simp only [Set.Icc_prod_Icc, Set.mem_Icc, unitSquareSet,
          ContinuousLinearEquiv.toHomeomorph_symm,
          ContinuousLinearEquiv.coe_symm_toHomeomorph, Set.mem_preimage,
          Complex.mem_reProdIm]
        constructor
        · intro hx
          exact ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2, hx.2.2⟩
        · intro hx
          exact ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2, hx.2.2⟩)
  exact toProd.trans toComplex

/-- Helper for Exercise II.1-extra-15: the square homeomorphism reads off the first coordinate as
the real part. -/
@[simp] theorem unitSquareSetHomeomorph_re (p : I × I) :
    (((unitSquareSetHomeomorph p : unitSquareSet) : ℂ).re) = (p.1 : ℝ) :=
  rfl

/-- Helper for Exercise II.1-extra-15: the square homeomorphism reads off the second coordinate as
the imaginary part. -/
@[simp] theorem unitSquareSetHomeomorph_im (p : I × I) :
    (((unitSquareSetHomeomorph p : unitSquareSet) : ℂ).im) = (p.2 : ℝ) :=
  rfl

/-- Helper for Exercise II.1-extra-15: the frontier of the ambient square is exactly the union of
its four sides. -/
theorem mem_frontier_unitSquareSet (z : ℂ) :
    z ∈ frontier unitSquareSet ↔
      z.re ∈ Set.Icc (0 : ℝ) 1 ∧ z.im ∈ Set.Icc (0 : ℝ) 1 ∧
        (z.re = 0 ∨ z.re = 1 ∨ z.im = 0 ∨ z.im = 1) := by
  -- Expand the frontier of the product rectangle into the two horizontal and two vertical sides.
  rw [unitSquareSet, Complex.frontier_reProdIm]
  constructor
  · intro h
    simp only [closure_Icc, zero_le_one, frontier_Icc, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc] at h
    aesop
  · intro h
    rcases h with ⟨hre, him, hbdry⟩
    rcases hre with ⟨hre0, hre1⟩
    rcases him with ⟨him0, him1⟩
    -- Repackage the side condition into the explicit union given by `frontier_reProdIm`.
    simp only [closure_Icc, zero_le_one, frontier_Icc, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc]
    rcases hbdry with hre_eq0 | hre_eq1 | him_eq0 | him_eq1
    · exact Or.inr ⟨Or.inl hre_eq0, him0, him1⟩
    · exact Or.inr ⟨Or.inr hre_eq1, him0, him1⟩
    · exact Or.inl ⟨⟨hre0, hre1⟩, Or.inl him_eq0⟩
    · exact Or.inl ⟨⟨hre0, hre1⟩, Or.inr him_eq1⟩

/-- Helper for Exercise II.1-extra-15: the square boundary predicate is the pullback of the
ambient-square frontier along `unitSquareSetHomeomorph`. -/
theorem unitSquareBoundary_preimage_frontier :
    unitSquareBoundary =
      unitSquareSetHomeomorph ⁻¹' {z : unitSquareSet | (z : ℂ) ∈ frontier unitSquareSet} := by
  ext p
  -- Transport the frontier characterization through the explicit square coordinates.
  simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_frontier_unitSquareSet, unitSquareBoundary,
    unitSquareSetHomeomorph_re, unitSquareSetHomeomorph_im, Set.mem_Icc]
  constructor
  · intro h
    exact ⟨p.1.2, p.2.2, by simpa using h⟩
  · intro h
    simpa using h.2.2

/-- Helper for Exercise II.1-extra-15: there is a homeomorphism from the square to the closed unit
disc carrying the square boundary to the circle boundary. -/
lemma existsUnitSquarePairHomeomorphClosedDisc :
    ∃ e : I × I ≃ₜ closedBall (0 : ℂ) 1,
      unitSquareBoundary = e ⁻¹' closedUnitDiscBoundary := by
  have hconvex : Convex ℝ unitSquareSet := by
    intro x hx y hy a b ha hb hab
    -- Convexity is coordinatewise because both real and imaginary coordinates stay in `Icc 0 1`.
    rw [unitSquareSet, Complex.mem_reProdIm] at hx hy ⊢
    exact
      ⟨by
          simpa [Complex.smul_re] using convex_Icc (0 : ℝ) 1 hx.1 hy.1 ha hb hab,
        by
          simpa [Complex.smul_im] using convex_Icc (0 : ℝ) 1 hx.2 hy.2 ha hb hab⟩
  have hinterior : (interior unitSquareSet).Nonempty := by
    -- The midpoint of the square lies in the interior box `(0,1) × (0,1)`.
    refine ⟨(1 / 2 : ℂ) + (1 / 2 : ℂ) * Complex.I, ?_⟩
    rw [unitSquareSet, Complex.interior_reProdIm, Complex.mem_reProdIm]
    simpa using
      (show ((1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1) ∧ ((1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1) by
        norm_num)
  have hbounded : Bornology.IsBounded unitSquareSet := by
    -- Each coordinate interval is bounded, so the product square is bounded as well.
    simpa [unitSquareSet] using
      (Metric.isBounded_Icc (0 : ℝ) 1).reProdIm (Metric.isBounded_Icc (0 : ℝ) 1)
  obtain ⟨h, -, hclosure, -⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconvex hinterior hbounded
  have hunitClosed : h '' unitSquareSet = closedBall (0 : ℂ) 1 := by
    -- The square is already closed, so the ambient theorem gives its exact image.
    simpa [unitSquareSet, closure_Icc, Complex.closure_reProdIm] using hclosure
  have hpre : unitSquareSet = h ⁻¹' (closedBall (0 : ℂ) 1) := by
    -- Turn the image statement into the preimage statement required by `Homeomorph.sets`.
    ext z
    constructor
    · intro hz
      simpa [hunitClosed] using Set.mem_image_of_mem h hz
    · intro hz
      rcases (show h z ∈ h '' unitSquareSet by simpa [hunitClosed] using hz) with
        ⟨w, hw, hwz⟩
      exact h.injective hwz ▸ hw
  let e : I × I ≃ₜ closedBall (0 : ℂ) 1 :=
    unitSquareSetHomeomorph.trans (h.sets hpre)
  refine ⟨e, ?_⟩
  ext p
  constructor
  · intro hp
    have hfrontSub :
        unitSquareSetHomeomorph p ∈ {z : unitSquareSet | (z : ℂ) ∈ frontier unitSquareSet} := by
      simpa [unitSquareBoundary_preimage_frontier] using hp
    have hmem :
        (unitSquareSetHomeomorph p : ℂ) ∈ h ⁻¹' closedBall (0 : ℂ) 1 := by
      simpa [hpre] using (unitSquareSetHomeomorph p).2
    have hnotint₀ : (unitSquareSetHomeomorph p : ℂ) ∉ interior unitSquareSet := by
      exact (mem_frontier_iff_notMem_interior (unitSquareSetHomeomorph p).2).1 hfrontSub
    have hnotint :
        (unitSquareSetHomeomorph p : ℂ) ∉ interior (h ⁻¹' closedBall (0 : ℂ) 1) := by
      simpa [hpre] using hnotint₀
    have hfront :
        (unitSquareSetHomeomorph p : ℂ) ∈ frontier (h ⁻¹' closedBall (0 : ℂ) 1) :=
      (mem_frontier_iff_notMem_interior hmem).2 hnotint
    have hzpre :
        (unitSquareSetHomeomorph p : ℂ) ∈ h ⁻¹' frontier (closedBall (0 : ℂ) 1) := by
      rw [h.preimage_frontier]
      exact hfront
    have hdisc : h (unitSquareSetHomeomorph p) ∈ sphere (0 : ℂ) 1 := by
      simpa [frontier_closedBall'] using hzpre
    -- The restricted homeomorphism therefore lands on the circle boundary.
    simpa [e, closedUnitDiscBoundary] using hdisc
  · intro hp
    have hzpre :
        (unitSquareSetHomeomorph p : ℂ) ∈ h ⁻¹' frontier (closedBall (0 : ℂ) 1) := by
      simpa [e, closedUnitDiscBoundary, frontier_closedBall'] using hp
    have hfront :
        (unitSquareSetHomeomorph p : ℂ) ∈ frontier (h ⁻¹' closedBall (0 : ℂ) 1) := by
      rw [h.preimage_frontier] at hzpre
      exact hzpre
    have hnotint :
        (unitSquareSetHomeomorph p : ℂ) ∉ interior (h ⁻¹' closedBall (0 : ℂ) 1) := by
      exact (mem_frontier_iff_notMem_interior (by
        simpa [hpre] using (unitSquareSetHomeomorph p).2)).1 hfront
    have hnotint₀ : (unitSquareSetHomeomorph p : ℂ) ∉ interior unitSquareSet := by
      simpa [hpre] using hnotint
    have hfront₀ : (unitSquareSetHomeomorph p : ℂ) ∈ frontier unitSquareSet :=
      (mem_frontier_iff_notMem_interior (unitSquareSetHomeomorph p).2).2 hnotint₀
    have hfrontSub :
        unitSquareSetHomeomorph p ∈ {z : unitSquareSet | (z : ℂ) ∈ frontier unitSquareSet} :=
      hfront₀
    -- Pull the frontier condition back to the explicit square boundary predicate.
    simpa [unitSquareBoundary_preimage_frontier] using hfrontSub

/-- Helper for Exercise II.1-extra-15: disc extension and square extension are equivalent after
transporting continuous maps along a boundary-preserving homeomorphism. -/
lemma discExtension_iff_squareExtension (D : Set ℂ) :
    (∀ f : C(closedUnitDiscBoundary, D),
        ∃ g : C(closedBall (0 : ℂ) 1, D), g.restrict closedUnitDiscBoundary = f) ↔
      (∀ f : C(unitSquareBoundary, D),
        ∃ g : C(I × I, D), g.restrict unitSquareBoundary = f) := by
  constructor
  · intro hdisc f
    -- Transport the square boundary datum across a boundary-preserving square-disc homeomorphism.
    obtain ⟨e, he⟩ := existsUnitSquarePairHomeomorphClosedDisc
    let eb : unitSquareBoundary ≃ₜ closedUnitDiscBoundary := e.sets he
    let fd : C(closedUnitDiscBoundary, D) :=
      f.comp (eb.symm : C(closedUnitDiscBoundary, unitSquareBoundary))
    obtain ⟨g, hg⟩ := hdisc fd
    refine ⟨g.comp (e : C(I × I, closedBall (0 : ℂ) 1)), ?_⟩
    -- The descended filler agrees with the original square boundary map after evaluation at `eb x`.
    ext x
    have hx := congrArg (fun h : C(closedUnitDiscBoundary, D) => h (eb x)) hg
    simpa [fd, eb, ContinuousMap.comp_apply] using congrArg Subtype.val hx
  · intro hsquare f
    -- Transport the disc boundary datum back to the square boundary and extend there.
    obtain ⟨e, he⟩ := existsUnitSquarePairHomeomorphClosedDisc
    let eb : unitSquareBoundary ≃ₜ closedUnitDiscBoundary := e.sets he
    let fs : C(unitSquareBoundary, D) :=
      f.comp (eb : C(unitSquareBoundary, closedUnitDiscBoundary))
    obtain ⟨g, hg⟩ := hsquare fs
    refine ⟨g.comp (e.symm : C(closedBall (0 : ℂ) 1, I × I)), ?_⟩
    -- Evaluating the square boundary equality at `eb.symm z` recovers the disc boundary datum.
    ext z
    have hz := congrArg (fun h : C(unitSquareBoundary, D) => h (eb.symm z)) hg
    simpa [fs, eb, ContinuousMap.comp_apply] using congrArg Subtype.val hz

/-- Helper for Exercise II.1-extra-15: the quotient-descended disc filler agrees with the original
boundary map on the circle boundary. -/
lemma restrictLiftOfDiscHomotopy_eq_boundary {D : Set ℂ} {f : C(closedUnitDiscBoundary, D)}
    {k : C(I × I, D)}
    (hkfactor : Function.FactorsThrough k disc_cone_param)
    (htop : ∀ t : I, k (1, t) = f (disc_boundary_point t)) :
    (disc_cone_param_isQuotientMap.lift k hkfactor).restrict closedUnitDiscBoundary = f := by
  ext z
  rcases disc_boundary_param_surjective z with ⟨t, rfl⟩
  -- Replace the boundary point by the explicit top-edge witness `(1, t)` before using the lift
  -- triangle.
  have hsurj :
      disc_cone_param (Function.surjInv disc_cone_param_surjective ↑(disc_boundary_point t)) =
        disc_boundary_carrier t := by
    simpa [disc_boundary_point] using
      (Function.rightInverse_surjInv disc_cone_param_surjective ↑(disc_boundary_point t))
  have hcone : disc_cone_param (1, t) = disc_boundary_carrier t := by
    simp [disc_cone_param, disc_cone_point_top]
  have hcomp :
      k (Function.surjInv disc_cone_param_surjective ↑(disc_boundary_point t)) = k (1, t) :=
    hkfactor (hsurj.trans hcone.symm)
  -- After rewriting the cone point on the top edge, the lifted map restricts to `f`.
  simpa [disc_boundary_param] using congrArg Subtype.val (hcomp.trans (htop t))

/-- Helper for Exercise II.1-extra-15: the explicit square-boundary formula attached to two paths
is continuous on the boundary subtype. -/
lemma continuous_squareBoundaryMapOfPaths {D : Set ℂ} {x y : D} (p q : Path x y) :
    Continuous fun z : unitSquareBoundary =>
      if _ : z.1.2 = 0 then
        q z.1.1
      else if _ : z.1.1 = 1 then
        y
      else if _ : z.1.2 = 1 then
        p z.1.1
      else
        x := by
  let f : unitSquareBoundary → D := fun z =>
    if _ : z.1.2 = 0 then
      q z.1.1
    else if _ : z.1.1 = 1 then
      y
    else if _ : z.1.2 = 1 then
      p z.1.1
    else
      x
  let S₀ : Set unitSquareBoundary := {z | z.1.2 = 0 ∨ z.1.1 = 0}
  let S₁ : Set unitSquareBoundary := {z | z.1.2 = 0 ∨ z.1.1 = 1}
  let S₂ : Set unitSquareBoundary := {z | z.1.1 = 1 ∨ z.1.2 = 1}
  let S₃ : Set unitSquareBoundary := {z | z.1.2 = 1 ∨ z.1.1 = 0}
  have hfst : Continuous fun z : unitSquareBoundary ↦ z.1.1 := by
    fun_prop
  have hq : Continuous fun z : unitSquareBoundary ↦ q z.1.1 := by
    simpa using q.continuous.comp hfst
  have hp : Continuous fun z : unitSquareBoundary ↦ p z.1.1 := by
    simpa using p.continuous.comp hfst
  have hS₀_closed : IsClosed S₀ := by
    dsimp [S₀]
    exact (isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const)
  have hS₁_closed : IsClosed S₁ := by
    dsimp [S₁]
    exact (isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const)
  have hS₂_closed : IsClosed S₂ := by
    dsimp [S₂]
    exact (isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const)
  have hS₃_closed : IsClosed S₃ := by
    dsimp [S₃]
    exact (isClosed_eq (by fun_prop) continuous_const).union
      (isClosed_eq (by fun_prop) continuous_const)
  have hEq₀ : Set.EqOn f (fun z : unitSquareBoundary ↦ q z.1.1) S₀ := by
    intro z hz
    rcases hz with hz0 | hx0
    · simp [f, hz0]
    · simp [f, hx0]
  have hEq₁ : Set.EqOn f (fun z : unitSquareBoundary ↦ q z.1.1) S₁ := by
    intro z hz
    rcases hz with hz0 | hx1
    · simp [f, hz0]
    · simp [f, hx1]
  have hEq₂ : Set.EqOn f (fun z : unitSquareBoundary ↦ p z.1.1) S₂ := by
    intro z hz
    rcases hz with hx1 | hz1
    · by_cases hz0 : z.1.2 = 0
      · simp [f, hx1, hz0, p.target]
      · simp [f, hx1, hz0, p.target]
    · by_cases hx1 : z.1.1 = 1
      · simp [f, hz1, hx1, p.target]
      · simp [f, hz1, hx1]
  have hEq₃ : Set.EqOn f (fun z : unitSquareBoundary ↦ p z.1.1) S₃ := by
    intro z hz
    rcases hz with hz1 | hx0
    · by_cases hx1 : z.1.1 = 1
      · simp [f, hz1, hx1, p.target]
      · simp [f, hz1, hx1]
    · simp [f, hx0]
  have hcont₀ : ContinuousOn f S₀ := (continuousOn_congr hEq₀).2 hq.continuousOn
  have hcont₁ : ContinuousOn f S₁ := (continuousOn_congr hEq₁).2 hq.continuousOn
  have hcont₂ : ContinuousOn f S₂ := (continuousOn_congr hEq₂).2 hp.continuousOn
  have hcont₃ : ContinuousOn f S₃ := (continuousOn_congr hEq₃).2 hp.continuousOn
  have hcont₀₁ : ContinuousOn f (S₀ ∪ S₁) :=
    hcont₀.union_of_isClosed hcont₁ hS₀_closed hS₁_closed
  have hcont₀₁₂ : ContinuousOn f ((S₀ ∪ S₁) ∪ S₂) :=
    hcont₀₁.union_of_isClosed hcont₂ (hS₀_closed.union hS₁_closed) hS₂_closed
  have hcover : (((S₀ ∪ S₁) ∪ S₂) ∪ S₃) = Set.univ := by
    ext z
    constructor
    · intro _
      trivial
    · intro _
      rcases z.2 with hx0 | hx1 | hy0 | hy1
      · simp [S₀, hx0]
      · simp [S₁, S₂, hx1]
      · simp [S₀, S₁, hy0]
      · simp [S₂, S₃, hy1]
  -- Glue the four closed arcs of the boundary circle, each carrying one of the two path formulas.
  have hcont :
      ContinuousOn f ((((S₀ ∪ S₁) ∪ S₂) ∪ S₃)) :=
    hcont₀₁₂.union_of_isClosed hcont₃
      ((hS₀_closed.union hS₁_closed).union hS₂_closed) hS₃_closed
  have hunion : S₀ ∪ (S₁ ∪ (S₂ ∪ S₃)) = Set.univ := by
    simpa [Set.union_assoc] using hcover
  have huniv : ContinuousOn f Set.univ := by
    simpa only [hunion, Set.union_assoc] using hcont
  simpa [f] using (continuousOn_univ.mp huniv)

/-- Helper for Exercise II.1-extra-15: the boundary datum with top edge `p`, bottom edge `q`,
and vertical edges fixed at the common endpoints. -/
def squareBoundaryMapOfPaths {D : Set ℂ} {x y : D} (p q : Path x y) : C(unitSquareBoundary, D) :=
  ⟨(fun z =>
      if _ : z.1.2 = 0 then
        q z.1.1
      else if _ : z.1.1 = 1 then
        y
      else if _ : z.1.2 = 1 then
        p z.1.1
      else
        x),
    continuous_squareBoundaryMapOfPaths p q⟩

/-- Helper for Exercise II.1-extra-15: the square-boundary map restricts to `q` on the bottom
edge. -/
@[simp] theorem squareBoundaryMapOfPaths_bottom {D : Set ℂ} {x y : D}
    (p q : Path x y) (t : I) :
    squareBoundaryMapOfPaths p q
        ⟨(t, 0), Or.inr <| Or.inr <| Or.inl rfl⟩ = q t := by
  -- On the bottom edge, the first branch of the boundary formula is active.
  simp [squareBoundaryMapOfPaths]

/-- Helper for Exercise II.1-extra-15: the square-boundary map restricts to `p` on the top edge. -/
@[simp] theorem squareBoundaryMapOfPaths_top {D : Set ℂ} {x y : D}
    (p q : Path x y) (t : I) :
    squareBoundaryMapOfPaths p q
        ⟨(t, 1), Or.inr <| Or.inr <| Or.inr rfl⟩ = p t := by
  -- On the top edge, the third branch records the path `p`.
  by_cases ht : t = 1
  · simp [squareBoundaryMapOfPaths, ht, p.target]
  · simp [squareBoundaryMapOfPaths, ht]

/-- Helper for Exercise II.1-extra-15: the square-boundary map is constantly `x` on the left
edge. -/
@[simp] theorem squareBoundaryMapOfPaths_left {D : Set ℂ} {x y : D}
    (p q : Path x y) (t : I) :
    squareBoundaryMapOfPaths p q ⟨(0, t), Or.inl rfl⟩ = x := by
  -- On the left edge, both path formulas collapse to the common source point.
  simp [squareBoundaryMapOfPaths]

/-- Helper for Exercise II.1-extra-15: the square-boundary map is constantly `y` on the right
edge. -/
@[simp] theorem squareBoundaryMapOfPaths_right {D : Set ℂ} {x y : D}
    (p q : Path x y) (t : I) :
    squareBoundaryMapOfPaths p q ⟨(1, t), Or.inr <| Or.inl rfl⟩ = y := by
  -- On the right edge, both path formulas collapse to the common target point.
  by_cases ht : t = 0
  · simp [squareBoundaryMapOfPaths, ht, q.target]
  · simp [squareBoundaryMapOfPaths, ht]

/-- Helper for Exercise II.1-extra-15: a square filler with the standard boundary data gives a
fixed-endpoint homotopy between the top and bottom paths. -/
lemma pathsHomotopic_of_squareExtension {D : Set ℂ}
    (hsquare :
      ∀ f : C(unitSquareBoundary, D), ∃ g : C(I × I, D), g.restrict unitSquareBoundary = f) :
    ∀ ⦃x y : D⦄ (p q : Path x y), p.Homotopic q := by
  intro x y p q
  obtain ⟨g, hg⟩ := hsquare (squareBoundaryMapOfPaths p q)
  have hbottom : ∀ s : I, g (s, 0) = q s := by
    intro s
    have hs :=
      congrArg (fun h : C(unitSquareBoundary, D) =>
        h ⟨(s, 0), Or.inr <| Or.inr <| Or.inl rfl⟩) hg
    simpa using hs
  have htop : ∀ s : I, g (s, 1) = p s := by
    intro s
    have hs :=
      congrArg (fun h : C(unitSquareBoundary, D) =>
        h ⟨(s, 1), Or.inr <| Or.inr <| Or.inr rfl⟩) hg
    simpa using hs
  have hleft : ∀ t : I, g (0, t) = x := by
    intro t
    have ht :=
      congrArg (fun h : C(unitSquareBoundary, D) => h ⟨(0, t), Or.inl rfl⟩) hg
    simpa using ht
  have hright : ∀ t : I, g (1, t) = y := by
    intro t
    have ht :=
      congrArg (fun h : C(unitSquareBoundary, D) =>
        h ⟨(1, t), Or.inr <| Or.inl rfl⟩) hg
    simpa using ht
  let Hqp : q.Homotopy p :=
    { toFun := fun z ↦ g (z.2, z.1)
      continuous_toFun := by
        -- Swapping the square coordinates reads the filler as a homotopy parameterized by time.
        have hswap : Continuous fun z : I × I ↦ (z.2, z.1) := by
          fun_prop
        simpa using g.continuous.comp hswap
      map_zero_left := by
        intro s
        simpa using hbottom s
      map_one_left := by
        intro s
        simpa using htop s
      prop' := by
        intro t s hs
        rcases hs with rfl | rfl
        · simpa using hleft t
        · simpa using hright t }
  -- The coordinate-swapped filler runs from `q` to `p`, so reverse it to obtain `p ~ q`.
  exact ⟨Hqp.symm⟩

lemma disc_extension_iff_isSimplyConnected (D : Set ℂ) (hD_open : IsOpen D)
    (hD_connected : IsConnected D) :
    IsSimplyConnected D ↔
      (∀ f : C(closedUnitDiscBoundary, D),
        ∃ g : C(closedBall (0 : ℂ) 1, D), g.restrict closedUnitDiscBoundary = f) := by
  constructor
  · intro hD_sc f
    let γ : Path (f disc_boundary_basepoint) (f disc_boundary_basepoint) :=
      Path.mk (f.comp disc_boundary_param) rfl
        (by
          -- The boundary parametrization closes up at the distinguished basepoint.
          simpa [disc_boundary_basepoint, ContinuousMap.comp_apply] using
            congrArg f disc_boundary_point_one_eq_basepoint)
    have hpaths :=
      (isSimplyConnected_iff_paths_homotopic_in_subtype D hD_open hD_connected).1 hD_sc
    obtain ⟨F⟩ := hpaths γ (Path.refl _)
    let k : C(I × I, D) :=
      ⟨(fun p : I × I ↦
          F (⟨1 - (p.1 : ℝ), by
            constructor
            · nlinarith [p.1.2.2]
            · nlinarith [p.1.2.1]⟩, p.2)),
        by
          -- Reindex the homotopy by the radial flip used by the cone quotient.
          fun_prop⟩
    have hkfactor : Function.FactorsThrough k disc_cone_param := by
      -- The cone fibers are exactly the endpoint identifications respected by the homotopy.
      simpa [k] using disc_cone_param_factors_through_homotopy (γ := γ) F
    have htop : ∀ t : I, k (1, t) = f (disc_boundary_point t) := by
      intro t
      -- On the top edge, the reindexed homotopy is exactly the original loop.
      have hγ : γ t = f (disc_boundary_point t) := by
        simp [γ, disc_boundary_param, ContinuousMap.comp_apply]
      simpa [k] using (F.map_zero_left t).trans hγ
    refine ⟨disc_cone_param_isQuotientMap.lift k hkfactor, ?_⟩
    -- The quotient lift already has the correct values on the circle boundary.
    exact restrictLiftOfDiscHomotopy_eq_boundary hkfactor htop
  · intro hdisc
    -- Route correction: instead of building a second quotient argument on the disc, transport the
    -- extension property to the square and use the square filler to compare paths directly.
    have hsquare := (discExtension_iff_squareExtension D).1 hdisc
    have hpaths := pathsHomotopic_of_squareExtension hsquare
    exact (isSimplyConnected_iff_paths_homotopic_in_subtype D hD_open hD_connected).2
      (fun {x y} p q ↦ hpaths p q)

/-- Helper for Exercise II.1-extra-15: extending maps from the boundary of the unit square should
be equivalent to null-homotopy of loops in `D`. -/
lemma square_extension_iff_isSimplyConnected (D : Set ℂ) (hD_open : IsOpen D)
    (hD_connected : IsConnected D) :
    IsSimplyConnected D ↔
      (∀ f : C(unitSquareBoundary, D),
        ∃ g : C(I × I, D), g.restrict unitSquareBoundary = f) := by
  -- Route correction: the square clause is just the disc clause transported along the explicit
  -- square-disc homeomorphism, so no separate square quotient package is needed.
  exact (disc_extension_iff_isSimplyConnected D hD_open hD_connected).trans
    (discExtension_iff_squareExtension D)

/-- Cartan section05 0025_Exercise_II_1_extra_15: for a connected open subset `D` of `ℂ`, the
following are equivalent: `D` is simply connected; every continuous map from the boundary of the
closed unit disc into `D` extends to the whole disc; every continuous map from the boundary of the
unit square into `D` extends to the whole square; and any two paths in `D` with the same endpoints
are homotopic with fixed endpoints. -/
-- Proof sketch: use that a connected open subset of `ℂ` is path connected, identify clause `(d)`
-- with `simply_connected_iff_paths_homotopic'` for the subtype `D`, and relate clauses `(b)` and
-- `(c)` to null-homotopies of loops via the standard quotient descriptions of the disc and square.
theorem isSimplyConnected_tfae_disc_square_extension_and_paths (D : Set ℂ) (hD_open : IsOpen D)
    (hD_connected : IsConnected D) :
    List.TFAE
      [ IsSimplyConnected D,
        ∀ f : C(closedUnitDiscBoundary, D),
          ∃ g : C(closedBall (0 : ℂ) 1, D), g.restrict closedUnitDiscBoundary = f,
        ∀ f : C(unitSquareBoundary, D),
          ∃ g : C(I × I, D),
            g.restrict unitSquareBoundary = f,
        ∀ ⦃x y : D⦄ (p q : Path x y), p.Homotopic q ]
    := by
  -- First identify clause `(d)` with the subtype formulation of simple connectedness.
  tfae_have 1 ↔ 4 :=
    isSimplyConnected_iff_paths_homotopic_in_subtype D hD_open hD_connected
  -- Next isolate the disc-extension clause as the boundary-null-homotopy bridge.
  tfae_have 1 ↔ 2 :=
    disc_extension_iff_isSimplyConnected D hD_open hD_connected
  -- Finally isolate the analogous square-extension bridge.
  tfae_have 1 ↔ 3 :=
    square_extension_iff_isSimplyConnected D hD_open hD_connected
  tfae_finish

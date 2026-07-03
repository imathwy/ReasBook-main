import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Instances.Sphere
import SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifoldsLee.Chap04.Sec04_24.Proposition_4_22
import SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_2
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Manifold

noncomputable section

local notation "R4" => EuclideanSpace ℝ (Fin 4)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "unitSphere2" => Metric.sphere (0 : R3) 1

/-- The polynomial map `Φ : ℝ⁴ → ℝ²` from Problem 5-1. -/
def problem_5_1_Phi : R4 → R2 :=
  fun p ↦
    WithLp.toLp 2
      ![p 0 ^ (2 : ℕ) + p 1, p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) + p 2 ^ (2 : ℕ) +
        p 3 ^ (2 : ℕ) + p 1]

/-- The target point `(0, 1)` in `ℝ²`. -/
def problem_5_1_target : R2 :=
  WithLp.toLp 2 ![(0 : ℝ), (1 : ℝ)]

/-- The level set `Φ⁻¹(0,1)` from Problem 5-1. -/
abbrev problem_5_1_levelSet : Set R4 :=
  problem_5_1_Phi ⁻¹' Set.singleton problem_5_1_target

/-- The coordinate formula for the map `Φ` in Problem 5-1. -/
theorem problem_5_1_Phi_apply (p : R4) :
    problem_5_1_Phi p =
      WithLp.toLp 2
        ![p 0 ^ (2 : ℕ) + p 1, p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) + p 2 ^ (2 : ℕ) +
          p 3 ^ (2 : ℕ) + p 1] := rfl

/-- Helper for Problem 5-1: the level-set equation is equivalent to the scalar system
`x² + y = 0` and `y² + s² + t² = 1`. -/
theorem problem_5_1_eq_target_iff (p : R4) :
    problem_5_1_Phi p = problem_5_1_target ↔
      p 0 ^ (2 : ℕ) + p 1 = 0 ∧ p 1 ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + p 3 ^ (2 : ℕ) = 1 := by
  constructor
  · intro hp
    have h0 : p 0 ^ (2 : ℕ) + p 1 = 0 := by
      have := congrArg (fun q : R2 ↦ q 0) hp
      simpa [problem_5_1_Phi, problem_5_1_target] using this
    have h1 : p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + p 3 ^ (2 : ℕ) + p 1 = 1 := by
      have := congrArg (fun q : R2 ↦ q 1) hp
      simpa [problem_5_1_Phi, problem_5_1_target] using this
    refine ⟨h0, ?_⟩
    nlinarith
  · rintro ⟨h0, h1⟩
    ext i
    fin_cases i
    · simpa [problem_5_1_Phi, problem_5_1_target] using h0
    · have hcoord :
        p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + p 3 ^ (2 : ℕ) + p 1 = 1 := by
        nlinarith
      simpa [problem_5_1_Phi, problem_5_1_target] using hcoord

/-- Helper for Problem 5-1: points of the fiber also satisfy the quartic equation
`x⁴ + s² + t² = 1`. -/
theorem problem_5_1_fiber_quartic_eq_one {p : R4}
    (hp : problem_5_1_Phi p = problem_5_1_target) :
    p 0 ^ (4 : ℕ) + p 2 ^ (2 : ℕ) + p 3 ^ (2 : ℕ) = 1 := by
  -- Replace `y` by `-x²` in the second scalar equation of the fiber.
  rcases (problem_5_1_eq_target_iff p).mp hp with ⟨h0, h1⟩
  nlinarith

/-- Helper for Problem 5-1: the scaling factor `1 + x²` is always positive. -/
theorem problem_5_1_one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ (2 : ℕ) := by
  nlinarith [sq_nonneg x]

/-- Helper for Problem 5-1: the scaling factor `√(1 + x²)` never vanishes. -/
theorem problem_5_1_sqrt_one_add_sq_ne_zero (x : ℝ) :
    Real.sqrt (1 + x ^ (2 : ℕ)) ≠ 0 := by
  exact Real.sqrt_ne_zero'.mpr (problem_5_1_one_add_sq_pos x)

/-- Helper for Problem 5-1: squaring `√(1 + x²)` recovers `1 + x²`. -/
theorem problem_5_1_sqrt_one_add_sq_sq (x : ℝ) :
    Real.sqrt (1 + x ^ (2 : ℕ)) ^ (2 : ℕ) = 1 + x ^ (2 : ℕ) := by
  -- The argument of the square root is nonnegative by construction.
  simpa using Real.sq_sqrt (show 0 ≤ 1 + x ^ (2 : ℕ) by nlinarith [sq_nonneg x])

/-- Helper for Problem 5-1: the derivative of `√(1 + x²)` has the simplified scalar factor
`x / √(1 + x²)`. -/
theorem problem_5_1_sqrt_deriv_scalar (x : ℝ) :
    (1 / (2 * Real.sqrt (1 + x ^ (2 : ℕ)))) * (2 * x) = x / Real.sqrt (1 + x ^ (2 : ℕ)) := by
  have hx : Real.sqrt (1 + x ^ (2 : ℕ)) ≠ 0 := problem_5_1_sqrt_one_add_sq_ne_zero x
  field_simp [hx]

/-- Helper for Problem 5-1: the scalar factor `x ↦ √(1 + x²)` has the expected derivative. -/
theorem problem_5_1_hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ (2 : ℕ)))
      (x / Real.sqrt (1 + x ^ (2 : ℕ))) x := by
  -- Differentiate `1 + x²` first, then compose with the square-root derivative.
  have h_inner : HasDerivAt (fun x : ℝ => 1 + x ^ (2 : ℕ)) (2 * x) x := by
    simpa [pow_two, two_mul, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using ((hasDerivAt_id x).pow 2).const_add 1
  have h_sqrt :
      HasDerivAt (fun x : ℝ => Real.sqrt (1 + x ^ (2 : ℕ)))
        ((2 * x) / (2 * Real.sqrt (1 + x ^ (2 : ℕ)))) x :=
    h_inner.sqrt (ne_of_gt (problem_5_1_one_add_sq_pos x))
  have h_scalar :
      (2 * x) / (2 * Real.sqrt (1 + x ^ (2 : ℕ))) =
        x / Real.sqrt (1 + x ^ (2 : ℕ)) := by
    have hx : Real.sqrt (1 + x ^ (2 : ℕ)) ≠ 0 := problem_5_1_sqrt_one_add_sq_ne_zero x
    field_simp [hx]
  -- Simplify the scalar coefficient to the textbook form `x / √(1 + x²)`.
  simpa [h_scalar] using h_sqrt

/-- Helper for Problem 5-1: evaluating the second scalar linearization of `Φ` on a tangent
vector gives the textbook coefficient formula. -/
theorem problem_5_1_Phi_second_coordinate_linearization_apply (p v : R4) :
    let d0 : R4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) 0
    let d1 : R4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) 1
    let d2 : R4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) 2
    let d3 : R4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) 3
    let L : R4 →L[ℝ] ℝ :=
      (2 * p 0) • d0 + (2 * p 1) • d1 + (2 * p 2) • d2 + (2 * p 3) • d3 + d1
    L v =
      2 * p 0 * v 0 + (2 * p 1 + 1) * v 1 + 2 * p 2 * v 2 + 2 * p 3 * v 3 := by
  -- Evaluate each projection on `v` and collect the scalar coefficients coordinatewise.
  simp only [PiLp.proj_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- Helper for Problem 5-1: the Jacobian of `Φ` applied to a tangent vector is the expected
coordinate formula. -/
theorem problem_5_1_Phi_fderiv_apply (p v : R4) :
    fderiv ℝ problem_5_1_Phi p v =
      WithLp.toLp 2
        ![2 * p 0 * v 0 + v 1,
          2 * p 0 * v 0 + (2 * p 1 + 1) * v 1 + 2 * p 2 * v 2 + 2 * p 3 * v 3] := by
  let d0 : R4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) 0
  let d1 : R4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) 1
  let d2 : R4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) 2
  let d3 : R4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 ↦ ℝ) 3
  let L0 : R4 →L[ℝ] ℝ := (2 * p 0) • d0 + d1
  let L1 : R4 →L[ℝ] ℝ := (2 * p 0) • d0 + (2 * p 1) • d1 + (2 * p 2) • d2 + (2 * p 3) • d3 + d1
  have h0 :
      HasFDerivAt (fun q : R4 ↦ q 0) d0 p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 4 ↦ ℝ) p 0
  have h1 :
      HasFDerivAt (fun q : R4 ↦ q 1) d1 p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 4 ↦ ℝ) p 1
  have h2 :
      HasFDerivAt (fun q : R4 ↦ q 2) d2 p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 4 ↦ ℝ) p 2
  have h3 :
      HasFDerivAt (fun q : R4 ↦ q 3) d3 p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 4 ↦ ℝ) p 3
  have hcoord0 :
      HasFDerivAt (fun q : R4 ↦ q 0 ^ (2 : ℕ) + q 1) L0 p := by
    -- Differentiate the first scalar coordinate directly.
    simpa [L0, d0, d1] using (h0.pow 2).add h1
  have hcoord1 :
      HasFDerivAt
        (fun q : R4 ↦ q 0 ^ (2 : ℕ) + q 1 ^ (2 : ℕ) + q 2 ^ (2 : ℕ) + q 3 ^ (2 : ℕ) + q 1)
        L1 p := by
    -- Differentiate the second scalar coordinate in the association order used in the formula.
    simpa [L1, d0, d1, d2, d3, add_assoc] using
      ((h0.pow 2).add ((h1.pow 2).add ((h2.pow 2).add ((h3.pow 2).add h1))))
  have hpi :
      HasFDerivAt
        (fun q : R4 ↦
          ![q 0 ^ (2 : ℕ) + q 1,
            q 0 ^ (2 : ℕ) + q 1 ^ (2 : ℕ) + q 2 ^ (2 : ℕ) + q 3 ^ (2 : ℕ) + q 1])
        (ContinuousLinearMap.pi ![L0, L1]) p := by
    -- Package the two scalar derivatives into a derivative of the `Fin 2 → ℝ` tuple.
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hcoord0
    · simpa using hcoord1
  have htoLp :
      HasFDerivAt
        (WithLp.toLp 2 : (Fin 2 → ℝ) → R2)
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap)
        ![p 0 ^ (2 : ℕ) + p 1,
          p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + p 3 ^ (2 : ℕ) + p 1] :=
    PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ)
      ![p 0 ^ (2 : ℕ) + p 1,
        p 0 ^ (2 : ℕ) + p 1 ^ (2 : ℕ) + p 2 ^ (2 : ℕ) + p 3 ^ (2 : ℕ) + p 1]
  have hPhi :
      HasFDerivAt problem_5_1_Phi
        (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.pi ![L0, L1])) p := by
    -- Compose the tuple derivative with the fixed linear equivalence `WithLp.toLp`.
    simpa [problem_5_1_Phi] using htoLp.comp p hpi
  rw [hPhi.fderiv]
  -- Compare the two coordinate tuples first, then reapply `WithLp.toLp`.
  have htuple :
      ![L0 v, L1 v] =
        ![2 * p 0 * v 0 + v 1,
          2 * p 0 * v 0 + (2 * p 1 + 1) * v 1 + 2 * p 2 * v 2 + 2 * p 3 * v 3] := by
    ext i
    fin_cases i
    · simp [L0, d0, d1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        PiLp.proj_apply, smul_eq_mul]
    · simpa [L1, d0, d1, d2, d3] using
        problem_5_1_Phi_second_coordinate_linearization_apply p v
  convert congrArg (WithLp.toLp 2) htuple using 1
  · ext i
    fin_cases i <;> rfl

/-- Helper for Problem 5-1: the ambient parametrization whose sphere restriction is the geometric
model for the fiber. -/
def problem_5_1_ambientParam : R3 → R4 :=
  fun p ↦
    WithLp.toLp 2
      ![p 0, -(p 0 ^ (2 : ℕ)),
        p 1 * Real.sqrt (1 + p 0 ^ (2 : ℕ)),
        p 2 * Real.sqrt (1 + p 0 ^ (2 : ℕ))]

/-- Helper for Problem 5-1: the sphere parametrization of the level set is the restriction of the
ambient parametrization to `S²`. -/
def problem_5_1_sphere_to_ambient : unitSphere2 → R4 :=
  fun q ↦ problem_5_1_ambientParam q

/-- Helper for Problem 5-1: the square-root scaling factor is smooth on all of `ℝ`. -/
theorem problem_5_1_scalarFactor_contDiff :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : ℝ => Real.sqrt (1 + x ^ (2 : ℕ))) := by
  have hpoly : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x : ℝ => 1 + x ^ (2 : ℕ)) := by
    fun_prop
  -- The source route differentiates the scalar factor before reassembling the ambient map.
  simpa using hpoly.sqrt (fun x ↦ ne_of_gt (problem_5_1_one_add_sq_pos x))

/-- Helper for Problem 5-1: the ambient parametrization is smooth on `ℝ³`. -/
theorem problem_5_1_ambientParam_contMDiff :
    ContMDiff (𝓡 3) (𝓡 4) ∞ problem_5_1_ambientParam := by
  rw [contMDiff_iff_contDiff]
  -- Rewrite to the explicit Euclidean formula before assembling the coordinates with `toLp`.
  have hExplicit :
      ContDiff ℝ ∞
        (fun p : R3 ↦
          WithLp.toLp 2
            ![p 0, -(p 0 ^ (2 : ℕ)),
              p 1 * Real.sqrt (1 + p 0 ^ (2 : ℕ)),
              p 2 * Real.sqrt (1 + p 0 ^ (2 : ℕ))]) := by
    -- Keep the smoothness proof on the Euclidean side and package the coordinates at the end.
    refine (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 4 ↦ ℝ)).comp ?_
    rw [contDiff_pi]
    intro i
    fin_cases i
    · simpa using
        (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := 0))
    · simpa using
        ((contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := 0)).pow 2).neg
    · have h1 :
          ContDiff ℝ ∞ (fun p : R3 ↦ p 1) :=
        contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := 1)
      have hsqrt :
          ContDiff ℝ ∞ (fun p : R3 ↦ Real.sqrt (1 + p 0 ^ (2 : ℕ))) := by
        simpa using (problem_5_1_scalarFactor_contDiff.of_le (by simp)).comp
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := 0))
      simpa using h1.mul hsqrt
    · have h2 :
          ContDiff ℝ ∞ (fun p : R3 ↦ p 2) :=
        contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := 2)
      have hsqrt :
          ContDiff ℝ ∞ (fun p : R3 ↦ Real.sqrt (1 + p 0 ^ (2 : ℕ))) := by
        simpa using (problem_5_1_scalarFactor_contDiff.of_le (by simp)).comp
          (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (i := 0))
      simpa using h2.mul hsqrt
  unfold problem_5_1_ambientParam
  simpa using hExplicit

/-- Helper for Problem 5-1: the scaled sphere coordinates in the ambient parametrization share one
uniform product-rule derivative formula. -/
theorem problem_5_1_scaled_sqrt_coord_fderiv_apply (j : Fin 2) (p v : R3) :
    fderiv ℝ (fun q : R3 ↦ q j.succ * Real.sqrt (1 + q 0 ^ (2 : ℕ))) p v =
      v j.succ * Real.sqrt (1 + p 0 ^ (2 : ℕ)) +
        p j.succ * (p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ))) * v 0 := by
  have hcoord :
      HasFDerivAt (fun q : R3 ↦ q j.succ)
        (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) j.succ) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p j.succ
  have hfirst :
      HasFDerivAt (fun q : R3 ↦ q 0)
        (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0
  have hsqrt :
      HasFDerivAt (fun q : R3 ↦ Real.sqrt (1 + q 0 ^ (2 : ℕ)))
        ((p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ))) •
          (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0 : R3 →L[ℝ] ℝ)) p := by
    -- Route correction: compose the scalar one-variable derivative with the first-coordinate
    -- projection before using the product rule for the ambient coordinates.
    simpa using
      (problem_5_1_hasDerivAt_sqrt_one_add_sq (p 0)).comp_hasFDerivAt p hfirst
  have hprod :
      HasFDerivAt (fun q : R3 ↦ q j.succ * Real.sqrt (1 + q 0 ^ (2 : ℕ)))
        (p j.succ •
            ((p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ))) •
              (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0 : R3 →L[ℝ] ℝ)) +
          Real.sqrt (1 + p 0 ^ (2 : ℕ)) •
            (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) j.succ : R3 →L[ℝ] ℝ)) p := by
    simpa [smul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      hcoord.mul hsqrt
  rw [hprod.fderiv]
  -- Evaluate the product-rule linear map on `v` and normalize the scalar coefficients.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply,
    smul_eq_mul]
  ring

/-- Helper for Problem 5-1: the Jacobian of the ambient parametrization is the expected
coordinate formula. -/
theorem problem_5_1_ambientParam_fderiv_apply (p v : R3) :
    fderiv ℝ problem_5_1_ambientParam p v =
      WithLp.toLp 2
        ![v 0,
          -(2 * p 0 * v 0),
          v 1 * Real.sqrt (1 + p 0 ^ (2 : ℕ)) +
            p 1 * (p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ))) * v 0,
          v 2 * Real.sqrt (1 + p 0 ^ (2 : ℕ)) +
            p 2 * (p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ))) * v 0] := by
  let d0 : R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let d1 : R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let d2 : R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  let L0 : R3 →L[ℝ] ℝ := d0
  let L1 : R3 →L[ℝ] ℝ := -((2 * p 0) • d0)
  let L2 : R3 →L[ℝ] ℝ :=
    (p 1 * (p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ)))) • d0 +
      Real.sqrt (1 + p 0 ^ (2 : ℕ)) • d1
  let L3 : R3 →L[ℝ] ℝ :=
    (p 2 * (p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ)))) • d0 +
      Real.sqrt (1 + p 0 ^ (2 : ℕ)) • d2
  have h0 :
      HasFDerivAt (fun q : R3 ↦ q 0) d0 p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0
  have hcoord0 :
      HasFDerivAt (fun q : R3 ↦ q 0) L0 p := by
    simpa [L0] using h0
  have hcoord1 :
      HasFDerivAt (fun q : R3 ↦ -(q 0 ^ (2 : ℕ))) L1 p := by
    -- Differentiate `-x²` in the first coordinate.
    simpa [L1, d0] using (h0.pow 2).neg
  have hsqrt :
      HasFDerivAt (fun q : R3 ↦ Real.sqrt (1 + q 0 ^ (2 : ℕ)))
        ((p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ))) • d0) p := by
    simpa [d0] using
      (problem_5_1_hasDerivAt_sqrt_one_add_sq (p 0)).comp_hasFDerivAt p h0
  have hcoord2 :
      HasFDerivAt
        (fun q : R3 ↦ q 1 * Real.sqrt (1 + q 0 ^ (2 : ℕ)))
        L2 p := by
    have h1 :
        HasFDerivAt (fun q : R3 ↦ q 1) d1 p :=
      PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 1
    -- Use the shared product-rule computation for the third coordinate.
    simpa [mul_comm, L2, d0, d1, smul_add, smul_smul, add_comm, add_left_comm, add_assoc,
      mul_left_comm, mul_assoc] using h1.mul hsqrt
  have hcoord3 :
      HasFDerivAt
        (fun q : R3 ↦ q 2 * Real.sqrt (1 + q 0 ^ (2 : ℕ)))
        L3 p := by
    have h2 :
        HasFDerivAt (fun q : R3 ↦ q 2) d2 p :=
      PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 2
    -- The fourth coordinate is the same product rule with index `2`.
    simpa [mul_comm, L3, d0, d2, smul_add, smul_smul, add_comm, add_left_comm, add_assoc,
      mul_left_comm, mul_assoc] using h2.mul hsqrt
  have hpi :
      HasFDerivAt
        (fun q : R3 ↦
          ![q 0, -(q 0 ^ (2 : ℕ)),
            q 1 * Real.sqrt (1 + q 0 ^ (2 : ℕ)),
            q 2 * Real.sqrt (1 + q 0 ^ (2 : ℕ))])
        (ContinuousLinearMap.pi ![L0, L1, L2, L3]) p := by
    -- Assemble the four scalar derivatives into the derivative of the ambient tuple.
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hcoord0
    · simpa using hcoord1
    · simpa using hcoord2
    · simpa using hcoord3
  have htoLp :
      HasFDerivAt
        (WithLp.toLp 2 : (Fin 4 → ℝ) → R4)
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).symm.toContinuousLinearMap)
        ![p 0, -(p 0 ^ (2 : ℕ)),
          p 1 * Real.sqrt (1 + p 0 ^ (2 : ℕ)),
          p 2 * Real.sqrt (1 + p 0 ^ (2 : ℕ))] :=
    PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 4 ↦ ℝ)
      ![p 0, -(p 0 ^ (2 : ℕ)),
        p 1 * Real.sqrt (1 + p 0 ^ (2 : ℕ)),
        p 2 * Real.sqrt (1 + p 0 ^ (2 : ℕ))]
  have hParam :
      HasFDerivAt problem_5_1_ambientParam
        (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.pi ![L0, L1, L2, L3])) p := by
    simpa [problem_5_1_ambientParam] using htoLp.comp p hpi
  rw [hParam.fderiv]
  -- Compare the explicit coordinate tuples and then transport them back with `WithLp.toLp`.
  have htuple :
      ![L0 v, L1 v, L2 v, L3 v] =
        ![v 0,
          -(2 * p 0 * v 0),
          v 1 * Real.sqrt (1 + p 0 ^ (2 : ℕ)) +
            p 1 * (p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ))) * v 0,
          v 2 * Real.sqrt (1 + p 0 ^ (2 : ℕ)) +
            p 2 * (p 0 / Real.sqrt (1 + p 0 ^ (2 : ℕ))) * v 0] := by
    ext i
    fin_cases i
    · simp [L0, d0, PiLp.proj_apply]
    · simp [L1, d0, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
        PiLp.proj_apply, smul_eq_mul]
    · simpa [L2, d0, d1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        PiLp.proj_apply, smul_eq_mul] using by ring
    · simpa [L3, d0, d2, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        PiLp.proj_apply, smul_eq_mul] using by ring
  convert congrArg (WithLp.toLp 2) htuple using 1
  · ext i
    fin_cases i <;> rfl

/-- Helper for Problem 5-1: the derivative of the ambient parametrization is injective at every
point. -/
theorem problem_5_1_ambientParam_fderiv_injective (p : R3) :
    Function.Injective (fderiv ℝ problem_5_1_ambientParam p) := by
  intro v w hvw
  have h0 : v 0 = w 0 := by
    have hcoord := congrArg (fun z : R4 ↦ z 0) hvw
    simpa [problem_5_1_ambientParam_fderiv_apply] using hcoord
  have hsqrt_ne : Real.sqrt (1 + p 0 ^ (2 : ℕ)) ≠ 0 :=
    problem_5_1_sqrt_one_add_sq_ne_zero (p 0)
  have h1 : v 1 = w 1 := by
    have hcoord := congrArg (fun z : R4 ↦ z 2) hvw
    have hcoord' :
        v 1 * Real.sqrt (1 + p 0 ^ (2 : ℕ)) =
          w 1 * Real.sqrt (1 + p 0 ^ (2 : ℕ)) := by
      simpa [problem_5_1_ambientParam_fderiv_apply, h0] using hcoord
    exact mul_right_cancel₀ hsqrt_ne hcoord'
  have h2 : v 2 = w 2 := by
    have hcoord := congrArg (fun z : R4 ↦ z 3) hvw
    have hcoord' :
        v 2 * Real.sqrt (1 + p 0 ^ (2 : ℕ)) =
          w 2 * Real.sqrt (1 + p 0 ^ (2 : ℕ)) := by
      simpa [problem_5_1_ambientParam_fderiv_apply, h0] using hcoord
    exact mul_right_cancel₀ hsqrt_ne hcoord'
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Helper for Problem 5-1: the ambient parametrization is an immersion because its first output
coordinate recovers the first tangent coordinate and the remaining scaled coordinates recover the
other two. -/
theorem problem_5_1_ambientParam_isImmersion :
    Manifold.IsImmersion (𝓡 3) (𝓡 4) ∞ problem_5_1_ambientParam := by
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv
    problem_5_1_ambientParam_contMDiff).2 ?_
  intro p
  -- Reduce the manifold derivative to the Euclidean derivative already computed above.
  rw [mfderiv_eq_fderiv]
  exact problem_5_1_ambientParam_fderiv_injective p

/-- Helper for Problem 5-1: points on `S²` satisfy the coordinate identity
`u² + v² + w² = 1`. -/
theorem problem_5_1_unitSphere_coord_sq_sum (q : unitSphere2) :
    q.1 0 ^ (2 : ℕ) + q.1 1 ^ (2 : ℕ) + q.1 2 ^ (2 : ℕ) = 1 := by
  -- Rewrite sphere membership as `‖q‖ = 1`, then expand the Euclidean norm square.
  have hnorm : ‖q.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using q.2
  have hnorm_sq : ‖q.1‖ ^ (2 : ℕ) = 1 := by
    nlinarith [hnorm]
  have hcoords : ‖q.1‖ ^ (2 : ℕ) = q.1 0 ^ (2 : ℕ) + q.1 1 ^ (2 : ℕ) + q.1 2 ^ (2 : ℕ) := by
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, add_assoc, add_comm, add_left_comm]
      using (EuclideanSpace.real_norm_sq_eq q.1)
  nlinarith [hcoords, hnorm_sq]

/-- Helper for Problem 5-1: the sphere parametrization indeed lands in the level set. -/
theorem problem_5_1_sphere_to_ambient_mem_levelSet (q : unitSphere2) :
    problem_5_1_sphere_to_ambient q ∈ problem_5_1_levelSet := by
  -- Verify the two scalar equations of the fiber using the sphere coordinate identity.
  change problem_5_1_Phi (problem_5_1_sphere_to_ambient q) = problem_5_1_target
  rw [problem_5_1_eq_target_iff]
  constructor
  · simp [problem_5_1_sphere_to_ambient, problem_5_1_ambientParam]
  · have hcoords := problem_5_1_unitSphere_coord_sq_sum q
    have hsqrt_sq := problem_5_1_sqrt_one_add_sq_sq (q.1 0)
    -- Route correction: keep the source-style coordinate algebra instead of introducing a new
    -- abstract transport layer for sphere membership.
    have hfiber :
        (-(q.1 0 ^ (2 : ℕ))) ^ (2 : ℕ) +
            (q.1 1 * Real.sqrt (1 + q.1 0 ^ (2 : ℕ))) ^ (2 : ℕ) +
            (q.1 2 * Real.sqrt (1 + q.1 0 ^ (2 : ℕ))) ^ (2 : ℕ) = 1 := by
      nlinarith [hcoords, hsqrt_sq]
    simpa [problem_5_1_sphere_to_ambient, problem_5_1_ambientParam] using hfiber

/-- Helper for Problem 5-1: the standard inclusion `S² ↪ ℝ³` is a smooth embedding. -/
theorem problem_5_1_unitSphere_subtype_val_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ ((↑) : unitSphere2 → R3) := by
  -- Package the canonical sphere inclusion as an immersion using the manifold derivative test.
  let _ : Fact (Module.finrank ℝ R3 = 2 + 1) := ⟨by simp⟩
  refine Manifold.IsSmoothEmbedding.mk ?_ ?_
  · exact
      (Manifold.is_immersion_iff_forall_injective_mfderiv
          (I := 𝓡 2) (J := 𝓡 3) (F := ((↑) : unitSphere2 → R3))
          (contMDiff_coe_sphere (n := 2))).2
        (fun q => mfderiv_coe_sphere_injective (n := 2) q)
  · -- The subtype inclusion is already a topological embedding.
    simpa using
      (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding ((↑) : unitSphere2 → R3))

/-- Helper for Problem 5-1: the sphere parametrization is injective, because the first coordinate
fixes the scale factor and then the last two coordinates recover the sphere point. -/
theorem problem_5_1_sphere_to_ambient_injective :
    Function.Injective problem_5_1_sphere_to_ambient := by
  intro q r hqr
  have h0 : q.1 0 = r.1 0 := by
    have hcoord := congrArg (fun p : R4 ↦ p 0) hqr
    simpa [problem_5_1_sphere_to_ambient, problem_5_1_ambientParam] using hcoord
  have hsqrt :
      Real.sqrt (1 + q.1 0 ^ (2 : ℕ)) = Real.sqrt (1 + r.1 0 ^ (2 : ℕ)) := by
    simp [h0]
  have hsqrt_ne : Real.sqrt (1 + q.1 0 ^ (2 : ℕ)) ≠ 0 :=
    problem_5_1_sqrt_one_add_sq_ne_zero (q.1 0)
  have h1 : q.1 1 = r.1 1 := by
    have hcoord := congrArg (fun p : R4 ↦ p 2) hqr
    have hcoord' :
        q.1 1 * Real.sqrt (1 + q.1 0 ^ (2 : ℕ)) =
          r.1 1 * Real.sqrt (1 + q.1 0 ^ (2 : ℕ)) := by
      simpa [problem_5_1_sphere_to_ambient, problem_5_1_ambientParam, h0] using hcoord
    exact mul_right_cancel₀ hsqrt_ne hcoord'
  have h2 : q.1 2 = r.1 2 := by
    have hcoord := congrArg (fun p : R4 ↦ p 3) hqr
    have hcoord' :
        q.1 2 * Real.sqrt (1 + q.1 0 ^ (2 : ℕ)) =
          r.1 2 * Real.sqrt (1 + q.1 0 ^ (2 : ℕ)) := by
      simpa [problem_5_1_sphere_to_ambient, problem_5_1_ambientParam, h0] using hcoord
    exact mul_right_cancel₀ hsqrt_ne hcoord'
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- Helper for Problem 5-1: the sphere parametrization is a smooth embedding. -/
theorem problem_5_1_sphere_to_ambient_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) ∞ problem_5_1_sphere_to_ambient := by
  have hsubImm :
      Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞ ((↑) : unitSphere2 → R3) :=
    problem_5_1_unitSphere_subtype_val_isSmoothEmbedding.1
  have hImm :
      Manifold.IsImmersion (𝓡 2) (𝓡 4) ∞ problem_5_1_sphere_to_ambient := by
    -- The sphere parametrization is the ambient immersion restricted along the sphere inclusion.
    simpa [problem_5_1_sphere_to_ambient, Function.comp] using
      Manifold.IsImmersion.comp problem_5_1_ambientParam_isImmersion hsubImm
  -- Compactness of the source upgrades the injective immersion to a smooth embedding.
  exact smooth_embedding_of_compact_source_injective_isImmersion
    problem_5_1_sphere_to_ambient_injective hImm

/-- Helper for Problem 5-1: the explicit inverse-point formula from the level set back to `S²`. -/
def problem_5_1_levelSet_to_sphere_point (p : problem_5_1_levelSet) : R3 :=
  WithLp.toLp 2
    ![p.1 0,
      p.1 2 / Real.sqrt (1 + p.1 0 ^ (2 : ℕ)),
      p.1 3 / Real.sqrt (1 + p.1 0 ^ (2 : ℕ))]

/-- Helper for Problem 5-1: the explicit inverse point has squared coordinates summing to `1`. -/
theorem problem_5_1_levelSet_to_sphere_point_coord_sq_sum (p : problem_5_1_levelSet) :
    (problem_5_1_levelSet_to_sphere_point p) 0 ^ (2 : ℕ) +
        (problem_5_1_levelSet_to_sphere_point p) 1 ^ (2 : ℕ) +
        (problem_5_1_levelSet_to_sphere_point p) 2 ^ (2 : ℕ) = 1 := by
  -- Expand the inverse-point coordinates and clear the common denominator using the quartic
  -- identity on the fiber.
  have hp_quartic : p.1 0 ^ (4 : ℕ) + p.1 2 ^ (2 : ℕ) + p.1 3 ^ (2 : ℕ) = 1 :=
    problem_5_1_fiber_quartic_eq_one p.2
  have hsqrt_ne : Real.sqrt (1 + p.1 0 ^ (2 : ℕ)) ≠ 0 :=
    problem_5_1_sqrt_one_add_sq_ne_zero (p.1 0)
  have hone_add_ne : 1 + p.1 0 ^ (2 : ℕ) ≠ 0 := by
    exact ne_of_gt (problem_5_1_one_add_sq_pos (p.1 0))
  have hsqrt_sq : Real.sqrt (1 + p.1 0 ^ (2 : ℕ)) ^ (2 : ℕ) = 1 + p.1 0 ^ (2 : ℕ) :=
    problem_5_1_sqrt_one_add_sq_sq (p.1 0)
  change p.1 0 ^ (2 : ℕ) +
      (p.1 2 / Real.sqrt (1 + p.1 0 ^ (2 : ℕ))) ^ (2 : ℕ) +
      (p.1 3 / Real.sqrt (1 + p.1 0 ^ (2 : ℕ))) ^ (2 : ℕ) = 1
  rw [div_pow, div_pow]
  field_simp [hone_add_ne]
  nlinarith [hp_quartic, hsqrt_sq]

/-- Helper for Problem 5-1: the inverse-point formula really lands on `S²`. -/
theorem problem_5_1_levelSet_to_sphere_point_mem (p : problem_5_1_levelSet) :
    problem_5_1_levelSet_to_sphere_point p ∈ unitSphere2 := by
  -- Convert the coordinate-sum identity into the Euclidean norm condition `‖x‖ = 1`.
  have hcoords := problem_5_1_levelSet_to_sphere_point_coord_sq_sum p
  have hnorm_sq :
      ‖problem_5_1_levelSet_to_sphere_point p‖ ^ (2 : ℕ) = 1 := by
    calc
      ‖problem_5_1_levelSet_to_sphere_point p‖ ^ (2 : ℕ) =
          (problem_5_1_levelSet_to_sphere_point p) 0 ^ (2 : ℕ) +
            (problem_5_1_levelSet_to_sphere_point p) 1 ^ (2 : ℕ) +
            (problem_5_1_levelSet_to_sphere_point p) 2 ^ (2 : ℕ) := by
              simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, add_assoc]
      _ = 1 := hcoords
  have hnorm : ‖problem_5_1_levelSet_to_sphere_point p‖ = 1 := by
    have hnonneg : 0 ≤ ‖problem_5_1_levelSet_to_sphere_point p‖ := norm_nonneg _
    nlinarith [hnorm_sq, hnonneg]
  simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hnorm

/-- Helper for Problem 5-1: the explicit inverse map from the level set to the sphere. -/
def problem_5_1_levelSet_to_sphere (p : problem_5_1_levelSet) : unitSphere2 :=
  ⟨problem_5_1_levelSet_to_sphere_point p, problem_5_1_levelSet_to_sphere_point_mem p⟩

/-- Helper for Problem 5-1: applying the sphere parametrization to the explicit inverse recovers
the original point of the fiber. -/
theorem problem_5_1_sphere_to_ambient_levelSet_inverse (p : problem_5_1_levelSet) :
    problem_5_1_sphere_to_ambient (problem_5_1_levelSet_to_sphere p) = p.1 := by
  -- The only nontrivial coordinates are the recovered `y = -x²` relation and the cancellation of
  -- the square-root scaling in the `s` and `t` coordinates.
  rcases (problem_5_1_eq_target_iff p.1).mp p.2 with ⟨hxy, _⟩
  have hsqrtNe := problem_5_1_sqrt_one_add_sq_ne_zero (p.1 0)
  ext i
  fin_cases i
  · simp [problem_5_1_sphere_to_ambient, problem_5_1_levelSet_to_sphere,
      problem_5_1_levelSet_to_sphere_point, problem_5_1_ambientParam]
  · simp [problem_5_1_sphere_to_ambient, problem_5_1_levelSet_to_sphere,
      problem_5_1_levelSet_to_sphere_point, problem_5_1_ambientParam]
    nlinarith
  · simp [problem_5_1_sphere_to_ambient, problem_5_1_levelSet_to_sphere,
      problem_5_1_levelSet_to_sphere_point, problem_5_1_ambientParam]
    field_simp [hsqrtNe]
  · simp [problem_5_1_sphere_to_ambient, problem_5_1_levelSet_to_sphere,
      problem_5_1_levelSet_to_sphere_point, problem_5_1_ambientParam]
    field_simp [hsqrtNe]

/-- Helper for Problem 5-1: the geometric sphere parametrization has image exactly the fiber
`Φ⁻¹(0, 1)`. -/
theorem problem_5_1_sphere_to_ambient_range_eq_levelSet :
    Set.range problem_5_1_sphere_to_ambient = problem_5_1_levelSet := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact problem_5_1_sphere_to_ambient_mem_levelSet q
  · intro hp
    refine ⟨problem_5_1_levelSet_to_sphere ⟨p, hp⟩, ?_⟩
    simpa using problem_5_1_sphere_to_ambient_levelSet_inverse ⟨p, hp⟩

/-- Helper for Problem 5-1: on the fiber over `(0,1)`, the Euclidean derivative of `Φ` is
surjective. -/
theorem problem_5_1_Phi_fderiv_surjective_on_levelSet (p : R4)
    (hp : problem_5_1_Phi p = problem_5_1_target) :
    Function.Surjective (fderiv ℝ problem_5_1_Phi p) := by
  rcases (problem_5_1_eq_target_iff p).mp hp with ⟨hxy, hst⟩
  intro y
  by_cases hs : p 2 ≠ 0
  · refine ⟨WithLp.toLp 2
      ![(0 : ℝ), y 0, (y 1 - (2 * p 1 + 1) * y 0) / (2 * p 2), (0 : ℝ)], ?_⟩
    -- Use the nonzero `s`-coordinate to solve the second linear equation directly.
    rw [problem_5_1_Phi_fderiv_apply]
    ext i
    fin_cases i
    · simp
    · simp
      field_simp [hs]
      ring
  by_cases ht : p 3 ≠ 0
  · refine ⟨WithLp.toLp 2
      ![(0 : ℝ), y 0, (0 : ℝ), (y 1 - (2 * p 1 + 1) * y 0) / (2 * p 3)], ?_⟩
    -- If `t ≠ 0`, the same linear solve works in the fourth coordinate instead.
    rw [problem_5_1_Phi_fderiv_apply]
    ext i
    fin_cases i
    · simp
    · simp
      field_simp [ht]
      ring
  have hp2 : p 2 = 0 := by simpa using hs
  have hp3 : p 3 = 0 := by simpa using ht
  have hp1_sq : p 1 ^ (2 : ℕ) = 1 := by simpa [hp2, hp3] using hst
  have hp1 : p 1 = -1 := by
    nlinarith [hxy, hp1_sq, sq_nonneg (p 0)]
  have hp0_sq : p 0 ^ (2 : ℕ) = 1 := by
    nlinarith [hxy, hp1]
  have hp0_ne : p 0 ≠ 0 := by
    intro hp0
    nlinarith [hp0_sq, hp0]
  refine ⟨WithLp.toLp 2 ![(y 0 + y 1) / (4 * p 0), (y 0 - y 1) / 2, (0 : ℝ), (0 : ℝ)], ?_⟩
  -- In the final branch, the fiber equations force `y = -1` and `x² = 1`, so `x ≠ 0`.
  rw [problem_5_1_Phi_fderiv_apply]
  ext i
  fin_cases i
  · simp [hp1]
    field_simp [hp0_ne]
    ring
  · simp [hp1, hp2, hp3]
    field_simp [hp0_ne]
    ring

-- Proof sketch: compute the Jacobian matrix of `problem_5_1_Phi` explicitly and check that at
-- each point of the fiber over `(0,1)` its two rows are linearly independent, hence the derivative
-- `ℝ⁴ →L[ℝ] ℝ²` is surjective.
/-- Problem 5-1 (1): `(0, 1)` is a regular value of the map `Φ`, i.e. the derivative of `Φ` is
surjective at every point of the level set `Φ⁻¹(0, 1)`. -/
theorem problem_5_1_target_is_regular_value :
    IsRegularValue (𝓡 4) (𝓡 2) problem_5_1_Phi problem_5_1_target := by
  intro p hp
  -- The manifold derivative on Euclidean space is the Fréchet derivative already computed above.
  rw [mfderiv_eq_fderiv]
  exact problem_5_1_Phi_fderiv_surjective_on_levelSet p hp

-- Proof sketch: solve the first equation of the level set to identify `Φ⁻¹(0,1)` with the smooth
-- surface `x^4 + s^2 + t^2 = 1`, give this subtype its induced two-dimensional manifold
-- structure, and then use the radial parametrization of this surface to build a diffeomorphism
-- with the unit sphere in `ℝ³`.
/-- Helper for Problem 5-1: Proposition 5.2 gives the image of the sphere parametrization its
induced `2`-manifold structure together with the tautological diffeomorphism from `S²`. -/
theorem problem_5_1_range_induced_image_structure :
    ∃ (_ : ChartedSpace R2 (Set.range problem_5_1_sphere_to_ambient))
      (_ : IsManifold (𝓡 2) ∞ (Set.range problem_5_1_sphere_to_ambient)),
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) ∞
          (Subtype.val : Set.range problem_5_1_sphere_to_ambient → R4) ∧
        ∃ Φ : unitSphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Set.range problem_5_1_sphere_to_ambient,
          ∀ q, ((Φ q : Set.range problem_5_1_sphere_to_ambient) : R4) =
            problem_5_1_sphere_to_ambient q := by
  -- Route correction: use the induced image structure from Proposition 5.2 directly on the range,
  -- instead of rebuilding the range manifold data separately from the pointwise formulas.
  rcases smooth_embedding_range_has_induced_manifold_structure
      (I := 𝓡 4) (J := 𝓡 2) (F := problem_5_1_sphere_to_ambient)
      problem_5_1_sphere_to_ambient_isSmoothEmbedding with ⟨cs, hcs⟩
  -- Unpack the proposition exactly into the charted-space, manifold, embedding, and diffeomorphism
  -- data needed for the endgame.
  have hcs' :
      ∃ (_ : IsManifold (𝓡 2) ∞ (Set.range problem_5_1_sphere_to_ambient)),
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) ∞
          (Subtype.val : Set.range problem_5_1_sphere_to_ambient → R4) ∧
        ∃ Φ : unitSphere2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Set.range problem_5_1_sphere_to_ambient,
          ∀ q, ((Φ q : Set.range problem_5_1_sphere_to_ambient) : R4) =
            problem_5_1_sphere_to_ambient q := by
    simpa [IsInducedImageManifoldStructure] using hcs
  rcases hcs' with ⟨hs, hSubtype, Φ, hΦ⟩
  exact ⟨cs, hs, hSubtype, Φ, hΦ⟩

/-- Helper for Problem 5-1: the image of the sphere parametrization carries the induced smooth
embedded `2`-manifold structure in `ℝ⁴`. -/
theorem problem_5_1_range_embedded_structure :
    ∃ (_ : ChartedSpace R2 (Set.range problem_5_1_sphere_to_ambient))
      (_ : IsManifold (𝓡 2) ∞ (Set.range problem_5_1_sphere_to_ambient)),
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) ∞
          (Subtype.val : Set.range problem_5_1_sphere_to_ambient → R4) := by
  rcases problem_5_1_range_induced_image_structure with ⟨cs, hs, hSubtype, Φ, hΦ⟩
  exact ⟨cs, hs, hSubtype⟩

/-- Helper for Problem 5-1: the range of the sphere parametrization carries the induced smooth
embedded `2`-manifold structure and is diffeomorphic to `S²`. -/
theorem problem_5_1_range_diffeomorphic_to_unitSphere :
    ∃ (_ : ChartedSpace R2 (Set.range problem_5_1_sphere_to_ambient))
      (_ : IsManifold (𝓡 2) ∞ (Set.range problem_5_1_sphere_to_ambient))
      (_ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) ∞
        (Subtype.val : Set.range problem_5_1_sphere_to_ambient → R4)),
        Nonempty (Set.range problem_5_1_sphere_to_ambient ≃ₘ⟮𝓡 2, 𝓡 2⟯ unitSphere2) := by
  rcases problem_5_1_range_induced_image_structure with ⟨cs, hs, hSubtype, Φ, hΦ⟩
  -- Keep the inverse diffeomorphism on the same chosen range structure.
  exact ⟨cs, hs, hSubtype, ⟨Φ.symm⟩⟩

/-- Problem 5-1 (2): the regular level set `Φ⁻¹(0, 1)` carries a smooth embedded `2`-manifold
structure in `ℝ⁴`. -/
theorem problem_5_1_levelSet_has_embedded_submanifold_structure :
    ∃ (_ : ChartedSpace R2 problem_5_1_levelSet)
      (_ : IsManifold (𝓡 2) ∞ problem_5_1_levelSet),
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) ∞
        (Subtype.val : problem_5_1_levelSet → R4) := by
  rcases problem_5_1_range_embedded_structure with ⟨cs, hs, hSubtype⟩
  rw [← problem_5_1_sphere_to_ambient_range_eq_levelSet]
  exact ⟨cs, hs, hSubtype⟩

/-- Problem 5-1 (2): the regular level set `Φ⁻¹(0, 1)` carries a smooth embedded `2`-manifold
structure in `ℝ⁴` for which it is diffeomorphic to the unit sphere `S²`. -/
theorem problem_5_1_levelSet_diffeomorphic_to_unitSphere :
    ∃ (_ : ChartedSpace R2 problem_5_1_levelSet)
      (_ : IsManifold (𝓡 2) ∞ problem_5_1_levelSet)
      (_ : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 4) ∞
        (Subtype.val : problem_5_1_levelSet → R4)),
        Nonempty (problem_5_1_levelSet ≃ₘ⟮𝓡 2, 𝓡 2⟯ unitSphere2) := by
  rcases problem_5_1_range_diffeomorphic_to_unitSphere with
    ⟨cs, hs, hSubtype, hDiffeomorph⟩
  rw [← problem_5_1_sphere_to_ambient_range_eq_levelSet]
  exact ⟨cs, hs, hSubtype, hDiffeomorph⟩

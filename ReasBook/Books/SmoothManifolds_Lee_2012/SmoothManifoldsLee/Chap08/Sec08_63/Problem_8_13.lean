import Mathlib
import SmoothManifolds_Lee_2012.Chap01.Sec01_07.Problem_1_7
import SmoothManifolds_Lee_2012.Chap04.Sec04_27.Problem_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace
open VectorField

noncomputable section

-- Domain sampling pass: this item lies in the smooth-manifold vector-field API on the standard
-- sphere. Relevant declarations checked before refinement:
-- `Cₛ^∞⟮I; E, TangentSpace I⟯` from the chapter's vector-field notation file,
-- the chapter's use of that owner in `Problem_8_3`,
-- `SmoothVectorField`/`ContMDiffSection` surfaces in `Example_8_5`, `Example_8_24`,
-- and the stereographic-sphere API in `Problem_1_7.lean`.
-- Primitive data here is only a smooth tangent-bundle section on `S²`; the local
-- `ContMDiffSection` alias carried no extra mathematics, so the theorem now uses the canonical
-- bundled smooth-section owner directly.

section

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "unitSphere2" => Metric.sphere (0 : R3) 1
local notation "SmoothVectorFieldOnSphere2" =>
  Cₛ^∞⟮𝓡 2; EuclideanSpace ℝ (Fin 2), fun p : unitSphere2 ↦ TangentSpace (𝓡 2) p⟯

/-- Helper for Problem 8-13: the constant `∂ / ∂x` coordinate vector in `ℝ²`. -/
def sphere2BasisX : R2 :=
  WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)]

/-- Helper for Problem 8-13: the constant vector `∂ / ∂x` in `ℝ²` is nonzero. -/
theorem sphere2BasisX_ne_zero : sphere2BasisX ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : R2 ↦ v 0) h
  simp [sphere2BasisX] at h0

/-- Helper for Problem 8-13: the stereographic rough field obtained by transporting the constant
`∂ / ∂x` field through the north-pole chart and setting the value at the north pole to `0`. -/
def sphere2NorthPoleRoughField (p : unitSphere2) : TangentSpace (𝓡 2) p :=
  if p = northPolePoint 2 then
    0
  else
    -- Away from the north pole, push the constant Euclidean vector through the chart inverse.
    mfderiv (𝓡 2) (𝓡 2) (stereographicNorthInv 2) (stereographicNorthMap 2 p)
      ((fromTangentSpace (stereographicNorthMap 2 p)).symm sphere2BasisX)

/-- Helper for Problem 8-13: on the north stereographic chart source, the rough field has the
constant chart-coordinate vector `∂ / ∂x`. -/
theorem northChartVector_sphere2NorthPoleRoughField
    (p : unitSphere2) (hp : p ∈ (northPoleComplement 2 : Set unitSphere2)) :
    NormedSpace.fromTangentSpace (stereographicNorthMap 2 p)
      (mfderiv (𝓡 2) (𝓡 2) (stereographicNorthMap 2) p
        (sphere2NorthPoleRoughField p)) =
      sphere2BasisX := by
  -- On the north-chart domain, the `if`-branch simplifies and the chart derivative cancels the
  -- inverse-chart derivative.
  have hpn : p ≠ northPolePoint 2 := by
    simpa [northPoleComplement] using hp
  set v : TangentSpace (𝓡 2) (stereographicNorthMap 2 p) :=
    (fromTangentSpace (stereographicNorthMap 2 p)).symm sphere2BasisX
  have hMap :
      MDifferentiableAt (𝓡 2) (𝓡 2) (stereographicNorthMap 2) p := by
    exact
      (contMDiffAt_of_mem_maximalAtlas
        (I := 𝓡 2) (n := (∞ : ℕ∞ω)) (e := stereographicNorthChart 2)
        stereographicNorthChart_mem_maximalAtlas hp).mdifferentiableAt (by simp)
  have hTarget : stereographicNorthMap 2 p ∈ (stereographicNorthChart 2).target := by
    simp [stereographicNorthChart]
  have hInv :
      MDifferentiableAt (𝓡 2) (𝓡 2) (stereographicNorthInv 2) (stereographicNorthMap 2 p) := by
    simpa using
      ((contMDiffAt_symm_of_mem_maximalAtlas
        (I := 𝓡 2) (n := (∞ : ℕ∞ω)) (e := stereographicNorthChart 2)
        stereographicNorthChart_mem_maximalAtlas
        hTarget).mdifferentiableAt (by simp))
  have hcompfun : stereographicNorthMap 2 ∘ stereographicNorthInv 2 = id := by
    funext u
    exact stereographicNorth_right_inv 2 u
  have hcancel :
      mfderiv (𝓡 2) (𝓡 2) (stereographicNorthMap 2) p
        ((mfderiv (𝓡 2) (𝓡 2) (stereographicNorthInv 2) (stereographicNorthMap 2 p)) v) =
      v := by
    -- Differentiate the identity `stereographicNorthMap ∘ stereographicNorthInv = id`.
    simpa [hcompfun, mfderiv_id, v] using
      (mfderiv_comp_apply_of_eq
        (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
        (g := stereographicNorthMap 2) (f := stereographicNorthInv 2)
        (x := stereographicNorthMap 2 p) (y := p)
        hMap hInv (stereographicNorth_left_inv 2 hp) v).symm
  -- Convert the tangent-vector equality back to the Euclidean chart model.
  simpa [sphere2NorthPoleRoughField, hpn, v] using
    congrArg (fromTangentSpace (stereographicNorthMap 2 p)) hcancel

/-- Helper for Problem 8-13: the south-chart coordinate model for the stereographic field. -/
def sphere2SouthPolynomial (u : R2) : R2 :=
  WithLp.toLp 2 ![u 1 ^ (2 : ℕ) - u 0 ^ (2 : ℕ), -(2 * u 0 * u 1)]

/-- Helper for Problem 8-13: the south-chart polynomial vanishes exactly at the origin. -/
theorem sphere2SouthPolynomial_eq_zero_iff (u : R2) :
    sphere2SouthPolynomial u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    have hSq : u 1 ^ (2 : ℕ) - u 0 ^ (2 : ℕ) = 0 := by
      simpa [sphere2SouthPolynomial] using congrArg (fun v : R2 ↦ v 0) hu
    have hMul : -(2 * u 0 * u 1) = 0 := by
      simpa [sphere2SouthPolynomial] using congrArg (fun v : R2 ↦ v 1) hu
    have hProd : u 0 * u 1 = 0 := by
      nlinarith [hMul]
    have hZero : u 0 = 0 ∨ u 1 = 0 := mul_eq_zero.mp hProd
    have hu0 : u 0 = 0 := by
      cases hZero with
      | inl h0 =>
          exact h0
      | inr h1 =>
          nlinarith [hSq, h1]
    have hu1 : u 1 = 0 := by
      nlinarith [hSq, hu0]
    ext i
    fin_cases i
    · simp [hu0]
    · simp [hu1]
  · intro hu
    simp [hu, sphere2SouthPolynomial]

/-- Helper for Problem 8-13: applying the north stereographic chart to a point written in south
coordinates gives the inversion `u ↦ ‖u‖⁻² • u`. -/
theorem stereographicNorthMap_stereographicSouthInv (u : R2) :
    stereographicNorthMap 2 (stereographicSouthInv 2 u) = (‖u‖ ^ 2)⁻¹ • u := by
  ext i
  fin_cases i
  · simp [stereographicNorthMap, stereographicSouthInv, stereographicSouthInvVector, Fin.snoc]
    by_cases hu : ‖u‖ ^ 2 = 0
    · simp [hu]
    · field_simp [hu]
      ring
  · simp [stereographicNorthMap, stereographicSouthInv, stereographicSouthInvVector, Fin.snoc]
    by_cases hu : ‖u‖ ^ 2 = 0
    · simp [hu]
    · field_simp [hu]
      ring

/-- Helper for Problem 8-13: the south stereographic inverse hits the north pole only at the
origin of `ℝ²`. -/
theorem stereographicSouthInv_eq_northPole_iff (u : R2) :
    stereographicSouthInv 2 u = northPolePoint 2 ↔ u = 0 := by
  constructor
  · intro hu
    -- Apply the south chart to the claimed north-pole identity and simplify both sides.
    have hNorth : stereographicSouthMap 2 (northPolePoint 2) = 0 := by
      simpa [stereographicSouthInv_zero_eq_northPole] using
        (stereographicSouth_right_inv 2 (0 : R2))
    have hmap := congrArg (stereographicSouthMap 2) hu
    simpa [hNorth, stereographicSouth_right_inv 2 u] using hmap
  · intro hu
    -- The origin is the already-known south stereographic coordinate of the north pole.
    simpa [hu] using stereographicSouthInv_zero_eq_northPole

/-- Helper for Problem 8-13: the north-to-south stereographic overlap is the inversion map on all
of `ℝ²` when both charts are viewed as total coordinate formulas. -/
theorem stereographicSouthMap_stereographicNorthInv (u : R2) :
    stereographicSouthMap 2 (stereographicNorthInv 2 u) = (‖u‖ ^ 2)⁻¹ • u := by
  by_cases hu : u = 0
  · -- At the origin both sides evaluate to zero because the totalized south chart sends the south
    -- pole to the origin by division-by-zero conventions.
    subst hu
    ext i
    fin_cases i
    · simp [stereographicSouthMap, stereographicNorthInv, stereographicNorthInvVector, Fin.snoc]
    · simp [stereographicSouthMap, stereographicNorthInv, stereographicNorthInvVector, Fin.snoc]
  · -- Away from the origin this is the textbook transition formula from Problem 1-7.
    exact stereographic_transition 2 u hu

/-- Helper for Problem 8-13: Euclidean inversion in the unit circle about the origin is the map
`v ↦ ‖v‖⁻² • v`. -/
theorem inversion_eq_invNormSqSmul (v : R2) :
    EuclideanGeometry.inversion (0 : R2) 1 v = (‖v‖ ^ 2)⁻¹ • v := by
  -- Rewrite Euclidean inversion at the origin coordinatewise into the explicit scalar formula.
  ext i
  fin_cases i <;> simp [EuclideanGeometry.inversion, dist_eq_norm]

/-- Helper for Problem 8-13: the north and south poles of `S²` are distinct. -/
theorem northPolePoint_ne_southPolePoint :
    northPolePoint 2 ≠ southPolePoint 2 := by
  intro h
  have hcoords := congrArg (fun x : unitSphere2 ↦ ((x : R3) 2)) h
  simp [northPolePoint, northPoleVec, southPolePoint, southPoleVec, Fin.snoc] at hcoords
  norm_num at hcoords

/-- Helper for Problem 8-13: in plain Euclidean coordinates, the overlap inversion derivative at
`(‖u‖²)⁻¹ • u` sends `∂ / ∂x` to the south-chart polynomial. -/
theorem stereographicTransition_fderiv_applyBasisX (u : R2) (hu : u ≠ 0) :
    fderiv ℝ (fun v : R2 ↦ (((‖v‖ ^ 2)⁻¹ : ℝ) • v))
      ((((‖u‖ ^ 2)⁻¹ : ℝ) • u)) sphere2BasisX =
      sphere2SouthPolynomial u := by
  let w : R2 := (((‖u‖ ^ 2)⁻¹ : ℝ) • u)
  have huNorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have huNormSq : ‖u‖ ^ 2 ≠ 0 := by exact pow_ne_zero 2 huNorm
  have huSq :
      ‖u‖ ^ 2 = u 0 ^ (2 : ℕ) + u 1 ^ (2 : ℕ) := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq u
  have hw : w ≠ 0 := by
    intro hw0
    apply hu
    exact smul_eq_zero.mp hw0 |>.resolve_left (inv_ne_zero huNormSq)
  have hinvfun :
      EuclideanGeometry.inversion (0 : R2) 1 = fun v : R2 ↦ (((‖v‖ ^ 2)⁻¹ : ℝ) • v) := by
    funext x
    simpa using inversion_eq_invNormSqSmul x
  have hEval :
      fderiv ℝ (fun v : R2 ↦ (((‖v‖ ^ 2)⁻¹ : ℝ) • v)) w sphere2BasisX =
        ((1 / dist w (0 : R2)) ^ 2) • (((ℝ ∙ w)ᗮ).reflection sphere2BasisX) := by
    -- Replace the explicit overlap map by Euclidean inversion at the origin.
    simpa [hinvfun, w] using
      congrArg (fun L : R2 →L[ℝ] R2 ↦ L sphere2BasisX) <|
        (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : R2)) (R := 1) (x := w) hw).fderiv
  have hwSq : ‖w‖ ^ 2 = (‖u‖ ^ 2)⁻¹ := by
    -- Expand the scaled norm in coordinates and simplify with `‖u‖² = u₀² + u₁²`.
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [w]
    field_simp [huNormSq]
    nlinarith [huSq]
  have hwInvSq : ‖w‖⁻¹ ^ 2 = ‖u‖ ^ 2 := by
    rw [show ‖w‖⁻¹ ^ 2 = (‖w‖ ^ 2)⁻¹ by
      field_simp [norm_ne_zero_iff.mpr hw]]
    rw [hwSq]
    field_simp [huNormSq]
  have hScalar : ((1 / dist w (0 : R2)) ^ 2 : ℝ) = ‖u‖ ^ 2 := by
    -- The inversion point `w = ‖u‖⁻² • u` has norm `‖u‖⁻¹`, so the scalar prefactor is `‖u‖²`.
    simpa [dist_eq_norm, sub_zero, one_div, inv_pow] using hwInvSq
  calc
    fderiv ℝ (fun v : R2 ↦ (((‖v‖ ^ 2)⁻¹ : ℝ) • v)) ((((‖u‖ ^ 2)⁻¹ : ℝ) • u)) sphere2BasisX
        = ((1 / dist w (0 : R2)) ^ 2) • (((ℝ ∙ w)ᗮ).reflection sphere2BasisX) := by
            simpa [w] using hEval
    _ = sphere2SouthPolynomial u := by
      rw [hScalar]
      ext i
      fin_cases i
      · -- Read the first coordinate of the reflected-and-rescaled vector explicitly.
        simp [w, sphere2BasisX, sphere2SouthPolynomial, Submodule.reflection_orthogonal_apply,
          Submodule.reflection_singleton_apply, PiLp.inner_apply, Fin.sum_univ_two]
        rw [show ‖(((‖u‖ ^ 2)⁻¹ : ℝ) • u)‖ ^ 2 = (‖u‖ ^ 2)⁻¹ by simpa [w] using hwSq]
        field_simp [huNormSq]
        rw [huSq]
        ring_nf
      · -- The second coordinate simplifies to the quadratic term `-2u₀u₁`.
        simp [w, sphere2BasisX, sphere2SouthPolynomial, Submodule.reflection_orthogonal_apply,
          Submodule.reflection_singleton_apply, PiLp.inner_apply, Fin.sum_univ_two]
        rw [show ‖(((‖u‖ ^ 2)⁻¹ : ℝ) • u)‖ ^ 2 = (‖u‖ ^ 2)⁻¹ by simpa [w] using hwSq]
        field_simp [huNormSq]

/-- Helper for Problem 8-13: the derivative of the stereographic overlap inversion sends the
constant `∂ / ∂x` vector to the south-chart polynomial field. -/
theorem stereographicTransition_applyBasisX (u : R2) (hu : u ≠ 0) :
    NormedSpace.fromTangentSpace (𝕜 := ℝ) u
      (mfderiv (𝓡 2) (𝓡 2) (fun v : R2 ↦ (((‖v‖ ^ 2)⁻¹ : ℝ) • v))
        ((((‖u‖ ^ 2)⁻¹ : ℝ) • u))
        ((((NormedSpace.fromTangentSpace (𝕜 := ℝ) ((((‖u‖ ^ 2)⁻¹ : ℝ) • u))).symm) sphere2BasisX))) =
      sphere2SouthPolynomial u := by
  -- Route correction: the remaining computation should stay in plain Euclidean `fderiv`
  -- coordinates until the final `mfderiv_eq_fderiv` adapter.
  simpa [mfderiv_eq_fderiv] using stereographicTransition_fderiv_applyBasisX u hu

/-- Helper for Problem 8-13: the constant `∂ / ∂x` field on `ℝ²`, viewed as a tangent-bundle
section over the model space. -/
def sphere2BasisXSection (u : R2) : TangentSpace (𝓡 2) u :=
  (fromTangentSpace u).symm sphere2BasisX

/-- Helper for Problem 8-13: every Euclidean tangent-bundle trivialization reads
`sphere2BasisXSection` as the constant coordinate vector `sphere2BasisX`. -/
@[simp] theorem trivializationAt_sphere2BasisXSection (x y : R2) :
    (trivializationAt R2 (TangentSpace (𝓡 2)) x ⟨y, sphere2BasisXSection y⟩).2 =
      sphere2BasisX := by
  -- On the Euclidean model, tangent-bundle trivializations are the standard coordinates.
  rw [trivializationAt_model_space_apply (I := 𝓡 2) (p := ⟨y, sphere2BasisXSection y⟩) x]
  rfl

/-- Helper for Problem 8-13: `sphere2BasisXSection` is a smooth tangent-bundle section on `ℝ²`. -/
theorem sphere2BasisXSection_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% sphere2BasisXSection) := by
  intro p
  -- Reduce section smoothness to the trivialized Euclidean coordinate.
  rw [Bundle.contMDiffAt_section p]
  -- The trivialized coordinate is constant.
  simpa using
    (contMDiffAt_const :
      ContMDiffAt (𝓡 2) (𝓡 2) ∞ (fun _ : R2 ↦ sphere2BasisX) p)

/-- Helper for Problem 8-13: the south-chart polynomial defines a smooth Euclidean vector field on
`ℝ²`. -/
theorem sphere2SouthPolynomial_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2) ∞ sphere2SouthPolynomial := by
  have h0 : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun u : R2 ↦ u 0) := by
    simpa using (((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) : R2 →L[ℝ] ℝ).contMDiff)
  have h1 : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun u : R2 ↦ u 1) := by
    simpa using (((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1) : R2 →L[ℝ] ℝ).contMDiff)
  have hcoords : ContMDiff (𝓡 2) 𝓘(ℝ, Fin 2 → ℝ) ∞
      (fun u : R2 ↦ ![u 1 ^ (2 : ℕ) - u 0 ^ (2 : ℕ), -(2 * u 0 * u 1)]) := by
    -- Prove smoothness coordinatewise on the finite product model.
    rw [contMDiff_pi_space]
    intro i
    fin_cases i
    · exact (h1.pow 2).sub (h0.pow 2)
    · simpa [neg_mul, mul_assoc] using ((contMDiff_const.mul h0).mul h1).neg
  have htoLp :
      ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (𝓡 2) ∞
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm : (Fin 2 → ℝ) → R2) := by
    -- Move from coordinate tuples back to the Euclidean model by the canonical linear equivalence.
    simpa using
      (((EuclideanSpace.equiv (Fin 2) ℝ).symm : (Fin 2 → ℝ) →L[ℝ] R2).contMDiff)
  simpa [sphere2SouthPolynomial] using htoLp.comp hcoords

/-- Helper for Problem 8-13: the south-chart polynomial field on `ℝ²`, viewed as a tangent-bundle
section over the model space. -/
def sphere2SouthPolynomialSection (u : R2) : TangentSpace (𝓡 2) u :=
  (fromTangentSpace u).symm (sphere2SouthPolynomial u)

/-- Helper for Problem 8-13: every Euclidean tangent-bundle trivialization reads
`sphere2SouthPolynomialSection` as the polynomial coordinate vector `sphere2SouthPolynomial`. -/
@[simp] theorem trivializationAt_sphere2SouthPolynomialSection (x y : R2) :
    (trivializationAt R2 (TangentSpace (𝓡 2)) x ⟨y, sphere2SouthPolynomialSection y⟩).2 =
      sphere2SouthPolynomial y := by
  -- On the Euclidean model, tangent-bundle trivializations are the standard coordinates.
  rw [trivializationAt_model_space_apply (I := 𝓡 2) (p := ⟨y, sphere2SouthPolynomialSection y⟩) x]
  rfl

/-- Helper for Problem 8-13: `sphere2SouthPolynomialSection` is a smooth tangent-bundle section on
`ℝ²`. -/
theorem sphere2SouthPolynomialSection_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% sphere2SouthPolynomialSection) := by
  intro p
  -- Reduce section smoothness to the trivialized Euclidean coordinate map.
  rw [Bundle.contMDiffAt_section p]
  -- The trivialized coordinate is the smooth polynomial map on `ℝ²`.
  simpa using sphere2SouthPolynomial_contMDiff.contMDiffAt

/-- Helper for Problem 8-13: the stereographic rough field vanishes exactly at the north pole. -/
theorem sphere2NorthPoleRoughField_eq_zero_iff (p : unitSphere2) :
    sphere2NorthPoleRoughField p = 0 ↔ p = northPolePoint 2 := by
  constructor
  · intro hp0
    by_cases hpn : p = northPolePoint 2
    · exact hpn
    · have hpNorth : p ∈ (northPoleComplement 2 : Set unitSphere2) := by
        simpa [northPoleComplement] using hpn
      have hcoords := northChartVector_sphere2NorthPoleRoughField p hpNorth
      have hzero : 0 = sphere2BasisX := by
        simpa [hp0] using hcoords
      exact False.elim (sphere2BasisX_ne_zero hzero.symm)
  · intro hp
    simp [sphere2NorthPoleRoughField, hp]

/-- Helper for Problem 8-13: in south stereographic coordinates, the rough field is given by the
polynomial vector field `sphere2SouthPolynomial`. -/
theorem southChartVector_sphere2NorthPoleRoughField (u : R2) :
    ((fromTangentSpace u : TangentSpace (𝓡 2) u ≃L[ℝ] R2))
      (mfderiv (𝓡 2) (𝓡 2) (stereographicSouthMap 2) (stereographicSouthInv 2 u)
        (sphere2NorthPoleRoughField (stereographicSouthInv 2 u))) =
      sphere2SouthPolynomial u := by
  by_cases hu : u = 0
  · subst hu
    -- At the north pole the rough field is defined to be zero, and the south polynomial also
    -- vanishes at the origin.
    have hzero :
        mfderiv (𝓡 2) (𝓡 2) (stereographicSouthMap 2) (stereographicSouthInv 2 (0 : R2))
          (sphere2NorthPoleRoughField (stereographicSouthInv 2 (0 : R2))) =
        0 := by
      simp [stereographicSouthInv_zero_eq_northPole, sphere2NorthPoleRoughField]
    have hcoord :=
      congrArg ((fromTangentSpace (0 : R2) : TangentSpace (𝓡 2) (0 : R2) ≃L[ℝ] R2)) hzero
    calc
      ((fromTangentSpace (0 : R2) : TangentSpace (𝓡 2) (0 : R2) ≃L[ℝ] R2))
          (mfderiv (𝓡 2) (𝓡 2) (stereographicSouthMap 2) (stereographicSouthInv 2 (0 : R2))
            (sphere2NorthPoleRoughField (stereographicSouthInv 2 (0 : R2)))) =
          ((fromTangentSpace (0 : R2) : TangentSpace (𝓡 2) (0 : R2) ≃L[ℝ] R2)) 0 := hcoord
      _ = 0 := by simp
      _ = sphere2SouthPolynomial 0 := by
        ext i
        fin_cases i <;> simp [sphere2SouthPolynomial]
  · let p : unitSphere2 := stereographicSouthInv 2 u
    let w : R2 := stereographicNorthMap 2 p
    let v : TangentSpace (𝓡 2) w := (fromTangentSpace w).symm sphere2BasisX
    have hpn : p ≠ northPolePoint 2 := by
      simpa [p, stereographicSouthInv_eq_northPole_iff] using hu
    have hpNorth : p ∈ (northPoleComplement 2 : Set unitSphere2) := by
      simpa [northPoleComplement] using hpn
    have hpSouth : p ∈ (southPoleComplement 2 : Set unitSphere2) := by
      simpa [p, southPoleComplement] using stereographicSouthInv_ne_southPole 2 u
    have hw : w = (((‖u‖ ^ 2)⁻¹ : ℝ) • u) := by
      simpa [p, w] using stereographicNorthMap_stereographicSouthInv u
    have hSouthMap :
        MDifferentiableAt (𝓡 2) (𝓡 2) (stereographicSouthMap 2) p := by
      exact
        (contMDiffAt_of_mem_maximalAtlas
          (I := 𝓡 2) (n := (∞ : ℕ∞ω)) (e := stereographicSouthChart 2)
          stereographicSouthChart_mem_maximalAtlas hpSouth).mdifferentiableAt (by simp)
    have hNorthInv :
        MDifferentiableAt (𝓡 2) (𝓡 2) (stereographicNorthInv 2) w := by
      simpa [w] using
        ((contMDiffAt_symm_of_mem_maximalAtlas
          (I := 𝓡 2) (n := (∞ : ℕ∞ω)) (e := stereographicNorthChart 2)
          stereographicNorthChart_mem_maximalAtlas
          (by simp [stereographicNorthChart])).mdifferentiableAt (by simp))
    have hcomp :
        mfderiv (𝓡 2) (𝓡 2) (stereographicSouthMap 2) p
            ((mfderiv (𝓡 2) (𝓡 2) (stereographicNorthInv 2) w) v) =
          mfderiv (𝓡 2) (𝓡 2) (stereographicSouthMap 2 ∘ stereographicNorthInv 2) w v := by
      -- Differentiate the south-after-north overlap at the north-chart point `w`.
      simpa [Function.comp, p, w] using
        (mfderiv_comp_apply_of_eq
          (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
          (g := stereographicSouthMap 2) (f := stereographicNorthInv 2)
          (x := w) (y := p) hSouthMap hNorthInv
          (stereographicNorth_left_inv 2 hpNorth) v).symm
    have hOverlap :
        ((fromTangentSpace u : TangentSpace (𝓡 2) u ≃L[ℝ] R2))
          (mfderiv (𝓡 2) (𝓡 2) (stereographicSouthMap 2 ∘ stereographicNorthInv 2) w v) =
        sphere2SouthPolynomial u := by
      -- Replace the overlap by its explicit Euclidean inversion formula.
      have hcompfun :
          stereographicSouthMap 2 ∘ stereographicNorthInv 2 =
            fun x : R2 ↦ (((‖x‖ ^ 2)⁻¹ : ℝ) • x) := by
        funext x
        exact stereographicSouthMap_stereographicNorthInv x
      simpa [hcompfun, hw, v] using
        stereographicTransition_applyBasisX u hu
    -- TODO: rewrite the rough field through the north chart, then use `hcomp` together with the
    -- explicit overlap formula `hOverlap` to close the south-chart computation.
    sorry

/-- Helper for Problem 8-13: on the south stereographic chart source, the rough field is the
pushforward of the polynomial model field `sphere2SouthPolynomialSection`. -/
theorem southChartLift_sphere2NorthPoleRoughField
    (p : unitSphere2) (hp : p ∈ (southPoleComplement 2 : Set unitSphere2)) :
    sphere2NorthPoleRoughField p =
      mfderiv (𝓡 2) (𝓡 2) (stereographicSouthInv 2) (stereographicSouthMap 2 p)
        (sphere2SouthPolynomialSection (stereographicSouthMap 2 p)) := by
  -- TODO: compare both sides after applying `mfderiv (stereographicSouthMap 2) p`, use
  -- `southChartVector_sphere2NorthPoleRoughField`, and cancel with the local identity
  -- `stereographicSouthInv 2 ∘ stereographicSouthMap 2 = id` on `southPoleComplement 2`.
  sorry

/-- Helper for Problem 8-13: the stereographic rough field is globally smooth on `S²`. -/
theorem sphere2NorthPoleRoughField_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% sphere2NorthPoleRoughField) := by
  -- Route correction: the remaining global step should glue the north pushforward of
  -- `sphere2BasisXSection` and the south pushforward of `sphere2SouthPolynomialSection`
  -- across the open stereographic cover using the two local identities proved above.
  -- TODO: package the north and south pushforward formulas as `ContMDiffOn` facts on the two open
  -- complements, then apply `contMDiff_of_contMDiffOn_union_of_isOpen`.
  sorry

/-- Problem 8-13: there exists a smooth vector field on `S²` that vanishes at exactly one point.
-/
theorem exists_smooth_vectorField_on_sphere2_vanishing_exactly_once :
    ∃ X : SmoothVectorFieldOnSphere2,
      ∃ p0 : unitSphere2, ∀ p : unitSphere2, X p = 0 ↔ p = p0 := by
  let X : SmoothVectorFieldOnSphere2 :=
    ⟨sphere2NorthPoleRoughField, sphere2NorthPoleRoughField_contMDiff⟩
  refine ⟨X, northPolePoint 2, ?_⟩
  intro p
  -- The zero-set computation is already encoded in the rough-field helper.
  simpa [X] using sphere2NorthPoleRoughField_eq_zero_iff p

end

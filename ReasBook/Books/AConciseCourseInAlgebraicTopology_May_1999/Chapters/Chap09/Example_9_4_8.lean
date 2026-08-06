import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Complex.Circle
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped TopCat LinearAlgebra.Projectivization

-- Semantic recall via `lean_leansearch`: mathlib exposes local bundle structure through
-- `Bundle.Trivialization`, while the Hopf map and the `ℂP¹` model do not already have local owners.

/-- The complex projective line `ℂP¹`, modeled as the projectivization of `ℂ²`. -/
abbrev ComplexProjectiveLine := ℙ ℂ (Fin 2 → ℂ)

/-- The projective-space model `ℂP¹` carries the quotient topology inherited from nonzero vectors
in `ℂ²`. -/
instance complexProjectiveLineTopologicalSpace : TopologicalSpace ComplexProjectiveLine :=
  instTopologicalSpaceQuotient

private abbrev complexFinTwoArrow : (Fin 2 → ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (LinearEquiv.finTwoArrow ℂ ℂ : (Fin 2 → ℂ) ≃ₗ[ℂ] (ℂ × ℂ))

private theorem complexFinTwoArrow_injective :
    Function.Injective complexFinTwoArrow :=
  ((LinearEquiv.finTwoArrow ℂ ℂ : (Fin 2 → ℂ) ≃ₗ[ℂ] (ℂ × ℂ))).injective

private abbrev complexFinTwoArrowSymm : (ℂ × ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  ((LinearEquiv.finTwoArrow ℂ ℂ).symm : (ℂ × ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))

private theorem complexFinTwoArrowSymm_injective :
    Function.Injective complexFinTwoArrowSymm :=
  (((LinearEquiv.finTwoArrow ℂ ℂ).symm : (ℂ × ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))).injective

/-- The canonical equivalence `OnePoint ℂ ≃ ℂP¹`, obtained by identifying the affine chart
`ℂ ∪ {∞}` with the projectivization model of `ℂ²`. -/
noncomputable def complexProjectiveLineEquivOnePointComplex :
    OnePoint ℂ ≃ ComplexProjectiveLine where
  toFun :=
    Projectivization.map complexFinTwoArrowSymm complexFinTwoArrowSymm_injective ∘
      OnePoint.equivProjectivization ℂ
  invFun :=
    (OnePoint.equivProjectivization ℂ).symm ∘
      Projectivization.map complexFinTwoArrow complexFinTwoArrow_injective
  left_inv z := by
    have h :
        Projectivization.map complexFinTwoArrow complexFinTwoArrow_injective
            (Projectivization.map complexFinTwoArrowSymm complexFinTwoArrowSymm_injective
              ((OnePoint.equivProjectivization ℂ) z)) =
          (OnePoint.equivProjectivization ℂ) z := by
      simpa [complexFinTwoArrow, complexFinTwoArrowSymm] using
        congrFun
          (Projectivization.map_comp complexFinTwoArrowSymm complexFinTwoArrowSymm_injective
            complexFinTwoArrow complexFinTwoArrow_injective
            (complexFinTwoArrow_injective.comp complexFinTwoArrowSymm_injective))
          ((OnePoint.equivProjectivization ℂ) z) |>.symm
    simpa [Function.comp] using congrArg (OnePoint.equivProjectivization ℂ).symm h
  right_inv x := by
    have h :
        x =
          Projectivization.map complexFinTwoArrowSymm complexFinTwoArrowSymm_injective
            (Projectivization.map complexFinTwoArrow complexFinTwoArrow_injective x) := by
      simpa [complexFinTwoArrow, complexFinTwoArrowSymm] using
        congrFun
          (Projectivization.map_comp complexFinTwoArrow complexFinTwoArrow_injective
            complexFinTwoArrowSymm complexFinTwoArrowSymm_injective
            (complexFinTwoArrowSymm_injective.comp complexFinTwoArrow_injective))
          x
    simpa [Function.comp] using h.symm

/-- Helper for Example 9.4.8: the finite affine chart `z ↦ [z : 1]` in `ℂP¹`. -/
private def complexProjectiveLineFinite (z : ℂ) : ComplexProjectiveLine :=
  Projectivization.mk ℂ (complexFinTwoArrowSymm (z, 1)) <| by
    -- The affine representative `(z, 1)` is nonzero because its second coordinate is `1`.
    intro hz
    have hz' : complexFinTwoArrowSymm (z, 1) = complexFinTwoArrowSymm 0 := by
      simpa using hz
    have hpair : ((z, (1 : ℂ)) : ℂ × ℂ) = 0 := complexFinTwoArrowSymm_injective hz'
    simpa using congrArg Prod.snd hpair

/-- Helper for Example 9.4.8: the point at infinity `[1 : 0]` in `ℂP¹`. -/
private def complexProjectiveLineInfinity : ComplexProjectiveLine :=
  Projectivization.mk ℂ (complexFinTwoArrowSymm (1, 0)) <| by
    -- The representative `(1, 0)` is nonzero because its first coordinate is `1`.
    intro hz
    have hz' : complexFinTwoArrowSymm (1, 0) = complexFinTwoArrowSymm 0 := by
      simpa using hz
    have hpair : (((1 : ℂ), 0) : ℂ × ℂ) = 0 := complexFinTwoArrowSymm_injective hz'
    simpa using congrArg Prod.fst hpair

/-- Helper for Example 9.4.8: the explicit affine chart agrees with the finite part of
`complexProjectiveLineEquivOnePointComplex`. -/
private theorem complexProjectiveLineFinite_eq_equiv (z : ℂ) :
    complexProjectiveLineFinite z = complexProjectiveLineEquivOnePointComplex z := by
  -- Unfolding both sides shows that they are the same projective class `[z : 1]`.
  simpa [complexProjectiveLineFinite, complexProjectiveLineEquivOnePointComplex, Function.comp,
    OnePoint.equivProjectivization_apply_coe] using
    (Projectivization.map_mk complexFinTwoArrowSymm complexFinTwoArrowSymm_injective
      ((z, 1) : ℂ × ℂ) (by simp)).symm

/-- Helper for Example 9.4.8: the chosen point at infinity agrees with the infinite part of
`complexProjectiveLineEquivOnePointComplex`. -/
private theorem complexProjectiveLineInfinity_eq_equiv :
    complexProjectiveLineInfinity =
      complexProjectiveLineEquivOnePointComplex (OnePoint.infty : OnePoint ℂ) := by
  -- Unfolding both sides shows that they are the same projective class `[1 : 0]`.
  simpa [complexProjectiveLineInfinity, complexProjectiveLineEquivOnePointComplex, Function.comp,
    OnePoint.equivProjectivization_apply_infinity] using
    (Projectivization.map_mk complexFinTwoArrowSymm complexFinTwoArrowSymm_injective
      ((1, 0) : ℂ × ℂ) (by simp)).symm

/-- Helper for Example 9.4.8: the affine chart `z ↦ [z : 1]` is continuous. -/
private theorem complexProjectiveLineFinite_continuous :
    Continuous complexProjectiveLineFinite := by
  let affineRep : ℂ → { v : Fin 2 → ℂ // v ≠ 0 } := fun z ↦
    ⟨complexFinTwoArrowSymm (z, 1), by
      intro hz
      have hz' : complexFinTwoArrowSymm (z, 1) = complexFinTwoArrowSymm 0 := by
        simpa using hz
      have hpair : ((z, (1 : ℂ)) : ℂ × ℂ) = 0 := complexFinTwoArrowSymm_injective hz'
      simpa using congrArg Prod.snd hpair⟩
  have haffineRep : Continuous affineRep := by
    -- The affine representatives vary continuously with `z`.
    exact
      (complexFinTwoArrowSymm.continuous_of_finiteDimensional.comp
        (continuous_id.prodMk continuous_const)).subtype_mk fun z ↦ (affineRep z).2
  -- The affine representatives are exactly the nonzero vectors used by `Projectivization.mk`.
  have hmk : Projectivization.mk' ℂ ∘ affineRep = complexProjectiveLineFinite := by
    funext z
    simp [affineRep, complexProjectiveLineFinite]
  -- The projective quotient map is continuous, so the affine chart inherits continuity.
  have hquot : Continuous (Projectivization.mk' ℂ ∘ affineRep) :=
    continuous_quotient_mk'.comp haffineRep
  simpa [hmk] using hquot

/-- Helper for Example 9.4.8: finite affine points never hit the point at infinity. -/
private theorem complexProjectiveLineFinite_ne_infinity (z : ℂ) :
    complexProjectiveLineFinite z ≠ complexProjectiveLineInfinity := by
  -- Passing through `complexProjectiveLineEquivOnePointComplex` would force `z = ∞`, impossible.
  intro hz
  have hfinite :
      (z : OnePoint ℂ) = (OnePoint.infty : OnePoint ℂ) := by
    apply complexProjectiveLineEquivOnePointComplex.injective
    simpa [complexProjectiveLineFinite_eq_equiv, complexProjectiveLineInfinity_eq_equiv] using hz
  exact OnePoint.coe_ne_infty z hfinite

/-- Helper for Example 9.4.8: the finite affine chart is injective. -/
private theorem complexProjectiveLineFinite_injective :
    Function.Injective complexProjectiveLineFinite := by
  intro z w hzw
  have hfinite :
      complexProjectiveLineEquivOnePointComplex (z : OnePoint ℂ) =
        complexProjectiveLineEquivOnePointComplex (w : OnePoint ℂ) := by
    simpa [complexProjectiveLineFinite_eq_equiv] using hzw
  simpa using complexProjectiveLineEquivOnePointComplex.injective hfinite

/-- Helper for Example 9.4.8: the image of the finite affine chart is exactly the complement of the
point at infinity. -/
private theorem mem_range_complexProjectiveLineFinite_iff_ne_infinity
    (x : ComplexProjectiveLine) :
    x ∈ Set.range complexProjectiveLineFinite ↔ x ≠ complexProjectiveLineInfinity := by
  constructor
  · rintro ⟨z, rfl⟩
    -- A finite affine point cannot equal the point at infinity.
    exact complexProjectiveLineFinite_ne_infinity z
  · intro hx
    -- The inverse equivalence cannot land at `∞`, so it comes from some finite affine coordinate.
    have hfinite :
        complexProjectiveLineEquivOnePointComplex.symm x ≠
          (OnePoint.infty : OnePoint ℂ) := by
      intro hinfty
      apply hx
      simpa [complexProjectiveLineInfinity_eq_equiv] using
        congrArg complexProjectiveLineEquivOnePointComplex hinfty
    rcases OnePoint.ne_infty_iff_exists.mp hfinite with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      complexProjectiveLineFinite z
          = complexProjectiveLineEquivOnePointComplex (z : OnePoint ℂ) := by
              simpa [complexProjectiveLineFinite_eq_equiv]
      _ = complexProjectiveLineEquivOnePointComplex (complexProjectiveLineEquivOnePointComplex.symm x) := by
            simpa [hz]
      _ = x := complexProjectiveLineEquivOnePointComplex.apply_symm_apply x

/-- The canonical homeomorphism `S² ≃ₜ OnePoint ℂ`, giving the standard comparison of `S²` with
the affine-line model of `ℂP¹`. -/
noncomputable def sphereTwoHomeomorphOnePointComplex :
    𝕊 2 ≃ₜ OnePoint ℂ :=
  Homeomorph.ulift.trans
    (onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := ℂ) (by simp)).symm

/-- The unit sphere in `ℂ²`, used as the concrete model of `S^3 ⊂ ℂ²`. -/
abbrev ComplexSphereThree := Metric.sphere (0 : Fin 2 → ℂ) 1

/-- A point of the unit sphere in `ℂ²` is nonzero as a vector. -/
theorem complexSphereThree_nonzero (z : ComplexSphereThree) : z.1 ≠ 0 := by
  intro hz
  have hz1 : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  simp [hz] at hz1

/-- The quotient map from the concrete sphere `S^3 ⊂ ℂ²` to `ℂP¹`. -/
def complexSphereThreeToProjectivization (z : ComplexSphereThree) : ComplexProjectiveLine :=
  Projectivization.mk ℂ z.1 (complexSphereThree_nonzero z)

/-- Helper for Example 9.4.8: scaling a nonzero real-normed vector by the inverse of its norm
lands on the unit sphere. -/
private theorem invNorm_smul_mem_unitSphere {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) (hx : x ≠ 0) :
    ((‖x‖)⁻¹ : ℝ) • x ∈ Metric.sphere (0 : E) 1 := by
  -- The normalization factor turns the norm into `‖x‖⁻¹ * ‖x‖ = 1`.
  rw [mem_sphere_zero_iff_norm]
  have hnorm : ‖x‖ ≠ 0 := by
    intro hnorm
    exact hx (norm_eq_zero.mp hnorm)
  calc
    ‖((‖x‖)⁻¹ : ℝ) • x‖ = ‖x‖⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    _ = 1 := by
      exact inv_mul_cancel₀ hnorm

/-- Helper for Example 9.4.8: normalizing a positive real multiple of a unit vector recovers the
original unit vector. -/
private theorem invNorm_smul_eq_of_mem_unitSphere {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    (hx : x ∈ Metric.sphere (0 : E) 1) {a : ℝ} (ha : 0 < a) :
    ((‖a • x‖)⁻¹ : ℝ) • (a • x) = x := by
  -- The norm of `a • x` is exactly `a` because `‖x‖ = 1` and `a > 0`.
  have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have hnorm : ‖a • x‖ = a := by
    rw [norm_smul, hxnorm, mul_one, Real.norm_eq_abs, abs_of_pos ha]
  calc
    ((‖a • x‖)⁻¹ : ℝ) • (a • x) = ((‖a • x‖)⁻¹ * a : ℝ) • x := by
      rw [smul_smul]
    _ = x := by
      simp [hnorm, ha.ne']

/-- Helper for Example 9.4.8: package the four real coordinates of `ℝ⁴` into two complex
coordinates. -/
private def sphereThreePack (x : EuclideanSpace ℝ (Fin 4)) : Fin 2 → ℂ
  | 0 => x 0 + x 1 * Complex.I
  | 1 => x 2 + x 3 * Complex.I

/-- Helper for Example 9.4.8: unpack two complex coordinates into the corresponding four real
coordinates. -/
private def sphereThreeUnpack (z : Fin 2 → ℂ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[Complex.re (z 0), Complex.im (z 0), Complex.re (z 1), Complex.im (z 1)]

/-- Helper for Example 9.4.8: packing followed by unpacking is the identity on `ℝ⁴`. -/
private theorem sphereThreeUnpack_pack (x : EuclideanSpace ℝ (Fin 4)) :
    sphereThreeUnpack (sphereThreePack x) = x := by
  -- Each real coordinate is recovered as the real or imaginary part of the packed complex pair.
  ext i
  fin_cases i <;> simp [sphereThreeUnpack, sphereThreePack]

/-- Helper for Example 9.4.8: unpacking followed by packing is the identity on `ℂ²`. -/
private theorem sphereThreePack_unpack (z : Fin 2 → ℂ) :
    sphereThreePack (sphereThreeUnpack z) = z := by
  -- The two complex coordinates are recovered from their real and imaginary parts.
  ext i
  fin_cases i <;> simp [sphereThreeUnpack, sphereThreePack]

/-- Helper for Example 9.4.8: the packing map sends `0` to `0`. -/
private theorem sphereThreePack_zero :
    sphereThreePack (0 : EuclideanSpace ℝ (Fin 4)) = 0 := by
  ext i
  fin_cases i <;> simp [sphereThreePack]

/-- Helper for Example 9.4.8: the unpacking map sends `0` to `0`. -/
private theorem sphereThreeUnpack_zero :
    sphereThreeUnpack (0 : Fin 2 → ℂ) = 0 := by
  ext i
  fin_cases i <;> simp [sphereThreeUnpack]

/-- Helper for Example 9.4.8: the coordinate-packing map is compatible with real scaling. -/
private theorem sphereThreePack_real_smul (a : ℝ) (x : EuclideanSpace ℝ (Fin 4)) :
    sphereThreePack (a • x) = a • sphereThreePack x := by
  -- Real scalars act coordinatewise on the packed complex pair.
  ext i
  fin_cases i <;> simp [sphereThreePack, mul_add, mul_assoc]

/-- Helper for Example 9.4.8: the unpacking map is compatible with real scaling. -/
private theorem sphereThreeUnpack_real_smul (a : ℝ) (z : Fin 2 → ℂ) :
    sphereThreeUnpack (a • z) = a • sphereThreeUnpack z := by
  -- Real scaling commutes with taking real and imaginary parts.
  ext i
  fin_cases i <;> simp [sphereThreeUnpack]

/-- Helper for Example 9.4.8: the coordinate-packing map is injective. -/
private theorem sphereThreePack_injective :
    Function.Injective sphereThreePack := by
  intro x y hxy
  simpa [sphereThreeUnpack_pack] using congrArg sphereThreeUnpack hxy

/-- Helper for Example 9.4.8: the coordinate-unpacking map is injective. -/
private theorem sphereThreeUnpack_injective :
    Function.Injective sphereThreeUnpack := by
  intro z w hzw
  simpa [sphereThreePack_unpack] using congrArg sphereThreePack hzw

/-- Helper for Example 9.4.8: the coordinate-packing map is continuous. -/
private theorem sphereThreePack_continuous :
    Continuous sphereThreePack := by
  -- Each packed coordinate is an explicit polynomial expression in the source coordinates.
  refine continuous_pi fun i ↦ ?_
  have h0 : Continuous fun a : EuclideanSpace ℝ (Fin 4) ↦ a 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 0).continuous
  have h1 : Continuous fun a : EuclideanSpace ℝ (Fin 4) ↦ a 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 1).continuous
  have h2 : Continuous fun a : EuclideanSpace ℝ (Fin 4) ↦ a 2 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 2).continuous
  have h3 : Continuous fun a : EuclideanSpace ℝ (Fin 4) ↦ a 3 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 3).continuous
  fin_cases i
  · simpa [sphereThreePack] using
      (Complex.continuous_ofReal.comp h0).add
        ((Complex.continuous_ofReal.comp h1).mul continuous_const)
  · simpa [sphereThreePack] using
      (Complex.continuous_ofReal.comp h2).add
        ((Complex.continuous_ofReal.comp h3).mul continuous_const)

/-- Helper for Example 9.4.8: the coordinate-unpacking map is continuous. -/
private theorem sphereThreeUnpack_continuous :
    Continuous sphereThreeUnpack := by
  -- Real and imaginary parts vary continuously with the complex coordinates.
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp ?_
  refine continuous_pi fun i : Fin 4 ↦ ?_
  have h0 : Continuous fun a : Fin 2 → ℂ ↦ a 0 := continuous_apply 0
  have h1 : Continuous fun a : Fin 2 → ℂ ↦ a 1 := continuous_apply 1
  fin_cases i
  · simpa [sphereThreeUnpack] using Complex.continuous_re.comp h0
  · simpa [sphereThreeUnpack] using Complex.continuous_im.comp h0
  · simpa [sphereThreeUnpack] using Complex.continuous_re.comp h1
  · simpa [sphereThreeUnpack] using Complex.continuous_im.comp h1

/-- Helper for Example 9.4.8: a point on the Euclidean `S^3` packs to a nonzero complex vector. -/
private theorem sphereThreePack_nonzero
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    sphereThreePack x.1 ≠ 0 := by
  -- Otherwise unpacking would force the source sphere point itself to be zero.
  intro hpack
  have hzero : sphereThreePack x.1 = sphereThreePack 0 := by
    exact hpack.trans sphereThreePack_zero.symm
  have hx0 : x.1 = 0 := sphereThreePack_injective hzero
  have hxnorm : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  simp [hx0] at hxnorm

/-- Helper for Example 9.4.8: a point on the packed complex sphere unpacks to a nonzero vector in
`ℝ⁴`. -/
private theorem sphereThreeUnpack_nonzero (z : ComplexSphereThree) :
    sphereThreeUnpack z.1 ≠ 0 := by
  -- Otherwise packing back would contradict that `z` lies on the unit sphere.
  intro hunpack
  have hzero : sphereThreeUnpack z.1 = sphereThreeUnpack 0 := by
    exact hunpack.trans sphereThreeUnpack_zero.symm
  have hz0 : z.1 = 0 := sphereThreeUnpack_injective hzero
  have hznorm : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  simp [hz0] at hznorm

/-- Helper for Example 9.4.8: the packed Euclidean sphere point, normalized in `ℂ²`, is the
chosen representative on `ComplexSphereThree`. -/
private def packedSpherePoint (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    ComplexSphereThree :=
  ⟨((‖sphereThreePack x.1‖)⁻¹ : ℝ) • sphereThreePack x.1,
    invNorm_smul_mem_unitSphere _ (sphereThreePack_nonzero x)⟩

/-- Helper for Example 9.4.8: the unpacked complex sphere point, normalized in `ℝ⁴`, is the
corresponding point on the Euclidean `S^3`. -/
private def unpackedSpherePoint (z : ComplexSphereThree) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  ⟨((‖sphereThreeUnpack z.1‖)⁻¹ : ℝ) • sphereThreeUnpack z.1,
    invNorm_smul_mem_unitSphere _ (sphereThreeUnpack_nonzero z)⟩

/-- Helper for Example 9.4.8: the radial normalization from the Euclidean `S^3` to the packed
complex sphere is continuous. -/
private theorem packedSpherePoint_continuous :
    Continuous packedSpherePoint := by
  -- The normalization factor is continuous because the packed vector never vanishes on the source
  -- sphere, so inversion of the norm is continuous on the whole subtype.
  have hpack : Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
      sphereThreePack x.1 :=
    sphereThreePack_continuous.comp continuous_subtype_val
  have hnormInv : Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
      ((‖sphereThreePack x.1‖)⁻¹ : ℝ) :=
    (hpack.norm).inv₀ fun x ↦ by
      exact norm_ne_zero_iff.mpr (sphereThreePack_nonzero x)
  have hnormInvC : Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
      (((‖sphereThreePack x.1‖)⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hnormInv
  have hcoord0 : Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
      ((‖sphereThreePack x.1‖)⁻¹ : ℝ) • sphereThreePack x.1 0 := by
    simpa [smul_eq_mul] using hnormInvC.mul ((continuous_apply 0).comp hpack)
  have hcoord1 : Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
      ((‖sphereThreePack x.1‖)⁻¹ : ℝ) • sphereThreePack x.1 1 := by
    simpa [smul_eq_mul] using hnormInvC.mul ((continuous_apply 1).comp hpack)
  have hnormalized : Continuous fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↦
      ((‖sphereThreePack x.1‖)⁻¹ : ℝ) • sphereThreePack x.1 := by
    refine continuous_pi fun i : Fin 2 ↦ ?_
    fin_cases i
    · simpa using hcoord0
    · simpa using hcoord1
  exact Continuous.subtype_mk hnormalized fun x ↦ (packedSpherePoint x).2

/-- Helper for Example 9.4.8: the restricted unpacking map from the complex unit sphere is
continuous. -/
private theorem unpackedSpherePoint_continuous :
    Continuous unpackedSpherePoint := by
  -- The same normalization argument applies to the unpacking map on the complex sphere.
  have hunpack : Continuous fun z : ComplexSphereThree ↦ sphereThreeUnpack z.1 :=
    sphereThreeUnpack_continuous.comp continuous_subtype_val
  have hnormInv : Continuous fun z : ComplexSphereThree ↦
      ((‖sphereThreeUnpack z.1‖)⁻¹ : ℝ) :=
    (hunpack.norm).inv₀ fun z ↦ by
      exact norm_ne_zero_iff.mpr (sphereThreeUnpack_nonzero z)
  have h0 : Continuous fun z : ComplexSphereThree ↦ sphereThreeUnpack z.1 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 0).continuous.comp hunpack
  have h1 : Continuous fun z : ComplexSphereThree ↦ sphereThreeUnpack z.1 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 1).continuous.comp hunpack
  have h2 : Continuous fun z : ComplexSphereThree ↦ sphereThreeUnpack z.1 2 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 2).continuous.comp hunpack
  have h3 : Continuous fun z : ComplexSphereThree ↦ sphereThreeUnpack z.1 3 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 3).continuous.comp hunpack
  have hnormalized : Continuous fun z : ComplexSphereThree ↦
      ((‖sphereThreeUnpack z.1‖)⁻¹ : ℝ) • sphereThreeUnpack z.1 := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 4 ↦ ?_
    fin_cases i
    · simpa [smul_eq_mul, sphereThreeUnpack] using hnormInv.mul h0
    · simpa [smul_eq_mul, sphereThreeUnpack] using hnormInv.mul h1
    · simpa [smul_eq_mul, sphereThreeUnpack] using hnormInv.mul h2
    · simpa [smul_eq_mul, sphereThreeUnpack] using hnormInv.mul h3
  exact Continuous.subtype_mk hnormalized fun z ↦ (unpackedSpherePoint z).2

/-- Helper for Example 9.4.8: unpacking the packed sphere point recovers the original point of the
real unit sphere. -/
private theorem unpackedSpherePoint_packedSpherePoint
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    unpackedSpherePoint (packedSpherePoint x) = x := by
  -- Unpacking the normalized packed vector gives the same positive real multiple of `x`, and the
  -- outer normalization returns the original unit vector.
  apply Subtype.ext
  have hpos : 0 < ((‖sphereThreePack x.1‖)⁻¹ : ℝ) := by
    exact inv_pos.mpr (norm_pos_iff.mpr (sphereThreePack_nonzero x))
  simpa [packedSpherePoint, unpackedSpherePoint, sphereThreeUnpack_real_smul,
    sphereThreeUnpack_pack] using
    (invNorm_smul_eq_of_mem_unitSphere x.2 hpos)

/-- Helper for Example 9.4.8: packing the unpacked sphere point recovers the original point of the
complex unit sphere. -/
private theorem packedSpherePoint_unpackedSpherePoint (z : ComplexSphereThree) :
    packedSpherePoint (unpackedSpherePoint z) = z := by
  -- Packing the normalized unpacked vector gives the same positive real multiple of `z`, and the
  -- outer normalization returns the original unit vector.
  apply Subtype.ext
  have hpos : 0 < ((‖sphereThreeUnpack z.1‖)⁻¹ : ℝ) := by
    exact inv_pos.mpr (norm_pos_iff.mpr (sphereThreeUnpack_nonzero z))
  simpa [packedSpherePoint, unpackedSpherePoint, sphereThreePack_real_smul,
    sphereThreePack_unpack] using
    (invNorm_smul_eq_of_mem_unitSphere z.2 hpos)

/-- Helper for Example 9.4.8: `𝕊 3` identifies with the unit sphere in `ℂ²` by packing the four
real coordinates into two complex coordinates. -/
-- Route correction: the intended proof uses the explicit coordinate-packing homeomorphism
-- `EuclideanSpace ℝ (Fin 4) ≃ Fin 2 → ℂ`; the remaining blocker is finishing the subtype-level
-- inverse and continuity bookkeeping cleanly.
private def sphereThreeHomeomorphComplexSphereThree :
    𝕊 3 ≃ₜ ComplexSphereThree := by
  -- The sphere model `𝕊 3` is `ULift` of the real unit sphere, so we package the explicit
  -- packing/unpacking equivalence at the subtype level and transport across `ULift`.
  let packedHomeomorph :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₜ ComplexSphereThree :=
    { toEquiv :=
        { toFun := packedSpherePoint
          invFun := unpackedSpherePoint
          left_inv := unpackedSpherePoint_packedSpherePoint
          right_inv := packedSpherePoint_unpackedSpherePoint }
      continuous_toFun := packedSpherePoint_continuous
      continuous_invFun := unpackedSpherePoint_continuous }
  exact Homeomorph.ulift.trans packedHomeomorph

/-- Helper for Example 9.4.8: the inverse source homeomorphism is the normalized unpacking map on
`ComplexSphereThree`. -/
private theorem sphereThreeHomeomorphComplexSphereThree_symm_eq_unpackedSpherePoint
    (z : ComplexSphereThree) :
    sphereThreeHomeomorphComplexSphereThree.symm z = ULift.up (unpackedSpherePoint z) := by
  -- The explicit source homeomorphism was built by transporting `unpackedSpherePoint` across
  -- `ULift`, so its inverse is definitionally the normalized unpacking map.
  rfl

/-- Helper for Example 9.4.8: the canonical quotient `S^3 ⊂ ℂ² → ℂP¹` is continuous. -/
private theorem complexSphereThreeToProjectivization_continuous :
    Continuous complexSphereThreeToProjectivization := by
  -- First lift a sphere point to the nonzero-vector subtype underlying projectivization.
  let nonzeroVector : ComplexSphereThree → { v : Fin 2 → ℂ // v ≠ 0 } :=
    fun z ↦ ⟨z.1, complexSphereThree_nonzero z⟩
  have hnonzeroVector : Continuous nonzeroVector :=
    Continuous.subtype_mk continuous_subtype_val fun z ↦ (nonzeroVector z).2
  -- Then the quotient map is the ambient projectivization quotient on nonzero vectors.
  simpa [complexSphereThreeToProjectivization, Projectivization.mk', nonzeroVector,
    Projectivization.mk'_eq_mk] using
    (continuous_quotient_mk'.comp hnonzeroVector)

/-- Helper for Example 9.4.8: in the affine chart `ℂP¹ ≃ OnePoint ℂ`, the quotient map is the
usual ratio `z₀ / z₁` with the point at infinity when `z₁ = 0`. -/
private def quotientAffineChartValue (z : ComplexSphereThree) : OnePoint ℂ :=
  if _h : z.1 1 = 0 then
    OnePoint.infty
  else
    ((z.1 1)⁻¹ * z.1 0 : ℂ)

/-- Helper for Example 9.4.8: in the affine chart `ℂP¹ ≃ OnePoint ℂ`, the quotient map is the
usual ratio `z₀ / z₁` with the point at infinity when `z₁ = 0`. -/
private theorem quotientAffineChartFormula (z : ComplexSphereThree) :
    complexProjectiveLineEquivOnePointComplex.symm (complexSphereThreeToProjectivization z) =
      quotientAffineChartValue z := by
  -- The projectivization chart on `ℂP¹` is defined by the standard affine ratio formula.
  simp [quotientAffineChartValue, complexProjectiveLineEquivOnePointComplex,
    complexSphereThreeToProjectivization,
    Function.comp, Projectivization.map_mk,
    OnePoint.equivProjectivization_symm_apply_mk]

/-- Helper for Example 9.4.8: every point of `ℂP¹` has a unit-norm representative in
`ComplexSphereThree`. -/
private theorem complexSphereThreeToProjectivization_surjective :
    Function.Surjective complexSphereThreeToProjectivization := by
  intro x
  induction x using Projectivization.ind with
  | h v hv =>
      let z : ComplexSphereThree :=
        ⟨((‖v‖)⁻¹ : ℝ) • v, invNorm_smul_mem_unitSphere v hv⟩
      refine ⟨z, ?_⟩
      -- The normalized representative spans the same complex line as the original vector.
      apply (Projectivization.mk_eq_mk_iff' ℂ z.1 v (complexSphereThree_nonzero z) hv).2
      refine ⟨((‖v‖)⁻¹ : ℂ), ?_⟩
      ext i
      simp [z]

/-- Helper for Example 9.4.8: `ComplexProjectiveLine` is compact because it is the continuous image
of the compact sphere `ComplexSphereThree`. -/
private theorem complexProjectiveLine_isCompact :
    IsCompact (Set.univ : Set ComplexProjectiveLine) := by
  simpa [Set.image_univ, complexSphereThreeToProjectivization_surjective.range_eq] using
    CompactSpace.isCompact_univ.image complexSphereThreeToProjectivization_continuous

/-- Helper for Example 9.4.8: the quotient model `ComplexProjectiveLine` inherits compactness from
the sphere model. -/
private noncomputable instance complexProjectiveLineCompactSpace :
    CompactSpace ComplexProjectiveLine :=
  isCompact_univ_iff.mp complexProjectiveLine_isCompact

/-- Helper for Example 9.4.8: the concrete `S²` model has ambient real dimension `3`. -/
private instance sphereTwoModelFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

/-- Helper for Example 9.4.8: the north pole of the concrete `S²` model. -/
private def sphereTwoNorthPoleModel :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single 2 (1 : ℝ), by
    -- The standard basis vector `e₂` has unit norm.
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single]
    simp⟩

/-- Helper for Example 9.4.8: the corresponding point of `𝕊 2`. -/
private def sphereTwoNorthPole : 𝕊 2 :=
  ULift.up sphereTwoNorthPoleModel

/-- Helper for Example 9.4.8: identify `ℂ` with `ℝ²` using the real and imaginary parts, scaled by
the factor compatible with the stereographic chart formula. -/
private def complexStereographicCoord (z : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (2 * Complex.re z) +
    EuclideanSpace.single 1 (2 * Complex.im z)

/-- Helper for Example 9.4.8: recover a complex number from its scaled `ℝ²` stereographic
coordinates. -/
private def stereographicCoordComplex (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (x 0 / 2 : ℝ) + (x 1 / 2 : ℝ) * Complex.I

/-- Helper for Example 9.4.8: the scaled real-imaginary coordinates recover the original complex
number. -/
private theorem stereographicCoordComplex_left_inv (z : ℂ) :
    stereographicCoordComplex (complexStereographicCoord z) = z := by
  -- Expanding the definitions leaves the real and imaginary parts of `z`.
  apply Complex.ext <;> simp [stereographicCoordComplex, complexStereographicCoord]

/-- Helper for Example 9.4.8: the complex number reconstructed from scaled `ℝ²` coordinates
recovers the original vector. -/
private theorem stereographicCoordComplex_right_inv
    (x : EuclideanSpace ℝ (Fin 2)) :
    complexStereographicCoord (stereographicCoordComplex x) = x := by
  -- Each coordinate is recovered by dividing and then rescaling by `2`.
  ext i
  fin_cases i
  · have h : (2 : ℝ) * (x 0 / 2) = x 0 := by ring
    simpa [complexStereographicCoord, stereographicCoordComplex] using h
  · have h : (2 : ℝ) * (x 1 / 2) = x 1 := by ring
    simpa [complexStereographicCoord, stereographicCoordComplex] using h

/-- Helper for Example 9.4.8: the scaled real-imaginary coordinate map is continuous. -/
private theorem complexStereographicCoord_continuous :
    Continuous complexStereographicCoord := by
  -- The two real coordinates are explicit continuous polynomial expressions in `z`.
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp ?_
  refine continuous_pi fun i : Fin 2 ↦ ?_
  fin_cases i
  · simpa [complexStereographicCoord] using continuous_const.mul Complex.continuous_re
  · simpa [complexStereographicCoord] using continuous_const.mul Complex.continuous_im

/-- Helper for Example 9.4.8: reconstructing a complex number from scaled `ℝ²` coordinates is
continuous. -/
private theorem stereographicCoordComplex_continuous :
    Continuous stereographicCoordComplex := by
  -- The inverse formula is affine in the two real coordinates.
  have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous
  have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous
  have h0' : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ (x 0 / 2 : ℝ) :=
    by simpa [div_eq_mul_inv] using h0.mul continuous_const
  have h1' : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ (x 1 / 2 : ℝ) :=
    by simpa [div_eq_mul_inv] using h1.mul continuous_const
  simpa [stereographicCoordComplex] using
    ((Complex.continuous_ofReal.comp h0').add
      ((Complex.continuous_ofReal.comp h1').mul continuous_const))

/-- Helper for Example 9.4.8: the scaled real-imaginary coordinates give a homeomorphism
`ℂ ≃ₜ ℝ²`. -/
private def complexStereographicCoordHomeomorph :
    ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) where
  toEquiv :=
    { toFun := complexStereographicCoord
      invFun := stereographicCoordComplex
      left_inv := stereographicCoordComplex_left_inv
      right_inv := stereographicCoordComplex_right_inv }
  continuous_toFun := complexStereographicCoord_continuous
  continuous_invFun := stereographicCoordComplex_continuous

/-- Helper for Example 9.4.8: insert an `ℝ²` point into the orthogonal complement of the north
pole by adding a zero third coordinate. -/
private def northPolePerpOfEuclidean (x : EuclideanSpace ℝ (Fin 2)) :
    (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ := by
  refine ⟨EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1), ?_⟩
  -- The inserted vector is orthogonal to the north pole because its third coordinate is zero.
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [sphereTwoNorthPoleModel, PiLp.inner_apply, Fin.sum_univ_three]

/-- Helper for Example 9.4.8: forget the forced zero third coordinate in the orthogonal
complement of the north pole. -/
private def euclideanOfNorthPolePerp
    (x : (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ) :
    EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (x.1 0) + EuclideanSpace.single 1 (x.1 1)

/-- Helper for Example 9.4.8: vectors orthogonal to the north pole have zero third coordinate. -/
private theorem northPolePerp_third_eq_zero
    (x : (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ) :
    x.1 2 = 0 := by
  -- Orthogonality to `e₂` is exactly the vanishing of the third coordinate.
  have horth := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.2
  have hcoord : inner ℝ (EuclideanSpace.single 2 (1 : ℝ)) x.1 = 0 := by
    simpa [sphereTwoNorthPoleModel] using horth
  have hsingle : inner ℝ (EuclideanSpace.single 2 (1 : ℝ)) x.1 = x.1 2 := by
    simpa using (EuclideanSpace.inner_single_left 2 (1 : ℝ) x.1)
  rw [hsingle] at hcoord
  -- Expanding the north pole turns orthogonality into the third-coordinate equation.
  simpa using hcoord

/-- Helper for Example 9.4.8: inserting into the equatorial plane and projecting back recovers the
original `ℝ²` coordinates. -/
private theorem euclideanOfNorthPolePerp_northPolePerpOfEuclidean
    (x : EuclideanSpace ℝ (Fin 2)) :
    euclideanOfNorthPolePerp (northPolePerpOfEuclidean x) = x := by
  -- The first two coordinates are unchanged by the insertion.
  ext i
  fin_cases i <;> simp [euclideanOfNorthPolePerp, northPolePerpOfEuclidean]

/-- Helper for Example 9.4.8: inserting the first two coordinates of an orthogonal vector gives
back the same vector. -/
private theorem northPolePerpOfEuclidean_euclideanOfNorthPolePerp
    (x : (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ) :
    northPolePerpOfEuclidean (euclideanOfNorthPolePerp x) = x := by
  -- The orthogonality condition forces the third coordinate to remain zero.
  apply Subtype.ext
  ext i
  fin_cases i
  · simp [euclideanOfNorthPolePerp, northPolePerpOfEuclidean]
  · simp [euclideanOfNorthPolePerp, northPolePerpOfEuclidean]
  · simp [euclideanOfNorthPolePerp, northPolePerpOfEuclidean, northPolePerp_third_eq_zero x]

/-- Helper for Example 9.4.8: the orthogonal complement of the north pole is explicitly
homeomorphic to the equatorial plane `ℝ²`. -/
private noncomputable def northPolePerpHomeomorph :
    EuclideanSpace ℝ (Fin 2) ≃ₜ
      (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ where
  toEquiv :=
    { toFun := northPolePerpOfEuclidean
      invFun := euclideanOfNorthPolePerp
      left_inv := euclideanOfNorthPolePerp_northPolePerpOfEuclidean
      right_inv := northPolePerpOfEuclidean_euclideanOfNorthPolePerp }
  continuous_toFun := by
    -- Each coordinate is a continuous projection, and the third coordinate is constantly zero.
    have h0 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous
    have h1 : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous
    have hambient : Continuous fun x : EuclideanSpace ℝ (Fin 2) ↦
        (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1) :
          EuclideanSpace ℝ (Fin 3)) := by
      refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp ?_
      refine continuous_pi fun i : Fin 3 ↦ ?_
      fin_cases i
      · simpa [northPolePerpOfEuclidean] using h0
      · simpa [northPolePerpOfEuclidean] using h1
      · simpa [northPolePerpOfEuclidean] using continuous_const
    -- The ambient continuous map lands in the orthogonal complement by construction.
    exact Continuous.subtype_mk hambient fun x ↦ (northPolePerpOfEuclidean x).2
  continuous_invFun := by
    -- Reading off the first two coordinates is continuous on the subtype as well.
    have h0 : Continuous fun x :
        (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ ↦ x.1 0 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).continuous.comp continuous_subtype_val
    have h1 : Continuous fun x :
        (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ ↦ x.1 1 :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).continuous.comp continuous_subtype_val
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 2 ↦ ?_
    fin_cases i
    · simpa [euclideanOfNorthPolePerp] using h0
    · simpa [euclideanOfNorthPolePerp] using h1

/-- Helper for Example 9.4.8: the finite stereographic branch `ℂ → S² \\ {north}`. -/
private def onePointComplexFiniteToSphereTwoModel (z : ℂ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  stereoInvFun (norm_eq_of_mem_sphere sphereTwoNorthPoleModel)
    (northPolePerpHomeomorph (complexStereographicCoordHomeomorph z))

/-- Helper for Example 9.4.8: the inserted stereographic-plane vector has squared norm
`4 * ‖z‖²`. -/
private theorem northPolePerpOfEuclidean_complexStereographicCoord_normSq (z : ℂ) :
    ‖(((northPolePerpOfEuclidean (complexStereographicCoord z) :
        (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ) :
        EuclideanSpace ℝ (Fin 3)))‖ ^ 2 =
      4 * Complex.normSq z := by
  -- Expanding the inserted equatorial vector leaves exactly the real and imaginary squares.
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [northPolePerpOfEuclidean, complexStereographicCoord, Complex.normSq_apply]
  ring

/-- Helper for Example 9.4.8: the finite stereographic branch has the classical explicit Hopf
coordinates. -/
private theorem onePointComplexFiniteToSphereTwoModel_formula (z : ℂ) :
    ((onePointComplexFiniteToSphereTwoModel z :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
        EuclideanSpace ℝ (Fin 3)) =
      EuclideanSpace.single 0 (2 * Complex.re z / (1 + Complex.normSq z)) +
        EuclideanSpace.single 1 (2 * Complex.im z / (1 + Complex.normSq z)) +
        EuclideanSpace.single 2 ((Complex.normSq z - 1) / (1 + Complex.normSq z)) := by
  -- Expand the inverse stereographic map in the concrete north-pole chart.
  rw [onePointComplexFiniteToSphereTwoModel, stereoInvFun_apply]
  let w : (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ :=
    northPolePerpOfEuclidean (complexStereographicCoord z)
  change
    (‖((w : (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ) :
          EuclideanSpace ℝ (Fin 3))‖ ^ 2 + 4)⁻¹ •
        ((4 : ℝ) •
            (((w : (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ) :
              EuclideanSpace ℝ (Fin 3))) +
          (‖((w : (ℝ ∙ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3)))ᗮ) :
                EuclideanSpace ℝ (Fin 3))‖ ^ 2 - 4) •
            ((sphereTwoNorthPoleModel :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
              EuclideanSpace ℝ (Fin 3))) =
      EuclideanSpace.single 0 (2 * Complex.re z / (1 + Complex.normSq z)) +
        EuclideanSpace.single 1 (2 * Complex.im z / (1 + Complex.normSq z)) +
        EuclideanSpace.single 2 ((Complex.normSq z - 1) / (1 + Complex.normSq z))
  rw [northPolePerpOfEuclidean_complexStereographicCoord_normSq]
  have hnormSq_nonneg : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hden : (1 + Complex.normSq z : ℝ) ≠ 0 := by
    linarith
  have hden' : (4 * Complex.normSq z + 4 : ℝ) ≠ 0 := by
    linarith
  ext i
  fin_cases i
  · -- The first coordinate is the normalized real part.
    simp [w, northPolePerpOfEuclidean, complexStereographicCoord, sphereTwoNorthPoleModel,
      div_eq_mul_inv]
    field_simp [hden, hden']
    field_simp [hden]
    ring
  · -- The second coordinate is the normalized imaginary part.
    simp [w, northPolePerpOfEuclidean, complexStereographicCoord, sphereTwoNorthPoleModel,
      div_eq_mul_inv]
    field_simp [hden, hden']
    field_simp [hden]
    ring
  · -- The third coordinate records the usual stereographic height.
    simp [w, northPolePerpOfEuclidean, complexStereographicCoord, sphereTwoNorthPoleModel,
      Complex.normSq_apply, div_eq_mul_inv]
    field_simp [hden, hden']
    ring_nf

/-- Helper for Example 9.4.8: the finite stereographic branch is an open embedding. -/
private theorem onePointComplexFiniteToSphereTwoModel_isOpenEmbedding :
    Topology.IsOpenEmbedding onePointComplexFiniteToSphereTwoModel := by
  -- Compose the `ℂ ≃ₜ ℝ²` homeomorphism with the explicit inverse stereographic chart.
  have hstereo :
      Topology.IsOpenEmbedding
        (stereoInvFun (norm_eq_of_mem_sphere sphereTwoNorthPoleModel)) := by
    simpa using
      (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere sphereTwoNorthPoleModel))
  exact hstereo.comp
    (northPolePerpHomeomorph.isOpenEmbedding.comp
      complexStereographicCoordHomeomorph.isOpenEmbedding)

/-- Helper for Example 9.4.8: the finite stereographic branch covers exactly the complement of the
north pole. -/
private theorem onePointComplexFiniteToSphereTwoModel_range :
    Set.range onePointComplexFiniteToSphereTwoModel =
      ({sphereTwoNorthPoleModel} : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))ᶜ := by
  -- The two auxiliary homeomorphisms are surjective, so the range is exactly the complement of the
  -- north pole for the explicit inverse stereographic chart as well.
  refine le_antisymm ?_ ?_
  · rintro x ⟨z, rfl⟩
    simpa [onePointComplexFiniteToSphereTwoModel] using
      stereoInvFun_ne_north_pole (norm_eq_of_mem_sphere sphereTwoNorthPoleModel)
        (northPolePerpHomeomorph (complexStereographicCoordHomeomorph z))
  · intro x hx
    refine
      ⟨complexStereographicCoordHomeomorph.symm
          (northPolePerpHomeomorph.symm
            ((stereographic (norm_eq_of_mem_sphere sphereTwoNorthPoleModel)) x)), ?_⟩
    -- Apply the left-inverse relation for stereographic projection away from the north pole.
    simpa [onePointComplexFiniteToSphereTwoModel] using
      stereo_left_inv (norm_eq_of_mem_sphere sphereTwoNorthPoleModel)
        (show (x : EuclideanSpace ℝ (Fin 3)) ≠ (sphereTwoNorthPoleModel : EuclideanSpace ℝ (Fin 3))
          from fun h ↦ hx (Subtype.ext h))

/-- Helper for Example 9.4.8: the standard stereographic homeomorphism `OnePoint ℂ ≃ₜ S²`,
normalized so that the finite coordinate `z` corresponds to the inverse stereographic image of the
scaled plane coordinate `(2 Re z, 2 Im z)` and `∞` goes to the north pole. -/
private noncomputable def onePointComplexStereographicHomeomorphSphereTwo :
    OnePoint ℂ ≃ₜ 𝕊 2 :=
  (OnePoint.equivOfIsEmbeddingOfRangeEq sphereTwoNorthPoleModel
      onePointComplexFiniteToSphereTwoModel
      onePointComplexFiniteToSphereTwoModel_isOpenEmbedding.toIsEmbedding
      onePointComplexFiniteToSphereTwoModel_range).trans Homeomorph.ulift.symm

/-- Helper for Example 9.4.8: on finite points, the stereographic homeomorphism agrees with the
explicit inverse stereographic branch. -/
private theorem onePointComplexStereographicHomeomorphSphereTwo_apply_coe (z : ℂ) :
    onePointComplexStereographicHomeomorphSphereTwo z =
      ULift.up (onePointComplexFiniteToSphereTwoModel z) := by
  -- This is the defining finite branch of `OnePoint.equivOfIsEmbeddingOfRangeEq`.
  rfl

/-- Helper for Example 9.4.8: the stereographic homeomorphism sends `∞` to the north pole. -/
private theorem onePointComplexStereographicHomeomorphSphereTwo_apply_infty :
    onePointComplexStereographicHomeomorphSphereTwo (OnePoint.infty : OnePoint ℂ) =
      sphereTwoNorthPole := by
  -- The unique point outside the finite image is exactly the north pole.
  rfl

/-- A map `η : 𝕊 3 → 𝕊 2` is a Hopf quotient map if, after identifying `𝕊 3` with the unit
sphere in `ℂ²`, it is induced from the quotient `S^3 ⊂ ℂ² → ℂP¹` followed by a homeomorphism
`ℂP¹ ≃ₜ S²`. -/
def IsHopfQuotientMap (η : 𝕊 3 → 𝕊 2) : Prop :=
  ∃ (eS3 : 𝕊 3 ≃ₜ ComplexSphereThree) (eCP1 : ComplexProjectiveLine ≃ₜ 𝕊 2),
    η = eCP1 ∘ complexSphereThreeToProjectivization ∘ eS3

namespace IsHopfQuotientMap

/-- A Hopf quotient map comes with the source-facing homeomorphisms identifying it with the
quotient `S^3 ⊂ ℂ² → ℂP¹ ≃ S²`. -/
theorem exists_homeomorphisms {η : 𝕊 3 → 𝕊 2} (hη : IsHopfQuotientMap η) :
    ∃ (eS3 : 𝕊 3 ≃ₜ ComplexSphereThree) (eCP1 : ComplexProjectiveLine ≃ₜ 𝕊 2),
      η = eCP1 ∘ complexSphereThreeToProjectivization ∘ eS3 :=
  hη

end IsHopfQuotientMap

/-- The explicit coordinate formula underlying the Hopf map `S^3 → S^2`. -/
def hopfMapVec (x : 𝕊 3) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0
      (2 * (x.down.1 0 * x.down.1 2 + x.down.1 1 * x.down.1 3)) +
    EuclideanSpace.single 1
      (2 * (x.down.1 1 * x.down.1 2 - x.down.1 0 * x.down.1 3)) +
    EuclideanSpace.single 2
      (x.down.1 0 ^ 2 + x.down.1 1 ^ 2 - x.down.1 2 ^ 2 - x.down.1 3 ^ 2)

/-- The coordinate formula of the Hopf map lands on the unit sphere `S²`. -/
theorem hopfMapVec_mem (x : 𝕊 3) :
    hopfMapVec x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- First rewrite the source sphere constraint as the usual quadratic equation in coordinates.
  have hx_sq :
      x.down.1 0 ^ 2 + x.down.1 1 ^ 2 + x.down.1 2 ^ 2 + x.down.1 3 ^ 2 = 1 := by
    have hx_norm : ‖x.down.1‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp x.down.2
    have hx_norm_sq : ‖x.down.1‖ ^ 2 = 1 := by
      nlinarith [hx_norm]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four] at hx_norm_sq
    nlinarith
  -- Then expand the target norm and apply the standard Hopf polynomial identity.
  rw [mem_sphere_zero_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [hopfMapVec]
  ring_nf
  nlinarith [hx_sq]

/-- The Hopf map `η : S^3 → S^2` given by the standard coordinate formula. -/
def hopfMap (x : 𝕊 3) : 𝕊 2 :=
  ULift.up ⟨hopfMapVec x, hopfMapVec_mem x⟩

/-- Helper for Example 9.4.8: the explicit Hopf map varies continuously with the source point on
`S^3`. -/
private theorem hopfMap_continuous :
    Continuous hopfMap := by
  -- Read the four real source coordinates through the `ULift` sphere model.
  have hdown : Continuous fun x : 𝕊 3 =>
      (((x.down :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : EuclideanSpace ℝ (Fin 4))) :=
    continuous_subtype_val.comp continuous_uliftDown
  have h0 : Continuous fun x : 𝕊 3 ↦ x.down.1 0 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 0).continuous.comp hdown
  have h1 : Continuous fun x : 𝕊 3 ↦ x.down.1 1 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 1).continuous.comp hdown
  have h2 : Continuous fun x : 𝕊 3 ↦ x.down.1 2 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 2).continuous.comp hdown
  have h3 : Continuous fun x : 𝕊 3 ↦ x.down.1 3 := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 3).continuous.comp hdown
  have hVec : Continuous hopfMapVec := by
    -- Each target coordinate is a polynomial in the four real source coordinates.
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp ?_
    refine continuous_pi fun i : Fin 3 ↦ ?_
    fin_cases i
    · simpa [hopfMapVec] using
        continuous_const.mul ((h0.mul h2).add (h1.mul h3))
    · simpa [hopfMapVec] using
        continuous_const.mul ((h1.mul h2).sub (h0.mul h3))
    · simpa [hopfMapVec] using
        (((h0.pow 2).add (h1.pow 2)).sub (h2.pow 2)).sub (h3.pow 2)
  have hSphere : Continuous fun x : 𝕊 3 ↦
      (⟨hopfMapVec x, hopfMapVec_mem x⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Continuous.subtype_mk hVec fun x ↦ hopfMapVec_mem x
  -- Then lift the subtype-valued map back to `𝕊 2`.
  simpa [hopfMap] using continuous_uliftUp.comp hSphere

/-- Helper for Example 9.4.8: unpacking a point of `ComplexSphereThree` identifies the Euclidean
norm square with the sum of the two complex norm squares. -/
private theorem complexSphereThreeNormSqAdd (z : ComplexSphereThree) :
    Complex.normSq (z.1 0) + Complex.normSq (z.1 1) = ‖sphereThreeUnpack z.1‖ ^ 2 := by
  -- The explicit unpacking formula records the Euclidean norm square in real coordinates.
  symm
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp [sphereThreeUnpack, Complex.normSq_apply]
  ring

/-- Helper for Example 9.4.8: unpacking a complex pair identifies the real norm square with the
sum of the two complex norm squares. -/
private theorem sphereThreeUnpack_normSq (z : Fin 2 → ℂ) :
    ‖sphereThreeUnpack z‖ ^ 2 = Complex.normSq (z 0) + Complex.normSq (z 1) := by
  -- Expand the four real coordinates and regroup them into the two complex norm squares.
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  simp [sphereThreeUnpack, Complex.normSq_apply]
  ring

/-- Helper for Example 9.4.8: normalizing the unpacked coordinates lands on the Euclidean unit
sphere `S^3 ⊂ ℝ⁴`. -/
private theorem sphereThreeUnpack_mem_unitSphere (z : ComplexSphereThree) :
    (((‖sphereThreeUnpack z.1‖)⁻¹ : ℝ) • sphereThreeUnpack z.1) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  -- This is exactly the normalization built into `unpackedSpherePoint`.
  exact (unpackedSpherePoint z).2

/-- Helper for Example 9.4.8: `unpackedSpherePoint` is the normalized unpacking of the complex
coordinates. -/
private theorem unpackedSpherePoint_eq (z : ComplexSphereThree) :
    unpackedSpherePoint z =
      ⟨((‖sphereThreeUnpack z.1‖)⁻¹ : ℝ) • sphereThreeUnpack z.1,
        sphereThreeUnpack_mem_unitSphere z⟩ := by
  -- The helper is just the explicit normalization formula packaged into the subtype.
  rfl

/-- Helper for Example 9.4.8: after the source-side normalization, the Hopf coordinates are the
standard complex expressions divided by the unpacked Euclidean norm square. -/
private theorem hopfMapComplexSphereThreeFormula (z : ComplexSphereThree) :
    hopfMapVec (sphereThreeHomeomorphComplexSphereThree.symm z) =
      EuclideanSpace.single 0
        (2 * ((z.1 0) * star (z.1 1)).re / ‖sphereThreeUnpack z.1‖ ^ 2) +
        EuclideanSpace.single 1
          (2 * ((z.1 0) * star (z.1 1)).im / ‖sphereThreeUnpack z.1‖ ^ 2) +
        EuclideanSpace.single 2
          ((Complex.normSq (z.1 0) - Complex.normSq (z.1 1)) / ‖sphereThreeUnpack z.1‖ ^ 2) := by
  -- Rewrite the inverse source homeomorphism once into the normalized unpacking formula.
  rw [sphereThreeHomeomorphComplexSphereThree_symm_eq_unpackedSpherePoint, unpackedSpherePoint_eq]
  have hnorm_ne : ‖sphereThreeUnpack z.1‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sphereThreeUnpack_nonzero z)
  have hsq_ne : ‖sphereThreeUnpack z.1‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm_ne
  ext i
  fin_cases i
  · -- The first Hopf coordinate is the normalized real part of `z₀ * conj z₁`.
    simp [hopfMapVec, sphereThreeUnpack, Complex.mul_re,
      Complex.normSq_apply, div_eq_mul_inv]
    field_simp [hsq_ne]
  · -- The second Hopf coordinate is the normalized imaginary part of `z₀ * conj z₁`.
    simp [hopfMapVec, sphereThreeUnpack, Complex.mul_im,
      Complex.normSq_apply, div_eq_mul_inv]
    field_simp [hsq_ne]
    ring
  · -- The height coordinate is the normalized norm-square difference.
    simp [hopfMapVec, sphereThreeUnpack, Complex.normSq_apply, div_eq_mul_inv]
    field_simp [hsq_ne]
    ring

/-- Helper for Example 9.4.8: multiplying the affine ratio `a / b` by `‖b‖²` recovers the Hopf
numerator `a * conj b`. -/
private theorem complexNormSq_mul_inv_mul_eq_mul_star (a b : ℂ) :
    ((Complex.normSq b : ℂ) * (b⁻¹ * a)) = a * star b := by
  -- Rewrite the inverse through complex conjugation, then cancel the scalar norm factor.
  by_cases hb : b = 0
  · simp [hb]
  · rw [Complex.inv_def]
    have hbnorm : (Complex.normSq b : ℂ) ≠ 0 := by
      exact_mod_cast (Complex.normSq_eq_zero.not.mpr hb)
    calc
      (Complex.normSq b : ℂ) * (star b * ((Complex.normSq b)⁻¹ : ℝ) * a) =
          (Complex.normSq b : ℂ) * star b * (((Complex.normSq b : ℂ)⁻¹) * a) := by
            simp [mul_assoc]
      _ = ((Complex.normSq b : ℂ) * ((Complex.normSq b : ℂ)⁻¹)) * (star b * a) := by
            ring_nf
      _ = a * star b := by
            simp [hbnorm, mul_comm]

/-- Helper for Example 9.4.8: the stereographic denominator for the affine ratio `a / b`
normalizes to the common Hopf denominator. -/
private theorem ratioNormSq_addOne_eq_normSqSum_div_normSq (a b : ℂ) (hb : b ≠ 0) :
    1 + Complex.normSq (b⁻¹ * a) =
      (Complex.normSq a + Complex.normSq b) / Complex.normSq b := by
  -- Clear the nonzero denominator `‖b‖²` to compare both scalar expressions directly.
  have hbnorm : Complex.normSq b ≠ 0 := Complex.normSq_eq_zero.not.mpr hb
  rw [Complex.normSq_mul, Complex.normSq_inv, div_eq_mul_inv]
  field_simp [hbnorm]
  ring

/-- Helper for Example 9.4.8: the real stereographic coordinate of `a / b` matches the real Hopf
coordinate once the common denominator is normalized. -/
private theorem ratioRe_eq_mulStarRe_div_normSqSum (a b : ℂ) (hb : b ≠ 0) :
    Complex.re (b⁻¹ * a) / (1 + Complex.normSq (b⁻¹ * a)) =
      (a * star b).re / (Complex.normSq a + Complex.normSq b) := by
  -- Multiply numerator and denominator by `‖b‖²`, then identify the resulting numerator with the
  -- real part of `a * conj b`.
  have hbnorm : Complex.normSq b ≠ 0 := Complex.normSq_eq_zero.not.mpr hb
  have hsum : Complex.normSq a + Complex.normSq b ≠ 0 := by
    have hbpos : 0 < Complex.normSq b := Complex.normSq_pos.mpr hb
    linarith [Complex.normSq_nonneg a]
  have hre : Complex.normSq b * Complex.re (b⁻¹ * a) = (a * star b).re := by
    simpa [Complex.mul_re] using
      congrArg Complex.re (complexNormSq_mul_inv_mul_eq_mul_star a b)
  rw [ratioNormSq_addOne_eq_normSqSum_div_normSq a b hb]
  field_simp [hbnorm, hsum]
  simpa [div_eq_mul_inv, mul_comm] using hre

/-- Helper for Example 9.4.8: the imaginary stereographic coordinate of `a / b` matches the
imaginary Hopf coordinate once the common denominator is normalized. -/
private theorem ratioIm_eq_mulStarIm_div_normSqSum (a b : ℂ) (hb : b ≠ 0) :
    Complex.im (b⁻¹ * a) / (1 + Complex.normSq (b⁻¹ * a)) =
      (a * star b).im / (Complex.normSq a + Complex.normSq b) := by
  -- The same denominator-clearing argument identifies the imaginary numerator with the imaginary
  -- part of `a * conj b`.
  have hbnorm : Complex.normSq b ≠ 0 := Complex.normSq_eq_zero.not.mpr hb
  have hsum : Complex.normSq a + Complex.normSq b ≠ 0 := by
    have hbpos : 0 < Complex.normSq b := Complex.normSq_pos.mpr hb
    linarith [Complex.normSq_nonneg a]
  have him : Complex.normSq b * Complex.im (b⁻¹ * a) = (a * star b).im := by
    simpa [Complex.mul_im] using
      congrArg Complex.im (complexNormSq_mul_inv_mul_eq_mul_star a b)
  rw [ratioNormSq_addOne_eq_normSqSum_div_normSq a b hb]
  field_simp [hbnorm, hsum]
  simpa [div_eq_mul_inv, mul_comm] using him

/-- Helper for Example 9.4.8: the stereographic height coordinate of `a / b` matches the Hopf
height coordinate after rewriting to the common denominator. -/
private theorem ratioHeight_eq_normSqSub_div_normSqSum (a b : ℂ) (hb : b ≠ 0) :
    (Complex.normSq (b⁻¹ * a) - 1) / (1 + Complex.normSq (b⁻¹ * a)) =
      (Complex.normSq a - Complex.normSq b) / (Complex.normSq a + Complex.normSq b) := by
  -- Normalize the denominator once, then the remaining identity is a direct scalar calculation.
  have hbnorm : Complex.normSq b ≠ 0 := Complex.normSq_eq_zero.not.mpr hb
  have hsum : Complex.normSq a + Complex.normSq b ≠ 0 := by
    have hbpos : 0 < Complex.normSq b := Complex.normSq_pos.mpr hb
    linarith [Complex.normSq_nonneg a]
  rw [ratioNormSq_addOne_eq_normSqSum_div_normSq a b hb, Complex.normSq_mul, Complex.normSq_inv]
  field_simp [hbnorm, hsum]

/-- Helper for Example 9.4.8: the finite stereographic formula matches the normalized Hopf
coordinates for the affine ratio `z₀ / z₁`. -/
private theorem finiteAffineFormula_eq_hopfCoordinates
    (z : ComplexSphereThree) (hz1 : z.1 1 ≠ 0) :
    EuclideanSpace.single (0 : Fin 3)
        (2 * Complex.re (((z.1 1)⁻¹ * z.1 0 : ℂ)) /
          (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ)))) +
      EuclideanSpace.single (1 : Fin 3)
        (2 * Complex.im (((z.1 1)⁻¹ * z.1 0 : ℂ)) /
          (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ)))) +
      EuclideanSpace.single (2 : Fin 3)
        ((Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ)) - 1) /
          (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ)))) =
      EuclideanSpace.single (0 : Fin 3)
        (2 * ((z.1 0) * star (z.1 1)).re / ‖sphereThreeUnpack z.1‖ ^ 2) +
        EuclideanSpace.single (1 : Fin 3)
          (2 * ((z.1 0) * star (z.1 1)).im / ‖sphereThreeUnpack z.1‖ ^ 2) +
        EuclideanSpace.single (2 : Fin 3)
          ((Complex.normSq (z.1 0) - Complex.normSq (z.1 1)) / ‖sphereThreeUnpack z.1‖ ^ 2) := by
  -- Compare the three ambient coordinates separately so each scalar ratio lemma applies directly.
  ext i
  fin_cases i
  · -- The first coordinate is the real-part comparison for the affine ratio `z₀ / z₁`.
    have hre :
        2 * Complex.re (((z.1 1)⁻¹ * z.1 0 : ℂ)) /
            (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ))) =
          2 * (z.1 0 * star (z.1 1)).re / ‖sphereThreeUnpack z.1‖ ^ 2 := by
      calc
        2 * Complex.re (((z.1 1)⁻¹ * z.1 0 : ℂ)) /
            (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ))) =
          2 * (Complex.re (((z.1 1)⁻¹ * z.1 0 : ℂ)) /
            (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ)))) := by
              ring
        _ = 2 * ((z.1 0 * star (z.1 1)).re /
              (Complex.normSq (z.1 0) + Complex.normSq (z.1 1))) := by
                rw [ratioRe_eq_mulStarRe_div_normSqSum (z.1 0) (z.1 1) hz1]
        _ = 2 * ((z.1 0 * star (z.1 1)).re / ‖sphereThreeUnpack z.1‖ ^ 2) := by
              rw [complexSphereThreeNormSqAdd z]
        _ = 2 * (z.1 0 * star (z.1 1)).re / ‖sphereThreeUnpack z.1‖ ^ 2 := by
              ring
    simpa using hre
  · -- The second coordinate is the imaginary-part comparison for the same affine ratio.
    have him :
        2 * Complex.im (((z.1 1)⁻¹ * z.1 0 : ℂ)) /
            (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ))) =
          2 * (z.1 0 * star (z.1 1)).im / ‖sphereThreeUnpack z.1‖ ^ 2 := by
      calc
        2 * Complex.im (((z.1 1)⁻¹ * z.1 0 : ℂ)) /
            (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ))) =
          2 * (Complex.im (((z.1 1)⁻¹ * z.1 0 : ℂ)) /
            (1 + Complex.normSq (((z.1 1)⁻¹ * z.1 0 : ℂ)))) := by
              ring
        _ = 2 * ((z.1 0 * star (z.1 1)).im /
              (Complex.normSq (z.1 0) + Complex.normSq (z.1 1))) := by
                rw [ratioIm_eq_mulStarIm_div_normSqSum (z.1 0) (z.1 1) hz1]
        _ = 2 * ((z.1 0 * star (z.1 1)).im / ‖sphereThreeUnpack z.1‖ ^ 2) := by
              rw [complexSphereThreeNormSqAdd z]
        _ = 2 * (z.1 0 * star (z.1 1)).im / ‖sphereThreeUnpack z.1‖ ^ 2 := by
              ring
    simpa using him
  · -- The height coordinate uses the normalized difference of norm squares.
    simpa [complexSphereThreeNormSqAdd z] using
      ratioHeight_eq_normSqSub_div_normSqSum (z.1 0) (z.1 1) hz1

/-- Helper for Example 9.4.8: equality in `𝕊 2` can be checked on the ambient `ℝ³` vectors after
descending through `ULift`. -/
private theorem sphereTwo_eq_of_down_val_eq {x y : 𝕊 2}
    (hxy : x.down.1 = y.down.1) : x = y := by
  -- Once the ambient vectors agree, the sphere points agree by subtype extensionality and then by
  -- `ULift.down_injective`.
  apply ULift.down_injective
  apply Subtype.ext
  simpa using hxy

/-- Helper for Example 9.4.8: the affine chart on `ComplexSphereThree` agrees with the explicit
Hopf map after the stereographic identification `OnePoint ℂ ≃ₜ S²`. -/
private theorem finiteAffineBranch_eq_hopfMap (z : ComplexSphereThree) (hz1 : z.1 1 ≠ 0) :
    onePointComplexStereographicHomeomorphSphereTwo (((z.1 1)⁻¹ * z.1 0 : ℂ)) =
      hopfMap (sphereThreeHomeomorphComplexSphereThree.symm z) := by
  -- Reduce the `𝕊 2` equality to the ambient `ℝ³` vectors, then plug in the explicit formulas on
  -- both sides.
  rw [onePointComplexStereographicHomeomorphSphereTwo_apply_coe]
  refine sphereTwo_eq_of_down_val_eq ?_
  -- The finite stereographic branch and the Hopf-coordinate formula now live in the same ambient
  -- vector space, so the scalar comparison lemma closes the goal.
  simp only [hopfMap]
  rw [onePointComplexFiniteToSphereTwoModel_formula, hopfMapComplexSphereThreeFormula]
  exact finiteAffineFormula_eq_hopfCoordinates z hz1

/-- Helper for Example 9.4.8: when the second complex coordinate vanishes, the Hopf map lands at
the north pole. -/
private theorem hopfMap_eq_northPole_of_second_eq_zero (z : ComplexSphereThree)
    (hz1 : z.1 1 = 0) :
    hopfMap (sphereThreeHomeomorphComplexSphereThree.symm z) = sphereTwoNorthPole := by
  -- Reduce to the ambient `ℝ³` coordinates, where the Hopf formula collapses to the north pole.
  refine sphereTwo_eq_of_down_val_eq ?_
  simp only [hopfMap, sphereTwoNorthPole]
  rw [hopfMapComplexSphereThreeFormula]
  have hz0 : z.1 0 ≠ 0 := by
    intro hz0
    apply complexSphereThree_nonzero z
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
  have hden : ‖sphereThreeUnpack z.1‖ ^ 2 = Complex.normSq (z.1 0) := by
    rw [sphereThreeUnpack_normSq]
    simp [hz1]
  have hden_ne : ‖sphereThreeUnpack z.1‖ ^ 2 ≠ 0 := by
    rw [hden]
    exact Complex.normSq_eq_zero.not.mpr hz0
  -- The first two coordinates vanish, and the height coordinate becomes `1`.
  ext i
  fin_cases i
  · simp [sphereTwoNorthPoleModel, hz1]
  · simp [sphereTwoNorthPoleModel, hz1]
  · rw [hden]
    have hz0norm : Complex.normSq (z.1 0) ≠ 0 := Complex.normSq_eq_zero.not.mpr hz0
    have hheight :
        (Complex.normSq (z.1 0) - Complex.normSq (z.1 1)) / Complex.normSq (z.1 0) = 1 := by
      simpa [hz1] using
        (div_self hz0norm : Complex.normSq (z.1 0) / Complex.normSq (z.1 0) = (1 : ℝ))
    simpa [sphereTwoNorthPoleModel] using hheight

/-- Helper for Example 9.4.8: the affine chart on `ComplexSphereThree` agrees with the explicit
Hopf map after the stereographic identification `OnePoint ℂ ≃ₜ S²`. -/
private theorem hopfQuotientAffineChartComparison (z : ComplexSphereThree) :
    onePointComplexStereographicHomeomorphSphereTwo
        (complexProjectiveLineEquivOnePointComplex.symm
          (complexSphereThreeToProjectivization z)) =
      hopfMap (sphereThreeHomeomorphComplexSphereThree.symm z) := by
  -- Route correction: split on `z.1 1 = 0`; the zero branch reduces to
  -- `hopfMap_eq_northPole_of_second_eq_zero`, and the nonzero branch reduces to
  -- `finiteAffineBranch_eq_hopfMap` after `quotientAffineChartFormula`.
  by_cases hz1 : z.1 1 = 0
  · -- In the zero branch the quotient lands at `∞`, which the stereographic homeomorphism sends
    -- to the north pole.
    rw [quotientAffineChartFormula, quotientAffineChartValue, dif_pos hz1,
      onePointComplexStereographicHomeomorphSphereTwo_apply_infty]
    exact (hopfMap_eq_northPole_of_second_eq_zero z hz1).symm
  · -- Away from `z₁ = 0`, the quotient chart is the finite affine ratio `z₀ / z₁`.
    rw [quotientAffineChartFormula, quotientAffineChartValue, dif_neg hz1]
    exact finiteAffineBranch_eq_hopfMap z hz1

/-- Helper for Example 9.4.8: the concrete `S²` carrier used in the quotient comparison. -/
private abbrev SphereTwo : Type := ↑(TopCat.sphere 2)

/-- Helper for Example 9.4.8: the concrete `S³` carrier used in the quotient comparison. -/
private abbrev SphereThree : Type := ↑(TopCat.sphere 3)

/-- Helper for Example 9.4.8: normalize a nonzero vector in `ℂ²` onto the unit sphere
`S^3 ⊂ ℂ²`. -/
private def normalizeNonzeroComplexVector
    (v : { w : Fin 2 → ℂ // w ≠ 0 }) : ComplexSphereThree :=
  ⟨((‖v.1‖)⁻¹ : ℝ) • v.1, invNorm_smul_mem_unitSphere _ v.2⟩

/-- Helper for Example 9.4.8: the projective affine chart on a nonzero vector is the ratio
`z₀ / z₁`, with `∞` when the denominator vanishes. -/
private def projectiveAffineChart
    (v : { w : Fin 2 → ℂ // w ≠ 0 }) : OnePoint ℂ :=
  if hv1 : v.1 1 = 0 then
    OnePoint.infty
  else
    ((v.1 1)⁻¹ * v.1 0 : ℂ)

/-- Helper for Example 9.4.8: the sphere-valued projective chart factors through the Hopf map on
the normalized representative. -/
private def projectiveSphereChart
    (v : { w : Fin 2 → ℂ // w ≠ 0 }) : SphereTwo :=
  (onePointComplexStereographicHomeomorphSphereTwo (projectiveAffineChart v) : SphereTwo)

/-- Helper for Example 9.4.8: the Hopf-map formula on the normalized nonzero representative. -/
private def normalizedProjectiveSphereChart
    (v : { w : Fin 2 → ℂ // w ≠ 0 }) : SphereTwo :=
  (hopfMap ((sphereThreeHomeomorphComplexSphereThree.symm
    (normalizeNonzeroComplexVector v)) : SphereThree) : SphereTwo)

/-- Helper for Example 9.4.8: normalizing a nonzero vector does not change its projective class. -/
private theorem complexSphereThreeToProjectivization_normalizeNonzeroComplexVector
    (v : { w : Fin 2 → ℂ // w ≠ 0 }) :
    complexSphereThreeToProjectivization (normalizeNonzeroComplexVector v) =
      Projectivization.mk ℂ v.1 v.2 := by
  -- The normalized vector differs from `v` by a nonzero real scalar, so it spans the same line.
  apply (Projectivization.mk_eq_mk_iff' ℂ
    ((normalizeNonzeroComplexVector v).1) v.1
    (complexSphereThree_nonzero (normalizeNonzeroComplexVector v)) v.2).2
  refine ⟨((‖v.1‖)⁻¹ : ℂ), ?_⟩
  ext i
  simp [normalizeNonzeroComplexVector]

/-- Helper for Example 9.4.8: normalizing a nonzero vector does not change its affine chart. -/
private theorem quotientAffineChartValue_normalizeNonzeroComplexVector
    (v : { w : Fin 2 → ℂ // w ≠ 0 }) :
    quotientAffineChartValue (normalizeNonzeroComplexVector v) = projectiveAffineChart v := by
  -- The normalization scalar is real and nonzero, so it neither changes the vanishing of the
  -- second coordinate nor the ratio `z₀ / z₁`.
  have hnorm_ne : ‖v.1‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
  by_cases hv1 : v.1 1 = 0
  · -- When `v₁ = 0`, both charts land at `∞`.
    have hnormCoord :
        ((normalizeNonzeroComplexVector v).1) 1 = 0 := by
      simp [normalizeNonzeroComplexVector, hv1]
    simp [quotientAffineChartValue, projectiveAffineChart, hv1, hnormCoord]
  · -- Away from `v₁ = 0`, the common scalar cancels out of the affine ratio.
    have hnormCoord :
        ((normalizeNonzeroComplexVector v).1) 1 ≠ 0 := by
      simp [normalizeNonzeroComplexVector, hv1, hnorm_ne]
    have hratio :
        ((((normalizeNonzeroComplexVector v).1) 1)⁻¹ *
            ((normalizeNonzeroComplexVector v).1 0) : ℂ) =
          ((v.1 1)⁻¹ * v.1 0 : ℂ) := by
      simp [normalizeNonzeroComplexVector, smul_eq_mul, hv1, hnorm_ne, mul_assoc]
    simp [quotientAffineChartValue, projectiveAffineChart, hv1, hnormCoord, hratio]

/-- Helper for Example 9.4.8: the sphere-valued projective chart agrees with the normalized Hopf
comparison. -/
private theorem projectiveSphereChart_eq_hopfComparison
    (v : { w : Fin 2 → ℂ // w ≠ 0 }) :
    projectiveSphereChart v = normalizedProjectiveSphereChart v := by
  -- First rewrite the affine chart through the normalized representative, then apply the
  -- already-established Hopf comparison on `ComplexSphereThree`.
  calc
    projectiveSphereChart v
        = onePointComplexStereographicHomeomorphSphereTwo
            (projectiveAffineChart v) := by
              rfl
    _ = onePointComplexStereographicHomeomorphSphereTwo
          (quotientAffineChartValue (normalizeNonzeroComplexVector v)) := by
            rw [quotientAffineChartValue_normalizeNonzeroComplexVector]
    _ = onePointComplexStereographicHomeomorphSphereTwo
          (complexProjectiveLineEquivOnePointComplex.symm
            (complexSphereThreeToProjectivization (normalizeNonzeroComplexVector v))) := by
              rw [quotientAffineChartFormula]
    _ = normalizedProjectiveSphereChart v := by
            exact hopfQuotientAffineChartComparison (normalizeNonzeroComplexVector v)

/-- Helper for Example 9.4.8: the normalized representative in `ComplexSphereThree` depends
continuously on the nonzero vector. -/
private theorem normalizeNonzeroComplexVector_continuous :
    Continuous normalizeNonzeroComplexVector := by
  -- The normalization factor is continuous on the nonzero-vector subtype, so each coordinate of
  -- the normalized representative varies continuously.
  have hval : Continuous fun v : { w : Fin 2 → ℂ // w ≠ 0 } ↦ (v : Fin 2 → ℂ) :=
    continuous_subtype_val
  have hnormInv : Continuous fun v : { w : Fin 2 → ℂ // w ≠ 0 } ↦
      ((‖(v : Fin 2 → ℂ)‖)⁻¹ : ℝ) :=
    (hval.norm).inv₀ fun v ↦ norm_ne_zero_iff.mpr v.2
  have hnormInvC : Continuous fun v : { w : Fin 2 → ℂ // w ≠ 0 } ↦
      (((‖(v : Fin 2 → ℂ)‖)⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hnormInv
  have hcoord0 : Continuous fun v : { w : Fin 2 → ℂ // w ≠ 0 } ↦
      ((‖(v : Fin 2 → ℂ)‖)⁻¹ : ℝ) • (v : Fin 2 → ℂ) 0 := by
    simpa [smul_eq_mul] using hnormInvC.mul ((continuous_apply 0).comp hval)
  have hcoord1 : Continuous fun v : { w : Fin 2 → ℂ // w ≠ 0 } ↦
      ((‖(v : Fin 2 → ℂ)‖)⁻¹ : ℝ) • (v : Fin 2 → ℂ) 1 := by
    simpa [smul_eq_mul] using hnormInvC.mul ((continuous_apply 1).comp hval)
  have hnormalized : Continuous fun v : { w : Fin 2 → ℂ // w ≠ 0 } ↦
      ((‖(v : Fin 2 → ℂ)‖)⁻¹ : ℝ) • (v : Fin 2 → ℂ) := by
    refine continuous_pi fun i : Fin 2 ↦ ?_
    fin_cases i
    · simpa using hcoord0
    · simpa using hcoord1
  exact Continuous.subtype_mk hnormalized fun v ↦ (normalizeNonzeroComplexVector v).2

/-- Helper for Example 9.4.8: the sphere-valued chart on nonzero vectors is continuous because it
is the Hopf map on the normalized representative. -/
private theorem projectiveSphereChart_continuous :
    Continuous projectiveSphereChart := by
  -- Rewrite the chart through the normalized Hopf comparison, where all maps are already known to
  -- be continuous.
  have hHopf : Continuous normalizedProjectiveSphereChart :=
    hopfMap_continuous.comp
      (sphereThreeHomeomorphComplexSphereThree.continuous_symm.comp
        normalizeNonzeroComplexVector_continuous)
  have hEq : projectiveSphereChart = normalizedProjectiveSphereChart := by
    funext v
    exact projectiveSphereChart_eq_hopfComparison v
  rw [hEq]
  exact hHopf

/-- Helper for Example 9.4.8: the affine ratio chart is unchanged by complex rescaling of a
nonzero vector. -/
private theorem projectiveAffineChart_scaleInvariant
    (a b : { w : Fin 2 → ℂ // w ≠ 0 }) (t : ℂ) (h : a = t • (b : Fin 2 → ℂ)) :
    projectiveAffineChart a = projectiveAffineChart b := by
  -- The affine ratio `(t • b)₀ / (t • b)₁` is the same as `b₀ / b₁`; the `t = 0` case is
  -- impossible because `a` is nonzero.
  have ht : t ≠ 0 := by
    intro ht
    apply a.2
    rw [h, ht, zero_smul]
  have hEq :
      projectiveAffineChart a = projectiveAffineChart b := by
    by_cases hb1 : b.1 1 = 0
    · have ha1 : a.1 1 = 0 := by
        simpa [Pi.smul_apply, hb1] using congrArg (fun z : Fin 2 → ℂ ↦ z 1) h
      simp [projectiveAffineChart, ha1, hb1]
    · have ha1 : a.1 1 ≠ 0 := by
        have ha1mul : a.1 1 = t * b.1 1 := by
          simpa [Pi.smul_apply] using congrArg (fun z : Fin 2 → ℂ ↦ z 1) h
        rw [ha1mul]
        exact mul_ne_zero ht hb1
      have hratio :
          ((a.1 1)⁻¹ * a.1 0 : ℂ) = ((b.1 1)⁻¹ * b.1 0 : ℂ) := by
        rw [h]
        simp [smul_eq_mul, ht, hb1, mul_assoc]
      simp [projectiveAffineChart, ha1, hb1, hratio]
  exact hEq

/-- Helper for Example 9.4.8: the sphere-valued affine chart is unchanged by complex rescaling of
a nonzero representative. -/
private theorem projectiveSphereChart_scaleInvariant
    (a b : { w : Fin 2 → ℂ // w ≠ 0 }) (t : ℂ) (h : a = t • (b : Fin 2 → ℂ)) :
    projectiveSphereChart a = projectiveSphereChart b := by
  -- The sphere-valued chart only depends on the affine ratio, so it inherits the same
  -- scale-invariance as `projectiveAffineChart`.
  rw [projectiveSphereChart, projectiveSphereChart]
  rw [projectiveAffineChart_scaleInvariant a b t h]

/-- Helper for Example 9.4.8: the descended sphere-valued chart agrees with the affine-line chart
on `ℂP¹`. -/
private theorem projectiveSphereChart_descends_toAffineChart
    (x : ComplexProjectiveLine) :
    Projectivization.lift projectiveSphereChart projectiveSphereChart_scaleInvariant x =
      onePointComplexStereographicHomeomorphSphereTwo
        (complexProjectiveLineEquivOnePointComplex.symm x) := by
  -- Check the equality on a nonzero representative, where the normalized representative gives the
  -- same projective point and the same affine chart.
  induction x using Projectivization.ind with
  | h v hv =>
      calc
        Projectivization.lift projectiveSphereChart projectiveSphereChart_scaleInvariant
            (Projectivization.mk ℂ v hv)
            = projectiveSphereChart ⟨v, hv⟩ := by
                simp [Projectivization.lift_mk]
        _ = onePointComplexStereographicHomeomorphSphereTwo
              (projectiveAffineChart ⟨v, hv⟩) := by
                rfl
        _ = onePointComplexStereographicHomeomorphSphereTwo
              (quotientAffineChartValue (normalizeNonzeroComplexVector ⟨v, hv⟩)) := by
                rw [quotientAffineChartValue_normalizeNonzeroComplexVector]
        _ = onePointComplexStereographicHomeomorphSphereTwo
              (complexProjectiveLineEquivOnePointComplex.symm
                (complexSphereThreeToProjectivization
                  (normalizeNonzeroComplexVector ⟨v, hv⟩))) := by
                    rw [quotientAffineChartFormula]
        _ = onePointComplexStereographicHomeomorphSphereTwo
              (complexProjectiveLineEquivOnePointComplex.symm
                (Projectivization.mk ℂ v hv)) := by
                    rw [complexSphereThreeToProjectivization_normalizeNonzeroComplexVector]

/-- Helper for Example 9.4.8: the sphere-valued projective chart descended to `ℂP¹`. -/
private def descendedProjectiveSphereChart : ComplexProjectiveLine → SphereTwo :=
  Projectivization.lift projectiveSphereChart fun a b t h ↦ by
    calc
      projectiveSphereChart a
          = onePointComplexStereographicHomeomorphSphereTwo (projectiveAffineChart a) := by
              rfl
      _ = onePointComplexStereographicHomeomorphSphereTwo (projectiveAffineChart b) := by
            rw [projectiveAffineChart_scaleInvariant a b t h]
      _ = projectiveSphereChart b := by
            rfl

/-- Helper for Example 9.4.8: the affine chart on `ℂP¹` composed with the stereographic
identification to `S²`. -/
private def affineSphereComparison (x : ComplexProjectiveLine) : SphereTwo :=
  (onePointComplexStereographicHomeomorphSphereTwo
    (complexProjectiveLineEquivOnePointComplex.symm x) : SphereTwo)

/-- Helper for Example 9.4.8: the affine-chart equivalence `ℂP¹ ≃ OnePoint ℂ` remains continuous
once the Hopf-quotient comparison is descended through the projectivization quotient. -/
private theorem complexProjectiveLineEquivOnePointComplex_symm_continuous :
    Continuous complexProjectiveLineEquivOnePointComplex.symm := by
  -- Route correction: descend the sphere-valued affine chart directly from nonzero vectors via
  -- `Projectivization.lift`, then recover the `OnePoint ℂ` chart by composing with the inverse
  -- stereographic homeomorphism.
  have hRel :
      ∀ a b : { w : Fin 2 → ℂ // w ≠ 0 },
        (projectivizationSetoid ℂ (Fin 2 → ℂ)).r a b →
          projectiveSphereChart a = projectiveSphereChart b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨u, rfl⟩
    let scaled : { w : Fin 2 → ℂ // w ≠ 0 } :=
      ⟨u • b, by
        intro hub
        apply ha
        simpa using hub⟩
    calc
      projectiveSphereChart scaled
          = onePointComplexStereographicHomeomorphSphereTwo
              (projectiveAffineChart scaled) := by
                    rfl
      _ = onePointComplexStereographicHomeomorphSphereTwo
            (projectiveAffineChart ⟨b, hb⟩) := by
              rw [projectiveAffineChart_scaleInvariant (a := scaled) (b := ⟨b, hb⟩)
                (t := (u : ℂ)) rfl]
      _ = projectiveSphereChart ⟨b, hb⟩ := by
            rfl
  have hDesc : Continuous descendedProjectiveSphereChart := by
    simpa [Projectivization.lift] using projectiveSphereChart_continuous.quotient_lift hRel
  have hDescEq : descendedProjectiveSphereChart = affineSphereComparison := by
    funext x
    exact projectiveSphereChart_descends_toAffineChart x
  have hComp : Continuous affineSphereComparison := by
    rw [← hDescEq]
    exact hDesc
  have hRecover :
      complexProjectiveLineEquivOnePointComplex.symm =
        onePointComplexStereographicHomeomorphSphereTwo.symm ∘ affineSphereComparison := by
    funext x
    simp [affineSphereComparison, Function.comp]
  -- Compose with the inverse stereographic homeomorphism to recover the affine chart itself.
  rw [hRecover]
  exact onePointComplexStereographicHomeomorphSphereTwo.continuous_symm.comp hComp

/-- Helper for Example 9.4.8: the quotient model `ℂP¹` is canonically homeomorphic to
`OnePoint ℂ` once the affine chart is known to agree with the Hopf quotient. -/
private noncomputable def complexProjectiveLineHomeomorphOnePointComplex :
    ComplexProjectiveLine ≃ₜ OnePoint ℂ :=
  Continuous.homeoOfEquivCompactToT2
    (f := complexProjectiveLineEquivOnePointComplex.symm)
    complexProjectiveLineEquivOnePointComplex_symm_continuous

/-- Helper for Example 9.4.8: the canonical `ComplexProjectiveLine ≃ₜ OnePoint ℂ` sends a
projective point to its affine-chart value. -/
private theorem complexProjectiveLineHomeomorphOnePointComplex_apply
    (x : ComplexProjectiveLine) :
    complexProjectiveLineHomeomorphOnePointComplex x =
      complexProjectiveLineEquivOnePointComplex.symm x := by
  -- The homeomorphism was packaged from the existing affine-chart equivalence without changing its
  -- underlying function.
  rfl

/-- Example 9.4.8 (1): the Hopf map `η : S^3 → S^2` is obtained from the quotient
`S^3 ⊂ ℂ² → ℂP¹ ≃ S²`. -/
theorem hopfMap_isHopfQuotient :
    IsHopfQuotientMap hopfMap := by
  -- Package the source and target identifications, then apply the affine-chart comparison pointwise.
  refine ⟨sphereThreeHomeomorphComplexSphereThree,
    complexProjectiveLineHomeomorphOnePointComplex.trans
      onePointComplexStereographicHomeomorphSphereTwo, ?_⟩
  funext x
  calc
    hopfMap x = hopfMap (sphereThreeHomeomorphComplexSphereThree.symm
        (sphereThreeHomeomorphComplexSphereThree x)) := by
          rw [sphereThreeHomeomorphComplexSphereThree.symm_apply_apply]
    _ = onePointComplexStereographicHomeomorphSphereTwo
          (complexProjectiveLineEquivOnePointComplex.symm
            (complexSphereThreeToProjectivization (sphereThreeHomeomorphComplexSphereThree x))) := by
          exact (hopfQuotientAffineChartComparison (sphereThreeHomeomorphComplexSphereThree x)).symm
    _ = (complexProjectiveLineHomeomorphOnePointComplex.trans
          onePointComplexStereographicHomeomorphSphereTwo)
          (complexSphereThreeToProjectivization (sphereThreeHomeomorphComplexSphereThree x)) := by
          simp [Homeomorph.trans_apply, complexProjectiveLineHomeomorphOnePointComplex_apply]

/-- Helper for Example 9.4.8: local trivializations transport across source and target
homeomorphisms. -/
theorem isFiberBundleMap_congrHomeomorph
    {E E' B B' F : Type*}
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace B']
    [TopologicalSpace F] {p : E → B} (hE : E' ≃ₜ E) (hB : B ≃ₜ B')
    (hp : IsFiberBundleMap F p) :
    IsFiberBundleMap F (hB ∘ p ∘ hE) := by
  intro b'
  -- Transport a trivialization around `hB.symm b'` to one around `b'`.
  obtain ⟨e, hb⟩ := hp (hB.symm b')
  refine ⟨(e.compHomeomorph hE).homeomorphComp hB, ?_⟩
  simpa [Function.comp_def]
    using hb

/-- Helper for Example 9.4.8: the quotient map written in the affine `OnePoint ℂ` chart. -/
private def qOnePoint : ComplexSphereThree → OnePoint ℂ :=
  complexProjectiveLineHomeomorphOnePointComplex ∘ complexSphereThreeToProjectivization

/-- Helper for Example 9.4.8: `qOnePoint` is the previously computed affine quotient chart. -/
private theorem qOnePoint_eq_quotientAffineChartValue (z : ComplexSphereThree) :
    qOnePoint z = quotientAffineChartValue z := by
  -- The chosen homeomorphism `ComplexProjectiveLine ≃ₜ OnePoint ℂ` has the affine-chart function
  -- as its underlying map, so the quotient formula is unchanged.
  simp [qOnePoint, complexProjectiveLineHomeomorphOnePointComplex_apply,
    quotientAffineChartFormula]

/-- Helper for Example 9.4.8: the affine quotient chart `qOnePoint` is continuous. -/
private theorem qOnePoint_continuous :
    Continuous qOnePoint := by
  -- Both pieces of the affine quotient chart were already constructed as continuous maps.
  exact complexProjectiveLineHomeomorphOnePointComplex.continuous.comp
    complexSphereThreeToProjectivization_continuous

/-- Helper for Example 9.4.8: the finite affine base set in the `OnePoint ℂ` chart. -/
private def onePointHopfFiniteBaseSet : Set (OnePoint ℂ) :=
  ({(OnePoint.infty : OnePoint ℂ)} : Set (OnePoint ℂ))ᶜ

/-- Helper for Example 9.4.8: the finite affine base set is open. -/
private theorem onePointHopfFiniteBaseSet_open :
    IsOpen onePointHopfFiniteBaseSet := by
  -- The complement of the closed singleton `{∞}` is open.
  simpa [onePointHopfFiniteBaseSet] using
    (isClosed_singleton : IsClosed ({(OnePoint.infty : OnePoint ℂ)} : Set (OnePoint ℂ))).isOpen_compl

/-- Helper for Example 9.4.8: every complex number lies in the preimage of the finite affine base
set under the inclusion `ℂ → OnePoint ℂ`. -/
private theorem onePointHopfFiniteBaseSet_preimage_coe :
    ((↑) : ℂ → OnePoint ℂ) ⁻¹' onePointHopfFiniteBaseSet = Set.univ := by
  -- Finite complex points are never equal to `∞`.
  ext z
  simp [onePointHopfFiniteBaseSet]

/-- Helper for Example 9.4.8: the finite affine base chart identifies `({∞} : Set (OnePoint ℂ))ᶜ`
with `ℂ`. -/
private noncomputable def onePointHopfFiniteBaseHomeomorph :
    ℂ ≃ₜ onePointHopfFiniteBaseSet :=
  (Homeomorph.Set.univ ℂ).symm.trans
    ((Homeomorph.setCongr onePointHopfFiniteBaseSet_preimage_coe.symm).trans
      (((OnePoint.isOpenEmbedding_coe :
            Topology.IsOpenEmbedding ((↑) : ℂ → OnePoint ℂ)).isEmbedding).homeomorphOfSubsetRange
        <| by
          simpa [onePointHopfFiniteBaseSet] using
            (show onePointHopfFiniteBaseSet ⊆ Set.range ((↑) : ℂ → OnePoint ℂ) by
              rw [onePointHopfFiniteBaseSet, OnePoint.compl_infty])))

/-- Helper for Example 9.4.8: the finite-base homeomorphism sends `z : ℂ` to the corresponding
finite point of `OnePoint ℂ`. -/
private theorem onePointHopfFiniteBaseHomeomorph_apply (z : ℂ) :
    onePointHopfFiniteBaseHomeomorph z =
      ⟨(z : OnePoint ℂ), by simpa [onePointHopfFiniteBaseSet] using OnePoint.coe_ne_infty z⟩ := by
  -- Both constituent homeomorphisms are definitionally the inclusion into the open finite chart.
  -- Taking underlying values reduces the composite homeomorphism to the canonical inclusion.
  ext
  change
    ↑((((OnePoint.isOpenEmbedding_coe :
          Topology.IsOpenEmbedding ((↑) : ℂ → OnePoint ℂ)).isEmbedding).homeomorphOfSubsetRange
        (by
          simpa [onePointHopfFiniteBaseSet] using
            (show onePointHopfFiniteBaseSet ⊆ Set.range ((↑) : ℂ → OnePoint ℂ) by
              rw [onePointHopfFiniteBaseSet, OnePoint.compl_infty])))
        ⟨z, by simpa [onePointHopfFiniteBaseSet] using OnePoint.coe_ne_infty z⟩) = (z : OnePoint ℂ)
  simpa [Topology.IsEmbedding.homeomorphOfSubsetRange_apply_coe]

/-- Helper for Example 9.4.8: applying the inverse finite-base homeomorphism and coercing back
recovers the original finite point. -/
private theorem onePointHopfFiniteBaseHomeomorph_symm_coe
    (x : onePointHopfFiniteBaseSet) :
    ((onePointHopfFiniteBaseHomeomorph.symm x : ℂ) : OnePoint ℂ) = x.1 := by
  -- This is just the `apply_symm_apply` identity, viewed back in `OnePoint ℂ`.
  -- Rewrite the forward computation at the inverse point and then forget the subtype proof.
  have h :=
    onePointHopfFiniteBaseHomeomorph_apply (onePointHopfFiniteBaseHomeomorph.symm x)
  rw [onePointHopfFiniteBaseHomeomorph.apply_symm_apply] at h
  exact congrArg Subtype.val h.symm

/-- Helper for Example 9.4.8: normalize a nonzero complex number to its phase on `Circle`. -/
private def circlePhase (w : {z : ℂ // z ≠ 0}) : Circle :=
  ⟨w.1 / ‖w.1‖, by
    -- The quotient by the norm has norm `1`.
    simp [Submonoid.unitSphere, norm_div, Complex.norm_real, norm_ne_zero_iff.mpr w.2]
  ⟩

/-- Helper for Example 9.4.8: the coercion of `circlePhase` is the expected normalized complex
number. -/
private theorem circlePhase_coe (w : {z : ℂ // z ≠ 0}) :
    ((circlePhase w : Circle) : ℂ) = w.1 / ‖w.1‖ := by
  -- The definition stores exactly this normalized complex number.
  rfl

/-- Helper for Example 9.4.8: the phase map on nonzero complex numbers is continuous. -/
private theorem circlePhase_continuous :
    Continuous circlePhase := by
  -- The normalized complex representative varies continuously on the nonzero subtype.
  refine Continuous.subtype_mk ?_ ?_
  have hnorm : Continuous fun w : {z : ℂ // z ≠ 0} ↦ ‖w.1‖ :=
    continuous_norm.comp continuous_subtype_val
  have hdenom : Continuous fun w : {z : ℂ // z ≠ 0} ↦ ((‖w.1‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hnorm
  have hinv : Continuous fun w : {z : ℂ // z ≠ 0} ↦ (((‖w.1‖ : ℝ) : ℂ)⁻¹) :=
    Continuous.inv₀ hdenom fun w ↦ by
      exact_mod_cast (norm_ne_zero_iff.mpr w.2)
  simpa [circlePhase, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    continuous_subtype_val.mul hinv

/-- Helper for Example 9.4.8: the phase of a positive real multiple of a circle element is the
original circle element. -/
private theorem circlePhaseOfPosRealMul (u : Circle) {r : ℝ} (hr : 0 < r) :
    circlePhase ⟨((r : ℂ) * u : ℂ), by
      exact mul_ne_zero (by exact_mod_cast hr.ne') (Circle.coe_ne_zero u)⟩ = u := by
  -- The positive real scalar contributes only a positive norm, so normalization cancels it.
  apply Circle.ext
  have hnorm : ‖((r : ℂ) * (u : ℂ))‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]
  rw [circlePhase_coe]
  calc
    ((r : ℂ) * (u : ℂ)) / ‖((r : ℂ) * (u : ℂ))‖ = ((r : ℂ) * (u : ℂ)) / (r : ℂ) := by
      rw [hnorm]
    _ = (u : ℂ) := by
      field_simp [hr.ne']

/-- Helper for Example 9.4.8: the finite affine chart is exactly the locus where the second
complex coordinate is nonzero. -/
private theorem mem_onePointHopfFiniteBaseSet_iff (z : ComplexSphereThree) :
    qOnePoint z ∈ onePointHopfFiniteBaseSet ↔ z.1 1 ≠ 0 := by
  -- Unfold the affine quotient formula once, then the statement is just the `if`-split on
  -- whether the second coordinate vanishes.
  rw [qOnePoint_eq_quotientAffineChartValue, onePointHopfFiniteBaseSet, quotientAffineChartValue]
  by_cases hz1 : z.1 1 = 0
  · simp [hz1]
  · simp [hz1]

/-- Helper for Example 9.4.8: the finite affine generator `[z : 1]` in `ℂ²`. -/
private def onePointHopfFiniteGenerator (z : ℂ) : Fin 2 → ℂ :=
  complexFinTwoArrowSymm (z, 1)

/-- Helper for Example 9.4.8: the finite affine generator is nonzero. -/
private theorem onePointHopfFiniteGenerator_nonzero (z : ℂ) :
    onePointHopfFiniteGenerator z ≠ 0 := by
  -- The second coordinate of `[z : 1]` is `1`, so the vector cannot vanish.
  intro hz
  have hpair : ((z, (1 : ℂ)) : ℂ × ℂ) = 0 := by
    apply complexFinTwoArrowSymm_injective
    simpa [onePointHopfFiniteGenerator] using hz
  simpa using congrArg Prod.snd hpair

/-- Helper for Example 9.4.8: the circle-scaled finite affine generator is still nonzero. -/
private theorem onePointHopfFiniteVector_nonzero (z : ℂ) (u : Circle) :
    (u : ℂ) • onePointHopfFiniteGenerator z ≠ 0 :=
  smul_ne_zero (Circle.coe_ne_zero u) (onePointHopfFiniteGenerator_nonzero z)

/-- Helper for Example 9.4.8: the nonzero vector used to build the finite Hopf chart section. -/
private def onePointHopfFiniteVector (z : ℂ) (u : Circle) :
    {w : Fin 2 → ℂ // w ≠ 0} :=
  ⟨(u : ℂ) • onePointHopfFiniteGenerator z, onePointHopfFiniteVector_nonzero z u⟩

/-- Helper for Example 9.4.8: the normalized finite affine Hopf section. -/
private def onePointHopfFiniteSection (z : ℂ) (u : Circle) : ComplexSphereThree :=
  normalizeNonzeroComplexVector (onePointHopfFiniteVector z u)

/-- Helper for Example 9.4.8: the finite affine Hopf section projects to the expected base
point `z`. -/
private theorem qOnePoint_onePointHopfFiniteSection (z : ℂ) (u : Circle) :
    qOnePoint (onePointHopfFiniteSection z u) = (z : OnePoint ℂ) := by
  -- Normalization preserves projective class, and scaling by the circle coordinate does not
  -- change the affine ratio `[z : 1]`.
  calc
    qOnePoint (onePointHopfFiniteSection z u)
        = quotientAffineChartValue (onePointHopfFiniteSection z u) := by
            exact qOnePoint_eq_quotientAffineChartValue _
    _ = projectiveAffineChart (onePointHopfFiniteVector z u) := by
          exact quotientAffineChartValue_normalizeNonzeroComplexVector _
    _ = projectiveAffineChart
          ⟨onePointHopfFiniteGenerator z, onePointHopfFiniteGenerator_nonzero z⟩ := by
            rw [projectiveAffineChart_scaleInvariant
              (a := onePointHopfFiniteVector z u)
              (b := ⟨onePointHopfFiniteGenerator z, onePointHopfFiniteGenerator_nonzero z⟩)
              (t := (u : ℂ)) rfl]
    _ = (z : OnePoint ℂ) := by
          simp [projectiveAffineChart, onePointHopfFiniteGenerator]

/-- Helper for Example 9.4.8: the explicit finite Hopf section depends continuously on the base
coordinate and fiber phase. -/
private theorem onePointHopfFiniteSection_continuous :
    Continuous fun p : ℂ × Circle ↦ onePointHopfFiniteSection p.1 p.2 := by
  -- The nonzero vector `(u • [z : 1])` varies continuously, and normalization is already known to
  -- be continuous on the nonzero-vector subtype.
  have hGenerator : Continuous fun p : ℂ × Circle ↦ onePointHopfFiniteGenerator p.1 := by
    simpa [onePointHopfFiniteGenerator] using
      complexFinTwoArrowSymm.continuous_of_finiteDimensional.comp
        (continuous_fst.prodMk continuous_const)
  have hScalar : Continuous fun p : ℂ × Circle ↦ ((p.2 : Circle) : ℂ) :=
    continuous_subtype_val.comp continuous_snd
  have hVector :
      Continuous fun p : ℂ × Circle ↦
        (((p.2 : Circle) : ℂ) • onePointHopfFiniteGenerator p.1 : Fin 2 → ℂ) := by
    simpa using hScalar.smul hGenerator
  have hNonzero : Continuous fun p : ℂ × Circle ↦ onePointHopfFiniteVector p.1 p.2 := by
    exact Continuous.subtype_mk hVector fun p ↦ onePointHopfFiniteVector_nonzero p.1 p.2
  exact normalizeNonzeroComplexVector_continuous.comp hNonzero

/-- Helper for Example 9.4.8: the second coordinate of the finite Hopf section never vanishes. -/
private theorem onePointHopfFiniteSection_second_ne_zero (z : ℂ) (u : Circle) :
    (onePointHopfFiniteSection z u).1 1 ≠ 0 := by
  -- The second coordinate is the positive normalization scalar times the circle element `u`.
  have hnorm_ne : ‖(u : ℂ) • onePointHopfFiniteGenerator z‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (onePointHopfFiniteVector_nonzero z u)
  simp [onePointHopfFiniteSection, normalizeNonzeroComplexVector, onePointHopfFiniteVector,
    onePointHopfFiniteGenerator, smul_eq_mul, hnorm_ne, Circle.coe_ne_zero u]

/-- Helper for Example 9.4.8: the phase extracted from the finite Hopf section recovers the input
circle coordinate. -/
private theorem onePointHopfFiniteSection_phase (z : ℂ) (u : Circle) :
    circlePhase ⟨(onePointHopfFiniteSection z u).1 1, onePointHopfFiniteSection_second_ne_zero z u⟩
      = u := by
  -- The second coordinate is a positive real multiple of `u`, so `circlePhase` removes the
  -- normalization factor and leaves the original phase.
  have hnorm_pos : 0 < ‖(u : ℂ) • onePointHopfFiniteGenerator z‖ := by
    exact norm_pos_iff.mpr (onePointHopfFiniteVector_nonzero z u)
  have hcoord :
      (onePointHopfFiniteSection z u).1 1 =
        ((‖(u : ℂ) • onePointHopfFiniteGenerator z‖)⁻¹ : ℂ) * (u : ℂ) := by
    simp [onePointHopfFiniteSection, normalizeNonzeroComplexVector, onePointHopfFiniteVector,
      onePointHopfFiniteGenerator, smul_eq_mul]
  -- Compare coercions in `ℂ`, where the subtype proof on `circlePhase` is definitionally hidden.
  apply Circle.ext
  simpa [circlePhase_coe, hcoord] using
    congrArg (fun v : Circle => (v : ℂ))
      (circlePhaseOfPosRealMul u (r := ‖(u : ℂ) • onePointHopfFiniteGenerator z‖⁻¹)
        (inv_pos.mpr hnorm_pos))

/-- Helper for Example 9.4.8: on the finite affine chart, the base coordinate together with the
phase of the second coordinate reconstructs the original sphere point. -/
private theorem onePointHopfFiniteSection_reconstruct
    (z : ComplexSphereThree) (hz : qOnePoint z ∈ onePointHopfFiniteBaseSet) :
    onePointHopfFiniteSection
        (onePointHopfFiniteBaseHomeomorph.symm ⟨qOnePoint z, hz⟩)
        (circlePhase ⟨z.1 1, (mem_onePointHopfFiniteBaseSet_iff z).mp hz⟩) = z := by
  -- Route correction: rather than packaging the chart first, identify the explicit scaled vector
  -- used by the section and then appeal to normalization on the unit sphere.
  have hz1 : z.1 1 ≠ 0 := (mem_onePointHopfFiniteBaseSet_iff z).mp hz
  let w : ℂ := onePointHopfFiniteBaseHomeomorph.symm ⟨qOnePoint z, hz⟩
  have hw :
      w = ((z.1 1)⁻¹ * z.1 0 : ℂ) := by
    apply (OnePoint.coe_eq_coe).mp
    calc
      ((w : ℂ) : OnePoint ℂ) = qOnePoint z := by
        simpa [w] using onePointHopfFiniteBaseHomeomorph_symm_coe ⟨qOnePoint z, hz⟩
      _ = ((z.1 1)⁻¹ * z.1 0 : ℂ) := by
        rw [qOnePoint_eq_quotientAffineChartValue, quotientAffineChartValue]
        simp [hz1]
  let u : Circle := circlePhase ⟨z.1 1, hz1⟩
  have hscaled :
      ((u : ℂ) • onePointHopfFiniteGenerator w : Fin 2 → ℂ) =
        ((‖z.1 1‖)⁻¹ : ℝ) • z.1 := by
    -- The section vector is exactly the positive real multiple `(‖z₁‖⁻¹) • z`.
    have hnorm_ne : ‖z.1 1‖ ≠ 0 := norm_ne_zero_iff.mpr hz1
    ext i
    fin_cases i
    · calc
        ((u : ℂ) • onePointHopfFiniteGenerator w) 0
            = (u : ℂ) * w := by simp [onePointHopfFiniteGenerator, smul_eq_mul]
        _ = (z.1 1 / ‖z.1 1‖) * (((z.1 1)⁻¹ * z.1 0 : ℂ)) := by
              rw [circlePhase_coe, hw]
        _ = (((z.1 1) * (z.1 1)⁻¹) * (((‖z.1 1‖ : ℝ) : ℂ)⁻¹)) * z.1 0 := by
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ = (((‖z.1 1‖ : ℝ) : ℂ)⁻¹) * z.1 0 := by
              simp [hz1]
        _ = (((‖z.1 1‖)⁻¹ : ℝ) : ℂ) * z.1 0 := by
              simp
        _ = (((‖z.1 1‖)⁻¹ : ℝ) • z.1) 0 := by
              simp [smul_eq_mul]
    · calc
        ((u : ℂ) • onePointHopfFiniteGenerator w) 1
            = (u : ℂ) := by simp [onePointHopfFiniteGenerator, smul_eq_mul]
        _ = (z.1 1 / ‖z.1 1‖ : ℂ) := by
              rw [circlePhase_coe]
        _ = (((‖z.1 1‖ : ℝ) : ℂ)⁻¹) * z.1 1 := by
              simp [div_eq_mul_inv, mul_comm]
        _ = (((‖z.1 1‖)⁻¹ : ℝ) : ℂ) * z.1 1 := by
              simp
        _ = (((‖z.1 1‖)⁻¹ : ℝ) • z.1) 1 := by
              simp [smul_eq_mul]
  -- Normalizing a positive real multiple of a unit vector returns the original sphere point.
  apply Subtype.ext
  simpa [onePointHopfFiniteSection, onePointHopfFiniteVector, normalizeNonzeroComplexVector, w, u,
    hscaled] using
    (invNorm_smul_eq_of_mem_unitSphere (E := Fin 2 → ℂ) (x := z.1) z.2
      (a := ‖z.1 1‖⁻¹) (inv_pos.mpr (norm_pos_iff.mpr hz1)))

/-- Helper for Example 9.4.8: the finite Hopf chart is a homeomorphism on the restricted source
`{z : ComplexSphereThree // qOnePoint z ∈ onePointHopfFiniteBaseSet}`. -/
private noncomputable def onePointHopfFiniteSourceHomeomorph :
    {z : ComplexSphereThree // qOnePoint z ∈ onePointHopfFiniteBaseSet} ≃ₜ
      onePointHopfFiniteBaseSet × Circle := by
  -- Route correction: work on the restricted source where the finite Hopf chart is literally a
  -- homeomorphism, so the inverse continuity is an ordinary composition with
  -- `onePointHopfFiniteSection_continuous`.
  let toFun :
      {z : ComplexSphereThree // qOnePoint z ∈ onePointHopfFiniteBaseSet} →
        onePointHopfFiniteBaseSet × Circle :=
    fun z ↦
      (⟨qOnePoint z.1, z.2⟩,
        circlePhase ⟨z.1.1 1, (mem_onePointHopfFiniteBaseSet_iff z.1).mp z.2⟩)
  let invFun :
      onePointHopfFiniteBaseSet × Circle →
        {z : ComplexSphereThree // qOnePoint z ∈ onePointHopfFiniteBaseSet} :=
    fun x ↦
    ⟨onePointHopfFiniteSection (onePointHopfFiniteBaseHomeomorph.symm x.1) x.2, by
      -- The reconstructed finite-section point lands back over the chosen finite base point.
      have hq :
          qOnePoint (onePointHopfFiniteSection (onePointHopfFiniteBaseHomeomorph.symm x.1) x.2) =
            ((onePointHopfFiniteBaseHomeomorph.symm x.1 : ℂ) : OnePoint ℂ) := by
        simpa using
          qOnePoint_onePointHopfFiniteSection (onePointHopfFiniteBaseHomeomorph.symm x.1) x.2
      exact (hq.trans (onePointHopfFiniteBaseHomeomorph_symm_coe x.1)).symm ▸ x.1.2⟩
  have htoFun :
      Continuous toFun := by
    -- The forward chart is the restricted quotient coordinate paired with the phase of `z₁`.
    have hbase :
        Continuous fun z : {z : ComplexSphereThree // qOnePoint z ∈ onePointHopfFiniteBaseSet} ↦
          (⟨qOnePoint z.1, z.2⟩ : onePointHopfFiniteBaseSet) := by
      exact Continuous.subtype_mk (qOnePoint_continuous.comp continuous_subtype_val) fun z ↦ z.2
    have hcoord :
        Continuous fun z : {z : ComplexSphereThree // qOnePoint z ∈ onePointHopfFiniteBaseSet} ↦
          z.1.1 1 := by
      exact continuous_apply 1 |>.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hphaseArg :
        Continuous fun z : {z : ComplexSphereThree // qOnePoint z ∈ onePointHopfFiniteBaseSet} ↦
          (⟨z.1.1 1, (mem_onePointHopfFiniteBaseSet_iff z.1).mp z.2⟩ : {w : ℂ // w ≠ 0}) := by
      exact Continuous.subtype_mk hcoord fun z ↦ (mem_onePointHopfFiniteBaseSet_iff z.1).mp z.2
    exact hbase.prodMk (circlePhase_continuous.comp hphaseArg)
  have hinvFun :
      Continuous invFun := by
    -- The inverse chart is the explicit finite section composed with the base homeomorphism.
    have hcoord :
        Continuous fun x : onePointHopfFiniteBaseSet × Circle ↦
          (onePointHopfFiniteBaseHomeomorph.symm x.1, x.2) := by
      exact (onePointHopfFiniteBaseHomeomorph.symm.continuous.comp continuous_fst).prodMk
        continuous_snd
    exact Continuous.subtype_mk (onePointHopfFiniteSection_continuous.comp hcoord) fun x ↦
      (invFun x).2
  refine
    { toEquiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := ?_
          right_inv := ?_ }
      continuous_toFun := htoFun
      continuous_invFun := hinvFun }
  · intro z
    -- The finite chart reconstruction theorem gives the inverse on the restricted source.
    apply Subtype.ext
    simpa [toFun, invFun] using onePointHopfFiniteSection_reconstruct z.1 z.2
  · intro x
    -- The section was designed so that it returns exactly the chosen base point and phase.
    rcases x with ⟨b, u⟩
    apply Prod.ext
    · apply Subtype.ext
      simpa [toFun, invFun] using
        (qOnePoint_onePointHopfFiniteSection (onePointHopfFiniteBaseHomeomorph.symm b) u).trans
          (onePointHopfFiniteBaseHomeomorph_symm_coe b)
    · simpa [toFun, invFun] using
        onePointHopfFiniteSection_phase (onePointHopfFiniteBaseHomeomorph.symm b) u

/-- Helper for Example 9.4.8: the restricted finite source carries a trivialization over the whole
subtype base `onePointHopfFiniteBaseSet`. -/
private noncomputable def onePointHopfFiniteRestrictedTrivialization :
    Bundle.Trivialization Circle
      (fun z : {z : ComplexSphereThree // qOnePoint z ∈ onePointHopfFiniteBaseSet} ↦
        (⟨qOnePoint z.1, z.2⟩ : onePointHopfFiniteBaseSet)) where
  -- The restricted-source homeomorphism is already a global trivialization over the subtype base.
  toOpenPartialHomeomorph := onePointHopfFiniteSourceHomeomorph.toOpenPartialHomeomorph
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := by
    ext z
    simp
  target_eq := by
    ext x
    simp
  proj_toFun z hz := by
    change (onePointHopfFiniteSourceHomeomorph z).1 = ⟨qOnePoint z.1, z.2⟩
    rfl

/-- Helper for Example 9.4.8: the finite affine Hopf chart packages into an ambient
`Bundle.Trivialization Circle qOnePoint`. -/
private noncomputable def onePointHopfFiniteTrivialization :
    Bundle.Trivialization Circle qOnePoint := by
  -- Extend first the subtype-valued base projection, then the restricted total space.
  let eBase :
      Bundle.Trivialization Circle
        (fun z : qOnePoint ⁻¹' onePointHopfFiniteBaseSet ↦ qOnePoint z.1) :=
    Bundle.Trivialization.codExtend (F := Circle)
      (s := onePointHopfFiniteBaseSet) onePointHopfFiniteBaseSet_open
      ⟨((0 : ℂ) : OnePoint ℂ), by simp [onePointHopfFiniteBaseSet]⟩
      onePointHopfFiniteRestrictedTrivialization
  have hsource : IsOpen (qOnePoint ⁻¹' onePointHopfFiniteBaseSet) :=
    onePointHopfFiniteBaseSet_open.preimage qOnePoint_continuous
  -- `domExtend` replaces the restricted source subtype by the ambient sphere.
  exact Bundle.Trivialization.domExtend (F := Circle) (proj := qOnePoint) hsource eBase

-- Local instance justification (decidable predicates): the finite-chart helper maps below use
-- explicit fallback branches outside the source/target sets, so Lean needs classical decidability
-- for membership in `onePointHopfFiniteBaseSet`.
private local instance : DecidablePred fun x : OnePoint ℂ => x ∈ onePointHopfFiniteBaseSet :=
  Classical.decPred _

/-- Helper for Example 9.4.8: the finite-chart fiber coordinate, extended by the constant `1`
outside the affine chart. -/
private def onePointHopfFiniteFiberCoord (z : ComplexSphereThree) : Circle :=
  if hz : qOnePoint z ∈ onePointHopfFiniteBaseSet then
    circlePhase ⟨z.1 1, (mem_onePointHopfFiniteBaseSet_iff z).mp hz⟩
  else
    1

/-- Helper for Example 9.4.8: on the finite affine chart, `onePointHopfFiniteFiberCoord` is the
phase of the second coordinate. -/
private theorem onePointHopfFiniteFiberCoord_eq_phase
    (z : ComplexSphereThree) (hz : qOnePoint z ∈ onePointHopfFiniteBaseSet) :
    onePointHopfFiniteFiberCoord z =
      circlePhase ⟨z.1 1, (mem_onePointHopfFiniteBaseSet_iff z).mp hz⟩ := by
  -- On the finite chart the defining `if` reduces to the phase formula.
  rw [onePointHopfFiniteFiberCoord]
  simp [hz]

/-- Helper for Example 9.4.8: the finite-chart fiber coordinate is continuous on the finite locus. -/
private theorem onePointHopfFiniteFiberCoord_continuousOn :
    ContinuousOn onePointHopfFiniteFiberCoord (qOnePoint ⁻¹' onePointHopfFiniteBaseSet) := by
  -- Restricting to the finite locus removes the default branch and leaves the continuous
  -- normalized phase map on the nonzero second coordinate.
  rw [continuousOn_iff_continuous_restrict]
  have hcoord :
      Continuous fun z : {z : ComplexSphereThree // z ∈ qOnePoint ⁻¹' onePointHopfFiniteBaseSet} ↦
        z.1.1 1 := by
    exact continuous_apply 1 |>.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hsubtype :
      Continuous fun z : {z : ComplexSphereThree // z ∈ qOnePoint ⁻¹' onePointHopfFiniteBaseSet} ↦
        (⟨z.1.1 1, (mem_onePointHopfFiniteBaseSet_iff z.1).mp z.2⟩ : {w : ℂ // w ≠ 0}) := by
    exact Continuous.subtype_mk hcoord fun z ↦ (mem_onePointHopfFiniteBaseSet_iff z.1).mp z.2
  -- After restricting the domain, the `if` defining the fiber coordinate is always in the
  -- finite-chart branch.
  have hrestrict :
      (qOnePoint ⁻¹' onePointHopfFiniteBaseSet).restrict onePointHopfFiniteFiberCoord =
        fun z : {z : ComplexSphereThree // z ∈ qOnePoint ⁻¹' onePointHopfFiniteBaseSet} ↦
          circlePhase ⟨z.1.1 1, (mem_onePointHopfFiniteBaseSet_iff z.1).mp z.2⟩ := by
    funext z
    exact onePointHopfFiniteFiberCoord_eq_phase z.1 z.2
  rw [hrestrict]
  exact circlePhase_continuous.comp hsubtype

/-- Helper for Example 9.4.8: the inverse finite-chart map, extended by a harmless default outside
the target set. -/
private def onePointHopfFiniteTrivializationInv (x : OnePoint ℂ × Circle) : ComplexSphereThree :=
  if hx : x.1 ∈ onePointHopfFiniteBaseSet then
    onePointHopfFiniteSection (onePointHopfFiniteBaseHomeomorph.symm ⟨x.1, hx⟩) x.2
  else
    onePointHopfFiniteSection 0 x.2

/-- Helper for Example 9.4.8: on the target of the finite chart, the inverse map is the explicit
finite Hopf section. -/
private theorem onePointHopfFiniteTrivializationInv_eq_section
    (x : OnePoint ℂ × Circle) (hx : x ∈ onePointHopfFiniteBaseSet ×ˢ (Set.univ : Set Circle)) :
    onePointHopfFiniteTrivializationInv x =
      onePointHopfFiniteSection
        (onePointHopfFiniteBaseHomeomorph.symm ⟨x.1, hx.1⟩) x.2 := by
  -- On the target set the defining `if` reduces to the explicit section branch.
  rw [onePointHopfFiniteTrivializationInv]
  simp [hx.1]

/-- Helper for Example 9.4.8: the inverse finite-chart map is continuous on the chart target. -/
private theorem onePointHopfFiniteTrivializationInv_continuousOn :
    ContinuousOn onePointHopfFiniteTrivializationInv
      (onePointHopfFiniteBaseSet ×ˢ (Set.univ : Set Circle)) := by
  -- Restricting to the target removes the default branch and leaves the explicit finite section.
  rw [continuousOn_iff_continuous_restrict]
  have hfst :
      Continuous fun x : {x : OnePoint ℂ × Circle //
          x ∈ onePointHopfFiniteBaseSet ×ˢ (Set.univ : Set Circle)} ↦ x.1.1 := by
    exact continuous_fst.comp continuous_subtype_val
  have hcoord :
      Continuous fun x : {x : OnePoint ℂ × Circle //
          x ∈ onePointHopfFiniteBaseSet ×ˢ (Set.univ : Set Circle)} ↦
        (onePointHopfFiniteBaseHomeomorph.symm ⟨x.1.1, x.2.1⟩, x.1.2) := by
    have hbase :
        Continuous fun x : {x : OnePoint ℂ × Circle //
            x ∈ onePointHopfFiniteBaseSet ×ˢ (Set.univ : Set Circle)} ↦
          (⟨x.1.1, x.2.1⟩ : onePointHopfFiniteBaseSet) := by
      exact Continuous.subtype_mk hfst fun x ↦ x.2.1
    exact
      (onePointHopfFiniteBaseHomeomorph.symm.continuous.comp hbase).prodMk
        (continuous_snd.comp continuous_subtype_val)
  have hrestrict :
      (onePointHopfFiniteBaseSet ×ˢ (Set.univ : Set Circle)).restrict
          onePointHopfFiniteTrivializationInv =
        fun x : {x : OnePoint ℂ × Circle //
            x ∈ onePointHopfFiniteBaseSet ×ˢ (Set.univ : Set Circle)} ↦
          onePointHopfFiniteSection
            (onePointHopfFiniteBaseHomeomorph.symm ⟨x.1.1, x.2.1⟩) x.1.2 := by
    funext x
    exact onePointHopfFiniteTrivializationInv_eq_section x.1 x.2
  rw [hrestrict]
  simpa [Function.comp] using onePointHopfFiniteSection_continuous.comp hcoord

/-- Helper for Example 9.4.8: the proved finite-chart maps should package into a
`Bundle.Trivialization` over `onePointHopfFiniteBaseSet`. -/
private theorem onePointHopfFiniteTrivializationExists :
    ∃ e : Bundle.Trivialization Circle qOnePoint, e.baseSet = onePointHopfFiniteBaseSet := by
  -- The ambient finite trivialization was built by extending the restricted homeomorphism.
  refine ⟨onePointHopfFiniteTrivialization, ?_⟩
  change
    (Bundle.Trivialization.codExtend onePointHopfFiniteBaseSet_open
        onePointHopfFiniteTrivialization._proof_1
        onePointHopfFiniteRestrictedTrivialization).toPretrivialization.baseSet =
      onePointHopfFiniteBaseSet
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact y.2
  · intro hx
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change ⟨x, hx⟩ ∈ (Set.univ :
      Set {x : OnePoint ℂ // x ∈ onePointHopfFiniteBaseSet})
    simp

/-- Helper for Example 9.4.8: the ambient finite trivialization has the expected finite-chart base
set. -/
private theorem onePointHopfFiniteTrivialization_baseSet :
    onePointHopfFiniteTrivialization.baseSet = onePointHopfFiniteBaseSet := by
  -- This is the same base-set computation used when packaging the finite trivialization above.
  change
    (Bundle.Trivialization.codExtend onePointHopfFiniteBaseSet_open
        onePointHopfFiniteTrivialization._proof_1
        onePointHopfFiniteRestrictedTrivialization).toPretrivialization.baseSet =
      onePointHopfFiniteBaseSet
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact y.2
  · intro hx
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change ⟨x, hx⟩ ∈ (Set.univ :
      Set {x : OnePoint ℂ // x ∈ onePointHopfFiniteBaseSet})
    simp

/-- Helper for Example 9.4.8: swap the two complex coordinates in `ℂ²`. -/
private noncomputable def complexTwoSwapLinearEquiv :
    (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  { toFun := fun z i ↦ z (Equiv.swap 0 1 i)
    invFun := fun z i ↦ z (Equiv.swap 0 1 i)
    left_inv := by
      intro z
      ext i
      fin_cases i <;> rfl
    right_inv := by
      intro z
      ext i
      fin_cases i <;> rfl
    map_add' := by
      intro z w
      ext i
      fin_cases i <;> rfl
    map_smul' := by
      intro a z
      ext i
      fin_cases i <;> rfl }

/-- Helper for Example 9.4.8: swapping coordinates preserves nonzeroness. -/
private theorem complexTwoSwap_nonzero {z : Fin 2 → ℂ} (hz : z ≠ 0) :
    complexTwoSwapLinearEquiv z ≠ 0 := by
  -- The coordinate swap is injective, so only the zero vector can map to zero.
  intro hswap
  exact hz (complexTwoSwapLinearEquiv.injective (by simpa using hswap))

/-- Helper for Example 9.4.8: swapping the two coordinates of `ℂ²` twice is the identity. -/
private theorem complexTwoSwapLinearEquiv_apply_apply (z : Fin 2 → ℂ) :
    complexTwoSwapLinearEquiv (complexTwoSwapLinearEquiv z) = z := by
  -- On each of the two coordinates, a second swap returns to the original entry.
  ext i
  fin_cases i <;> rfl

/-- Helper for Example 9.4.8: swapping the coordinates of `(z, w)` interchanges the affine and
infinite representatives used throughout this item. -/
private theorem complexTwoSwapLinearEquiv_complexFinTwoArrowSymm (z w : ℂ) :
    complexTwoSwapLinearEquiv (complexFinTwoArrowSymm (z, w)) = complexFinTwoArrowSymm (w, z) := by
  -- Expanding the `Fin 2` coordinates shows that the linear equivalence just swaps them.
  ext i
  fin_cases i <;> rfl

/-- Helper for Example 9.4.8: the coordinate swap preserves the complex unit sphere. -/
private theorem complexTwoSwap_mem_complexSphereThree {z : Fin 2 → ℂ}
    (hz : z ∈ Metric.sphere (0 : Fin 2 → ℂ) 1) :
    complexTwoSwapLinearEquiv z ∈ Metric.sphere (0 : Fin 2 → ℂ) 1 := by
  -- The swap is an isometry of the ambient `Fin 2 → ℂ`, so it preserves the sphere.
  let swapIso : (Fin 2 → ℂ) ≃ᵢ (Fin 2 → ℂ) :=
    IsometryEquiv.piCongrLeft (Y := fun _ : Fin 2 => ℂ) (Equiv.swap 0 1)
  have hzero : swapIso.symm (0 : Fin 2 → ℂ) = 0 := by
    ext i
    fin_cases i <;> rfl
  have hpre :
      z ∈ (swapIso : (Fin 2 → ℂ) → (Fin 2 → ℂ)) ⁻¹'
        Metric.sphere (0 : Fin 2 → ℂ) 1 := by
    rw [swapIso.preimage_sphere (0 : Fin 2 → ℂ) 1, hzero]
    exact hz
  have hval : swapIso z = complexTwoSwapLinearEquiv z := by
    ext i
    fin_cases i <;> rfl
  change swapIso z ∈ Metric.sphere (0 : Fin 2 → ℂ) 1 at hpre
  simpa [hval] using hpre

/-- Helper for Example 9.4.8: swapping the two coordinates gives a homeomorphism of the complex
unit sphere. -/
private noncomputable def complexSphereThreeSwapHomeomorph :
    ComplexSphereThree ≃ₜ ComplexSphereThree where
  toEquiv :=
    { toFun := fun z ↦
        ⟨complexTwoSwapLinearEquiv z.1, complexTwoSwap_mem_complexSphereThree z.2⟩
      invFun := fun z ↦
        ⟨complexTwoSwapLinearEquiv z.1, complexTwoSwap_mem_complexSphereThree z.2⟩
      left_inv := by
        intro z
        -- Route correction: keep the sphere-level symmetry as the literal coordinate swap so the
        -- later transport only has to rewrite one stable ambient vector formula.
        apply Subtype.ext
        exact complexTwoSwapLinearEquiv_apply_apply z.1
      right_inv := by
        intro z
        apply Subtype.ext
        exact complexTwoSwapLinearEquiv_apply_apply z.1 }
  continuous_toFun := by
    -- The ambient linear coordinate swap is continuous, and the sphere membership proof was
    -- isolated above.
    refine Continuous.subtype_mk ?_ fun z ↦ (complexTwoSwap_mem_complexSphereThree z.2)
    exact complexTwoSwapLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp
      continuous_subtype_val
  continuous_invFun := by
    -- The inverse is the same ambient coordinate swap, so the continuity proof is identical.
    refine Continuous.subtype_mk ?_ fun z ↦ (complexTwoSwap_mem_complexSphereThree z.2)
    exact complexTwoSwapLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp
      continuous_subtype_val

/-- Helper for Example 9.4.8: the coordinate swap descends to the projective line. -/
private noncomputable def complexProjectiveLineSwap :
    ComplexProjectiveLine → ComplexProjectiveLine :=
  Quotient.lift
    (fun v : {w : Fin 2 → ℂ // w ≠ 0} ↦
      Projectivization.mk' ℂ ⟨complexTwoSwapLinearEquiv v.1, complexTwoSwap_nonzero v.2⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨t, rfl⟩
      -- Swapping coordinates commutes with complex scaling, so the quotient class is unchanged.
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _
        (complexTwoSwap_nonzero hu) (complexTwoSwap_nonzero hv)).2
      refine ⟨t, ?_⟩
      ext i
      fin_cases i <;> simpa [complexTwoSwapLinearEquiv, Units.smul_def])

/-- Helper for Example 9.4.8: the descended projective swap is computed by swapping the ambient
nonzero representative. -/
private theorem complexProjectiveLineSwap_mk (z : Fin 2 → ℂ) (hz : z ≠ 0) :
    complexProjectiveLineSwap (Projectivization.mk ℂ z hz) =
      Projectivization.mk ℂ (complexTwoSwapLinearEquiv z) (complexTwoSwap_nonzero hz) := by
  -- The quotient lift computes directly on projective classes represented by nonzero vectors.
  rfl

/-- Helper for Example 9.4.8: the descended projective coordinate swap is continuous. -/
private theorem complexProjectiveLineSwap_continuous :
    Continuous complexProjectiveLineSwap := by
  let swapNonzero : {w : Fin 2 → ℂ // w ≠ 0} → {w : Fin 2 → ℂ // w ≠ 0} := fun v ↦
    ⟨complexTwoSwapLinearEquiv v.1, complexTwoSwap_nonzero v.2⟩
  have hswapNonzero : Continuous swapNonzero := by
    -- The ambient coordinate swap is continuous, so it is continuous on the nonzero subtype too.
    have hambient :
        Continuous fun v : {w : Fin 2 → ℂ // w ≠ 0} ↦ complexTwoSwapLinearEquiv v.1 :=
      complexTwoSwapLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val
    exact Continuous.subtype_mk hambient fun v ↦ (swapNonzero v).2
  have hmk :
      Continuous fun v : {w : Fin 2 → ℂ // w ≠ 0} ↦ Projectivization.mk' ℂ (swapNonzero v) :=
    continuous_quotient_mk'.comp hswapNonzero
  -- The projective swap is the quotient descent of the continuous map on nonzero representatives.
  simpa [complexProjectiveLineSwap, swapNonzero] using
    hmk.quotient_lift (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨t, rfl⟩
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _
        (complexTwoSwap_nonzero hu) (complexTwoSwap_nonzero hv)).2
      refine ⟨t, ?_⟩
      ext i
      fin_cases i <;> simpa [complexTwoSwapLinearEquiv, Units.smul_def])

/-- Helper for Example 9.4.8: the descended projective coordinate swap is involutive. -/
private theorem complexProjectiveLineSwap_involutive (x : ComplexProjectiveLine) :
    complexProjectiveLineSwap (complexProjectiveLineSwap x) = x := by
  -- On a chosen nonzero representative, two swaps of the ambient coordinates cancel.
  induction x using Projectivization.ind with
  | h z hz =>
      simp [complexProjectiveLineSwap_mk, complexTwoSwapLinearEquiv_apply_apply]

/-- Helper for Example 9.4.8: the projective swap sends `[1 : 0]` to `[0 : 1]`. -/
private theorem complexProjectiveLineSwap_infinity :
    complexProjectiveLineSwap complexProjectiveLineInfinity = complexProjectiveLineFinite 0 := by
  -- Swapping the coordinates of the infinity representative `(1, 0)` gives the finite point
  -- `(0, 1)`, i.e. the affine coordinate `0`.
  rw [complexProjectiveLineInfinity, complexProjectiveLineFinite, complexProjectiveLineSwap_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ (complexTwoSwap_nonzero (by
    intro hz
    have hz' : complexFinTwoArrowSymm (1, 0) = complexFinTwoArrowSymm 0 := by
      simpa using hz
    have hpair : (((1 : ℂ), 0) : ℂ × ℂ) = 0 := complexFinTwoArrowSymm_injective hz'
    simpa using congrArg Prod.fst hpair)) (by
      intro hz
      have hz' : complexFinTwoArrowSymm (0, 1) = complexFinTwoArrowSymm 0 := by
        simpa using hz
      have hpair : (((0 : ℂ), 1) : ℂ × ℂ) = 0 := complexFinTwoArrowSymm_injective hz'
      simpa using congrArg Prod.snd hpair)).2
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> simp [complexTwoSwapLinearEquiv, complexFinTwoArrowSymm]

/-- Helper for Example 9.4.8: the projective swap sends `[0 : 1]` to `[1 : 0]`. -/
private theorem complexProjectiveLineSwap_zero :
    complexProjectiveLineSwap (complexProjectiveLineFinite 0) = complexProjectiveLineInfinity := by
  -- Swapping the coordinates of the finite representative `(0, 1)` gives `(1, 0)`.
  rw [complexProjectiveLineFinite, complexProjectiveLineInfinity, complexProjectiveLineSwap_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ (complexTwoSwap_nonzero (by
    intro hz
    have hz' : complexFinTwoArrowSymm (0, 1) = complexFinTwoArrowSymm 0 := by
      simpa using hz
    have hpair : (((0 : ℂ), 1) : ℂ × ℂ) = 0 := complexFinTwoArrowSymm_injective hz'
    simpa using congrArg Prod.snd hpair)) (by
      intro hz
      have hz' : complexFinTwoArrowSymm (1, 0) = complexFinTwoArrowSymm 0 := by
        simpa using hz
      have hpair : (((1 : ℂ), 0) : ℂ × ℂ) = 0 := complexFinTwoArrowSymm_injective hz'
      simpa using congrArg Prod.fst hpair)).2
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> simp [complexTwoSwapLinearEquiv, complexFinTwoArrowSymm]

/-- Helper for Example 9.4.8: the quotient map commutes with the source-side coordinate swap. -/
private theorem complexSphereThreeToProjectivization_swap (z : ComplexSphereThree) :
    complexSphereThreeToProjectivization (complexSphereThreeSwapHomeomorph z) =
      complexProjectiveLineSwap (complexSphereThreeToProjectivization z) := by
  -- Both sides are the projective class of the same swapped representative in `ℂ²`.
  simp [complexSphereThreeToProjectivization, complexSphereThreeSwapHomeomorph,
    complexProjectiveLineSwap_mk]

/-- Helper for Example 9.4.8: the descended projective coordinate swap is an equivalence. -/
private noncomputable def complexProjectiveLineSwapEquiv :
    ComplexProjectiveLine ≃ ComplexProjectiveLine where
  toFun := complexProjectiveLineSwap
  invFun := complexProjectiveLineSwap
  left_inv := complexProjectiveLineSwap_involutive
  right_inv := complexProjectiveLineSwap_involutive

/-- Helper for Example 9.4.8: the descended projective coordinate swap is a homeomorphism. -/
private noncomputable def complexProjectiveLineSwapHomeomorph :
    ComplexProjectiveLine ≃ₜ ComplexProjectiveLine where
  toEquiv := complexProjectiveLineSwapEquiv
  continuous_toFun := complexProjectiveLineSwap_continuous
  continuous_invFun := complexProjectiveLineSwap_continuous

/-- Helper for Example 9.4.8: the base-side coordinate swap on `OnePoint ℂ` is a homeomorphism. -/
private noncomputable def onePointComplexSwapHomeomorph :
    OnePoint ℂ ≃ₜ OnePoint ℂ :=
  complexProjectiveLineHomeomorphOnePointComplex.symm.trans
    (complexProjectiveLineSwapHomeomorph.trans complexProjectiveLineHomeomorphOnePointComplex)

/-- Helper for Example 9.4.8: the base swap is the projective swap seen in affine coordinates. -/
private theorem onePointComplexSwapHomeomorph_apply_eq (x : OnePoint ℂ) :
    onePointComplexSwapHomeomorph x =
      complexProjectiveLineHomeomorphOnePointComplex
        (complexProjectiveLineSwap (complexProjectiveLineEquivOnePointComplex x)) := by
  -- The homeomorphism was packaged directly from this explicit affine-chart equivalence.
  rfl

/-- Helper for Example 9.4.8: the base-side swap sends `∞` to `0`. -/
private theorem onePointComplexSwapHomeomorph_apply_infty :
    onePointComplexSwapHomeomorph (OnePoint.infty : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
  -- The point `[1 : 0]` goes to `[0 : 1]`, which is the affine coordinate `0`.
  calc
    onePointComplexSwapHomeomorph (OnePoint.infty : OnePoint ℂ)
        = complexProjectiveLineHomeomorphOnePointComplex
            (complexProjectiveLineSwap complexProjectiveLineInfinity) := by
              simp [onePointComplexSwapHomeomorph_apply_eq, complexProjectiveLineInfinity_eq_equiv]
    _ = complexProjectiveLineHomeomorphOnePointComplex (complexProjectiveLineFinite 0) := by
          rw [complexProjectiveLineSwap_infinity]
    _ = ((0 : ℂ) : OnePoint ℂ) := by
          simpa [complexProjectiveLineHomeomorphOnePointComplex_apply] using
            congrArg complexProjectiveLineHomeomorphOnePointComplex
              (complexProjectiveLineFinite_eq_equiv 0)

/-- Helper for Example 9.4.8: the base-side swap sends `0` to `∞`. -/
private theorem onePointComplexSwapHomeomorph_apply_zero :
    onePointComplexSwapHomeomorph (((0 : ℂ) : OnePoint ℂ)) = OnePoint.infty := by
  -- The finite affine point `[0 : 1]` swaps to the point at infinity `[1 : 0]`.
  calc
    onePointComplexSwapHomeomorph (((0 : ℂ) : OnePoint ℂ))
        = complexProjectiveLineHomeomorphOnePointComplex
            (complexProjectiveLineSwap (complexProjectiveLineFinite 0)) := by
              simp [onePointComplexSwapHomeomorph_apply_eq, complexProjectiveLineFinite_eq_equiv]
    _ = complexProjectiveLineHomeomorphOnePointComplex complexProjectiveLineInfinity := by
          rw [complexProjectiveLineSwap_zero]
    _ = (OnePoint.infty : OnePoint ℂ) := by
          simpa [complexProjectiveLineHomeomorphOnePointComplex_apply] using
            congrArg complexProjectiveLineHomeomorphOnePointComplex
              complexProjectiveLineInfinity_eq_equiv

/-- Helper for Example 9.4.8: the inverse base swap sends `∞` back to `0`. -/
private theorem onePointComplexSwapHomeomorph_symm_apply_infty :
    onePointComplexSwapHomeomorph.symm (OnePoint.infty : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
  -- Since the swap sends `0` to `∞`, applying the inverse at `∞` must recover `0`.
  apply onePointComplexSwapHomeomorph.injective
  calc
    onePointComplexSwapHomeomorph (onePointComplexSwapHomeomorph.symm (OnePoint.infty : OnePoint ℂ))
        = (OnePoint.infty : OnePoint ℂ) := by simp
    _ = onePointComplexSwapHomeomorph (((0 : ℂ) : OnePoint ℂ)) := by
          rw [onePointComplexSwapHomeomorph_apply_zero]

/-- Helper for Example 9.4.8: the source and base coordinate swaps conjugate `qOnePoint` to
itself. -/
private theorem qOnePointSwapConjugacy :
    onePointComplexSwapHomeomorph ∘ qOnePoint ∘ complexSphereThreeSwapHomeomorph = qOnePoint := by
  funext z
  -- Route correction: stabilize all transport through one source swap, one projective swap, and
  -- one affine-chart swap, then the final identity is just involutivity on `ℂP¹`.
  have hchart :
      complexProjectiveLineEquivOnePointComplex
        (complexProjectiveLineHomeomorphOnePointComplex
          (complexSphereThreeToProjectivization (complexSphereThreeSwapHomeomorph z))) =
        complexSphereThreeToProjectivization (complexSphereThreeSwapHomeomorph z) := by
    simpa [complexProjectiveLineHomeomorphOnePointComplex_apply] using
      complexProjectiveLineEquivOnePointComplex.apply_symm_apply
        (complexSphereThreeToProjectivization (complexSphereThreeSwapHomeomorph z))
  calc
    (onePointComplexSwapHomeomorph ∘ qOnePoint ∘ complexSphereThreeSwapHomeomorph) z
        = complexProjectiveLineHomeomorphOnePointComplex
            (complexProjectiveLineSwap
              (complexProjectiveLineEquivOnePointComplex
                (complexProjectiveLineHomeomorphOnePointComplex
                  (complexSphereThreeToProjectivization
                    (complexSphereThreeSwapHomeomorph z))))) := by
                      simp [qOnePoint, Function.comp, onePointComplexSwapHomeomorph_apply_eq]
    _ = complexProjectiveLineHomeomorphOnePointComplex
          (complexProjectiveLineSwap
            (complexSphereThreeToProjectivization (complexSphereThreeSwapHomeomorph z))) := by
              rw [hchart]
    _ = complexProjectiveLineHomeomorphOnePointComplex
          (complexProjectiveLineSwap
            (complexProjectiveLineSwap (complexSphereThreeToProjectivization z))) := by
              rw [complexSphereThreeToProjectivization_swap]
    _ = complexProjectiveLineHomeomorphOnePointComplex
          (complexSphereThreeToProjectivization z) := by
            rw [complexProjectiveLineSwap_involutive]
    _ = qOnePoint z := by
          rfl

/-- Helper for Example 9.4.8: after the finite chart is packaged, the remaining gap is to
transport it by the coordinate-swap symmetry so that the point `∞` is also covered. -/
private theorem qOnePoint_isFiberBundle :
    IsFiberBundleMap Circle qOnePoint := by
  intro b
  by_cases hb : b = OnePoint.infty
  · subst b
    let eInfRaw :
        Bundle.Trivialization Circle
          (onePointComplexSwapHomeomorph ∘ qOnePoint ∘ complexSphereThreeSwapHomeomorph) :=
      Bundle.Trivialization.homeomorphComp
        (e := onePointHopfFiniteTrivialization.compHomeomorph complexSphereThreeSwapHomeomorph)
        onePointComplexSwapHomeomorph
    let eInf : Bundle.Trivialization Circle qOnePoint := by
      refine
        { toOpenPartialHomeomorph := eInfRaw.toOpenPartialHomeomorph
          baseSet := eInfRaw.baseSet
          open_baseSet := eInfRaw.open_baseSet
          source_eq := ?_
          target_eq := eInfRaw.target_eq
          proj_toFun := ?_ }
      · simpa [qOnePointSwapConjugacy, Function.comp] using eInfRaw.source_eq
      · intro p hp
        calc
          (eInfRaw p).1
              = (onePointComplexSwapHomeomorph ∘ qOnePoint ∘ complexSphereThreeSwapHomeomorph) p := by
                  exact eInfRaw.proj_toFun p hp
          _ = qOnePoint p := by
                simpa [Function.comp] using congrFun qOnePointSwapConjugacy p
    have hbase : (OnePoint.infty : OnePoint ℂ) ∈ eInfRaw.baseSet := by
      have hbaseSet :
          eInfRaw.baseSet = onePointComplexSwapHomeomorph.symm ⁻¹' onePointHopfFiniteBaseSet := by
        calc
          eInfRaw.baseSet
              = onePointComplexSwapHomeomorph.symm ⁻¹' onePointHopfFiniteTrivialization.baseSet := by
                  unfold eInfRaw Bundle.Trivialization.homeomorphComp Bundle.Trivialization.compHomeomorph
                  rfl
          _ = onePointComplexSwapHomeomorph.symm ⁻¹' onePointHopfFiniteBaseSet := by
                rw [onePointHopfFiniteTrivialization_baseSet]
      rw [hbaseSet]
      simpa [onePointComplexSwapHomeomorph_symm_apply_infty, onePointHopfFiniteBaseSet]
    refine ⟨eInf, ?_⟩
    -- The transported chart covers `∞` because the inverse base swap sends `∞` to the finite
    -- point `0`, which already lies in the finite chart base set.
    exact hbase
  · obtain ⟨e, he⟩ := onePointHopfFiniteTrivializationExists
    refine ⟨e, ?_⟩
    -- Outside `∞`, the existing finite chart already provides the required local trivialization.
    rw [he]
    simpa [onePointHopfFiniteBaseSet] using hb

/-- Helper for Example 9.4.8: the canonical quotient `ComplexSphereThree → ComplexProjectiveLine`
is locally a `Circle`-bundle. -/
private theorem complexSphereThreeToProjectivization_isFiberBundle :
    IsFiberBundleMap Circle complexSphereThreeToProjectivization := by
  -- Prove local triviality in the affine `OnePoint ℂ` chart, then transport back to `ℂP¹`.
  convert
    (isFiberBundleMap_congrHomeomorph
      (F := Circle) (p := qOnePoint) (Homeomorph.refl _)
      complexProjectiveLineHomeomorphOnePointComplex.symm qOnePoint_isFiberBundle) using 1
  funext z
  simp [qOnePoint, Function.comp]

/-- Any Hopf quotient map `η : S^3 → S^2` is a bundle map with fiber `S¹`. -/
theorem hopfQuotientMap_isFiberBundle {η : 𝕊 3 → 𝕊 2} (hη : IsHopfQuotientMap η) :
    IsFiberBundleMap Circle η := by
  obtain ⟨eS3, eCP1, hη_eq⟩ := hη
  -- Transport the canonical quotient trivializations across the chosen source and target
  -- homeomorphisms.
  simpa [hη_eq, Function.comp] using
    (isFiberBundleMap_congrHomeomorph
      (F := Circle) (p := complexSphereThreeToProjectivization)
      eS3 eCP1 complexSphereThreeToProjectivization_isFiberBundle)

/-- Example 9.4.8 (2): the Hopf map is a fiber bundle over `S²` with fiber `S¹`. -/
theorem hopfMap_isFiberBundle :
    IsFiberBundleMap Circle hopfMap := by
  -- Once the quotient-model bundle theorem is available, the explicit Hopf map follows
  -- immediately from part (1).
  exact hopfQuotientMap_isFiberBundle hopfMap_isHopfQuotient

import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.LinearAlgebra.Dimension.Constructions
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic recall note: `lean_leansearch` surfaced `IsLocalFrameOn`, while local precedent from
-- `Problem_8_6` fixes the sphere endpoint here: keep the Cayley-Dickson formulas on `ℍ × ℍ`,
-- package them through a bundled bilinear multiplication map on `𝕆`, and transport
-- the right-multiplication fields to `S^7` through the sphere
-- tangent-space/orthogonal-complement equivalence.

open scoped Quaternion RealInnerProductSpace ContDiff Manifold

local notation "𝕆" => ℍ × ℍ
local notation "𝕆₂" => WithLp 2 𝕆
local notation "unitOctonionSphere" => Metric.sphere (0 : 𝕆₂) 1
local instance : Coe unitOctonionSphere 𝕆 := ⟨fun Q ↦ WithLp.ofLp (Q : 𝕆₂)⟩

/-- The octonion multiplication on `ℍ × ℍ` is the Cayley-Dickson product
`(p, q) (r, s) = (pr - s q^*, p^* s + rq)`. -/
def octonionMul (P Q : 𝕆) : 𝕆 :=
  (P.1 * Q.1 - Q.2 * star P.2, star P.1 * Q.2 + Q.1 * P.2)

/-- Expanded form of the octonion multiplication. -/
theorem octonionMul_apply (P Q : 𝕆) :
    octonionMul P Q = (P.1 * Q.1 - Q.2 * star P.2, star P.1 * Q.2 + Q.1 * P.2) := sorry

/-- Octonion conjugation is given by `(p, q)^* = (p^*, -q)`. -/
def octonionStar (P : 𝕆) : 𝕆 :=
  (star P.1, -P.2)

/-- Expanded form of octonion conjugation. -/
theorem octonionStar_apply (P : 𝕆) :
    octonionStar P = (star P.1, -P.2) := sorry

/-- The seven standard imaginary unit octonions coming from the quaternion basis of `ℍ × ℍ`. -/
def problem_8_7_basisVec : Fin 7 → 𝕆 :=
  ![(((⟨0, 1, 0, 0⟩ : ℍ)), (0 : ℍ)),
    (((⟨0, 0, 1, 0⟩ : ℍ)), (0 : ℍ)),
    (((⟨0, 0, 0, 1⟩ : ℍ)), (0 : ℍ)),
    ((0 : ℍ), (1 : ℍ)),
    ((0 : ℍ), ((⟨0, 1, 0, 0⟩ : ℍ))),
    ((0 : ℍ), ((⟨0, 0, 1, 0⟩ : ℍ))),
    ((0 : ℍ), ((⟨0, 0, 0, 1⟩ : ℍ)))]

/-- Explicit form of the standard imaginary basis of octonions. -/
theorem problem_8_7_basisVec_apply :
    problem_8_7_basisVec =
      ![(((⟨0, 1, 0, 0⟩ : ℍ)), (0 : ℍ)),
        (((⟨0, 0, 1, 0⟩ : ℍ)), (0 : ℍ)),
        (((⟨0, 0, 0, 1⟩ : ℍ)), (0 : ℍ)),
        ((0 : ℍ), (1 : ℍ)),
        ((0 : ℍ), ((⟨0, 1, 0, 0⟩ : ℍ))),
        ((0 : ℍ), ((⟨0, 0, 1, 0⟩ : ℍ))),
        ((0 : ℍ), ((⟨0, 0, 0, 1⟩ : ℍ)))] := sorry

/-- The octonions form an `8`-dimensional real vector space. -/
theorem octonion_finrank :
    Module.finrank ℝ 𝕆 = 8 := sorry

private theorem problem_8_7_finrank_real_octonion_l2_fact : Fact (Module.finrank ℝ 𝕆₂ = 7 + 1) := by
  have hfinrank : Module.finrank ℝ 𝕆₂ = Module.finrank ℝ 𝕆 := by
    simpa using (LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ 𝕆))
  exact ⟨by rw [hfinrank]; simpa using octonion_finrank⟩

attribute [local instance] problem_8_7_finrank_real_octonion_l2_fact

/-- The Cayley-Dickson product on `𝕆` is additive in the left variable. -/
theorem octonionMul_add_left (P₁ P₂ Q : 𝕆) :
    octonionMul (P₁ + P₂) Q = octonionMul P₁ Q + octonionMul P₂ Q := sorry

/-- The Cayley-Dickson product on `𝕆` is `ℝ`-linear in the left variable. -/
theorem octonionMul_smul_left (a : ℝ) (P Q : 𝕆) :
    octonionMul (a • P) Q = a • octonionMul P Q := sorry

/-- The Cayley-Dickson product on `𝕆` is additive in the right variable. -/
theorem octonionMul_add_right (P Q₁ Q₂ : 𝕆) :
    octonionMul P (Q₁ + Q₂) = octonionMul P Q₁ + octonionMul P Q₂ := sorry

/-- The Cayley-Dickson product on `𝕆` is `ℝ`-linear in the right variable. -/
theorem octonionMul_smul_right (a : ℝ) (P Q : 𝕆) :
    octonionMul P (a • Q) = a • octonionMul P Q := sorry

/-- The Cayley-Dickson product packaged as the canonical `ℝ`-bilinear multiplication map on
the octonion algebra `𝕆 = ℍ × ℍ`. -/
def octonionMulBilinear : 𝕆 →ₗ[ℝ] 𝕆 →ₗ[ℝ] 𝕆 :=
  LinearMap.mk₂ ℝ octonionMul
    octonionMul_add_left octonionMul_smul_left
    octonionMul_add_right octonionMul_smul_right

/-- Expanded form of the bundled octonion multiplication map. -/
theorem octonionMulBilinear_apply (P Q : 𝕆) :
    octonionMulBilinear P Q = octonionMul P Q := rfl

/-- The textbook hint identity `(P Q^*) Q = P (Q^* Q)` for octonions. -/
theorem octonion_mul_star_right_assoc (P Q : 𝕆) :
    octonionMul (octonionMul P (octonionStar Q)) Q =
      octonionMul P (octonionMul (octonionStar Q) Q) := sorry

/-- Octonion multiplication is not commutative. -/
theorem octonion_noncommutative :
    octonionMul (problem_8_7_basisVec 0) (problem_8_7_basisVec 1) ≠
      octonionMul (problem_8_7_basisVec 1) (problem_8_7_basisVec 0) := sorry

/-- Octonion multiplication is not associative. -/
theorem octonion_nonassociative :
    octonionMul (octonionMul (problem_8_7_basisVec 0) (problem_8_7_basisVec 1))
        (problem_8_7_basisVec 3) ≠
      octonionMul (problem_8_7_basisVec 0)
        (octonionMul (problem_8_7_basisVec 1) (problem_8_7_basisVec 3)) := sorry

/-- The seven octonionic ambient vector fields on `ℍ × ℍ` are obtained by right multiplication by
the standard imaginary basis vectors. -/
def problem_8_7_vectorField (i : Fin 7) : 𝕆 → 𝕆 :=
  fun Q ↦ octonionMul Q (problem_8_7_basisVec i)

/-- Expanded form of the octonionic ambient vector fields. -/
theorem problem_8_7_vectorField_apply (i : Fin 7) (Q : 𝕆) :
    problem_8_7_vectorField i Q = octonionMul Q (problem_8_7_basisVec i) := sorry

/-- Helper: right multiplication by a real scalar octonion is ordinary scalar
multiplication on `𝕆`. -/
theorem octonionMul_realScalar (P : 𝕆) (a : ℝ) :
    octonionMul P ((a : ℍ), 0) = a • P := sorry

/-- Helper: the product `Q^* Q` is the real scalar octonion given by the sum of
the quaternion norm-squares of the two components, in the source-hint order. -/
theorem octonionMul_star_self (Q : 𝕆) :
    octonionMul (octonionStar Q) Q =
      ((((Quaternion.normSq Q.1 + Quaternion.normSq Q.2 : ℝ)) : ℍ), 0) := sorry

/-- Helper: the product `Q Q^*` is the same real scalar octonion. -/
theorem octonionMul_self_star (Q : 𝕆) :
    octonionMul Q (octonionStar Q) =
      ((((Quaternion.normSq Q.1 + Quaternion.normSq Q.2 : ℝ)) : ℍ), 0) := sorry

/-- Helper: a unit octonion in the ambient sphere has nonzero quaternion
norm-square sum. -/
theorem octonionNormSqSum_ne_zero_of_unitSphere (Q : unitOctonionSphere) :
    Quaternion.normSq ((Q : 𝕆).1) + Quaternion.normSq ((Q : 𝕆).2) ≠ 0 := sorry

/-- Helper: the seven standard imaginary octonion basis vectors are linearly
independent over `ℝ`. -/
theorem problem_8_7_basisVec_linearIndependent :
    LinearIndependent ℝ problem_8_7_basisVec := sorry

/-- Helper: right multiplication by a fixed octonion is an `ℝ`-linear map. -/
def octonionRightMulLinear (Q : 𝕆) : 𝕆 →ₗ[ℝ] 𝕆 where
  toFun := fun P ↦ octonionMul P Q
  map_add' := fun P₁ P₂ ↦ octonionMul_add_left P₁ P₂ Q
  map_smul' := fun a P ↦ octonionMul_smul_left a P Q

/-- Helper: expanded form of `octonionRightMulLinear`. -/
theorem octonionRightMulLinear_apply (Q P : 𝕆) :
    octonionRightMulLinear Q P = octonionMul P Q := sorry

/-- Helper: right multiplication by a unit octonion is injective. -/
theorem octonionRightMul_injective_of_unitSphere (Q : unitOctonionSphere) :
    Function.Injective (fun P : 𝕆 ↦ octonionMul P (Q : 𝕆)) := sorry

/-- Helper: each octonionic ambient right-multiplication field is smooth on
`ℍ × ℍ`. -/
theorem problem_8_7_vectorField_contDiff (i : Fin 7) :
    ContDiff ℝ ∞ (problem_8_7_vectorField i) := sorry

/-- Helper: the ambient inner product of `Q` with `Eᵢ Q` vanishes. -/
theorem problem_8_7_vectorField_innerZero (i : Fin 7) (Q : unitOctonionSphere) :
    inner ℝ (Q : 𝕆₂) (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆))) = 0 := sorry

/-- For each unit octonion `Q`, the vector `Eᵢ Q` is tangent to the unit sphere `S^7`; in the
ambient `L²` inner-product-space structure on pairs of quaternions, this is membership in the
orthogonal complement of `ℝ ∙ Q`.
-/
theorem problem_8_7_vectorField_mem_orthogonal (i : Fin 7) (Q : unitOctonionSphere) :
    WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)) ∈ (ℝ ∙ (Q : 𝕆₂))ᗮ := sorry

/-- The sphere tangent space identifies with the orthogonal complement of the radial line in the
ambient octonion space. -/
private def problem_8_7_tangentOrthogonalEquiv (Q : unitOctonionSphere) :
    TangentSpace (𝓡 7) Q ≃ₗ[ℝ] (ℝ ∙ (Q : 𝕆₂))ᗮ :=
  let coeMfderiv : TangentSpace (𝓡 7) Q →L[ℝ] 𝕆₂ :=
    mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q
  (LinearEquiv.ofInjective coeMfderiv (mfderiv_coe_sphere_injective Q)).trans
    (LinearEquiv.ofEq _ _ (range_mfderiv_coe_sphere Q))

/-- The intrinsic octonionic frame on `S^7` is obtained by transporting the ambient
right-multiplication fields through the sphere tangent-space identification. -/
def problem_8_7_frame : Fin 7 → (Q : unitOctonionSphere) → TangentSpace (𝓡 7) Q :=
  fun i Q ↦
    (problem_8_7_tangentOrthogonalEquiv Q).symm
      ⟨WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)),
        problem_8_7_vectorField_mem_orthogonal i Q⟩

/-- Expanded form of the intrinsic octonionic frame on `S^7`. -/
theorem problem_8_7_frame_apply (i : Fin 7) (Q : unitOctonionSphere) :
    problem_8_7_frame i Q =
      (problem_8_7_tangentOrthogonalEquiv Q).symm
        ⟨WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)),
          problem_8_7_vectorField_mem_orthogonal i Q⟩ := sorry

/-- At each unit octonion, the seven octonionic vectors `Eᵢ Q` are linearly independent in the
ambient `ℍ × ℍ`. -/
theorem problem_8_7_vectorField_linearIndependent (Q : unitOctonionSphere) :
    LinearIndependent ℝ (fun i : Fin 7 ↦ problem_8_7_vectorField i (Q : 𝕆)) := sorry

/-- The intrinsic octonionic frame is pointwise linearly independent on the unit sphere. -/
theorem problem_8_7_frame_conditions (Q : unitOctonionSphere) :
    LinearIndependent ℝ (fun i : Fin 7 ↦ problem_8_7_frame i Q) := sorry

/-- Problem 8-7: for the Cayley-Dickson octonion multiplication on `𝕆 = ℍ × ℍ`, the companion
theorems `octonion_noncommutative` and `octonion_nonassociative` record the source's algebraic
noncommutativity and nonassociativity, and the explicit right-multiplication fields by the seven
standard imaginary basis vectors restrict to a smooth global frame on the unit sphere `S^7`. -/
theorem problem_8_7_isLocalFrameOn :
    IsLocalFrameOn (𝓡 7) (EuclideanSpace ℝ (Fin 7)) ∞ problem_8_7_frame Set.univ := sorry

end

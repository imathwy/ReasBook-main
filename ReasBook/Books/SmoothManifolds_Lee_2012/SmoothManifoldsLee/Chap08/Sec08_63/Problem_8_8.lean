import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import SmoothManifolds_Lee_2012.Chap08.Sec08_63.Problem_8_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContDiff Manifold Quaternion RealInnerProductSpace

local notation "𝕆" => ℍ × ℍ
local notation "𝕊" => 𝕆 × 𝕆
local notation "unitSedenionSphere" => Metric.sphere (0 : 𝕊) 1

/-- Problem 8-8: the sedenion multiplication on `𝕆 × 𝕆` is the next Cayley-Dickson doubling of
the octonion multiplication from Problem 8-7. -/
def sedenionMul (P Q : 𝕊) : 𝕊 :=
  (octonionMul P.1 Q.1 - octonionMul Q.2 (octonionStar P.2),
    octonionMul (octonionStar P.1) Q.2 + octonionMul Q.1 P.2)

scoped[Sedenion] infixl:70 " *ₛ " => sedenionMul

open scoped Sedenion

/-- Problem 8-8: the fifteen standard imaginary unit sedenions, obtained by doubling the standard
imaginary basis of the octonions from Problem 8-7. -/
def problem_8_8_basisVec : Fin 15 → 𝕊 :=
  ![((problem_8_7_basisVec 0), (0 : 𝕆)),
    ((problem_8_7_basisVec 1), (0 : 𝕆)),
    ((problem_8_7_basisVec 2), (0 : 𝕆)),
    ((problem_8_7_basisVec 3), (0 : 𝕆)),
    ((problem_8_7_basisVec 4), (0 : 𝕆)),
    ((problem_8_7_basisVec 5), (0 : 𝕆)),
    ((problem_8_7_basisVec 6), (0 : 𝕆)),
    ((0 : 𝕆), (((1 : ℍ), (0 : ℍ)) : 𝕆)),
    ((0 : 𝕆), (problem_8_7_basisVec 0)),
    ((0 : 𝕆), (problem_8_7_basisVec 1)),
    ((0 : 𝕆), (problem_8_7_basisVec 2)),
    ((0 : 𝕆), (problem_8_7_basisVec 3)),
    ((0 : 𝕆), (problem_8_7_basisVec 4)),
    ((0 : 𝕆), (problem_8_7_basisVec 5)),
    ((0 : 𝕆), (problem_8_7_basisVec 6))]

/-- Problem 8-8: the sedenionic vector fields are obtained by left multiplication by the standard
imaginary basis vectors. -/
def problem_8_8_vectorField (i : Fin 15) : 𝕊 → 𝕊 :=
  fun Q ↦ problem_8_8_basisVec i *ₛ Q

/-- Problem 8-8: expanded form of the sedenionic vector fields. -/
theorem problem_8_8_vectorField_apply (i : Fin 15) (Q : 𝕊) :
    problem_8_8_vectorField i Q = problem_8_8_basisVec i *ₛ Q := rfl

/-- Sedenion multiplication is additive in the left variable. -/
theorem sedenionMul_add_left (P₁ P₂ Q : 𝕊) :
    (P₁ + P₂) *ₛ Q = P₁ *ₛ Q + P₂ *ₛ Q := by
  sorry

/-- Sedenion multiplication is `ℝ`-linear in the left variable. -/
theorem sedenionMul_smul_left (a : ℝ) (P Q : 𝕊) :
    (a • P) *ₛ Q = a • (P *ₛ Q) := by
  sorry

/-- Sedenion multiplication is additive in the right variable. -/
theorem sedenionMul_add_right (P Q₁ Q₂ : 𝕊) :
    P *ₛ (Q₁ + Q₂) = P *ₛ Q₁ + P *ₛ Q₂ := by
  sorry

/-- Sedenion multiplication is `ℝ`-linear in the right variable. -/
theorem sedenionMul_smul_right (a : ℝ) (P Q : 𝕊) :
    P *ₛ (a • Q) = a • (P *ₛ Q) := by
  sorry

/-- The sedenions form a `16`-dimensional real vector space. -/
theorem problem_8_8_finrank :
    Module.finrank ℝ 𝕊 = 15 + 1 := by
  have hq : Module.finrank ℝ ℍ = 4 := by
    simpa using (Quaternion.finrank_eq_four : Module.finrank ℝ ℍ = 4)
  calc
    Module.finrank ℝ 𝕊 = Module.finrank ℝ 𝕆 + Module.finrank ℝ 𝕆 := by
      exact
        (Module.finrank_prod :
          Module.finrank ℝ (𝕆 × 𝕆) = Module.finrank ℝ 𝕆 + Module.finrank ℝ 𝕆)
    _ = 15 + 1 := by
      norm_num [hq]

local instance problem_8_8_finrank_fact : Fact (Module.finrank ℝ 𝕊 = 15 + 1) :=
  ⟨problem_8_8_finrank⟩

/-- Problem 8-8: a concrete nonzero left zero divisor for the sedenion algebra. -/
def problem_8_8_leftZeroDivisor : 𝕊 :=
  problem_8_8_basisVec 2 + problem_8_8_basisVec 9

/-- Problem 8-8: a concrete nonzero right zero divisor for the sedenion algebra. -/
def problem_8_8_rightZeroDivisor : 𝕊 :=
  problem_8_8_basisVec 5 - problem_8_8_basisVec 14

/-- Problem 8-8: the explicit left zero divisor is nonzero. -/
theorem problem_8_8_leftZeroDivisor_ne_zero :
    problem_8_8_leftZeroDivisor ≠ 0 := by
  sorry

/-- Problem 8-8: the explicit right zero divisor is nonzero. -/
theorem problem_8_8_rightZeroDivisor_ne_zero :
    problem_8_8_rightZeroDivisor ≠ 0 := by
  sorry

/-- Problem 8-8: the standard left-multiplication construction on the sedenions has explicit zero
divisors. -/
theorem problem_8_8_zeroDivisor :
    problem_8_8_leftZeroDivisor *ₛ problem_8_8_rightZeroDivisor = 0 := by
  sorry

/-- Problem 8-8: the normalized right zero divisor gives a unit sedenion. -/
def problem_8_8_obstructionPoint : 𝕊 :=
  (1 / Real.sqrt 2) • problem_8_8_rightZeroDivisor

/-- The obstruction point lies on the unit sedenion sphere. -/
theorem problem_8_8_obstructionPoint_mem_unitSedenionSphere :
    problem_8_8_obstructionPoint ∈ unitSedenionSphere := by
  sorry

/-- The explicit unit sedenion at which the left-multiplication family satisfies a nontrivial
linear relation. -/
def problem_8_8_obstructionUnit : unitSedenionSphere :=
  ⟨problem_8_8_obstructionPoint, problem_8_8_obstructionPoint_mem_unitSedenionSphere⟩

/-- Problem 8-8: the sedenionic left-multiplication family has an explicit nontrivial relation at
the unit sedenion coming from the zero-divisor pair. -/
theorem problem_8_8_linearRelation :
    problem_8_8_vectorField 2 problem_8_8_obstructionPoint +
        problem_8_8_vectorField 9 problem_8_8_obstructionPoint = 0 := by
  unfold problem_8_8_obstructionPoint
  rw [problem_8_8_vectorField_apply, problem_8_8_vectorField_apply, ← sedenionMul_add_left,
    sedenionMul_smul_right]
  simpa [problem_8_8_leftZeroDivisor, problem_8_8_rightZeroDivisor] using
    problem_8_8_zeroDivisor

/-- Problem 8-8: at the explicit unit zero-divisor witness, the fifteen left-multiplication fields
are not linearly independent. -/
theorem problem_8_8_vectorField_not_linearIndependent :
    ¬ LinearIndependent ℝ
      (fun i : Fin 15 ↦ problem_8_8_vectorField i (problem_8_8_obstructionUnit : 𝕊)) := by
  sorry

section problem_8_8_sphereFrameObstruction

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 15)) M]
variable [IsManifold (𝓡 15) ∞ M]
variable {f : M → 𝕊} {p₀ : M}
variable {e : Fin 15 → (p : M) → TangentSpace (𝓡 15) p}

/-- Problem 8-8: any tangent-bundle realization of the sedenionic left-multiplication family
fails pointwise linear independence at the explicit obstruction point once its ambient pushforward
agrees there with the sedenionic left-multiplication fields and is injective there. The local-frame
obstruction is the immediate corollary via `IsLocalFrameOn.linearIndependent`. -/
theorem problem_8_8_not_linearIndependent_of_mfderiv_eq
    (hp₀ : f p₀ = problem_8_8_obstructionPoint)
    (hinj :
      Function.Injective
        (mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀))
    (he : ∀ i : Fin 15,
      mfderiv (𝓡 15) 𝓘(ℝ, 𝕊) f p₀ (e i p₀) = problem_8_8_vectorField i (f p₀)) :
    ¬ LinearIndependent ℝ (fun i : Fin 15 ↦ e i p₀) := by
  sorry

end problem_8_8_sphereFrameObstruction

end

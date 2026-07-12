import Mathlib
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_8
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_9
import SmoothManifolds_Lee_2012.Chap03.Sec03_20.Problem_3_4
import SmoothManifolds_Lee_2012.Chap08.Sec08_63.Problem_8_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold Torus

-- Semantic search note: `lean_leansearch` is unavailable in this environment, so the domain
-- owners were checked directly against mathlib's `GroupLieAlgebra` / `AddGroupLieAlgebra` APIs,
-- the canonical tangent-space owner `NormedSpace.fromTangentSpace`, the project bridge
-- from `Problem_3_4`, and the chapter owner-level `IsLieAbelian` instances on `GroupLieAlgebra`
-- and `AddGroupLieAlgebra` over commutative Lie groups.

/- Example 8.40 (1): for Euclidean space `ℝⁿ` viewed as a Lie group under addition, the Lie
algebra is identified with `ℝⁿ` itself by the canonical tangent-space owner at the origin. -/
section

variable (n : ℕ)

#check
  ((NormedSpace.fromTangentSpace (0 : EuclideanSpace ℝ (Fin n))).toLinearEquiv :
    AddGroupLieAlgebra (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin n))

end

/- Example 8.40 (2): Euclidean space is an abelian additive Lie group, so its Lie algebra is
abelian by the canonical `IsLieAbelian` instance on `AddGroupLieAlgebra`. -/
section

variable (n : ℕ)

#synth
  IsLieAbelian
    (AddGroupLieAlgebra (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)))

end

/- Example 8.40 (3): the Lie algebra of the circle group `S¹` is identified with `ℝ` by
differentiating the standard chart at the identity; this reuses the canonical tangent-fiber
identification from Problem 3-4. -/
#check
  (circleTangentFiberContinuousLinearEquiv.toLinearEquiv :
    GroupLieAlgebra (𝓡 1) Circle ≃ₗ[ℝ] ℝ)

/- Example 8.40 (4): the circle is a commutative Lie group, so its Lie algebra is abelian by the
canonical `IsLieAbelian` instance on `GroupLieAlgebra`. -/
#check (inferInstance : IsLieAbelian (GroupLieAlgebra (𝓡 1) Circle))

section

variable (n : ℕ)

local notation "TnModel" => ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)
local notation "TnFiber" => ModelPi (fun _ : Fin n ↦ EuclideanSpace ℝ (Fin 1))

local instance : AddCommMonoid TnFiber :=
  inferInstanceAs (AddCommMonoid (Fin n → EuclideanSpace ℝ (Fin 1)))

local instance : NormedAddCommGroup TnFiber :=
  inferInstanceAs (NormedAddCommGroup (Fin n → EuclideanSpace ℝ (Fin 1)))

local instance : NormedSpace ℝ TnFiber :=
  inferInstanceAs (NormedSpace ℝ (Fin n → EuclideanSpace ℝ (Fin 1)))

/-- Example 8.40 (5): for the `n`-torus `𝕋ⁿ = (S¹)^n`, the Lie algebra is identified with `ℝⁿ`
through the tangent-space model at the identity. -/
def torus_group_lie_algebra_equiv_euclidean :
    GroupLieAlgebra TnModel (𝕋^{n}) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  let e₁ :
      GroupLieAlgebra TnModel (𝕋^{n}) ≃L[ℝ]
        TnFiber :=
    ((mdifferentiable_chart (1 : 𝕋^{n})).mfderiv
      (mem_chart_source TnFiber (1 : 𝕋^{n}))).trans
      (NormedSpace.fromTangentSpace ((chartAt TnFiber (1 : 𝕋^{n})) (1 : 𝕋^{n})))
  let e₂ : TnFiber ≃L[ℝ] Fin n → ℝ :=
    ContinuousLinearEquiv.piCongrRight fun _ ↦
      (EuclideanSpace.equiv (Fin 1) ℝ).trans
        (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
  let e₃ : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  ((e₁.trans e₂).trans e₃).toLinearEquiv

/- Example 8.40 (6): the `n`-torus is a commutative Lie group, so its Lie algebra is abelian by
the canonical `IsLieAbelian` instance on `GroupLieAlgebra`. -/
#check (inferInstance : IsLieAbelian (GroupLieAlgebra TnModel (𝕋^{n})))

end

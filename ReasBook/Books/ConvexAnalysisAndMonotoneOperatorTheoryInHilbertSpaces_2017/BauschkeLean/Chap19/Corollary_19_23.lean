import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import BauschkeLean.Chap19.Remark_19_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators InnerProductSpace

universe u

namespace ERealFunction

section EqualityConstraints

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {m : ℕ}

local notation "EqualitySpace" => EuclideanSpace ℝ (Fin m)

attribute [local instance] Classical.propDecidable

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

section Basic

/-- The continuous linear map `x ↦ (⟪x, u_i⟫)_i` attached to a finite family of equality
constraints. -/
def equalityCoordinateMap (u : Fin m → H) : H →L[ℝ] EqualitySpace :=
  ((EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (u i))

-- Proof sketch: unfold `equalityCoordinateMap`, evaluate the `ContinuousLinearMap.pi` coordinate,
-- and rewrite `⟪u_i, x⟫` as `⟪x, u_i⟫` using symmetry of the real inner product.
/-- The `i`th coordinate of `equalityCoordinateMap u x` is `⟪x, u_i⟫`. -/
@[simp] theorem equalityCoordinateMap_apply
    (u : Fin m → H) (x : H) (i : Fin m) :
    equalityCoordinateMap u x i = ⟪x, u i⟫_ℝ := by
  -- Unfold the coordinate map and let `simp` evaluate the `i`th coordinate.
  simp [equalityCoordinateMap, real_inner_comm]

/-- The equality `equalityCoordinateMap u x = η` is exactly the coordinate family
`⟪x, u_i⟫ = η_i`. -/
@[simp] theorem equalityCoordinateMap_eq_iff
    (u : Fin m → H) (x : H) (η : EqualitySpace) :
    equalityCoordinateMap u x = η ↔ ∀ i : Fin m, ⟪x, u i⟫_ℝ = η i := by
  constructor
  · intro h i
    simpa [equalityCoordinateMap_apply] using congrArg (fun z : EqualitySpace ↦ z i) h
  · intro h
    ext i
    exact (equalityCoordinateMap_apply u x i).trans (h i)

/-- Helper for Corollary 19 23: on `ℝ`, the real inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul
    (a b : ℝ) :
    ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

-- Proof sketch: expand the Euclidean inner product coordinatewise and rewrite each scalar
-- inner product as multiplication in `ℝ`.
/-- Helper for Corollary 19 23: the Euclidean inner product on `EqualitySpace` is the coordinate
sum `∑ i, a_i b_i`. -/
theorem inner_equalitySpace_eq_sum
    (a b : EqualitySpace) :
    ⟪a, b⟫_ℝ = ∑ i : Fin m, a i * b i := by
  -- Reduce the `PiLp` inner product to a finite sum over coordinates.
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [real_inner_eq_mul]

/-- Pairing the coordinate equality map with a multiplier gives the expected finite sum. -/
theorem inner_equalityCoordinateMap
    (u : Fin m → H) (x : H) (ν : EqualitySpace) :
    ⟪equalityCoordinateMap u x, ν⟫_ℝ =
      ∑ i : Fin m, ν i * ⟪x, u i⟫_ℝ := by
  -- Rewrite the Euclidean pairing as a coordinate sum and then evaluate each coordinate.
  calc
    ⟪equalityCoordinateMap u x, ν⟫_ℝ =
        ∑ i : Fin m, equalityCoordinateMap u x i * ν i := by
          exact inner_equalitySpace_eq_sum (equalityCoordinateMap u x) ν
    _ = ∑ i : Fin m, ν i * ⟪x, u i⟫_ℝ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [equalityCoordinateMap_apply]
          ring

/-- Helper for Corollary 19 23: pairing the residual `equalityCoordinateMap u x - ρ` with a
multiplier expands coordinatewise. -/
theorem inner_sub_equalityCoordinateMap
    (u : Fin m → H) (x : H) (ρ ν : EqualitySpace) :
    ⟪equalityCoordinateMap u x - ρ, ν⟫_ℝ =
      ∑ i : Fin m, ν i * (⟪x, u i⟫_ℝ - ρ i) := by
  -- Again rewrite the Euclidean pairing as a coordinate sum and simplify each residual term.
  calc
    ⟪equalityCoordinateMap u x - ρ, ν⟫_ℝ =
        ∑ i : Fin m, (equalityCoordinateMap u x - ρ) i * ν i := by
          exact inner_equalitySpace_eq_sum (equalityCoordinateMap u x - ρ) ν
    _ = ∑ i : Fin m, ν i * (⟪x, u i⟫_ℝ - ρ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [PiLp.sub_apply, equalityCoordinateMap_apply]
          ring

variable (f : H → Set.Ioi (⊥ : EReal)) (u : Fin m → H) (ρ : EqualitySpace)

-- Proof sketch: specialize the singleton-indicator composite perturbation to
-- `equalityCoordinateMap u`, then rewrite equality in `EuclideanSpace ℝ (Fin m)`
-- coordinatewise using `equalityCoordinateMap_apply`.
/-- Evaluating the perturbation function gives the piecewise formula from `(19.45)`. -/
@[simp] theorem coordinateEqualityConstraintPerturbation_apply
    (η : EqualitySpace) (x : H) :
    (equalityConstraintPerturbation f (equalityCoordinateMap u) ρ (x, η) : EReal) =
      if ∀ i : Fin m, ⟪x, u i⟫_ℝ = ρ i - η i then
        (f x : EReal)
      else
        ⊤ := by
  -- Convert the bundled equation `equalityCoordinateMap u x = ρ - η` into coordinates.
  simpa [equalityCoordinateMap_eq_iff, PiLp.sub_apply] using
    equalityConstraintPerturbation_apply f (equalityCoordinateMap u) ρ x η

-- Proof sketch: evaluate `perturbationPrimalObjective` at the zero perturbation and rewrite the
-- resulting coordinate equalities using `equalityCoordinateMap_apply`.
/-- The primal problem attached to the perturbation is the minimization of `f(x)` under the
equality constraints `⟪x, u_i⟫ = ρ_i`. -/
theorem perturbationPrimalObjective_coordinateEqualityConstraintPerturbation
    :
    perturbationPrimalObjective (equalityConstraintPerturbation f (equalityCoordinateMap u) ρ) =
      fun x : H ↦
        if ∀ i : Fin m, ⟪x, u i⟫_ℝ = ρ i then
          (f x : EReal)
        else
          ⊤ := by
  funext x
  -- The owner theorem already computes the primal objective; only the coordinate rewrite remains.
  simpa [equalityCoordinateMap_eq_iff] using
    congrFun
      (perturbationPrimalObjective_equalityConstraintPerturbation
        f (equalityCoordinateMap u) ρ) x

-- Proof sketch: specialize Proposition 19.21 (4), rewrite `⟪equalityCoordinateMap u x - ρ, ν⟫`
-- as the finite sum `∑ i ν_i (⟪x, u_i⟫ - ρ_i)`, and keep the `x ∈ effectiveDomain f` branch
-- structure unchanged.
/-- The Lagrangian has the branch formula from `(19.48)`. -/
theorem lagrangian_coordinateEqualityConstraintPerturbation
    (x : H) (ν : EqualitySpace) :
    ℒ[equalityConstraintPerturbation f (equalityCoordinateMap u) ρ] x ν =
      if _hx : x ∈ effectiveDomain f then
        (f x : EReal) +
          (((∑ i : Fin m, ν i * (⟪x, u i⟫_ℝ - ρ i)) : ℝ) : EReal)
      else
        ⊤ := by
  by_cases hx : x ∈ effectiveDomain f
  · -- On the effective domain, only the residual pairing needs to be rewritten coordinatewise.
    simpa [inner_sub_equalityCoordinateMap, hx] using
      lagrangian_equalityConstraintPerturbation f (equalityCoordinateMap u) ρ x ν
  · -- Outside the effective domain, both formulas are `⊤`.
    simpa [hx] using
      lagrangian_equalityConstraintPerturbation f (equalityCoordinateMap u) ρ x ν

end Basic

section ProductL2Ambient

-- Proof sketch: specialize Proposition 19.21 (1) to the continuous linear map
-- `equalityCoordinateMap u`. The hypothesis `ρ ∈ equalityCoordinateMap u '' effectiveDomain f`
-- is exactly the coordinate version of the feasibility assumption in the corollary.
/-- Corollary 19 23: if `f ∈ Γ₀(H)` and the constraint vector `ρ` is attained by
`x ↦ (⟪x, u_i⟫)_i` on `effectiveDomain f`, then the perturbation function from `(19.45)` belongs
to `Γ₀(H × ℝ^m)`. -/
theorem coordinateEqualityConstraintPerturbation_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (u : Fin m → H) (ρ : EqualitySpace)
    (hρ : ρ ∈ equalityCoordinateMap u '' effectiveDomain f) :
    equalityConstraintPerturbation f (equalityCoordinateMap u) ρ ∈ Γ₀(H × EqualitySpace) := by
  simpa using equalityConstraintPerturbation_mem_gammaZero hf (equalityCoordinateMap u) ρ hρ

end ProductL2Ambient

section CompleteDuality

variable [CompleteSpace H]
variable (u : Fin m → H)

-- Proof sketch: the adjoint of the coordinate map is the sum of the adjoints of its coordinate
-- functionals, and the adjoint of `x ↦ ⟪x, u_i⟫` is `t ↦ t • u_i`.
/-- The adjoint of the coordinate equality map is the finite linear combination
`ν ↦ ∑ i, ν_i u_i`. -/
theorem equalityCoordinateMap_adjoint_apply
    (ν : EqualitySpace) :
    (equalityCoordinateMap u).adjoint ν = ∑ i : Fin m, ν i • u i := by
  -- Characterize the adjoint by testing against an arbitrary vector `x`.
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, inner_sum]
  calc
    ⟪equalityCoordinateMap u x, ν⟫_ℝ =
        ∑ i : Fin m, ν i * ⟪x, u i⟫_ℝ := inner_equalityCoordinateMap u x ν
    _ = ∑ i : Fin m, ⟪x, ν i • u i⟫_ℝ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [real_inner_smul_right]

variable (f : H → Set.Ioi (⊥ : EReal)) (ρ : EqualitySpace)

-- Proof sketch: apply Proposition 19.21 (3), compute the adjoint of `equalityCoordinateMap u`
-- using `equalityCoordinateMap_adjoint_apply`, and rewrite the Euclidean inner product with
-- `inner_equalitySpace_eq_sum`.
/-- The dual problem is the minimization of the explicit finite-dimensional objective from
`(19.47)`. -/
theorem perturbationDualObjective_coordinateEqualityConstraintPerturbation
    :
    perturbationDualObjective (equalityConstraintPerturbation f (equalityCoordinateMap u) ρ) =
      fun ν : EqualitySpace ↦
        f.asEReal∗ (-∑ i : Fin m, ν i • u i) + (((∑ i : Fin m, ν i * ρ i) : ℝ) : EReal) := by
  -- The owner theorem already gives the dual formula; rewrite the adjoint and Euclidean pairing.
  simpa [equalityCoordinateMap_adjoint_apply, inner_equalitySpace_eq_sum] using
    perturbationDualObjective_equalityConstraintPerturbation
      (L := equalityCoordinateMap u) (r := ρ) f

variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (ρ : EqualitySpace)
variable (hρ : ρ ∈ equalityCoordinateMap u '' effectiveDomain f)
variable
    (hμ :
      ∃ μ : ℝ,
        sInf
            (Set.range
              (perturbationPrimalObjective
                (equalityConstraintPerturbation f (equalityCoordinateMap u) ρ))) = μ ∧
          sInf
              (Set.range
                (perturbationDualObjective
                  (equalityConstraintPerturbation f (equalityCoordinateMap u) ρ))) =
            -μ)

include ρ hf hρ hμ

-- Proof sketch: specialize Proposition 19.21 (5) to `L = equalityCoordinateMap u`, rewrite
-- `-L.adjoint ν̄` via `equalityCoordinateMap_adjoint_apply`, and expand the constraint
-- `L x̄ = ρ` coordinatewise using `equalityCoordinateMap_apply`.
/-- Under strong duality, a pair `(x̄, ν̄)` is a saddle point of the Lagrangian if and only if
`-∑ i ν̄_i u_i ∈ ∂ f(x̄)` and `⟪x̄, u_i⟫ = ρ_i` for every coordinate. -/
theorem isSaddlePointOn_lagrangian_coordinateEqualityConstraintPerturbation_iff
    (xbar : H) (νbar : EqualitySpace) :
    IsSaddlePointOn (Set.univ : Set H)
      (Set.univ : Set EqualitySpace)
      (ℒ[equalityConstraintPerturbation f (equalityCoordinateMap u) ρ]) xbar νbar ↔
      -∑ i : Fin m, νbar i • u i ∈ (∂ f) xbar ∧
        ∀ i : Fin m, ⟪xbar, u i⟫_ℝ = ρ i := by
  -- Rewrite the general saddle-point criterion into coordinate form.
  simpa [equalityCoordinateMap_adjoint_apply, equalityCoordinateMap_eq_iff] using
    isSaddlePointOn_lagrangian_equalityConstraintPerturbation_iff
      (L := equalityCoordinateMap u) (r := ρ) hf hρ hμ xbar νbar

-- Proof sketch: after specializing Proposition 19.21 to the coordinate map, apply the canonical
-- owner theorem for the primal solution conclusion to the perturbation
-- `equalityConstraintPerturbation f (equalityCoordinateMap u) ρ`.
/-- The primal component of a saddle point solves the constrained minimization problem `(19.46)`. -/
theorem
    mem_argmin_perturbationPrimalObjective_of_coordinateEqualityConstraintPerturbation_isSaddlePoint
    {xbar : H} {νbar : EqualitySpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set EqualitySpace)
        (ℒ[equalityConstraintPerturbation f (equalityCoordinateMap u) ρ]) xbar νbar) :
    xbar ∈ Argmin (perturbationPrimalObjective
      (equalityConstraintPerturbation f (equalityCoordinateMap u) ρ)) := by
  -- This is exactly the owner theorem specialized to the coordinate map.
  simpa using
 mem_argmin_perturbationPrimalObjective_of_isSaddlePointOn_lagrangian_equalityConstraintPerturbation
      f
      (equalityCoordinateMap u)
      ρ
      hsaddle

-- Proof sketch: apply
-- `mem_argmin_of_isSaddlePointOn_lagrangian_equalityConstraintPerturbation`
-- to the coordinate map `equalityCoordinateMap u`, then rewrite
-- `⟪equalityCoordinateMap u x, ν̄⟫` as `∑ i ν̄_i ⟪x, u_i⟫` using
-- `inner_equalityCoordinateMap`.
/-- Corollary 19.23 `(19.50)`: the primal component of a saddle point minimizes the explicit
affine objective `x ↦ f(x) + ∑ i ν_i ⟪x, u_i⟫`. -/
theorem mem_argmin_coordinateAffineFormula_of_isSaddlePoint
    {xbar : H} {νbar : EqualitySpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set EqualitySpace)
        (ℒ[equalityConstraintPerturbation f (equalityCoordinateMap u) ρ]) xbar νbar) :
    xbar ∈ Argmin
      (fun x : H ↦
        (f x : EReal) +
          (((∑ i : Fin m, νbar i * ⟪x, u i⟫_ℝ) : ℝ) : EReal)) := by
  -- Only the pairing term needs to be rewritten into the explicit coordinate sum.
  simpa [inner_equalityCoordinateMap] using
    mem_argmin_of_isSaddlePointOn_lagrangian_equalityConstraintPerturbation
      f
      (equalityCoordinateMap u)
      ρ
      hsaddle

end CompleteDuality

end EqualityConstraints

end ERealFunction

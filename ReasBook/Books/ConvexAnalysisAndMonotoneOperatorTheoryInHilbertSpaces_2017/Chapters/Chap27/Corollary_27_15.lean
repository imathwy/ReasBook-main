import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap19.Corollary_19_23
import BauschkeLean.Chap27.Proposition_27_14

noncomputable section

open scoped BigOperators InnerProductSpace

universe u

namespace ERealFunction

section EqualityConstraints

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {m : ℕ}

local notation "EqualitySpace" => EuclideanSpace ℝ (Fin m)

-- Semantic recall note: this item is a bridge/view specialization of Proposition 27.14 to the
-- Chapter 19 coordinate map `equalityCoordinateMap`.

/-- The textbook coordinate constraint set is the linear fiber of `equalityCoordinateMap`. -/
theorem coordinateEqualityConstraintSet_eq_preimage_singleton
    (u : Fin m → H) (ρ : EqualitySpace) :
    ({x : H | ∀ i : Fin m, ⟪x, u i⟫_ℝ = ρ i} : Set H) =
      equalityCoordinateMap u ⁻¹' ({ρ} : Set EqualitySpace) := by
  ext x
  simp [equalityCoordinateMap_eq_iff]

variable [CompleteSpace H]

/-- Pairing `x` with the adjoint multiplier from `equalityCoordinateMap` gives the explicit finite
sum `∑ i, vbar i * ⟪x, u_i⟫`. -/
theorem inner_adjoint_equalityCoordinateMap
    (u : Fin m → H) (x : H) (vbar : EqualitySpace) :
    ⟪x, (equalityCoordinateMap u).adjoint vbar⟫_ℝ =
      ∑ i : Fin m, vbar i * ⟪x, u i⟫_ℝ := by
  calc
    ⟪x, (equalityCoordinateMap u).adjoint vbar⟫_ℝ = ⟪equalityCoordinateMap u x, vbar⟫_ℝ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ∑ i : Fin m, vbar i * ⟪x, u i⟫_ℝ := inner_equalityCoordinateMap u x vbar

/-- Corollary 27.15 (1): the coordinate-equality specialization of Proposition 27.14. The source
assumes a positive number of constraints, but that positivity hypothesis is redundant for the
canonical linear-fiber statement. -/
theorem mem_argmin_coordinate_equality_constraints_iff_exists_neg_sum_smul_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {u : Fin m → H} {ρ : EqualitySpace}
    (hri : ρ ∈ Set.relativeInterior (equalityCoordinateMap u '' effectiveDomain f))
    {xbar : H} :
    xbar ∈ Argmin[({x : H | ∀ i : Fin m, ⟪x, u i⟫_ℝ = ρ i} : Set H)] f.asEReal ↔
      (∀ i : Fin m, ⟪xbar, u i⟫_ℝ = ρ i) ∧
        ∃ vbar : EqualitySpace, -∑ i : Fin m, vbar i • u i ∈ (∂ f) xbar := by
  have himage_convex : Convex ℝ (equalityCoordinateMap u '' effectiveDomain f) := by
    simpa using hf.2.convex_effectiveDomain.linear_image (equalityCoordinateMap u).toLinearMap
  have hsri : ρ ∈ Set.strongRelativeInterior (equalityCoordinateMap u '' effectiveDomain f) := by
    rw [strongRelativeInterior_eq_relativeInterior_of_finiteDimensional himage_convex]
    simpa using hri
  simpa [coordinateEqualityConstraintSet_eq_preimage_singleton, equalityCoordinateMap_eq_iff,
    equalityCoordinateMap_adjoint_apply] using
    (mem_argminOn_linear_fiber_iff_exists_neg_adjoint_mem_subdifferential
      hf (equalityCoordinateMap u) hsri)

/-- Corollary 27.15 (2): every multiplier vector `vbar` satisfying the coordinate subgradient
condition from clause `(1)` makes `xbar` a minimizer of the affine objective
`x ↦ f x + ∑ i, vbar i * ⟪x, u_i⟫`. The feasibility data from clause `(1)` and the target value
`ρ` are redundant for this affine-tilt conclusion, so they are omitted. -/
theorem mem_argmin_coordinate_affine_objective_of_neg_sum_smul_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} {u : Fin m → H} {xbar : H} {vbar : EqualitySpace}
    (hsub : -∑ i : Fin m, vbar i • u i ∈ (∂ f) xbar) :
    xbar ∈ Argmin
      (fun x : H ↦
        (f x : EReal) + (((∑ i : Fin m, vbar i * ⟪x, u i⟫_ℝ) : ℝ) : EReal)) := by
  have hsub' : -(equalityCoordinateMap u).adjoint vbar ∈ (∂ f) xbar := by
    simpa [equalityCoordinateMap_adjoint_apply] using hsub
  have harg :
      xbar ∈ Argmin
        (fun x : H ↦
          (f x : EReal) + (⟪x, (equalityCoordinateMap u).adjoint vbar⟫_ℝ : EReal)) := by
    exact mem_argmin_affineObjective_of_neg_mem_subdifferential hsub'
  simpa [inner_adjoint_equalityCoordinateMap] using harg

/-- Corollary 27.15 (3): if `f` is Gâteaux differentiable at `xbar`, then the multiplier
condition from clause `(1)` is equivalently the explicit gradient identity
`gradf = -∑ i, vbar i • u i`. As in clause `(1)`, the positivity hypothesis on the number of
constraints is redundant and omitted. -/
theorem
    mem_argmin_coordinate_equality_constraints_iff_exists_eq_neg_sum_smul_of_hasGateauxDerivativeAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {u : Fin m → H} {ρ : EqualitySpace}
    (hri : ρ ∈ Set.relativeInterior (equalityCoordinateMap u '' effectiveDomain f))
    {xbar gradf : H} (hxbar : xbar ∈ effectiveDomain f)
    (hgrad :
      HasGateauxDerivativeAt
        (fun x : H ↦ (f x : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H gradf) xbar) :
    xbar ∈ Argmin[({x : H | ∀ i : Fin m, ⟪x, u i⟫_ℝ = ρ i} : Set H)] f.asEReal ↔
      (∀ i : Fin m, ⟪xbar, u i⟫_ℝ = ρ i) ∧
        ∃ vbar : EqualitySpace, gradf = -∑ i : Fin m, vbar i • u i := by
  have himage_convex : Convex ℝ (equalityCoordinateMap u '' effectiveDomain f) := by
    simpa using hf.2.convex_effectiveDomain.linear_image (equalityCoordinateMap u).toLinearMap
  have hsri : ρ ∈ Set.strongRelativeInterior (equalityCoordinateMap u '' effectiveDomain f) := by
    rw [strongRelativeInterior_eq_relativeInterior_of_finiteDimensional himage_convex]
    simpa using hri
  simpa [coordinateEqualityConstraintSet_eq_preimage_singleton, equalityCoordinateMap_eq_iff,
    equalityCoordinateMap_adjoint_apply] using
    (mem_argminOn_linear_fiber_iff_exists_eq_neg_adjoint_of_hasGateauxDerivativeAt
      hf (equalityCoordinateMap u) hsri hxbar hgrad)

end EqualityConstraints

end ERealFunction

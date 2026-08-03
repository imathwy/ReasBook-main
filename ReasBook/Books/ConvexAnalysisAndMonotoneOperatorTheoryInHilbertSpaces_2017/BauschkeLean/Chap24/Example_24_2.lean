import BauschkeLean.Chap02.Definition_2_23
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap17.Proposition_17_36
import BauschkeLean.Chap20.Proposition_20_24
import BauschkeLean.Chap24.Proposition_24_1
import BauschkeLean.Chap12.ProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped ContinuousLinearMap InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Source/core/bridge triage:
-- `source-facing`: Example 24.2 owns the quadratic-affine functional
--   `x ↦ (1 / 2) ⟪L x, x⟫_ℝ + ⟪x, u⟫_ℝ + α`.
-- `core/canonical`: the surrounding chapter reuses the canonical `Γ₀(H)`, `IsProxPoint`,
--   and `proximityOperator` surfaces from `Chap12/ProximityOperator.lean`.
-- `bridge/view`: the derivative companion below exposes the Chapter 24 gradient equation in the
--   form required by Proposition 24.1, and the proximal-point bridge packages the resolvent
--   formula without fixing a sorry-backed `Γ₀` witness inside the public theorem statement.

-- Semantic recall note: `lean_leansearch` did not surface a usable local owner for this quadratic
-- prox formula, so the statement follows the project's canonical `Γ₀(H)` / `IsProxPoint`
-- surface from `Chap12/ProximityOperator.lean` and the Chapter 24 gradient characterization in
-- `Proposition_24_1.lean`.

/-- The quadratic-affine `Γ₀(H)` owner from Example 24.2, namely
`x ↦ (1 / 2) ⟪L x, x⟫ + ⟪x, u⟫ + α`. -/
def example_24_2_function (L : H →L[ℝ] H) (u : H) (α : ℝ) :
    H → Set.Ioi (⊥ : EReal) :=
  (fun x ↦ (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ + ⟪x, u⟫_ℝ + α).toEReal

/-- Coercing the quadratic-affine owner back to `EReal` recovers its defining real expression. -/
@[simp] theorem example_24_2_function_apply (L : H →L[ℝ] H) (u x : H) (α : ℝ) :
    (example_24_2_function L u α x : EReal) =
      (((1 / 2 : ℝ) * ⟪L x, x⟫_ℝ + ⟪x, u⟫_ℝ + α : ℝ) : EReal) := by
  simp [example_24_2_function]

/-- The real-valued representative of Example 24.2 is exactly the defining quadratic-affine
expression. -/
@[simp] theorem example_24_2_function_toReal (L : H →L[ℝ] H) (u x : H) (α : ℝ) :
    (example_24_2_function L u α x : EReal).toReal =
      (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ + ⟪x, u⟫_ℝ + α := by
  simpa using
    (EReal.toReal_coe ((1 / 2 : ℝ) * ⟪L x, x⟫_ℝ + ⟪x, u⟫_ℝ + α))

/-- The quadratic-affine owner from Example 24.2 is finite everywhere. -/
theorem effectiveDomain_example_24_2_function_eq_univ
    (L : H →L[ℝ] H) (u : H) (α : ℝ) :
    effectiveDomain (example_24_2_function L u α) = Set.univ := by
  ext x
  simp [example_24_2_function]

/-- Every point belongs to the interior effective domain of the quadratic-affine owner. -/
theorem mem_interior_effectiveDomain_example_24_2_function
    (L : H →L[ℝ] H) (u x : H) (α : ℝ) :
    x ∈ interior (effectiveDomain (example_24_2_function L u α)) := by
  simp [effectiveDomain_example_24_2_function_eq_univ]

/-- The real-valued representative of the quadratic-affine owner has Gâteaux gradient `L x + u`
when the quadratic part is symmetric. -/
theorem hasGateauxDerivativeAt_example_24_2_function_toReal
    [CompleteSpace H]
    (L : H →L[ℝ] H) (hL_symm : L.toLinearMap.IsSymmetric) (u x : H) (α : ℝ) :
    HasGateauxDerivativeAt
      (fun y ↦ (example_24_2_function L u α y : EReal).toReal)
      (toDualMap ℝ H (L x + u)) x := by
  -- Differentiate the normalized quadratic-affine model from Example 2.57, then rescale it.
  have hquad :
      HasGradientAt
        (quadratic_affine_functional L (-(2 : ℝ) • u))
        (((L + L.adjoint) x) - (-(2 : ℝ) • u)) x := by
    simpa using quadratic_affine_functional_hasGradientAt L (-(2 : ℝ) • u) x
  have hscaled :
      HasGradientAt
        (fun y ↦ α + (1 / 2 : ℝ) * quadratic_affine_functional L (-(2 : ℝ) • u) y)
        ((1 / 2 : ℝ) • ((((L + L.adjoint) x) - (-(2 : ℝ) • u)))) x := by
    have hscaled' := hquad.hasFDerivAt.const_smul (1 / 2 : ℝ)
    have hshifted := hscaled'.const_add α
    simpa using hshifted.hasGradientAt
  have howner :
      HasGradientAt
        (fun y ↦ (example_24_2_function L u α y : EReal).toReal)
        ((1 / 2 : ℝ) • ((((L + L.adjoint) x) - (-(2 : ℝ) • u)))) x := by
    -- Rewrite the scaled quadratic-affine model back to the source-facing owner.
    convert hscaled using 1
    funext y
    rw [example_24_2_function_toReal]
    simp [quadratic_affine_functional, real_inner_smul_right]
    ring
  have hgrad_eq :
      (1 / 2 : ℝ) • L x + (1 / 2 : ℝ) • (ContinuousLinearMap.adjoint L) x + u = L x + u := by
    -- Collapse the symmetrized gradient under the symmetry hypothesis.
    have hhalf (v : H) : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = v := by
      calc
        (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • v := by
          rw [← add_smul]
        _ = v := by norm_num
    calc
      (1 / 2 : ℝ) • L x + (1 / 2 : ℝ) • (ContinuousLinearMap.adjoint L) x + u
          = ((1 / 2 : ℝ) • L x + (1 / 2 : ℝ) • L x) + u := by
              rw [hL_symm.clm_adjoint_eq]
      _ = L x + u := by rw [hhalf]
  have howner' :
      HasGradientAt
        (fun y ↦ (example_24_2_function L u α y : EReal).toReal)
        (L x + u) x := by
    have howner_simplified :
        HasGradientAt
          (fun y ↦ (example_24_2_function L u α y : EReal).toReal)
          ((1 / 2 : ℝ) • L x + (1 / 2 : ℝ) • (ContinuousLinearMap.adjoint L) x + u) x := by
      simpa [ContinuousLinearMap.add_apply, sub_eq_add_neg] using howner
    convert howner_simplified using 1
    exact hgrad_eq.symm
  -- Convert the Hilbert-space gradient back to the Gâteaux derivative surface.
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
    howner'.hasFDerivAt.hasGateauxDerivativeAt

section Hilbert

variable [CompleteSpace H]

/-- Helper for Example 24.2: if `L` is monotone, then `Id + L` is `1`-strongly monotone. -/
theorem one_add_isStronglyMonotone_of_isMonotone
    (L : H →L[ℝ] H) (hL_mono : L.toLinearMap.IsMonotone) :
    ((1 : H →L[ℝ] H) + L).toLinearMap.IsStronglyMonotone 1 := by
  refine ⟨by norm_num, ?_⟩
  intro x
  -- The identity contributes `‖x‖²`, and the monotone part contributes a nonnegative defect.
  have hmono : 0 ≤ ⟪L x, x⟫_ℝ := hL_mono x
  calc
    (1 : ℝ) * ‖x‖ ^ 2 = ⟪(1 : H →L[ℝ] H) x, x⟫_ℝ := by
      simp
    _ ≤ ⟪(1 : H →L[ℝ] H) x, x⟫_ℝ + ⟪L x, x⟫_ℝ := by
      linarith
    _ = ⟪(((1 : H →L[ℝ] H) + L) x), x⟫_ℝ := by
      simp [inner_add_left]

/-- In a real Hilbert space, self-adjointness supplies the symmetry hypothesis needed for the
derivative formula above. -/
theorem hasGateauxDerivativeAt_example_24_2_function_toReal_of_isSelfAdjoint
    (L : H →L[ℝ] H) (hL_self : IsSelfAdjoint L) (u x : H) (α : ℝ) :
    HasGateauxDerivativeAt
      (fun y ↦ (example_24_2_function L u α y : EReal).toReal)
      (toDualMap ℝ H (L x + u)) x := by
  simpa using
    hasGateauxDerivativeAt_example_24_2_function_toReal L hL_self.isSymmetric u x α

/-- Example 24.2 (1): if `L : H →L[ℝ] H` is self-adjoint and monotone, `u ∈ H`, and `α ∈ ℝ`,
then the quadratic-affine functional
`x ↦ (1 / 2) ⟪L x, x⟫_ℝ + ⟪x, u⟫_ℝ + α` belongs to `Γ₀(H)`. -/
theorem example_24_2_function_mem_gammaZero
    (L : H →L[ℝ] H) (hL_self : IsSelfAdjoint L) (hL_mono : L.toLinearMap.IsMonotone)
    (u : H) (α : ℝ) :
    example_24_2_function L u α ∈ Γ₀(H) := by
  let φ : H → ℝ := fun x ↦ q[L] x + ⟪x, u⟫_ℝ + α
  have hcont : Continuous φ := by
    -- The quadratic potential and the affine term are both continuous on `H`.
    have hquad : Continuous (q[L]) := ContinuousLinearMap.quadraticPotential_continuous L
    have hlin : Continuous (fun x : H ↦ ⟪x, u⟫_ℝ + α) := by
      exact (continuous_id.inner continuous_const).add continuous_const
    have hsum : Continuous (fun x : H ↦ q[L] x + (⟪x, u⟫_ℝ + α)) := hquad.add hlin
    -- Rewrite the canonical quadratic potential to the source-facing inner-product formula.
    simpa [φ, ContinuousLinearMap.quadraticPotential_apply, real_inner_comm, add_assoc,
      add_left_comm, add_comm] using hsum
  have hlin_conv : _root_.ConvexOn ℝ Set.univ (fun x : H ↦ ⟪x, u⟫_ℝ + α) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    -- The linear part is affine, so the Jensen inequality is an equality.
    apply le_of_eq
    have hreal :
        ⟪a • x + b • y, u⟫_ℝ + α = a * (⟪x, u⟫_ℝ + α) + b * (⟪y, u⟫_ℝ + α) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have hα : α = a * α + b * α := by
        calc
          α = (a + b) * α := by rw [hab, one_mul]
          _ = a * α + b * α := by ring
      calc
        a * ⟪x, u⟫_ℝ + b * ⟪y, u⟫_ℝ + α
            = a * ⟪x, u⟫_ℝ + b * ⟪y, u⟫_ℝ + (a * α + b * α) := by
                conv_lhs => rw [hα]
        _ = a * (⟪x, u⟫_ℝ + α) + b * (⟪y, u⟫_ℝ + α) := by ring
    simpa [smul_eq_mul] using hreal
  have hconv : _root_.ConvexOn ℝ Set.univ φ := by
    -- Add the monotone quadratic potential to the affine perturbation.
    have hquad :
        _root_.ConvexOn ℝ Set.univ (q[L]) :=
      ContinuousLinearMap.quadraticPotential_convexOn_univ_of_isMonotone L hL_mono
    have hsum : _root_.ConvexOn ℝ Set.univ (fun x : H ↦ q[L] x + (⟪x, u⟫_ℝ + α)) :=
      hquad.add hlin_conv
    -- Rewrite the canonical quadratic potential to the source-facing inner-product formula.
    simpa [φ, ContinuousLinearMap.quadraticPotential_apply, real_inner_comm, add_assoc,
      add_left_comm, add_comm] using hsum
  have hφ :
      example_24_2_function L u α = φ.toEReal := by
    -- Rewrite the source owner through the canonical quadratic potential `q[L]`.
    ext x
    simp [φ, example_24_2_function, ContinuousLinearMap.quadraticPotential_apply,
      real_inner_comm]
  rw [hφ]
  exact real_toEReal_mem_gammaZero_of_continuous_convexOn_univ φ hcont hconv

/-- Example 24.2 (2): under the same hypotheses, a point `p` is proximal for
`x ↦ (1 / 2) ⟪L x, x⟫_ℝ + ⟪x, u⟫_ℝ + α` at `x` if and only if it is the affine resolvent value
`(Id + L)⁻¹ (x - u)`. -/
theorem isProxPoint_example_24_2_function_iff_eq_inverse_sub
    (L : H →L[ℝ] H) (hL_self : IsSelfAdjoint L) (hL_mono : L.toLinearMap.IsMonotone)
    (u : H) (α : ℝ) {x p : H} :
    IsProxPoint (example_24_2_function L u α) x p ↔
      p = (((1 : H →L[ℝ] H) + L).inverse) (x - u) := by
  let f := example_24_2_function L u α
  let U : H →L[ℝ] H := (1 : H →L[ℝ] H) + L
  have hf : f ∈ Γ₀(H) := example_24_2_function_mem_gammaZero L hL_self hL_mono u α
  have hp_int : p ∈ interior (effectiveDomain f) :=
    mem_interior_effectiveDomain_example_24_2_function L u p α
  have hgrad :
      HasGateauxDerivativeAt
        (fun y ↦ (f y : EReal).toReal)
        (toDualMap ℝ H (L p + u)) p := by
    simpa [f] using
      hasGateauxDerivativeAt_example_24_2_function_toReal_of_isSelfAdjoint L hL_self u p α
  have hprox_iff :
      p = Prox[f, hf] x ↔ L p + u + p = x := by
    simpa [f] using
      (eq_proximityOperator_iff_gateauxGradient_add_eq
        f hf (x := x) (p := p) (gradf := L p + u) hp_int hgrad)
  have hU_self : IsSelfAdjoint U := by
    -- Self-adjointness is stable under adding the identity.
    refine LinearMap.IsSymmetric.isSelfAdjoint ?_
    intro z w
    calc
      ⟪U z, w⟫_ℝ = ⟪z, w⟫_ℝ + ⟪L z, w⟫_ℝ := by
        simp [U, inner_add_left]
      _ = ⟪z, w⟫_ℝ + ⟪z, L w⟫_ℝ := by
        simpa using congrArg (fun t : ℝ ↦ ⟪z, w⟫_ℝ + t) (hL_self.isSymmetric z w)
      _ = ⟪z, U w⟫_ℝ := by
        simp [U, inner_add_right]
  have hU_strong : U.toLinearMap.IsStronglyMonotone 1 :=
    one_add_isStronglyMonotone_of_isMonotone L hL_mono
  have hU_inv : U.IsInvertible :=
    ContinuousLinearMap.isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  constructor
  · intro hp_prox
    -- First identify `p` with the unique proximal point, then solve the resulting linear equation.
    have hp_eq : p = Prox[f, hf] x := by
      exact eq_proximityOperator_of_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) hp_prox
    have hgrad_eq : L p + u + p = x := hprox_iff.mp hp_eq
    have hU_eq : U p = x - u := by
      -- Move the affine term to the right-hand side to isolate `U p`.
      rw [eq_sub_iff_add_eq]
      simpa [U, ContinuousLinearMap.add_apply, add_assoc, add_left_comm, add_comm] using hgrad_eq
    calc
      p = U.inverse (U p) := by rw [hU_inv.inverse_apply_self]
      _ = U.inverse (x - u) := by rw [hU_eq]
  · intro hp_eq
    -- Rewrite the resolvent identity back to the Chapter 24 gradient equation.
    have hU_eq : U p = x - u := by
      rw [hp_eq, hU_inv.self_apply_inverse]
    have hgrad_eq : L p + u + p = x := by
      have hadd : U p + u = x := by
        exact (eq_sub_iff_add_eq.mp hU_eq)
      simpa [U, ContinuousLinearMap.add_apply, add_assoc, add_left_comm, add_comm] using hadd
    have hp_prox_eq : p = Prox[f, hf] x := hprox_iff.mpr hgrad_eq
    rw [hp_prox_eq]
    exact proximityOperator_isProxPoint f (hasUniqueProxPoint_of_mem_gammaZero f hf) x

/-- Example 24.2 (2): any chosen proximity operator for the quadratic-affine owner agrees with
the affine resolvent `x ↦ (Id + L)⁻¹ (x - u)`. -/
theorem prox_example_24_2_function_eq_inverse_sub
    (L : H →L[ℝ] H) (hL_self : IsSelfAdjoint L) (hL_mono : L.toLinearMap.IsMonotone)
    (u : H) (α : ℝ) (hprox : HasUniqueProxPoint (example_24_2_function L u α)) (x : H) :
    proximityOperator (example_24_2_function L u α) hprox x =
      (((1 : H →L[ℝ] H) + L).inverse) (x - u) := by
  rw [← isProxPoint_example_24_2_function_iff_eq_inverse_sub L hL_self hL_mono u α]
  exact proximityOperator_isProxPoint (example_24_2_function L u α) hprox x

end Hilbert

end

end ERealFunction

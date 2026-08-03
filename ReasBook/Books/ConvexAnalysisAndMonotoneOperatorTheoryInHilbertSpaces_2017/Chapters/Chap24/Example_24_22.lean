import Mathlib
import BauschkeLean.Chap07.Exercise_7_9
import BauschkeLean.Chap24.Example_24_20
import BauschkeLean.Chap24.Proposition_24_11
import BauschkeLean.Chap24.Proposition_24_17
import BauschkeLean.Chap12.Proposition_12_29

open scoped EuclideanSpace InnerProductSpace

namespace ERealFunction

noncomputable section

-- Domain sampling:
-- - primary domain: finite-dimensional proximal calculus for the `ℓ¹` penalty on `ℝ^N`
-- - inspected owners:
--   `EuclideanSpace.lpNorm` from `Chap07/Exercise_7_9.lean`
--   `Set.lpClosedUnitBall` from `Chap07/Exercise_7_9.lean`
--   `weightedCoordinateAbsPenalty` from `Chap24/Proposition_24_17.lean`
--   `directSumCoordinatewiseProx` from `Chap24/Proposition_24_11.lean`
--   `scaledNormKernel` from `Chap12/Definition_12_16.lean`
--   `example_24_20_2_proximityOperator_scaledNorm_real_eq_sign_mul_max` from
--   `Chap24/Example_24_20.lean`
-- - primitive data: the scalar `γ ∈ ℝ₊`
-- - derived API: the source-facing owner `scaledL1Penalty γ = γ ‖·‖_[1]`, its `Γ₀`
--   membership, and the weighted-coordinate/direct-sum bridge lemmas used to prove the proximal
--   formula
-- Source/core/bridge triage:
-- - `source-facing`: Example 24.22 is the constant-weight `γ ‖·‖₁` penalty on `ℝ^N`,
--   together with its coordinatewise soft-threshold formula.
-- - `core/canonical`: the Chapter 7 owner `EuclideanSpace.lpNorm N 1`, written `‖·‖_[1]`.
-- - `bridge/view`: the constant-weight specialization of
--   `weightedCoordinateAbsPenalty` and the transport of `directSumCoordinatewiseProx` along the
--   canonical `lpPiLpₗᵢ` equivalence between `ℓ²(Fin N, ℝ)` and `EuclideanSpace ℝ (Fin N)`.

section Euclidean

variable {N : ℕ}

private abbrev constantWeightVector (γ : NNReal) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm fun _ : Fin N ↦ (γ : ℝ)

/-- Example 24.22 source-facing owner: the scaled `ℓ¹` penalty `x ↦ γ ‖x‖_[1]` on `ℝ^N`. -/
abbrev scaledL1Penalty (γ : NNReal) :
    EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal) :=
  (fun x ↦ (γ : ℝ) * ‖x‖_[1]).toEReal

@[simp] theorem scaledL1Penalty_apply
    (γ : NNReal) (x : EuclideanSpace ℝ (Fin N)) :
    (scaledL1Penalty γ x : EReal) = (((γ : ℝ) * ‖x‖_[1] : ℝ) : EReal) := by
  simp [scaledL1Penalty]

/-- Bridge view: `γ ‖·‖_[1]` is the constant-weight specialization of the coordinatewise
absolute-value penalty from Proposition 24.17. -/
private theorem scaledL1Penalty_apply_eq_weightedCoordinateAbsPenalty_constant
    (γ : NNReal) (x : EuclideanSpace ℝ (Fin N)) :
    (scaledL1Penalty γ x : EReal) =
      (weightedCoordinateAbsPenalty (constantWeightVector γ) x : EReal) := by
  rw [scaledL1Penalty_apply, weightedCoordinateAbsPenalty_apply, EuclideanSpace.lpNorm_apply]
  rw [PiLp.norm_eq_of_L1]
  simp [constantWeightVector, Finset.mul_sum, Real.norm_eq_abs]

/-- Bridge view: transporting `γ ‖·‖_[1]` across the canonical finite direct-sum owner recovers
the constant scalar family `ξ ↦ γ |ξ|` on the `lp` side. -/
private theorem scaledL1Penalty_apply_eq_directSumFunction_scaledNorm
    (γ : NNReal) (x : EuclideanSpace ℝ (Fin N)) :
    (scaledL1Penalty γ x : EReal) =
      (directSumFunction
        (fun _ : Fin N ↦ scaledNormKernel γ)
        ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) : EReal) := by
  rw [scaledL1Penalty_apply_eq_weightedCoordinateAbsPenalty_constant]
  simpa [directSumFunction_apply] using
    (weightedCoordinateAbsPenalty_apply_eq_sum_scaledNormKernel
      (constantWeightVector γ)
      (fun _ : Fin N ↦ γ.2)
      x)

/-- On `ℝ`, the proximity operator of `x ↦ γ ‖x‖` is the soft-threshold map
`x ↦ sign(x) max {|x| - γ, 0}` for every nonnegative `γ`. The positive branch is the
Chapter 14/24 owner, and the zero branch reduces to the identity map. -/
@[simp] theorem proximityOperator_scaledNorm_eq_sign_mul_max
    (γ : NNReal) (x : ℝ) :
    Prox[scaledNormKernel γ, scaledNormKernel_mem_gammaZero γ] x =
      Real.sign x * max (|x| - (γ : ℝ)) 0 := by
  by_cases hγ : γ = 0
  · subst hγ
    let f : ℝ → Set.Ioi (⊥ : EReal) := scaledNormKernel 0
    have hf : f ∈ Γ₀(ℝ) := by
      simpa [f] using (scaledNormKernel_mem_gammaZero 0)
    have hx_argmin : x ∈ Argmin f.asEReal := by
      rw [mem_argmin_iff, isMinOn_univ_iff]
      intro y
      simp [f, scaledNormKernel_apply]
    have hx_fixed : x ∈ Function.fixedPoints (Prox[f, hf]) :=
      (mem_fixedPoints_proximityOperator_iff_mem_argmin_of_mem_gammaZero hf).2 hx_argmin
    rw [Function.mem_fixedPoints_iff] at hx_fixed
    calc
      Prox[f, hf] x = x := hx_fixed
      _ = Real.sign x * max (|x| - (0 : ℝ)) 0 := by
        simp only [sub_zero, max_eq_left (abs_nonneg x)]
        by_cases hx_nonneg : 0 ≤ x
        · by_cases hx_zero : x = 0
          · simp [hx_zero]
          · have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_zero)
            rw [Real.sign_of_pos hx_pos, abs_of_nonneg hx_nonneg]
            simp
        · have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
          rw [Real.sign_of_neg hx_neg, abs_of_neg hx_neg]
          ring
  · let γpos : Set.Ioi (0 : ℝ) := ⟨(γ : ℝ), by
      have hγ_real : (γ : ℝ) ≠ 0 := by
        exact_mod_cast hγ
      exact lt_of_le_of_ne γ.2 (Ne.symm hγ_real)⟩
    have hγ_eq : (⟨(γ : ℝ), γpos.2.le⟩ : NNReal) = γ := by
      ext
      rfl
    simpa [scaledNormKernelOfPos, hγ_eq] using
      congrFun (example_24_20_2_proximityOperator_scaledNorm_real_eq_sign_mul_max γpos) x

/-- Evaluating the transported canonical finite-family proximal map for the constant scalar family
`scaledNormKernel γ` gives the usual soft-threshold formula in each coordinate. -/
@[simp] private theorem directSumCoordinatewiseProx_scaledNorm_apply
    (γ : NNReal) (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    directSumCoordinatewiseProx
        (fun _ : Fin N ↦ scaledNormKernel γ)
        (fun _ : Fin N ↦ scaledNormKernel_mem_gammaZero γ)
        ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) i =
      Real.sign (x i) * max (|x i| - (γ : ℝ)) 0 := by
  rw [directSumCoordinatewiseProx_apply]
  change Prox[scaledNormKernel γ, scaledNormKernel_mem_gammaZero γ]
      (((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) i) =
    Real.sign (((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) i) *
      max (|((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) i| - (γ : ℝ)) 0
  exact
    proximityOperator_scaledNorm_eq_sign_mul_max γ
      (((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) i)

/-- The scaled `ℓ¹` penalty `ξ ↦ γ ‖ξ‖₁` belongs to `Γ₀(ℝ^N)` for every
nonnegative scalar `γ`. -/
theorem scaledL1Penalty_mem_gammaZero (γ : NNReal) :
    scaledL1Penalty γ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := by
  have hEq :
      (scaledL1Penalty γ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)) =
        weightedCoordinateAbsPenalty (constantWeightVector γ) := by
    funext x
    apply Subtype.ext
    exact scaledL1Penalty_apply_eq_weightedCoordinateAbsPenalty_constant γ x
  rw [hEq]
  exact
    weightedCoordinateAbsPenalty_mem_gammaZero
      (constantWeightVector γ)
      (fun _ : Fin N ↦ γ.2)

/-- Bridge view for Example 24.22: the proximity operator of the constant-weight `ℓ¹` penalty is
the Euclidean transport of the canonical finite direct-sum proximal map. -/
theorem example_24_22_proximityOperator_scaledL1Penalty_eq_directSumCoordinatewiseProx
    (γ : NNReal) (x : EuclideanSpace ℝ (Fin N)) :
    let hγ : scaledL1Penalty γ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := scaledL1Penalty_mem_gammaZero γ
    Prox[scaledL1Penalty γ, hγ] x =
      (lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ)
        (directSumCoordinatewiseProx
          (fun _ : Fin N ↦ scaledNormKernel γ)
          (fun _ : Fin N ↦ scaledNormKernel_mem_gammaZero γ)
          ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x)) := by
  let hγ : scaledL1Penalty γ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := scaledL1Penalty_mem_gammaZero γ
  change Prox[scaledL1Penalty γ, hγ] x =
      (lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ)
        (directSumCoordinatewiseProx
          (fun _ : Fin N ↦ scaledNormKernel γ)
          (fun _ : Fin N ↦ scaledNormKernel_mem_gammaZero γ)
          ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x))
  let e : lp (fun _ : Fin N ↦ ℝ) 2 ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
    lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ
  let f : Fin N → ℝ → Set.Ioi (⊥ : EReal) := fun _ : Fin N ↦ scaledNormKernel γ
  let hf : ∀ i, f i ∈ Γ₀(ℝ) := fun _ : Fin N ↦ scaledNormKernel_mem_gammaZero γ
  let F : lp (fun _ : Fin N ↦ ℝ) 2 → Set.Ioi (⊥ : EReal) := directSumFunction f
  have hF : F ∈ Γ₀(lp (fun _ : Fin N ↦ ℝ) 2) :=
    directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf
  let xLp := e.symm x
  let pLp := directSumCoordinatewiseProx f hf xLp
  have hpLp_eq : pLp = Prox[F, hF] xLp := by
    simpa [F, pLp] using (prox_directSumFunction_eq_directSumCoordinatewiseProx f hf xLp).symm
  have hpLp : IsProxPoint F xLp pLp := by
    rw [hpLp_eq]
    simpa [F, xLp] using
      proximityOperator_isProxPoint F
        (hasUniqueProxPoint_of_mem_gammaZero F hF)
        xLp
  have hp :
      IsProxPoint (scaledL1Penalty γ) x (e pLp) := by
    rw [isProxPoint_iff_forall_inner_add_le (scaledL1Penalty γ) hγ.2]
    intro y
    let yLp := e.symm y
    have hvar :=
      (isProxPoint_iff_forall_inner_add_le F hF.2 xLp pLp).1 hpLp yLp
    have hinner :
        ⟪y - e pLp, x - e pLp⟫_ℝ = ⟪yLp - pLp, xLp - pLp⟫_ℝ := by
      simpa [xLp, yLp, e] using
        (e.inner_map_map (yLp - pLp) (xLp - pLp))
    have hpLp_value :
        (scaledL1Penalty γ (e pLp) : EReal) = (F pLp : EReal) := by
      simpa [F, f, pLp, e] using
        scaledL1Penalty_apply_eq_directSumFunction_scaledNorm γ (e pLp)
    have hy_value :
        (F yLp : EReal) = (scaledL1Penalty γ y : EReal) := by
      simpa [F, f, yLp, e] using
        (scaledL1Penalty_apply_eq_directSumFunction_scaledNorm γ y).symm
    calc
      (⟪y - e pLp, x - e pLp⟫_ℝ : EReal) + (scaledL1Penalty γ (e pLp) : EReal)
          = (⟪yLp - pLp, xLp - pLp⟫_ℝ : EReal) + (F pLp : EReal) := by
                rw [hinner, hpLp_value]
      _ ≤ (F yLp : EReal) := hvar
      _ = (scaledL1Penalty γ y : EReal) := hy_value
  have hprox :
      e pLp = Prox[scaledL1Penalty γ, hγ] x :=
    eq_proximityOperator_of_isProxPoint
      (scaledL1Penalty γ)
      (hasUniqueProxPoint_of_mem_gammaZero (scaledL1Penalty γ) hγ)
      hp
  simpa [pLp, e] using hprox.symm

/-- Example 24.22: if `ℋ = ℝ^N`, `γ ∈ ℝ_+`, and `x = (ξᵢ)ᵢ`, then
`Prox_(γ ‖·‖_[1])(x) = (sign(ξᵢ) max {|ξᵢ| - γ, 0})ᵢ`. -/
theorem example_24_22_proximityOperator_scaledL1Penalty_eq_coordinatewise_sign_mul_max
    (γ : NNReal) (x : EuclideanSpace ℝ (Fin N)) :
    let hγ : scaledL1Penalty γ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := scaledL1Penalty_mem_gammaZero γ
    Prox[scaledL1Penalty γ, hγ] x =
      (EuclideanSpace.equiv (Fin N) ℝ).symm
        (fun i ↦ Real.sign (x i) * max (|x i| - (γ : ℝ)) 0) := by
  let hγ : scaledL1Penalty γ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := scaledL1Penalty_mem_gammaZero γ
  change Prox[scaledL1Penalty γ, hγ] x =
      (EuclideanSpace.equiv (Fin N) ℝ).symm
        (fun i ↦ Real.sign (x i) * max (|x i| - (γ : ℝ)) 0)
  ext i
  have htransport :
      Prox[scaledL1Penalty γ, hγ] x =
        (lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ)
          (directSumCoordinatewiseProx
            (fun _ : Fin N ↦ scaledNormKernel γ)
            (fun _ : Fin N ↦ scaledNormKernel_mem_gammaZero γ)
            ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x)) := by
    simpa [hγ] using
      example_24_22_proximityOperator_scaledL1Penalty_eq_directSumCoordinatewiseProx γ x
  rw [htransport]
  change directSumCoordinatewiseProx
      (fun _ : Fin N ↦ scaledNormKernel γ)
      (fun _ : Fin N ↦ scaledNormKernel_mem_gammaZero γ)
      ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm x) i =
    Real.sign (x i) * max (|x i| - (γ : ℝ)) 0
  simpa using directSumCoordinatewiseProx_scaledNorm_apply γ x i

/-- In Example 24.22, each coordinate of the proximal point is the scalar soft-threshold value
from Example 24.20. -/
@[simp] theorem example_24_22_proximityOperator_scaledL1Penalty_eq_coordinatewise_sign_mul_max_apply
    (γ : NNReal) (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    let hγ : scaledL1Penalty γ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := scaledL1Penalty_mem_gammaZero γ
    Prox[scaledL1Penalty γ, hγ] x i =
      Real.sign (x i) * max (|x i| - (γ : ℝ)) 0 := by
  let hγ : scaledL1Penalty γ ∈ Γ₀(EuclideanSpace ℝ (Fin N)) := scaledL1Penalty_mem_gammaZero γ
  change Prox[scaledL1Penalty γ, hγ] x i =
      Real.sign (x i) * max (|x i| - (γ : ℝ)) 0
  rw [show Prox[scaledL1Penalty γ, hγ] x =
      (EuclideanSpace.equiv (Fin N) ℝ).symm
        (fun i ↦ Real.sign (x i) * max (|x i| - (γ : ℝ)) 0) by
    simpa [hγ] using
      example_24_22_proximityOperator_scaledL1Penalty_eq_coordinatewise_sign_mul_max γ x]
  rfl

end Euclidean

end

end ERealFunction

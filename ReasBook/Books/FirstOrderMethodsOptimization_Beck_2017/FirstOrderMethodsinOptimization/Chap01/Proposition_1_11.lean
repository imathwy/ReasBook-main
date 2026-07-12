import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_37
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_42

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (ofLp toLp)

noncomputable section

universe u

section

variable {m : ℕ}
variable {E : Fin m → Type u}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, NormedSpace ℝ (E i)]

/-- The coordinatewise pairing functional associated to a family of linear functionals on the
finite product `∏ i : Fin m, E i`. -/
def compositeWeightedL2Pairing
    (v : ∀ i, Module.Dual ℝ (E i)) : Module.Dual ℝ (∀ i, E i) :=
  ∑ i, (v i).comp (LinearMap.proj i)

@[simp] theorem compositeWeightedL2Pairing_apply
    (v : ∀ i, Module.Dual ℝ (E i)) (u : ∀ i, E i) :
    compositeWeightedL2Pairing v u = ∑ i, v i (u i) := by
  simp [compositeWeightedL2Pairing]

/-- The componentwise rescaling that identifies the weighted-product norm with the canonical
`L²` norm on `PiLp (2 : ENNReal) E`. This is the bridge from the source-facing weighted product to
the owner object used by mathlib. -/
def compositeWeightedL2LinearEquivToPiLp (ω : Fin m → Set.Ioi (0 : ℝ)) :
    (∀ i, E i) ≃ₗ[ℝ] PiLp (2 : ENNReal) E where
  toFun u := toLp (2 : ENNReal) (fun i ↦ Real.sqrt (ω i : ℝ) • u i)
  invFun x i := (Real.sqrt (ω i : ℝ))⁻¹ • x i
  left_inv u := by
    ext i
    have hs : Real.sqrt (ω i : ℝ) ≠ 0 := (Real.sqrt_pos.2 (ω i).2).ne'
    simp [hs]
  right_inv x := by
    ext i
    have hs : Real.sqrt (ω i : ℝ) ≠ 0 := (Real.sqrt_pos.2 (ω i).2).ne'
    simp [hs]
  map_add' u w := by
    ext i
    simp [smul_add]
  map_smul' c u := by
    ext i
    simp [smul_smul, mul_comm]

/-- The weighted rescaling bridge has norm equal to the textbook weighted `l_2` formula from
Definition 1.37. -/
theorem norm_compositeWeightedL2LinearEquivToPiLp_eq
    (ω : Fin m → Set.Ioi (0 : ℝ)) (u : ∀ i, E i) :
    ‖compositeWeightedL2LinearEquivToPiLp ω u‖ = compositeWeightedL2Norm ω u :=
  rfl

/-- The owner-side functional on `PiLp (2 : ENNReal) E` corresponding to the weighted-product
pairing after the canonical rescaling bridge. -/
def compositeWeightedL2PiLpPairing
    (ω : Fin m → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    Module.Dual ℝ (PiLp (2 : ENNReal) E) :=
  (compositeWeightedL2Pairing (fun i ↦ (Real.sqrt (ω i : ℝ))⁻¹ • v i)).comp
    (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ E).toLinearEquiv.toLinearMap

@[simp] theorem compositeWeightedL2PiLpPairing_apply
    (ω : Fin m → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) (x : PiLp (2 : ENNReal) E) :
    compositeWeightedL2PiLpPairing ω v x =
      ∑ i, (Real.sqrt (ω i : ℝ))⁻¹ * v i (x i) := by
  simp [compositeWeightedL2PiLpPairing, compositeWeightedL2Pairing_apply]

@[simp] theorem compositeWeightedL2PiLpPairing_apply_bridge
    (ω : Fin m → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) (u : ∀ i, E i) :
    compositeWeightedL2PiLpPairing ω v (compositeWeightedL2LinearEquivToPiLp ω u) =
      compositeWeightedL2Pairing v u := by
  rw [compositeWeightedL2PiLpPairing_apply, compositeWeightedL2Pairing_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs : Real.sqrt (ω i : ℝ) ≠ 0 := (Real.sqrt_pos.2 (ω i).2).ne'
  simp [compositeWeightedL2LinearEquivToPiLp, PiLp.toLp_apply, map_smul, hs]

end

section

variable {m : ℕ}
variable {E : Fin m → Type u}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, NormedSpace ℝ (E i)]
variable [∀ i, FiniteDimensional ℝ (E i)]

-- Proof sketch: once the weighted norm is organized through the induced owner structure, the
-- source weighted unit ball is exactly the closed unit ball for that owner, so the `sSup` formula
-- is the standard unit-ball realization of `dualNorm (compositeWeightedL2PiLpPairing ω v)`.
/-- The source-facing weighted-unit-ball supremum is the unit-ball realization of the dual norm of
`compositeWeightedL2PiLpPairing ω v` on the canonical owner `PiLp (2 : ENNReal) E`. -/
theorem unit_compositeWeightedL2Pairing_sSup_eq_dualNorm_compositeWeightedL2PiLpPairing
    (ω : Fin m → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    sSup ((fun u : ∀ i, E i ↦ |compositeWeightedL2Pairing v u|) ''
      {u | compositeWeightedL2Norm ω u ≤ 1}) =
      dualNorm (compositeWeightedL2PiLpPairing ω v) := sorry

-- Proof sketch: for the upper bound, apply the defining inequality for each factor
-- dual norm and then Cauchy-Schwarz to the weighted sequences
-- `(dualNorm (v i) / sqrt (ω i))` and `(sqrt (ω i) * ‖u i‖)`. For the reverse
-- bound, choose almost-maximizers for each factor dual norm and scale them by
-- `dualNorm (v i) / (ω i * A)`, where `A` is the right-hand side.
/-- Auxiliary bridge: on the canonical owner `PiLp (2 : ENNReal) E`, the transferred
weighted-product pairing has dual norm equal to the square root of the inverse-weighted sum of
the squared factor dual norms. -/
theorem dualNorm_compositeWeightedL2PiLpPairing_eq_sqrt_sum_invWeight_mul_sq
    (ω : Fin m → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    dualNorm (compositeWeightedL2PiLpPairing ω v) =
      √(∑ i, (ω i : ℝ)⁻¹ * dualNorm (v i) ^ (2 : ℕ)) := sorry

-- Proof sketch: combine the owner-level dual-norm formula with the source-facing unit-ball
-- translation through the weighted rescaling bridge.
/-- Proposition 1.11: the supremum of the coordinatewise pairing over the weighted `l_2` unit ball
is the square root of the inverse-weighted sum of the squared factor dual norms. -/
theorem unit_compositeWeightedL2Pairing_sSup_eq_sqrt_sum_invWeight_mul_sq
    (ω : Fin m → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    sSup ((fun u : ∀ i, E i ↦ |compositeWeightedL2Pairing v u|) ''
      {u | compositeWeightedL2Norm ω u ≤ 1}) =
      √(∑ i, (ω i : ℝ)⁻¹ * dualNorm (v i) ^ (2 : ℕ)) := by
  rw [unit_compositeWeightedL2Pairing_sSup_eq_dualNorm_compositeWeightedL2PiLpPairing,
    dualNorm_compositeWeightedL2PiLpPairing_eq_sqrt_sum_invWeight_mul_sq]

end

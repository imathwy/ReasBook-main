import BauschkeLean.Chap08.Proposition_8_6
import BauschkeLean.Chap12.ProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped ERealFunction InnerProductSpace Topology

noncomputable section

universe u

namespace ERealFunction

variable {I : Type u}

local notation "ell2" => lp (fun _ : I ↦ ℝ) 2

-- Domain-style sampling:
-- - primary domain: proximal calculus for separable `Γ₀` penalties on the Hilbert sum `ℓ²(I)`
-- - inspected owners:
--   `hilbertSumFunction` / `⨁ i, ...` from `Chap08/Proposition_8_6.lean`
--   `directSumFunction_coe_eq_hilbertSumFunction` and
--   `directSumFunction_mem_gammaZero_of_forall_mem_gammaZero` from `Chap09/Remark_9_37.lean`
--   `directSumCoordinatewiseProx` from `Chap24/Proposition_24_11.lean`
--   `Prox[_, _]` from `Chap12/ProximityOperator.lean`
-- Source/core/bridge triage:
-- - `source-facing`: the textbook separable penalty `x ↦ ⨁ i, φᵢ(xᵢ)`
--   and its coordinatewise proximal map
-- - `core/canonical`: the arbitrary-index `EReal` owner `hilbertSumFunction`
-- - `bridge/view`: the `Set.Ioi (⊥ : EReal)` packaging needed for the
--   Chapter 12 `Γ₀` and `Prox` APIs; no upstream arbitrary-index owner at
--   that codomain was found

/-- Helper for Proposition 24.12: the arbitrary-index Hilbert sum of coordinate values in
`]-∞,+∞]` still lies in `]-∞,+∞]`. -/
theorem hilbertSum_value_mem_Ioi_bot
    (φ : I → ℝ → Set.Ioi (⊥ : EReal)) (x : ell2) :
    (⨁ i, fun xi ↦ (φ i xi : EReal)) x ∈ Set.Ioi (⊥ : EReal) := sorry

/-- The Hilbert-sum penalty `x ↦ ⨁ i, φᵢ(xᵢ)` on `ℓ²(I)` attached to a family
`φ : I → (ℝ → ]-∞,+∞])`. -/
def hilbertSum
    (φ : I → ℝ → Set.Ioi (⊥ : EReal)) :
    ell2 → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨(⨁ i, fun xi ↦ (φ i xi : EReal)) x, hilbertSum_value_mem_Ioi_bot φ x⟩

/-- Evaluating `hilbertSum φ` gives the textbook Hilbert-sum formula `⨁ i, φᵢ(xᵢ)`. -/
@[simp] theorem hilbertSum_apply
    (φ : I → ℝ → Set.Ioi (⊥ : EReal)) (x : ell2) :
    (hilbertSum φ x : EReal) = (⨁ i, fun xi ↦ (φ i xi : EReal)) x :=
  rfl

/-- The `EReal` coercion of the packaged Hilbert-sum bridge is the canonical owner
`hilbertSumFunction`. -/
@[simp] theorem hilbertSum_asEReal
    (φ : I → ℝ → Set.Ioi (⊥ : EReal)) :
    (hilbertSum φ).asEReal = (⨁ i, fun xi ↦ (φ i xi : EReal)) :=
  rfl

variable (φ : I → ℝ → Set.Ioi (⊥ : EReal))

section CoordinatewiseProx

variable (hφ : ∀ i, φ i ∈ Γ₀(ℝ))

/-- Helper for Proposition 24.12: the coordinatewise proximal values again form an `ℓ²(I)`
vector. -/
theorem hilbertSumCoordinatewiseProx_memℓp
    (x : ell2) :
    Memℓp (fun i ↦ Prox[φ i, hφ i] (x i)) 2 := sorry

/-- The coordinatewise proximal vector for the Hilbert-sum penalty
`x ↦ ⨁ i, φᵢ(xᵢ)`, namely `x ↦ (Prox_{φᵢ}(xᵢ))ᵢ`. -/
def hilbertSumCoordinatewiseProx
    : ell2 → ell2 :=
  fun x ↦
    ⟨fun i ↦ Prox[φ i, hφ i] (x i), hilbertSumCoordinatewiseProx_memℓp φ hφ x⟩

/-- The `i`th coordinate of `hilbertSumCoordinatewiseProx φ hφ x` is `Prox_{φᵢ}(xᵢ)`. -/
@[simp] theorem hilbertSumCoordinatewiseProx_apply
    (x : ell2) (i : I) :
    hilbertSumCoordinatewiseProx φ hφ x i = Prox[φ i, hφ i] (x i) :=
  rfl

end CoordinatewiseProx

section HilbertSum

/-- Proposition 24.12 (1): if each `φᵢ ∈ Γ₀(ℝ)` satisfies `φᵢ ≥ φᵢ(0) = 0`,
then the Hilbert-sum penalty `x ↦ ⨁ i, φᵢ(xᵢ)` belongs to `Γ₀(ℓ²(I))`. -/
theorem hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero
    (hφ : ∀ i, φ i ∈ Γ₀(ℝ))
    (hmin : ∀ i x, (φ i 0 : EReal) ≤ (φ i x : EReal))
    (hzero : ∀ i, (φ i 0 : EReal) = 0)
    : hilbertSum φ ∈ Γ₀(ell2) := sorry

section GammaZero

/-- If the packaged Hilbert-sum penalty is already known to lie in `Γ₀(ℓ²(I))`, then its
proximity operator agrees with the coordinatewise proximal map. -/
theorem prox_hilbertSum_eq_coordinatewise_of_mem_gammaZero
    (hφ : ∀ i, φ i ∈ Γ₀(ℝ))
    (hHilbertSum : hilbertSum φ ∈ Γ₀(ell2))
    (x : ell2) :
    Prox[hilbertSum φ, hHilbertSum] x =
      hilbertSumCoordinatewiseProx φ hφ x := sorry

/-- If the packaged Hilbert-sum penalty is already known to lie in `Γ₀(ℓ²(I))`, then its
proximity operator is weakly sequentially continuous. -/
theorem prox_hilbertSum_tendsto_toWeakSpace_of_mem_gammaZero
    (hHilbertSum : hilbertSum φ ∈ Γ₀(ell2))
    {xSeq : ℕ → ell2} {x : ell2}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ ell2 (xSeq n)) atTop
      (𝓝 (toWeakSpace ℝ ell2 x))) :
    Tendsto
      (fun n ↦
        toWeakSpace ℝ ell2 (Prox[hilbertSum φ, hHilbertSum] (xSeq n)))
      atTop
      (𝓝 <| toWeakSpace ℝ ell2 (Prox[hilbertSum φ, hHilbertSum] x)) :=
  sorry

/-- If the packaged Hilbert-sum penalty already lies in `Γ₀(ℓ²(I))`, then the source-facing
coordinatewise proximal map is weakly sequentially continuous. -/
theorem hilbertSumCoordinatewiseProx_tendsto_toWeakSpace_of_mem_gammaZero
    (hφ : ∀ i, φ i ∈ Γ₀(ℝ))
    (hHilbertSum : hilbertSum φ ∈ Γ₀(ell2))
    {xSeq : ℕ → ell2} {x : ell2}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ ell2 (xSeq n)) atTop
      (𝓝 (toWeakSpace ℝ ell2 x))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ ell2 (hilbertSumCoordinatewiseProx φ hφ (xSeq n)))
      atTop
      (𝓝 <| toWeakSpace ℝ ell2 (hilbertSumCoordinatewiseProx φ hφ x)) := by
  have hEq :
      ∀ x : ell2,
        Prox[hilbertSum φ, hHilbertSum] x = hilbertSumCoordinatewiseProx φ hφ x :=
    prox_hilbertSum_eq_coordinatewise_of_mem_gammaZero φ hφ hHilbertSum
  simpa [hEq] using prox_hilbertSum_tendsto_toWeakSpace_of_mem_gammaZero φ hHilbertSum hx

end GammaZero

/-- Proposition 24.12 (2): for the Hilbert-sum penalty `f = ⨁ i, φᵢ`
on `ℓ²(I)`, the proximity operator acts coordinatewise:
`Prox_f((ξᵢ)ᵢ) = (Prox_{φᵢ}(ξᵢ))ᵢ`. -/
theorem prox_hilbertSum_eq_coordinatewise
    (hφ : ∀ i, φ i ∈ Γ₀(ℝ))
    (hmin : ∀ i x, (φ i 0 : EReal) ≤ (φ i x : EReal))
    (hzero : ∀ i, (φ i 0 : EReal) = 0)
    (x : ell2) :
    Prox[hilbertSum φ,
      hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero φ hφ hmin hzero] x =
      hilbertSumCoordinatewiseProx φ hφ x := by
  have hHilbertSum : hilbertSum φ ∈ Γ₀(ell2) :=
    hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero φ hφ hmin hzero
  simpa [hHilbertSum] using
    prox_hilbertSum_eq_coordinatewise_of_mem_gammaZero φ hφ hHilbertSum x

/-- Proposition 24.12 (3): for the Hilbert-sum penalty `f = ⨁ i, φᵢ`
on `ℓ²(I)`, the proximity operator is weakly sequentially continuous. -/
theorem prox_hilbertSum_tendsto_toWeakSpace
    (hφ : ∀ i, φ i ∈ Γ₀(ℝ))
    (hmin : ∀ i x, (φ i 0 : EReal) ≤ (φ i x : EReal))
    (hzero : ∀ i, (φ i 0 : EReal) = 0)
    {xSeq : ℕ → ell2} {x : ell2}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ ell2 (xSeq n)) atTop
      (𝓝 (toWeakSpace ℝ ell2 x))) :
    Tendsto
      (fun n ↦
        toWeakSpace ℝ ell2
          (Prox[hilbertSum φ,
            hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero φ hφ hmin hzero]
            (xSeq n)))
      atTop
      (𝓝 <| toWeakSpace ℝ ell2
        (Prox[hilbertSum φ,
          hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero φ hφ hmin hzero] x)) := by
  have hHilbertSum : hilbertSum φ ∈ Γ₀(ell2) :=
    hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero φ hφ hmin hzero
  simpa [hHilbertSum] using
    prox_hilbertSum_tendsto_toWeakSpace_of_mem_gammaZero φ hHilbertSum hx

/-- Proposition 24.12 (3), rewritten on the source-facing coordinatewise proximal map:
`x ↦ (Prox_{φᵢ}(xᵢ))ᵢ` is weakly sequentially continuous on `ℓ²(I)`. -/
theorem hilbertSumCoordinatewiseProx_tendsto_toWeakSpace
    (hφ : ∀ i, φ i ∈ Γ₀(ℝ))
    (hmin : ∀ i x, (φ i 0 : EReal) ≤ (φ i x : EReal))
    (hzero : ∀ i, (φ i 0 : EReal) = 0)
    {xSeq : ℕ → ell2} {x : ell2}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ ell2 (xSeq n)) atTop
      (𝓝 (toWeakSpace ℝ ell2 x))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ ell2 (hilbertSumCoordinatewiseProx φ hφ (xSeq n)))
      atTop
      (𝓝 <| toWeakSpace ℝ ell2 (hilbertSumCoordinatewiseProx φ hφ x)) := by
  have hHilbertSum : hilbertSum φ ∈ Γ₀(ell2) :=
    hilbertSum_mem_gammaZero_of_forall_mem_gammaZero_of_min_zero φ hφ hmin hzero
  exact hilbertSumCoordinatewiseProx_tendsto_toWeakSpace_of_mem_gammaZero φ hφ hHilbertSum hx

end HilbertSum

end ERealFunction

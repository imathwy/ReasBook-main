import Mathlib

open scoped BigOperators

noncomputable section

universe u v

namespace Representation

section

variable (K : Type v) {G : Type u} [Field K] [Group G] [Finite G] [Fintype G]

/-- The normalized bilinear pairing on `K`-valued functions on a finite group,
given by `⟨φ, ψ⟩ = (1 / |G|) ∑ s, φ(s⁻¹) ψ(s)`. -/
def groupFunctionPairingOverField (φ ψ : G → K) : K :=
  (Fintype.card G : K)⁻¹ * ∑ s : G, φ s⁻¹ * ψ s

scoped[Representation] notation "⟪" φ ", " ψ "⟫" =>
  groupFunctionPairingOverField _ φ ψ

end

section

variable {K : Type v} {G : Type u} [Field K] [Group G] [Finite G] [Fintype G]

-- Proof sketch: reindex the finite sum by the involution `t ↦ t⁻¹`; because inversion is a
-- permutation of `G`, the averaged sum with `φ(t⁻¹) ψ(t)` equals the averaged sum with
-- `φ(t) ψ(t⁻¹)`.
/-- The normalized pairing can equally be written with inversion on the second factor. -/
theorem groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply
    (φ ψ : G → K) :
    ⟪φ, ψ⟫ = (Nat.card G : K)⁻¹ * ∑ t : G, φ t * ψ t⁻¹ := by
  have hsum : ∑ t : G, φ t⁻¹ * ψ t = ∑ t : G, φ t * ψ t⁻¹ := by
    simpa using Equiv.sum_comp (Equiv.inv G) (fun t : G ↦ φ t * ψ t⁻¹)
  simpa [groupFunctionPairingOverField, Nat.card_eq_fintype_card] using
    congrArg (fun x : K ↦ (Nat.card G : K)⁻¹ * x) hsum

-- Proof sketch: rewrite the first pairing with
-- `groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply` and compare with the defining formula
-- for the second pairing.
/-- The normalized pairing is symmetric. -/
theorem groupFunctionPairing_comm
    (φ ψ : G → K) :
    ⟪φ, ψ⟫ = ⟪ψ, φ⟫ := by
  rw [groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply]
  rw [groupFunctionPairingOverField, Nat.card_eq_fintype_card]
  have hsum : ∑ t : G, φ t * ψ t⁻¹ = ∑ t : G, ψ t⁻¹ * φ t := by
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_comm]
  simpa [Nat.card_eq_fintype_card] using
    congrArg (fun x : K ↦ (Nat.card G : K)⁻¹ * x) hsum

-- Proof sketch: expand the definition of `⟪φ + ψ, χ⟫`, distribute the finite sum over addition,
-- and factor out the common scalar `(Fintype.card G : K)⁻¹`.
/-- The normalized pairing is additive in its left argument. -/
theorem groupFunctionPairing_add_left
    (φ ψ χ : G → K) :
    ⟪φ + ψ, χ⟫ = ⟪φ, χ⟫ + ⟪ψ, χ⟫ := by
  simp [groupFunctionPairingOverField, add_mul, Finset.sum_add_distrib, left_distrib]

-- Proof sketch: expand the definition of `⟪a • φ, ψ⟫`, pull the scalar `a` through the finite
-- sum, and factor it out of the average.
/-- The normalized pairing is homogeneous in its left argument. -/
theorem groupFunctionPairing_smul_left
    (a : K) (φ ψ : G → K) :
    ⟪a • φ, ψ⟫ = a * ⟪φ, ψ⟫ := by
  rw [groupFunctionPairingOverField, groupFunctionPairingOverField]
  simp_rw [Pi.smul_apply]
  calc
    (Fintype.card G : K)⁻¹ * ∑ t : G, a * φ t⁻¹ * ψ t
      = (Fintype.card G : K)⁻¹ * ∑ t : G, a * (φ t⁻¹ * ψ t) := by
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          ring
    _ = (Fintype.card G : K)⁻¹ * (a * ∑ t : G, φ t⁻¹ * ψ t) := by
          rw [← Finset.mul_sum]
    _ = a * ((Fintype.card G : K)⁻¹ * ∑ t : G, φ t⁻¹ * ψ t) := by
          ring

-- Proof sketch: expand the definition of `⟪φ, ψ + χ⟫`, distribute the finite sum over addition,
-- and factor out the common scalar `(Fintype.card G : K)⁻¹`.
/-- The normalized pairing is additive in its right argument. -/
theorem groupFunctionPairing_add_right
    (φ ψ χ : G → K) :
    ⟪φ, ψ + χ⟫ = ⟪φ, ψ⟫ + ⟪φ, χ⟫ := by
  simp [groupFunctionPairingOverField, mul_add, Finset.sum_add_distrib]

-- Proof sketch: expand the definition of `⟪φ, a • ψ⟫`, pull the scalar `a` through the finite
-- sum, and factor it out of the average.
/-- The normalized pairing is homogeneous in its right argument. -/
theorem groupFunctionPairing_smul_right
    (a : K) (φ ψ : G → K) :
    ⟪φ, a • ψ⟫ = a * ⟪φ, ψ⟫ := by
  rw [groupFunctionPairingOverField, groupFunctionPairingOverField]
  simp_rw [Pi.smul_apply]
  calc
    (Fintype.card G : K)⁻¹ * ∑ t : G, φ t⁻¹ * (a * ψ t)
      = (Fintype.card G : K)⁻¹ * ∑ t : G, a * (φ t⁻¹ * ψ t) := by
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          ring
    _ = (Fintype.card G : K)⁻¹ * (a * ∑ t : G, φ t⁻¹ * ψ t) := by
          rw [← Finset.mul_sum]
    _ = a * ((Fintype.card G : K)⁻¹ * ∑ t : G, φ t⁻¹ * ψ t) := by
          ring

end

section

variable (K : Type v) {G : Type u} [Field K] [Group G] [Finite G]
variable [Invertible (Nat.card G : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

open scoped Representation

local instance instFintypeGGroupFunctionPairingCharacter : Fintype G := Fintype.ofFinite G

-- Proof sketch: rewrite the normalized sum using
-- `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`; the invertibility assumption on
-- `(Nat.card G : K)` identifies that canonical owner theorem with Serre's normalized pairing.
/-- The normalized pairing of two characters equals the `K`-dimension of the intertwining space. -/
theorem groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
    (ρ : Representation K G V) (σ : Representation K G W) :
    ⟪ρ.character, σ.character⟫ = Module.finrank K (ρ.IntertwiningMap σ) := by
  simpa [groupFunctionPairingOverField, Nat.card_eq_fintype_card, mul_comm] using
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := σ))

end

end Representation

import LinearRepresentations_Serre_1977.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra

noncomputable section

universe u v w u₁ u₂

namespace Representation

section

variable {K : Type v} [Field K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGRemark2225 : Fintype G := Fintype.ofFinite G

/- Remark 2-2.2-5 uses LinearRepresentations_Serre_1977's complex pairing; the canonical owner in the project is the
field-valued pairing `groupFunctionPairingOverField`, and the bracket notation is the source-facing
surface form. -/
open scoped Representation

/- Layer triage for this remark:
* core/canonical: `groupFunctionPairingOverField`
* source-facing: the symmetric bilinear pairing statements written with `⟪-, -⟫`
* bridge/view: the chapter corollaries on matrix coefficients, restated here in the pairing
  notation. -/

/- Remark 2-2.2-5 first records basic owner-level API for LinearRepresentations_Serre_1977's normalized pairing. Those
canonical statements now live with `groupFunctionPairingOverField` itself:
`groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply`, `groupFunctionPairing_comm`,
`groupFunctionPairing_add_left`, `groupFunctionPairing_smul_left`,
`groupFunctionPairing_add_right`, and `groupFunctionPairing_smul_right`. -/

variable [Invertible (Nat.card G : K)]
variable {V1 : Type w} [AddCommGroup V1] [Module K V1]
variable {V2 : Type u₁} [AddCommGroup V2] [Module K V2]
variable {ι1 : Type u₁} [Fintype ι1]
variable {ι2 : Type u₂} [Fintype ι2]

-- Proof sketch: unfold the canonical pairing owner `groupFunctionPairingOverField`; the result is
-- exactly the vanishing specialization of the canonical averaged-intertwiner bridge
-- `averageMap_linHom_basis_entry_eq`.
open scoped Classical in
/-- The orthogonality relation for matrix coefficients of nonisomorphic irreducible
representations, expressed with the pairing notation. -/
theorem matrixCoefficient_pairing_eq_zero_of_not_isomorphic
    (ρ1 : Representation K G V1) (ρ2 : Representation K G V2)
    [ρ1.IsIrreducible] [ρ2.IsIrreducible]
    (hρ : ¬ Nonempty (ρ1.Equiv ρ2))
    (b1 : Module.Basis ι1 K V1) (b2 : Module.Basis ι2 K V2)
    (i1 j1 : ι1) (i2 j2 : ι2) :
    ⟪fun t ↦ (ρ2 t).toMatrix b2 b2 i2 j2, fun t ↦ (ρ1 t).toMatrix b1 b1 j1 i1⟫ = 0 := by
  letI : Invertible (Fintype.card G : K) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  calc
    ⟪fun t ↦ (ρ2 t).toMatrix b2 b2 i2 j2, fun t ↦ (ρ1 t).toMatrix b1 b1 j1 i1⟫
      = (((ρ1.linHom ρ2).averageMap (b1.linearMap b2 (j2, j1))).toMatrix b1 b2 i2 i1) := by
          simpa [groupFunctionPairingOverField, Nat.card_eq_fintype_card] using
            (averageMap_linHom_basis_entry_eq ρ1 ρ2 b1 b2 i1 j1 i2 j2).symm
    _ = 0 := by
          simpa using congrArg (fun f ↦ f.toMatrix b1 b2 i2 i1) <|
            averageMap_linHom_eq_zero_of_not_isomorphic ρ1 ρ2 (b1.linearMap b2 (j2, j1)) hρ

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
variable {ι : Type u₁} [Fintype ι]

-- Proof sketch: apply `averageMap_linHom_self_eq_trace_smul_id` to the canonical basis vector
-- `b.end (j2, j1)` of `Module.End ℂ V`, read off the `(i2, i1)` matrix entry using
-- `averageMap_linHom_basis_entry_eq`, and compute the trace of that matrix unit.
open scoped Classical in
/-- The orthogonality relation for matrix coefficients of one irreducible representation, expressed
with the pairing notation. -/
theorem matrixCoefficient_pairing_of_irreducible
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (b : Module.Basis ι ℂ V) (i1 j1 i2 j2 : ι) :
    ⟪fun t ↦ (ρ t).toMatrix b b i2 j2, fun t ↦ (ρ t).toMatrix b b j1 i1⟫ =
      if i2 = i1 then
        if j2 = j1 then (Module.finrank ℂ V : ℂ)⁻¹ else 0
      else 0 := by
  letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  letI : NeZero (Module.finrank ℂ V) := NeZero.of_pos Module.finrank_pos
  have htrace : LinearMap.trace ℂ V (b.end (j2, j1)) = if j2 = j1 then 1 else 0 := by
    rw [Module.Basis.end_apply, Matrix.trace_toLin_eq, Matrix.stdBasis_eq_single]
    by_cases h : j2 = j1
    · subst h
      simp [Matrix.trace_single_eq_same]
    · simp [Matrix.trace_single_eq_of_ne j2 j1 (1 : ℂ) h, h]
  calc
    ⟪fun t ↦ (ρ t).toMatrix b b i2 j2, fun t ↦ (ρ t).toMatrix b b j1 i1⟫
      = (((ρ.linHom ρ).averageMap (b.end (j2, j1))).toMatrix b b i2 i1) := by
          simpa [groupFunctionPairingOverField, Nat.card_eq_fintype_card] using
            (averageMap_linHom_basis_entry_eq ρ ρ b b i1 j1 i2 j2).symm
    _ = ((((Module.finrank ℂ V : ℂ)⁻¹ * LinearMap.trace ℂ V (b.end (j2, j1))) •
          (LinearMap.id : V →ₗ[ℂ] V)).toMatrix b b i2 i1) := by
          simpa using congrArg (fun f ↦ f.toMatrix b b i2 i1)
            (averageMap_linHom_self_eq_trace_smul_id ρ (b.end (j2, j1)))
    _ = if i2 = i1 then
          if j2 = j1 then (Module.finrank ℂ V : ℂ)⁻¹ else 0
        else 0 := by
          rw [htrace]
          by_cases hi : i2 = i1
          · subst hi
            by_cases hj : j2 = j1
            · simp [hj]
            · simp [hj]
          · by_cases hj : j2 = j1
            · simp [hj, hi]
            · simp [hj, hi]

end

end Representation

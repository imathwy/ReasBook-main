import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Representation

universe u v w

namespace Representation

private theorem span_eq_overlineCharacterRing_of_isFiniteRelIndex
    (K : Type v) (G : Type u) [Field K] [CharZero K] [Group G] [Finite G]
    (A : Type w) [Field A] [CharZero A] [Algebra A K] :
    Submodule.span A (R[K](G) : Set (G → K)) =
      Submodule.span A (R̄[K](G) : Set (G → K)) := by
  let RK : Submodule ℤ (G → K) := (R[K](G)).toSubmodule
  let RbarK : Submodule ℤ (G → K) := (R̄[K](G)).toSubmodule
  have hle : RK ≤ RbarK := by
    simpa [RK, RbarK] using
      (characterRingOverField_le_overlineCharacterRing K G :
        (R[K](G)).toSubmodule ≤ (R̄[K](G)).toSubmodule)
  have hfin : RK.toAddSubgroup.IsFiniteRelIndex RbarK.toAddSubgroup := by
    simpa [RK, RbarK] using
      (characterRingOverField_isFiniteRelIndex_overlineCharacterRing K :
        (R[K](G)).toSubmodule.toAddSubgroup.IsFiniteRelIndex
          (R̄[K](G)).toSubmodule.toAddSubgroup)
  letI := hfin
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.2 ?_
    intro χ hχ
    have hχRK : χ ∈ RK := by
      simpa [RK] using hχ
    exact Submodule.subset_span <| by
      simpa [RbarK] using hle hχRK
  · refine Submodule.span_le.2 fun χ hχ ↦ ?_
    let n := RK.toAddSubgroup.relIndex RbarK.toAddSubgroup
    have hχRbarK : χ ∈ RbarK.toAddSubgroup := by
      simpa [RbarK] using hχ
    have hnsmul_mem : n • χ ∈ (R[K](G) : Set (G → K)) := by
      simpa [RK, n] using RK.toAddSubgroup.nsmul_relIndex_mem hχRbarK
    have hn_ne_zero : (n : A) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr <| by
        simpa [n] using (AddSubgroup.relIndex_ne_zero :
          RK.toAddSubgroup.relIndex RbarK.toAddSubgroup ≠ 0)
    have hχ :
        χ = ((n : A)⁻¹) • (n • χ) := by
      rw [← Nat.cast_smul_eq_nsmul A, ← mul_smul, inv_mul_cancel₀ hn_ne_zero, one_smul]
    rw [hχ]
    exact (Submodule.span A (R[K](G) : Set (G → K))).smul_mem _ <|
      Submodule.subset_span hnsmul_mem

/-- The `ℚ`-scalar-extension form of Remark 12-12.4-4: the chapter owner `ℚ ⊗ R_K(G)` is exactly
the `ℚ`-span of `\overline{R}_K(G)` inside `G → K`. This is the owner-level equality underlying
the replacement of `R_K(G)` by `\overline{R}_K(G)` in Corollary `12-12.4-2`. -/
theorem characterRingOverField_rationalScalarExtension_eq_overlineCharacterRing_span
    (K : Type v) (G : Type u) [Field K] [CharZero K] [Group G] [Finite G] :
    (ℚ⊗R[K](G) : Submodule ℚ (G → K)) =
      Submodule.span ℚ (R̄[K](G) : Set (G → K)) := by
  simpa [characterRingOverFieldScalarExtension] using
    span_eq_overlineCharacterRing_of_isFiniteRelIndex K G ℚ

/-- Remark 12-12.4-4: after extending scalars from `ℤ` to `K`, the canonical `K`-span generated
by `R_K(G)` agrees with the `K`-span of `\overline{R}_K(G)` inside `G → K`. -/
theorem characterRingOverField_scalarExtension_eq_overlineCharacterRing_span
    (K : Type v) (G : Type u) [Field K] [CharZero K] [Group G] [Finite G] :
    K ⊗R[K](G) = Submodule.span K (R̄[K](G) : Set (G → K)) := by
  simpa [characterRingOverFieldAlgebraScalarExtension] using
    span_eq_overlineCharacterRing_of_isFiniteRelIndex K G K

end Representation

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-- Lemma 10.123.5: in the finite polynomial-map situation with integrally closed constant image, if
`u * φ p` lies in the conductor ideal `conductor R (φ X)` of `φ : R[X] →+* S`, then after
multiplying `u` by a power of the image of the leading coefficient of `p`, the result still lies in
that same conductor ideal. -/
@[stacks 00PX]
theorem exists_pow_leadingCoeff_mul_mem_conductor
    {φ : Polynomial R →+* S} (hfinite : φ.Finite)
    (hintegrallyClosed : IsIntegrallyClosedIn ((φ.comp C).range) S)
    {u : S} {p : Polynomial R}
    (hu :
      letI : Algebra R S := (φ.comp C).toAlgebra
      u * φ p ∈ conductor R (φ X)) :
    letI : Algebra R S := (φ.comp C).toAlgebra
    ∃ m : ℕ, u * φ (C p.leadingCoeff) ^ m ∈ conductor R (φ X) := by
  letI : Algebra R S := (φ.comp C).toAlgebra
  let φ' : Polynomial R →ₐ[R] S := aeval (φ X)
  have hφ' : φ'.toRingHom = φ := by
    apply Polynomial.ringHom_ext'
    · ext r
      simp [φ', RingHom.algebraMap_toAlgebra]
    · simp [φ']
  have hφp : φ' p = φ p := by
    simpa using DFunLike.congr_fun hφ' p
  have hφX : φ' X = φ X := by
    simpa using DFunLike.congr_fun hφ' X
  have hRS : integralClosure R S = ⊥ := by
    letI : Algebra R ((φ.comp C).range) := RingHom.toAlgebra (φ.comp C).rangeRestrict
    letI : IsScalarTower R ((φ.comp C).range) S := .of_algebraMap_eq fun _ ↦ rfl
    letI : Algebra.IsIntegral R ((φ.comp C).range) := {
      isIntegral := fun x ↦ by
        rcases x with ⟨x, ⟨r, rfl⟩⟩
        simpa [RingHom.algebraMap_toAlgebra] using
          (show _root_.IsIntegral R (algebraMap R ((φ.comp C).range) r) from
            isIntegral_algebraMap)
    }
    apply le_antisymm
    · intro x hx
      rw [Algebra.mem_bot]
      have hx' : _root_.IsIntegral ((φ.comp C).range) x :=
        (show _root_.IsIntegral R x from hx).tower_top
      have hx'' : x ∈ (φ.comp C).range := (Subring.isIntegrallyClosedIn_iff.mp
        hintegrallyClosed) hx'
      simpa [RingHom.algebraMap_toAlgebra] using hx''
    · exact bot_le
  obtain ⟨m, hm⟩ := exists_leadingCoeff_pow_smul_mem_conductor
    φ' u p hRS
    (by
      show φ'.toRingHom.Finite
      rw [hφ']
      exact hfinite)
    (by simpa [hφp, hφX, mul_comm] using hu)
  refine ⟨m, ?_⟩
  simpa [φ', hφ', Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hm

end RingHom

end

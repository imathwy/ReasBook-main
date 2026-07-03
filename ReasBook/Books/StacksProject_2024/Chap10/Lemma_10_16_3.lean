import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Polynomial

/-
Lemma 10.16.3 lives in the finite-module Cayley-Hamilton / ideal-power coefficient domain.
Its core/canonical owner is mathlib's
`LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul`; the source wording
below is a bridge/view that reindexes the coefficients into textbook order.
-/
recall LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul

namespace LinearMap

section

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M]

/-- Source-facing bridge for Lemma 10.16.3: reindex the canonical owner theorem into the textbook
coefficient order `aⱼ ∈ I ^ j`. -/
theorem exists_monic_and_coeff_natDegree_sub_mem_pow_and_aeval_eq_zero_of_range_le_smul
    (φ : Module.End R M) (I : Ideal R) (hI : range φ ≤ I • ⊤) :
    ∃ p : R[X], p.Monic ∧ (∀ j ≤ p.natDegree, p.coeff (p.natDegree - j) ∈ I ^ j) ∧ aeval φ p = 0 := by
  obtain ⟨p, hpM, hpC, hpA⟩ :=
    exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R φ I hI
  refine ⟨p, hpM, ?_, hpA⟩
  intro j hj
  simpa [Nat.sub_sub_self hj] using hpC (p.natDegree - j)

end

end LinearMap

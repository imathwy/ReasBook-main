import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_38_3

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-
Domain triage:
* source-facing: `φ.IsIntegralOverIdeal I x`, the chapter's ideal-relative integrality predicate.
* core/canonical owner: `Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map`.
* bridge/view: this lemma repackages the owner theorem for an arbitrary integral ring hom `φ`.
-/
recall Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map

/-- Lemma 10.38.4: every element of the extended ideal `I.map φ = IS` is integral over `I`
whenever `φ : R →+* S` is integral. -/
@[stacks 00H5]
theorem isIntegralOverIdeal_of_mem_map {φ : R →+* S} (hφ : φ.IsIntegral) {I : Ideal R} {x : S}
    (hx : x ∈ I.map φ) :
    φ.IsIntegralOverIdeal I x := by
  letI := φ.toAlgebra
  letI : Algebra.IsIntegral R S := ⟨hφ⟩
  simpa [IsIntegralOverIdeal, Polynomial.aeval_def] using
    Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map hx

end RingHom

end

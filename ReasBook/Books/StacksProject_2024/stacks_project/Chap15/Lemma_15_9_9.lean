import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_38_4

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open Ideal.Quotient (eq_zero_iff_mem)

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B]

/- 
Domain triage:
* `source-facing`: this theorem's specialized polynomial witness for an idempotent modulo `I B`.
* `core/canonical`: the Chapter 10 owner theorem
  `RingHom.isIntegralOverIdeal_of_mem_map`, built on
  `Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map`.
* `bridge/view`: composing an annihilating polynomial for `b ^ 2 - b` with `X * (X - 1)`.

Primitive data: the quotient idempotence hypothesis on `b`.
Derived API: first obtain the owner proposition
`(algebraMap A B).IsIntegralOverIdeal I (b ^ 2 - b)` from Chapter 10, then compose its
polynomial witness with `X * (X - 1)`.

The previous local helper only repackaged the owner theorem for this one use, so the public surface
keeps only the direct existential source statement.
-/

-- Proof sketch: apply the Chapter 10 owner theorem directly to `b ^ 2 - b`, obtaining a monic
-- polynomial `g` over `A` whose non-leading coefficients lie in `I` and with
-- `aeval (b ^ 2 - b) g = 0`. Then set `f := g.comp (X * (X - 1))`. This remains monic,
-- satisfies `aeval b f = 0`, and reduces modulo `I` to `X ^ d * (X - 1) ^ d` because `g` is
-- `I`-distinguished, so `(g mod I) = X ^ d` by the canonical owner theorem
-- `Polynomial.IsDistinguishedAt.map_eq_X_pow`.
/-- Lemma 15.9.9: if `b : B` becomes idempotent modulo the extended ideal `I B`, then there is a
monic polynomial over `A` vanishing at `b` whose reduction modulo `I` is `X ^ d * (X - 1) ^ d`
for some `d ≥ 1`. -/
theorem exists_monic_polynomial_of_isIdempotentElem_mod_map
    (I : Ideal A) (b : B)
    (hb :
      IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A B)) b : B ⧸ I.map (algebraMap A B))) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A[X],
      f.Monic ∧
        aeval b f = 0 ∧
          f.map (Ideal.Quotient.mk I) = (X ^ d * (X - 1) ^ d : (A ⧸ I)[X]) := by
  have hXMonic : (X * (X - 1) : A[X]).Monic := by
    simpa using (monic_X : (X : A[X]).Monic).mul (monic_X_sub_C (1 : A))
  by_cases hA : Subsingleton A
  · letI := hA
    have hA01 : (0 : A) = 1 := Subsingleton.elim _ _
    have hB01 : (0 : B) = 1 := by
      calc
        (0 : B) = algebraMap A B 0 := by simp
        _ = algebraMap A B 1 := by simpa using congrArg (algebraMap A B) hA01
        _ = 1 := by simp
    letI : Subsingleton B := by
      refine ⟨fun x y ↦ ?_⟩
      have hzero : ∀ z : B, z = 0 := fun z ↦ by
        calc
          z = 1 * z := by simp
          _ = 0 * z := by simpa [hB01]
          _ = 0 := by simp
      exact (hzero x).trans (hzero y).symm
    refine ⟨1, Nat.one_pos, 1, ?_, ?_, ?_⟩
    · change leadingCoeff (1 : A[X]) = 1
      exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
  · letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    by_cases hB : Subsingleton B
    · letI := hB
      refine ⟨1, Nat.one_pos, X * (X - 1), hXMonic, ?_, ?_⟩
      · have hb0 : b = 0 := Subsingleton.elim _ _
        simp [hb0]
      · simpa using (mul_pow (X : (A ⧸ I)[X]) (X - 1) 1)
    · letI : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
      let J : Ideal B := I.map (algebraMap A B)
      have hsq : b ^ 2 - b ∈ J := by
        rw [← eq_zero_iff_mem]
        change (Ideal.Quotient.mk J b) ^ 2 - Ideal.Quotient.mk J b = 0
        simpa [J, pow_two, sub_eq_zero] using hb.eq
      obtain ⟨g, hgM, hg0, hgI⟩ :
          (algebraMap A B).IsIntegralOverIdeal I (b ^ 2 - b) := by
        simpa [J] using
          RingHom.isIntegralOverIdeal_of_mem_map
            (algebraMap_isIntegral_iff.mpr inferInstance) hsq
      let d := g.natDegree
      have hd : d ≠ 0 := by
        intro hd0
        have hg1 : g = 1 := hgM.natDegree_eq_zero.mp hd0
        simpa [hg1] using hg0
      let f := g.comp (X * (X - 1))
      have hXEval : aeval b (X * (X - 1) : A[X]) = b ^ 2 - b := by
        simpa [pow_two] using (mul_sub b b (1 : B))
      have hXSubNatDegree : (X - C (1 : A) : A[X]).natDegree = 1 := by
        simpa using (natDegree_X_sub_C (1 : A))
      have hXLeadingCoeff :
          leadingCoeff (X : A[X]) * leadingCoeff (X - C (1 : A) : A[X]) ≠ 0 := by
        rw [leadingCoeff_X, leadingCoeff_X_sub_C]
        simpa using (one_ne_zero : (1 : A) ≠ 0)
      have hXNatDegree : (X * (X - 1) : A[X]).natDegree ≠ 0 := by
        change natDegree ((X : A[X]) * (X - C (1 : A))) ≠ 0
        rw [natDegree_mul' hXLeadingCoeff, natDegree_X, hXSubNatDegree]
        simp
      have hfM : f.Monic := hgM.comp hXMonic hXNatDegree
      have hf0 : aeval b f = 0 := by
        change aeval b (g.comp (X * (X - 1) : A[X])) = 0
        rw [aeval_comp, hXEval]
        simpa [aeval_def] using hg0
      have hgDistinguished : g.IsDistinguishedAt I := by
        refine ⟨⟨fun {i} hi ↦ ?_⟩, hgM⟩
        simpa [d] using Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hi) (hgI i)
      have hgMap : g.map (Ideal.Quotient.mk I) = (X ^ d : (A ⧸ I)[X]) := by
        simpa [d] using hgDistinguished.map_eq_X_pow
      have hfMap : f.map (Ideal.Quotient.mk I) = (X ^ d * (X - 1) ^ d : (A ⧸ I)[X]) := by
        calc
          f.map (Ideal.Quotient.mk I)
              = (g.map (Ideal.Quotient.mk I)).comp (X * (X - 1) : (A ⧸ I)[X]) := by
                  simp [f, Polynomial.map_comp]
          _ = ((X ^ d : (A ⧸ I)[X])).comp (X * (X - 1)) := by rw [hgMap]
          _ = (X * (X - 1) : (A ⧸ I)[X]) ^ d := by simp
          _ = (X ^ d * (X - 1) ^ d : (A ⧸ I)[X]) := by
                simpa using (mul_pow (X : (A ⧸ I)[X]) (X - 1) d)
      refine ⟨d, Nat.pos_iff_ne_zero.2 hd, f, hfM, hf0, hfMap⟩

end

end Algebra

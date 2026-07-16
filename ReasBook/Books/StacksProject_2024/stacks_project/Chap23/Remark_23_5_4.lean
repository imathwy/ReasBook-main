import StacksProject_2024.stacks_project.Chap23.Lemma_23_5_3

open scoped BigOperators
open Nat Ring

namespace Ideal

-- This remark uses the same source-facing candidate `p`th divided-power endomorphism of the ideal
-- as `Lemma_23_5_3`.

open DividedPowers Function

variable {A : Type*} [CommRing A]
variable {p : ℕ} [Fact p.Prime]

/-
Source/core/bridge triage for Remark 23.5.4:
- `source-facing`: the factorial identity follows from the scalar-compatibility and additivity
  hypotheses from Lemma 23.5.3;
- `core/canonical`: the bundled predicate `Function.IsDpowPrime`;
- `bridge/view`: the companion theorem `isDpowPrime_of_add_smul`, which repackages the source-facing
  factorial consequence together with the given hypotheses into the canonical predicate.
-/

/-- Remark 23.5.4: for a map `δ : I → I` satisfying the scalar-compatibility and additivity
conditions from Lemma 23.5.3, the remaining factorial identity already follows. -/
@[stacks 0H87]
theorem factorial_mul_dpowPrime_eq_pow_of_add_smul (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    (δ : I → I)
    (hsmul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x)
    (hadd : ∀ x y : I,
      (δ (x + y) : A) =
        (δ x : A) + dpowPrimeAddCorrection p x y + δ y)
    (x : I) :
    ((p ! : A) * (δ x : A)) = (x : A) ^ p := by
  sorry

/-- Remark 23.5.4 companion: under the prime-to-`p` unit hypothesis, the scalar-compatibility and
additivity identities already imply the missing factorial identity, so they assemble to the source
predicate `Function.IsDpowPrime`. -/
@[stacks 0H87]
theorem isDpowPrime_of_add_smul (I : Ideal A)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : A))
    (δ : I → I)
    (hsmul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x)
    (hadd : ∀ x y : I,
      (δ (x + y) : A) =
        (δ x : A) +
          dpowPrimeAddCorrection p x y +
        δ y) :
    δ.IsDpowPrime p := by
  refine ⟨factorial_mul_dpowPrime_eq_pow_of_add_smul I hunit δ hsmul hadd, hsmul, hadd⟩

end Ideal

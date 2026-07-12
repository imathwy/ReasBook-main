import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Tactic.Recall

universe u

/-
Source/core/bridge triage:
- `source-facing`: Lemma 23.2.2 collects the factorial characterization of divided powers and the
  torsion-free consequences for existence and uniqueness on an ideal.
- `core/canonical`: the mathlib owner `DividedPowers I` and the canonical theorem
  `DividedPowers.factorial_mul_dpow_eq_pow`.
- `bridge/view`: parts (2)–(4) keep the source-facing torsion-free characterizations while using
  the canonical owner throughout.
-/

namespace DividedPowers

section

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- For a positive index, the `n`th divided power canonically refines to an endomorphism of the
ideal `I`. -/
abbrev dpowPos (hI : DividedPowers I) (n : ℕ+) : I → I := fun x ↦
  ⟨hI.dpow n x, hI.dpow_mem n.2.ne' x.2⟩

/-- Coercing the positive-index divided power back to `A` recovers the underlying divided power. -/
@[simp] theorem coe_dpowPos_apply (hI : DividedPowers I) (n : ℕ+) (x : I) :
    (hI.dpowPos n x : A) = hI.dpow n x := rfl

/-- For positive indices, the factorial formula can be stated directly with the ideal-valued map
`dpowPos`. -/
@[simp] theorem factorial_mul_dpowPos_eq_pow (hI : DividedPowers I) (n : ℕ+) (x : I) :
    (((n : ℕ).factorial : A) * (hI.dpowPos n x : A)) = (x : A) ^ (n : ℕ) := by
  simpa using
    (hI.factorial_mul_dpow_eq_pow x.2 :
      (((n : ℕ).factorial : A) * hI.dpow n x) = (x : A) ^ (n : ℕ))

end

end DividedPowers

/- Lemma 23.2.2 (1): if `γ` is a divided power structure on the ideal `I`, then
`n! * γ_n(x) = x^n` for every `x ∈ I`. This is exactly the canonical theorem
`DividedPowers.factorial_mul_dpow_eq_pow`; the source hypothesis `n ≥ 1` is redundant. -/
recall DividedPowers.factorial_mul_dpow_eq_pow

namespace Ideal

section

variable {A : Type u} [CommRing A] [Module.IsTorsionFree ℤ A]

/-- Lemma 23.2.2 (2): if `A` is torsion free as a `ℤ`-module, then an ideal `I` carries at most
one divided power structure. -/
@[stacks 07GM]
theorem subsingleton_dividedPowers_of_isTorsionFree (I : Ideal A) :
    Subsingleton (DividedPowers I) := by
  sorry

/-- Divided power structures on an ideal of a `ℤ`-torsion-free ring inherit the canonical
`Subsingleton` instance. -/
instance instSubsingletonDividedPowersOfIsTorsionFree (I : Ideal A) :
    Subsingleton (DividedPowers I) :=
  subsingleton_dividedPowers_of_isTorsionFree I

/-- Lemma 23.2.2 (2) companion: in the torsion-free case, any two divided power structures on `I`
coincide. -/
@[stacks 07GM]
theorem eq_dividedPowers_of_isTorsionFree {I : Ideal A} (γ δ : DividedPowers I) :
    γ = δ := by
  exact Subsingleton.elim γ δ

/-- Lemma 23.2.2 (3): if `A` is torsion free as a `ℤ`-module and `γ_n : I → I` is a family of
maps indexed by positive integers, then this family is induced by a divided power structure on `I`
exactly when it satisfies `n! * γ_n(x) = x^n` for every `x ∈ I`. -/
@[stacks 07GM]
theorem exists_dividedPowers_iff_factorial_mul_eq_pow
    (I : Ideal A) (γ : ℕ+ → I → I) :
    (∃ hI : DividedPowers I, ∀ n : ℕ+, ∀ x : I, hI.dpowPos n x = γ n x) ↔
      ∀ n : ℕ+, ∀ x : I, ((n : ℕ).factorial : A) * (γ n x : A) = (x : A) ^ (n : ℕ) := by
  sorry

/-- Lemma 23.2.2 (3) companion: over a torsion-free ring, the factorial identities determine a
divided power structure on `I` uniquely when they determine one at all. -/
@[stacks 07GM]
theorem existsUnique_dividedPowers_iff_factorial_mul_eq_pow
    (I : Ideal A) (γ : ℕ+ → I → I) :
    (∃! hI : DividedPowers I, ∀ n : ℕ+, ∀ x : I, hI.dpowPos n x = γ n x) ↔
      ∀ n : ℕ+, ∀ x : I, ((n : ℕ).factorial : A) * (γ n x : A) = (x : A) ^ (n : ℕ) := by
  sorry

/-- Lemma 23.2.2 (4): if `A` is torsion free as a `ℤ`-module, then an ideal `I` has a divided
power structure if and only if it admits a generating set whose `n`th powers lie in `(n!)I` for
every `n ≥ 1`. -/
@[stacks 07GM]
theorem nonempty_dividedPowers_iff_exists_span_eq_and_pow_mem_factorial_smul
    (I : Ideal A) :
    Nonempty (DividedPowers I) ↔
      ∃ S : Set A, Ideal.span S = I ∧
        ∀ ⦃x : A⦄, x ∈ S → ∀ ⦃n : ℕ⦄, 1 ≤ n →
          x ^ n ∈ Ideal.span {(n.factorial : A)} • I := by
  sorry

end

end Ideal

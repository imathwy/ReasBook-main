import Mathlib.RingTheory.DividedPowers.Basic

universe u

open Finset

/-
Source/core/bridge triage:
- `source-facing`: generator-level axioms for a family `γ` on an ideal `I`;
- `core/canonical`: the mathlib owner `DividedPowers I`;
- `bridge/view`: the theorem below is the source-facing bridge from those generator axioms to the
  canonical owner.
-/

section

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : ℕ → A → A) {S : Set A}

/-- Lemma 23.2.4: if an `A`-valued family `γ` on an ideal `I` satisfies the divided-power
axioms `γ₀ = 1`, `γ₁ = id`, scalar compatibility, and the addition formula on all elements of
`I`, and the multiplicative identity on generators in the source range `m > 0` together with the
iterated divided-power identity on a generating set of `I`, then `γ` determines a divided power
structure on `I`. -/
@[stacks 07GP]
theorem exists_dividedPowers_of_axioms_on_generators
    (hS : I = Ideal.span S)
    (hγ_zero : ∀ ⦃x : A⦄, x ∈ I → γ 0 x = 1)
    (hγ_one : ∀ ⦃x : A⦄, x ∈ I → γ 1 x = x)
    (hγ_mem : ∀ ⦃n : ℕ⦄ ⦃x : A⦄, n ≠ 0 → x ∈ I → γ n x ∈ I)
    (hγ_add : ∀ ⦃n : ℕ⦄ ⦃x y : A⦄, x ∈ I → y ∈ I →
      γ n (x + y) = (antidiagonal n).sum fun k ↦ γ k.1 x * γ k.2 y)
    (hγ_mul : ∀ ⦃n : ℕ⦄ ⦃a x : A⦄, x ∈ I → γ n (a * x) = a ^ n * γ n x)
    (hγ_mul_dpow_gen : ∀ ⦃m n : ℕ⦄ ⦃x : A⦄, m ≠ 0 → x ∈ S →
      γ m x * γ n x = Nat.choose (m + n) m * γ (m + n) x)
    (hγ_comp_gen : ∀ ⦃m n : ℕ⦄ ⦃x : A⦄, n ≠ 0 → x ∈ S →
      γ m (γ n x) = Nat.uniformBell m n * γ (m * n) x) :
    ∃ hI : DividedPowers I, ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ I → hI.dpow n x = γ n x := sorry

/-- Lemma 23.2.4 companion: the divided power structure on `I` induced by the generator-level
axioms for `γ` is unique among structures whose divided powers agree with `γ` on `I`. -/
@[stacks 07GP]
theorem existsUnique_dividedPowers_of_axioms_on_generators
    (hS : I = Ideal.span S)
    (hγ_zero : ∀ ⦃x : A⦄, x ∈ I → γ 0 x = 1)
    (hγ_one : ∀ ⦃x : A⦄, x ∈ I → γ 1 x = x)
    (hγ_mem : ∀ ⦃n : ℕ⦄ ⦃x : A⦄, n ≠ 0 → x ∈ I → γ n x ∈ I)
    (hγ_add : ∀ ⦃n : ℕ⦄ ⦃x y : A⦄, x ∈ I → y ∈ I →
      γ n (x + y) = (antidiagonal n).sum fun k ↦ γ k.1 x * γ k.2 y)
    (hγ_mul : ∀ ⦃n : ℕ⦄ ⦃a x : A⦄, x ∈ I → γ n (a * x) = a ^ n * γ n x)
    (hγ_mul_dpow_gen : ∀ ⦃m n : ℕ⦄ ⦃x : A⦄, m ≠ 0 → x ∈ S →
      γ m x * γ n x = Nat.choose (m + n) m * γ (m + n) x)
    (hγ_comp_gen : ∀ ⦃m n : ℕ⦄ ⦃x : A⦄, n ≠ 0 → x ∈ S →
      γ m (γ n x) = Nat.uniformBell m n * γ (m * n) x) :
    ∃! hI : DividedPowers I, ∀ ⦃n : ℕ⦄ ⦃x : A⦄, x ∈ I → hI.dpow n x = γ n x := by
  rcases exists_dividedPowers_of_axioms_on_generators I γ hS hγ_zero hγ_one hγ_mem hγ_add
      hγ_mul hγ_mul_dpow_gen hγ_comp_gen with ⟨hI, hhI⟩
  refine ⟨hI, hhI, ?_⟩
  intro hI' hhI'
  apply DividedPowers.ext
  intro n x hx
  rw [hhI hx, hhI' hx]

end

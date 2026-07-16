import StacksProject_2024.stacks_project.Chap10.Definition_10_58_3
import StacksProject_2024.stacks_project.Chap10.Proposition_10_58_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Filter

section

variable {A : Type u} [AddCommGroup A]

/-- A function on the integers is a periodic polynomial if, on each congruence class modulo some
positive integer, its restriction to that residue class eventually agrees with a numerical
polynomial. The owner notion on each residue class is the project definition
`IsNumericalPolynomial`, compared by eventual equality on the restricted `Filter.atTop` filter of
that residue class. -/
def IsPeriodicPolynomial (f : ℤ → A) : Prop :=
  ∃ n : ℕ+, ∀ a : ZMod n, ∃ g : ℤ → A,
    IsNumericalPolynomial g ∧
      f =ᶠ[atTop ⊓ principal {m : ℤ | (m : ZMod n) = a}] g

/-- A numerical polynomial is periodic, with period `1`. -/
theorem IsNumericalPolynomial.isPeriodicPolynomial {f : ℤ → A}
    (hf : IsNumericalPolynomial f) : IsPeriodicPolynomial f := by
  refine ⟨1, fun _ ↦ ?_⟩
  exact ⟨f, hf, EventuallyEq.rfl⟩

end

section

local instance : AddAction ℕ ℤ where
  vadd n d := (n : ℤ) + d
  zero_vadd := by
    intro d
    change ((0 : ℕ) : ℤ) + d = d
    simp
  add_vadd := by
    intro m n d
    change (((m + n : ℕ) : ℤ) + d) = (m : ℤ) + ((n : ℤ) + d)
    simp [Nat.cast_add, add_assoc]

variable {S : Type u} [CommRing S]
variable (𝒜 : ℕ → Submodule ℤ S) [GradedAlgebra 𝒜] [IsNoetherianRing S]

-- Proof sketch: use `sufficiently_divisible_veronese_generated_in_degree_one` to choose a positive
-- Veronese period. On each residue class modulo that period, reindex the graded pieces as a module
-- over the corresponding Veronese subring, convert the resulting generated-in-degree-one
-- hypothesis to `Ideal.span (S₁) = S₊` via Lemma `10.58.1`, and then apply Proposition `10.58.7`.
/-- Remark 10.58.8: if `S` is Noetherian but need not be generated in degree `1`, then the
`K'_0(S₀)`-valued function `n ↦ [Mₙ]` attached to a finite graded `S`-module, where
`S₀ = 𝒜 0`, is a periodic polynomial. -/
theorem gradedPieceFiniteGrothendieckGroupClass_isPeriodicPolynomial_of_isNoetherianRing
    {M : Type v} [AddCommGroup M] [Module S M]
    (ℳ : ℤ → Submodule S M)
    [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] [Module.Finite S M] :
    IsPeriodicPolynomial (gradedPieceFiniteGrothendieckGroupClass 𝒜 ℳ) := sorry

end

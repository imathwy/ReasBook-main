import StacksProject_2024.Chap10.Definition_10_58_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [AddCommGroup A]
variable {A' : Type v} [AddCommGroup A']

/-- Lemma 10.58.4: postcomposing a numerical polynomial with a homomorphism of abelian groups
again gives a numerical polynomial. -/
@[stacks 00JY]
theorem IsNumericalPolynomial.comp {f : ℤ → A} (hf : IsNumericalPolynomial f) (φ : A →+ A') :
    IsNumericalPolynomial (φ ∘ f) := by
  rcases hf with ⟨r, a, ha⟩
  refine ⟨r, φ ∘ a, (ha.fun_comp φ).trans ?_⟩
  exact .of_eq <| by
    funext n
    simp [Function.comp, map_sum, map_zsmul]

end

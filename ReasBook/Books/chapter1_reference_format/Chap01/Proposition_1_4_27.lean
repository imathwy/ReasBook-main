import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Proposition 1.4.27 (1) is already the canonical mathlib instance
`Submodule.finiteDimensional_sup`. -/
recall Submodule.finiteDimensional_sup {K : Type u} {V : Type v} [DivisionRing K]
    [AddCommGroup V] [Module K V] (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁]
    [h₂ : FiniteDimensional K S₂] : FiniteDimensional K (S₁ ⊔ S₂ : Submodule K V)

section

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Proposition 1.4.27 (2): for finite-dimensional subspaces `V₁` and `V₂`, the dimension of
their sum satisfies the usual inclusion-exclusion formula. -/
theorem finrank_sup_eq_finrank_add_finrank_sub_finrank_inf
    (V₁ V₂ : Submodule K V) [FiniteDimensional K V₁] [FiniteDimensional K V₂] :
    Module.finrank K (V₁ ⊔ V₂ : Submodule K V) =
      Module.finrank K V₁ + Module.finrank K V₂ - Module.finrank K (V₁ ⊓ V₂ : Submodule K V) := by
  -- Start from the canonical sup/inf finrank identity supplied by mathlib.
  have h := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  -- Rearrange the natural-number equality into the subtraction form of the proposition.
  omega

end

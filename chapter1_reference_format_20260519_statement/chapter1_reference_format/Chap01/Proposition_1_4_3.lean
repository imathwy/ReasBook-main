import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]

/-- Proposition 1.4.3, expressed at the canonical owner level `Submodule R M`: a subset `W` of
an `R`-module `M` is the carrier of a submodule exactly when `W` is nonempty and is closed under
two-term linear combinations `a • x + b • y`. Over a field, this is the usual subspace
criterion. -/
-- Proof sketch: for the forward implication, use the zero, addition, and scalar-multiplication
-- closure of a submodule to show closure under `a • x + b • y`, and obtain nonemptiness from `0`.
-- For the reverse implication, apply `Submodule.ofLinearComb` to build the corresponding
-- submodule with carrier `W`.
theorem exists_submodule_iff_nonempty_and_linear_combination_closed (W : Set M) :
    (∃ U : Submodule R M, (U : Set M) = W) ↔
      W.Nonempty ∧ ∀ ⦃x y : M⦄ (_ : x ∈ W) (_ : y ∈ W) (a b : R), a • x + b • y ∈ W := by
  constructor
  · rintro ⟨U, rfl⟩
    refine ⟨⟨0, U.zero_mem⟩, ?_⟩
    intro x y hx hy a b
    exact U.add_mem (U.smul_mem a hx) (U.smul_mem b hy)
  · rintro ⟨hW, hlinearComb⟩
    refine ⟨Submodule.ofLinearComb W hW ?_, rfl⟩
    intro x hx y hy a b
    exact hlinearComb hx hy a b

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Function

section FiniteModule

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/- Definition 10.5.1 (1): a finite, or finitely generated, `R`-module is the canonical typeclass
`Module.Finite R M`. -/
recall Module.Finite

namespace Module.Finite

-- Proof sketch: use `Module.Finite.exists_fin'` for the forward implication and
-- `Module.Finite.of_surjective` for the converse.
/-- A module is finite exactly when it is the quotient of a finite free module `Fin n → R`. -/
theorem iff_exists_surjective_free :
    Module.Finite R M ↔ ∃ n : ℕ, ∃ f : (Fin n → R) →ₗ[R] M, Surjective f := by
  constructor
  · intro hM
    letI := hM
    simpa using Module.Finite.exists_fin' R M
  · rintro ⟨n, f, hf⟩
    exact Module.Finite.of_surjective f hf

end Module.Finite

end FiniteModule

section FinitePresentation

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

/- Definition 10.5.1 (2): a finitely presented `R`-module is the canonical typeclass
`Module.FinitePresentation R M`. -/
recall Module.FinitePresentation

namespace Module.FinitePresentation

-- Proof sketch: combine `Module.FinitePresentation.exists_fin` with
-- `Submodule.fg_iff_exists_fin_linearMap`; for the converse, use the owner-level kernel criterion
-- `Module.FinitePresentation.fg_ker_iff` after identifying `ker g` with `range f`.
/-- A module is finitely presented exactly when it admits an exact sequence
`(Fin m → R) → (Fin n → R) → M → 0`, encoded as `Exact f g` together with the surjectivity of
`g`. -/
theorem iff_exists_exact_free_sequence :
    Module.FinitePresentation R M ↔
      ∃ n m : ℕ,
        ∃ f : (Fin m → R) →ₗ[R] (Fin n → R),
          ∃ g : (Fin n → R) →ₗ[R] M,
            Exact f g ∧ Surjective g := by
  constructor
  · intro hM
    letI := hM
    obtain ⟨n, K, e, hKfg⟩ := Module.FinitePresentation.exists_fin R M
    obtain ⟨m, f, hfK⟩ := (Submodule.fg_iff_exists_fin_linearMap R (Fin n → R)).mp hKfg
    let g : (Fin n → R) →ₗ[R] M := e.symm.toLinearMap ∘ₗ Submodule.mkQ K
    refine ⟨n, m, f, g, ?_, ?_⟩
    · change Exact f (e.symm.toLinearMap ∘ₗ Submodule.mkQ K)
      rw [LinearMap.exact_iff, LinearEquiv.ker_comp, Submodule.ker_mkQ, hfK]
    · intro x
      obtain ⟨y, hy⟩ := Submodule.mkQ_surjective K (e x)
      refine ⟨y, ?_⟩
      change e.symm (Submodule.mkQ K y) = x
      rw [hy, e.symm_apply_apply]
  · rintro ⟨n, m, f, g, hfg, hg⟩
    rw [LinearMap.exact_iff] at hfg
    exact (Module.FinitePresentation.fg_ker_iff g hg).1 (hfg.symm ▸ Submodule.fg_range f)

end Module.FinitePresentation

end FinitePresentation

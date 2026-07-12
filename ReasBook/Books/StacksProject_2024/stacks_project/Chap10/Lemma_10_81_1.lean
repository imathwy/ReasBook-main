import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: clause (1) is the equational criterion `Module.Flat.iff_forall_isTrivialRelation`
-- rewritten for maps out of finite free modules. Clause (2) implies clause (3) by factoring the
-- intermediate map `g` further to kill `h x`. Clause (3) implies clause (4) by induction on a
-- finite set of generators of `N`, adjoining one generator at a time. Clause (4) implies clause
-- (2) by taking `N = ⊥`.
/-- Lemma 10.81.1: for an `R`-module `M`, the following are equivalent: `M` is flat; every kernel
element of a map `R^n → M` can be killed after factoring through some finite free module; a
factorization that kills a submodule `N` can be refined to kill `N + Rx` for any additional kernel
element `x`; and every finitely generated submodule of such a kernel can be killed by a
factorization through a finite free module. -/
theorem flat_tfae_kernel_factorization_criterion :
    List.TFAE
      [ Module.Flat R M,
        ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R),
          f x = 0 →
            ∃ (m : ℕ) (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
              f = g ∘ₗ h ∧ h x = 0,
        ∀ ⦃n m : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (N : Submodule R (Fin n → R))
          (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)),
          N ≤ ker f →
            N ≤ ker h →
            (∃ g : (Fin m →₀ R) →ₗ[R] M, f = g ∘ₗ h) →
            ∀ x : Fin n → R,
              f x = 0 →
                ∃ (m' : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m' →₀ R)),
                  N + Submodule.span R ({x} : Set (Fin n → R)) ≤ ker h' ∧
                    ∃ g' : (Fin m' →₀ R) →ₗ[R] M, f = g' ∘ₗ h',
        ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (N : Submodule R (Fin n → R)),
          N ≤ ker f →
            N.FG →
            ∃ (m : ℕ) (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)) (g : (Fin m →₀ R) →ₗ[R] M),
              f = g ∘ₗ h ∧ N ≤ ker h ] := sorry

end

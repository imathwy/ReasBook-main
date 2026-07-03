import Mathlib
import Mathlib.Tactic.TFAE
import stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]

-- Proof sketch: `(1) → (2)` is Lemma `15.15.3`. The equivalence of `(3)` and `(4)` is the
-- standard splitting criterion for short exact sequences with finite projective end terms, where
-- clause `(4)` is phrased via the canonical owner property `IsComplemented` on submodules, and
-- `(2) → (3)` follows from the universal-exactness splitting criterion of Lemma `10.82.4`
-- applied to `0 → N → M → coker u → 0`. Clause `(5)` is the special case of `(4)` for
-- submodules of finite free modules of rank `n`, while `(5) → (1)` is proved by applying a
-- splitting obstruction to the map `R → Rⁿ` determined by generators of a proper finitely
-- generated ideal and extracting a nonzero annihilator element from its kernel.
/-- Lemma 15.15.4: for a commutative ring `R`, the following are equivalent: every proper finitely
generated ideal of `R` has nonzero annihilator, every injective map of projective `R`-modules is
universally injective, the cokernel of an injective map of finite projective `R`-modules is finite
projective, every finite projective submodule of a finite projective `R`-module is a direct
summand, and every injective map `R → R^{⊕ n}` is split. -/
theorem proper_fg_ideal_annihilator_ne_bot_tfae :
    List.TFAE
      [ (∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)),
        (∀ {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
            {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
            (u : N →ₗ[R] M), Function.Injective u → u.UniversallyInjective),
        (∀ {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
            {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
            (u : N →ₗ[R] M), Function.Injective u →
              Module.Finite R (M ⧸ u.range) ∧ Module.Projective R (M ⧸ u.range)),
        (∀ {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
            (N : Submodule R M) [Module.Finite R N] [Module.Projective R N],
            IsComplemented N),
        (∀ n : ℕ, ∀ u : R →ₗ[R] (Fin n → R), Function.Injective u →
            ∃ v : (Fin n → R) →ₗ[R] R, v.comp u = LinearMap.id) ] := sorry

/-- Clause `(1) ↔ (2)` of Lemma `15.15.4`: over a commutative ring `R`, every proper finitely
generated ideal has nonzero annihilator if and only if every injective map of projective
`R`-modules is universally injective. -/
theorem proper_fg_ideal_annihilator_ne_bot_iff_injective_projective_maps_universallyInjective :
    (∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R)) ↔
      (∀ {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
          {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
          (u : N →ₗ[R] M), Function.Injective u → u.UniversallyInjective) := by
  simpa using proper_fg_ideal_annihilator_ne_bot_tfae.out 0 1 rfl rfl

end

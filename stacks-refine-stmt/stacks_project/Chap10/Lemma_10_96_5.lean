import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open AdicCompletion

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

-- Domain-style sampling:
-- * source-facing layer: a criterion for when the completion `AdicCompletion I M` is itself
--   `I`-adically complete, phrased by the kernels of the canonical quotient maps.
-- * core/canonical owner: `IsAdicComplete I (AdicCompletion I M)` together with the kernel
--   description `AdicCompletion.pow_smul_top_eq_ker_eval`.
-- * relevant sampled declarations:
--   `IsAdicComplete`,
--   `AdicCompletion.of_bijective_iff`,
--   `AdicCompletion.isAdicComplete`,
--   `AdicCompletion.pow_smul_top_eq_ker_eval`.
-- * primitive data: the owner object `AdicCompletion I M`; the submodules `ker (eval I M n)` are
--   derived from its canonical projections.
-- * bridge/view output: the textbook iff re-expressed directly in terms of the owner completion
--   object and its canonical evaluation maps.
--
-- Proof sketch: let `K_n = (AdicCompletion.eval I M n).ker`. The short exact sequences
-- `0 → K_n / I^n M^∧ → M^∧ / I^n M^∧ → M / I^n M → 0` form an inverse system with surjective
-- transition maps on the left. Applying Lemma `10.87.1` to these systems identifies the adic
-- completion of `M^∧` with `M^∧` precisely when each quotient `K_n / I^n M^∧` vanishes, i.e. when
-- `K_n = I^n M^∧` for every positive `n`.
/-- Lemma 10.96.5: the `I`-adic completion `AdicCompletion I M` is `I`-adically complete if and
only if, for every positive integer `n`, the kernel of the canonical projection
`AdicCompletion I M → M ⧸ (I ^ n • ⊤)` is exactly `I ^ n` times the completed module. -/
theorem isAdicComplete_adicCompletion_iff_ker_eval_eq_pow_smul_top :
    IsAdicComplete I (AdicCompletion I M) ↔
      ∀ n : ℕ+,
        (eval I M (n : ℕ)).ker =
          I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) := sorry

end

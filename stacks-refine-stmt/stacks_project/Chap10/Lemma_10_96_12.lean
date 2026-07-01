import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [IsAdicComplete I R]
variable [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]

-- Domain-style sampling:
-- * source-facing layer: the Stacks criterion that finite generation of `M / IM` plus
--   `⋂ n, I ^ n M = 0` over an `I`-adically complete ring forces `M` itself to be finite.
-- * core/canonical owner: `IsHausdorff I M` for the separatedness hypothesis.
-- * sampled upstream declarations:
--   `IsAdicComplete`,
--   `IsHausdorff`,
--   `IsHausdorff.iInf_pow_smul`,
--   `isAdicComplete_of_finite_of_iInf_pow_smul_eq_bot`.
-- * primitive data: the ring-completeness hypothesis and the finite quotient module
--   `M ⧸ I • ⊤`.
-- * derived API: the equality `⨅ n, I ^ n • ⊤ = ⊥` is the source-facing formulation of the
--   canonical separatedness owner `IsHausdorff I M`.

-- Proof sketch: choose finitely many lifts in `M` of generators of `M / IM`, and let `M'` be the
-- submodule they generate. Lemma `10.96.1` gives a surjection `(M')^∧ → M^∧`, while
-- Lemma `10.96.11` makes `M'` complete because it is finite and inherits
-- `⋂ n, I^n M' = 0`. Thus `M' → M^∧` is surjective. Since the kernel of `M → M^∧` is
-- `⋂ n, I^n M = 0`, the inclusion `M' → M` is surjective, so `M` is finitely generated.
/-- Lemma 10.96.12: if `R` is `I`-adically complete, `⋂ n, I ^ n M = 0`, and the quotient
`M / IM` is a finite `R / I`-module, then `M` is a finite `R`-module. -/
theorem moduleFinite_of_finite_quotient_of_iInf_pow_smul_eq_bot
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    Module.Finite R M := sorry

/-- Canonical owner-facing form of Lemma `10.96.12`, using `IsHausdorff I M` for the separatedness
hypothesis instead of the explicit intersection formula. -/
theorem moduleFinite_of_finite_quotient_of_isHausdorff [IsHausdorff I M] :
    Module.Finite R M := by
  have hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥ :=
    IsHausdorff.iInf_pow_smul inferInstance
  simpa using moduleFinite_of_finite_quotient_of_iInf_pow_smul_eq_bot hM

end

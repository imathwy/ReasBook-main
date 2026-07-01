import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open AdicCompletion

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

-- Proof sketch: apply the finitely generated ideal case from `Lemma_10_96_3` using
-- `I.fg_of_isNoetherianRing`. The first clause is `AdicCompletion.isAdicComplete`, and the second
-- follows by identifying both the image of `AdicCompletion.ofPowSMul I M n` and
-- `I ^ n • ⊤` with the kernel of `AdicCompletion.eval I M n`.
/-- Lemma 10.97.4: over a Noetherian ring, the `I`-adic completion of `M` is `I`-adically
complete, and for every `n` the canonical map from the completion of `I ^ n M` to the completion
of `M` has image exactly `I ^ n M^`. -/
theorem adicCompletion_isAdicComplete_and_completed_pow_smul_range_eq_pow_smul :
    IsAdicComplete I (AdicCompletion I M) ∧
      ∀ n : ℕ,
        (ofPowSMul I M n).range.restrictScalars R =
          I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
  constructor
  · exact isAdicComplete I.fg_of_isNoetherianRing
  intro n
  calc
    (ofPowSMul I M n).range.restrictScalars R = (eval I M n).ker :=
      restrictScalars_range_ofPowSMul_eq_ker_eval I
    _ = I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
      symm
      exact pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing

/-- The quotient of the completed module by `I ^ n` times the completed module is canonically
identified with the quotient `M / I ^ n M`. -/
abbrev adicCompletionQuotientPowLinearEquiv (n : ℕ) :
    ((AdicCompletion I M) ⧸ (I ^ n • (⊤ : Submodule R (AdicCompletion I M)))) ≃ₗ[R]
      M ⧸ (I ^ n • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _
      (pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing)).trans
    ((eval I M n).quotKerEquivOfSurjective (eval_surjective I M n))

end

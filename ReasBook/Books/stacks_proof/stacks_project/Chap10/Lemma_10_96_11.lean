import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open AdicCompletion

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: since `R` is `I`-adically complete, the canonical map `R → AdicCompletion I R`
-- is bijective. For finite `M`, Lemma `10.96.1` makes the tensor-comparison map
-- `M ⊗[R] AdicCompletion I R → AdicCompletion I M` surjective, and transporting along the
-- completion isomorphism of `R` yields surjectivity of `AdicCompletion.of I M`. The hypothesis
-- `⋂ n, I^n M = 0` gives injectivity of `AdicCompletion.of I M`, so
-- `AdicCompletion.of_bijective_iff` implies that `M` is `I`-adically complete.
/-- Lemma 10.96.11: if `R` is `I`-adically complete, `M` is a finite `R`-module, and
`⋂ n, I^n M = 0`, then `M` is `I`-adically complete. -/
@[stacks 031B]
theorem isAdicComplete_of_finite_of_iInf_pow_smul_eq_bot
    [IsAdicComplete I R] [Module.Finite R M]
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥) :
    IsAdicComplete I M := by
  let e : M ≃ₗ[R] TensorProduct R (AdicCompletion I R) M :=
    (TensorProduct.lid R M).symm.trans
      (TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R M))
  have hof_one : (AdicCompletion.of I R) 1 = 1 := by
    ext n
    simp [AdicCompletion.of_apply]
  have hsurj : Function.Surjective (AdicCompletion.of I M) := by
    intro y
    obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
    obtain ⟨z, rfl⟩ := e.surjective x
    refine ⟨z, ?_⟩
    simp [e, hof_one]
  have hhaus : IsHausdorff I M := by
    refine ⟨fun x hx ↦ ?_⟩
    have hx' : x ∈ (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M) : Submodule R M) := by
      simpa [SModEq.zero] using hx
    simpa [hM] using hx'
  exact (AdicCompletion.of_bijective_iff).mp
    ⟨(AdicCompletion.of_injective_iff).mpr hhaus, hsurj⟩

end

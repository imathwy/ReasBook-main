import Mathlib
import StacksProject_2024.Chap15.Remark_15_91_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped IdealPowerTorsion
open scoped TensorProduct
open Ideal.Quotient (eq_zero_iff_mem)

noncomputable section

universe u

/- Domain-style sampling:
- primary domain: Beauville-Laszlo completion glueability for modules over the principal-adic
  completion pair;
- sampled owner declarations:
  `principalAdicCompletion`,
  `(beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact`,
  `completionFPowerTorsionToCompletionTensor`,
  `isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor`;
- best owner abstraction: the source-facing chapter owner
  `(beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact`; the
  completion-specific injectivity criterion in Remark `15.91.11` is the canonical bridge/view
  specialization used to detect failure of that owner;
- primitive data: the quotient module `R ⧸ φR` and an explicit witness `ψ` whose class in
  `R ⧸ φR` is `f`-torsion, nonzero, and maps to zero in
  `(R ⧸ φR) ⊗[R] principalAdicCompletion f`;
- derived API: the generic completion-kernel obstruction from Remark `15.91.11`, and the
  resulting non-glueability statement for the quotient module;
- triage: the theorem below is `source-facing`; `principalAdicCompletion`,
  `(beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact` are the
  `core/canonical` owners; `completionFPowerTorsionToCompletionTensor` and the completion-specific
  kernel-obstruction criterion from Remark `15.91.11` are the `bridge/view` API to the full
  tensor product.
-/

section

variable {R : Type u} [CommRing R]
variable {f φ : R}

local notation "I" => principalIdeal φ
local notation "Q" => R ⧸ I

lemma quotientBySingleElement_mk_mem_fPowerTorsion {ψ : R} (hmul : f * ψ = φ) :
    Ideal.Quotient.mk I ψ ∈ (Q[f^∞] : Submodule R Q) := by
  rw [Submodule.mem_torsion'_iff]
  refine ⟨⟨f, ⟨1, by simp⟩⟩, ?_⟩
  change Ideal.Quotient.mk I (f * ψ) = 0
  rw [eq_zero_iff_mem, hmul]
  exact Ideal.subset_span (by simp)

-- Proof sketch: in the textbook example, `R` is the ring of germs at `0` of smooth real-valued
-- functions, `f(x) = x`, `φ(x) = exp(-1 / x^2)`, and `ψ = φ / f`. The class of `ψ` in `R / φR`
-- gives a nonzero element of `M[f] ⊆ M[f^∞]` whose image in `M ⊗[R] R^∧` is zero.
/-- Example 15.91.12 (Non glueable module): let `M = R / φR`. If `ψ : R` has image `f * ψ = φ`,
the class of `ψ` in `M` is nonzero, and that class maps to zero in
`M ⊗[R] R^∧`, then `M` is not Beauville-Laszlo glueable for the principal completion pair
`(R → R^∧, f)`. In the smooth-germ ring from the source text, one takes `ψ = φ / f`. -/
theorem quotientBySingleElement_not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
    {ψ : R}
    (hmul : f * ψ = φ)
    (hψ_ne : Ideal.Quotient.mk I ψ ≠ 0)
    (hcompletion :
      completionFPowerTorsionToCompletionTensor Q f
          ⟨Ideal.Quotient.mk I ψ, quotientBySingleElement_mk_mem_fPowerTorsion hmul⟩ = 0) :
    ¬ (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact := by
  let x : Q[f^∞] :=
    ⟨Ideal.Quotient.mk I ψ, quotientBySingleElement_mk_mem_fPowerTorsion hmul⟩
  have hx_ne : x ≠ 0 := by
    simpa [x] using hψ_ne
  have hx_completion : completionFPowerTorsionToCompletionTensor Q f x = 0 := by
    simpa [x] using hcompletion
  exact
    not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
      f
      hx_ne
      hx_completion

end

import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_89_1
import stacks_proof.stacks_project.Chap15.PrincipalIdeal
import stacks_proof.stacks_project.Chap15.Lemma_15_90_3
import stacks_proof.stacks_project.Chap15.«15_91_9_1»

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

/-- Helper for Example 15.91.12 (Non glueable module): this is the completion-side tensor map
from the `f^∞`-torsion of `M` into the full tensor product with the principal adic completion. -/
abbrev completionFPowerTorsionToCompletionTensor
    (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (M[f^∞] : Submodule R M) →ₗ[R] M ⊗[R] principalAdicCompletion f :=
  let A := principalAdicCompletion f
  let targetTorsion : Submodule R (A ⊗[R] M) :=
    ((Ideal.map (algebraMap R A) (principalIdeal f)).primaryComponent (A ⊗[R] M)).restrictScalars R
  let hsource : (principalIdeal f).primaryComponent M = (M[f^∞] : Submodule R M) :=
    Module.primaryComponent_principalIdeal_eq_fPowerTorsion f
  let η : (M[f^∞] : Submodule R M) →ₗ[R] targetTorsion :=
    (tensorBaseChangeUnitPrimaryComponent A (principalIdeal f) M).comp
      (LinearEquiv.ofEq _ _ hsource).symm.toLinearMap
  (TensorProduct.comm R A M).toLinearMap.comp <|
    targetTorsion.subtype.comp η

/-- Helper for Example 15.91.12 (Non glueable module): a nonzero class in the kernel of the
completion-side tensor map obstructs Beauville-Laszlo glueability for the completion pair. -/
theorem not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : R)
    {x : M[f^∞]} (hx_ne : x ≠ 0)
    (hcompletion : completionFPowerTorsionToCompletionTensor M f x = 0) :
    ¬ (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact := by
  sorry

/-- Helper for Example 15.91.12 (Non glueable module): the quotient class of `ψ` in `R / φR`
is `f`-power torsion once `f * ψ = φ`. -/
lemma quotientBySingleElement_mk_mem_fPowerTorsion {ψ : R} (hmul : f * ψ = φ) :
    Ideal.Quotient.mk I ψ ∈ (Q[f^∞] : Submodule R Q) := by
  -- We use the explicit annihilator `f`: multiplying the quotient class of `ψ` by `f`
  -- becomes the class of `φ`, hence vanishes modulo the principal ideal `(φ)`.
  rw [Submodule.mem_torsion'_iff]
  refine ⟨⟨f, ⟨1, by simp⟩⟩, ?_⟩
  change Ideal.Quotient.mk I (f * ψ) = 0
  rw [eq_zero_iff_mem, hmul]
  exact Ideal.subset_span (by simp)

/-- Helper for Example 15.91.12 (Non glueable module): the source-proof witness is the quotient
class of `ψ`, viewed inside the canonical `f^∞`-torsion submodule of `R / φR`. -/
abbrev quotientBySingleElement_fPowerTorsionWitness {ψ : R} (hmul : f * ψ = φ) :
    ↥((Q[f^∞] : Submodule R Q)) :=
  ⟨Ideal.Quotient.mk I ψ, quotientBySingleElement_mk_mem_fPowerTorsion hmul⟩

/-- Helper for Example 15.91.12 (Non glueable module): bundling the quotient class of `ψ` into
`Q[f^∞]` does not create a new vanishing relation. -/
lemma quotientBySingleElement_fPowerTorsionWitness_ne_zero {ψ : R}
    (hmul : f * ψ = φ)
    (hψ_ne : Ideal.Quotient.mk I ψ ≠ 0) :
    quotientBySingleElement_fPowerTorsionWitness (f := f) (φ := φ) hmul ≠ 0 := by
  -- A zero torsion witness would already have zero underlying quotient class in `Q`.
  intro hx_zero
  exact hψ_ne (by
    simpa [quotientBySingleElement_fPowerTorsionWitness] using congrArg Subtype.val hx_zero)

-- Proof sketch: in the textbook example, `R` is the ring of germs at `0` of smooth real-valued
-- functions, `f(x) = x`, `φ(x) = exp(-1 / x^2)`, and `ψ = φ / f`. The class of `ψ` in `R / φR`
-- gives a nonzero element of `M[f] ⊆ M[f^∞]` whose image in `M ⊗[R] R^∧` is zero.
/-- Example 15.91.12 (Non glueable module): let `M = R / φR`. If `ψ : R` has image `f * ψ = φ`,
the class of `ψ` in `M` is nonzero, and that class maps to zero in
`M ⊗[R] R^∧`, then `M` is not Beauville-Laszlo glueable for the principal completion pair
`(R → R^∧, f)`. In the smooth-germ ring from the source text, one takes `ψ = φ / f`. -/
@[stacks 0BNY]
theorem quotientBySingleElement_not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
    {ψ : R}
    (hmul : f * ψ = φ)
    (hψ_ne : Ideal.Quotient.mk I ψ ≠ 0)
    (hcompletion :
      completionFPowerTorsionToCompletionTensor Q f
          ⟨Ideal.Quotient.mk I ψ, quotientBySingleElement_mk_mem_fPowerTorsion hmul⟩ = 0) :
    ¬ (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) Q f).ShortExact := by
  -- Package the quotient class of `ψ` as the canonical `f`-power torsion witness in `Q`.
  let x : ↥((Q[f^∞] : Submodule R Q)) :=
    quotientBySingleElement_fPowerTorsionWitness (f := f) (φ := φ) hmul
  -- The hypothesis `hψ_ne` says this torsion witness is genuinely nonzero.
  have hx_ne : x ≠ 0 := by
    simpa [x] using
      quotientBySingleElement_fPowerTorsionWitness_ne_zero (f := f) (φ := φ) hmul hψ_ne
  -- The completion hypothesis says the same witness dies after tensoring with the completion.
  have hx_completion : completionFPowerTorsionToCompletionTensor Q f x = 0 := by
    simpa [x, quotientBySingleElement_fPowerTorsionWitness] using hcompletion
  -- Remark 15.91.11 turns a nonzero torsion class in the kernel into non-glueability.
  exact
    not_glueable_along_principalAdicCompletion_of_nonzero_completionTensor_kernel
      f
      hx_ne
      hx_completion

end

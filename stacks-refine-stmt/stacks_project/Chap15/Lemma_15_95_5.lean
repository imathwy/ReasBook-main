import Mathlib
import stacks_project.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {I : Ideal A} {M : ModuleCat A}

namespace ModuleCat

/-
Domain-style sampling for Lemma 15.95.5:
- primary domain: derived completeness, adic completeness, and finite generation of modules over
  the completed ring `AdicCompletion I A`;
- sampled owner declarations:
  `IsAdicComplete`,
  `ModuleCat.isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff`,
  `moduleFinite_of_finite_quotient_of_isHausdorff`,
  `AdicCompletion.module`,
  `AdicCompletion.ofLinearEquiv`;
- best owner abstraction: this is a `source-facing` theorem on `M`; the core owners are
  `IsAdicComplete I M` and `Module.Finite (AdicCompletion I A) M`, while the completion-side
  statement for `AdicCompletion I M` is only a `bridge/view`;
- primitive vs. derived:
  primitive data are the ideal `I`, the module `M`, the derived-completeness hypothesis, and the
  finite quotient `M / I M`;
  derived API is the canonical `Module (AdicCompletion I A) M` instance under
  `IsAdicComplete I M`, together with the completion-side finiteness conclusion for
  `AdicCompletion I M`.
-/

open AdicCompletion

namespace IsAdicComplete

-- Transport the canonical `AdicCompletion I A`-action on `AdicCompletion I M` across
-- `AdicCompletion.ofLinearEquiv I M`.
noncomputable instance [IsAdicComplete I M] :
    Module (AdicCompletion I A) M :=
  Module.compHom M <|
    ((ofLinearEquiv I M).symm.conjRingEquiv.toRingHom).comp
      (Module.toModuleEnd A (AdicCompletion I M))

-- Proof sketch: equip `M` with its canonical `AdicCompletion I A`-module structure from `hM`,
-- compare it with the canonical completion module `AdicCompletion I M` using
-- `AdicCompletion.ofLinearEquiv I M`, and apply the owner-facing finiteness criterion from
-- Lemma `10.96.12`.
/-- If `M` is already `I`-adically complete, then `M`, equipped with its canonical
`AdicCompletion I A`-module structure, is finite as soon as `M / I M` is finite over `A / I`. -/
theorem moduleFinite_over_adicCompletion_of_finite_quotient
    [IsAdicComplete I M]
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    Module.Finite (AdicCompletion I A) M := sorry

end IsAdicComplete

section

variable [IsNoetherianRing A]

-- Proof sketch: use Proposition `15.92.5` to identify adic completeness with derived
-- completeness plus `I`-adic separatedness, prove the separatedness hypothesis from the
-- Noetherian finiteness input, and conclude by Chapter `10`.
/-- Under the hypotheses of Lemma `15.95.5`, the module `M` is `I`-adically complete. -/
theorem isAdicComplete_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    IsAdicComplete I M := sorry

-- Proof sketch: combine the completeness bridge above with the owner theorem in the
-- `IsAdicComplete` namespace.
/-- Lemma 15.95.5: if `M` is derived complete with respect to `I` and `M / I M` is finite over
`A / I`, then `M`, equipped with its canonical `AdicCompletion I A`-module structure, is a finite
module over the completed ring `AdicCompletion I A`. -/
theorem moduleFinite_over_adicCompletion_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    let _ : IsAdicComplete I M :=
      isAdicComplete_of_isDerivedComplete_of_finite_quotient hM
    Module.Finite (AdicCompletion I A) M := by
  let _ : IsAdicComplete I M :=
    isAdicComplete_of_isDerivedComplete_of_finite_quotient hM
  exact IsAdicComplete.moduleFinite_over_adicCompletion_of_finite_quotient

-- Proof sketch: first apply Lemma `15.95.5` to `M`, then transport finite generation across the
-- canonical identification `AdicCompletion.ofLinearEquiv I M`.
/-- Completion-side companion to Lemma `15.95.5`: under the same hypotheses,
`AdicCompletion I M` is a finite module over `AdicCompletion I A`. -/
theorem moduleFinite_adicCompletion_of_isDerivedComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    Module.Finite (AdicCompletion I A) (AdicCompletion I M) := sorry

end

end ModuleCat

end

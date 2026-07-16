import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import StacksProject_2024.stacks_project.Chap10.Lemma_10_67_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/- Layering for this item.
Sampled declarations in this localization/quotient domain:
* `embeddedPrimeFreeSubmodule` from `Lemma_10_67_2` is the source-facing submodule.
* `localizedQuotientEquiv` is the owner equivalence for localizing quotients.
* `Submodule.quotEquivOfEq` is the canonical rewrite once the localized submodule is identified.
* `Lemma_10_9_13` already recalls the same owner pattern for localized quotients in this chapter.
Target triage:
* source-facing: the quotient identification
  `LocalizedModule.Away f (M ⧸ embeddedPrimeFreeSubmodule R M) ≃ₗ[Localization.Away f]
    (LocalizedModule.Away f M ⧸
      embeddedPrimeFreeSubmodule (Localization.Away f) (LocalizedModule.Away f M))`.
* core/canonical owner: `localizedQuotientEquiv`.
* bridge/view: the supporting equality
  `(embeddedPrimeFreeSubmodule R M).localized (.powers f) =
    embeddedPrimeFreeSubmodule (Localization.Away f) (LocalizedModule.Away f M)`
  rewrites the owner equivalence into the source-facing quotient statement.
-/

/- Core/canonical owner recall: localization of quotients is controlled by
`localizedQuotientEquiv`. -/
recall localizedQuotientEquiv

variable (f : R)

local notation "Rloc" => Localization.Away f
local notation "Mloc" => LocalizedModule.Away f M

/-- Supporting bridge: the canonical submodule from Lemma 10.67.2 is compatible with away
localization. -/
theorem embeddedPrimeFreeSubmodule_localized_eq :
    (embeddedPrimeFreeSubmodule R M).localized (.powers f) =
      embeddedPrimeFreeSubmodule Rloc Mloc :=
  sorry

/-- Lemma 10.67.3: after inverting `f`, the quotient by the canonical submodule from
Lemma 10.67.2 agrees with the canonical quotient of the localized module. -/
noncomputable def away_embeddedPrimeFreeQuotientEquiv :
    LocalizedModule.Away f (M ⧸ embeddedPrimeFreeSubmodule R M) ≃ₗ[Localization.Away f]
      Mloc ⧸ embeddedPrimeFreeSubmodule Rloc Mloc :=
  (localizedQuotientEquiv (.powers f) (embeddedPrimeFreeSubmodule R M)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (embeddedPrimeFreeSubmodule_localized_eq R M f)

-- Proof sketch: unfold `away_embeddedPrimeFreeQuotientEquiv`; the statement is exactly its
-- defining composition of the canonical localized quotient equivalence with the quotient rewrite
-- coming from `embeddedPrimeFreeSubmodule_localized_eq`.
/-- The equivalence in Lemma 10.67.3 is defined by composing the canonical localization-of-quotient
equivalence with the quotient rewrite induced by
`embeddedPrimeFreeSubmodule_localized_eq`. -/
theorem away_embeddedPrimeFreeQuotientEquiv_def :
    away_embeddedPrimeFreeQuotientEquiv R M f =
      (localizedQuotientEquiv (.powers f) (embeddedPrimeFreeSubmodule R M)).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ (embeddedPrimeFreeSubmodule_localized_eq R M f) :=
  sorry

end

import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Lemma_17_22_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits MonoidalClosed

noncomputable section

namespace SheafOfModules

/- Domain-style sampling for Lemma 18.27.11:
- primary domain: internal Hom in `SheafOfModules 𝒪` and its filtered-colimit comparison;
- sampled owner declarations:
  `colimit.post`,
  `isIso_internalHomColimitComparison_of_isFinitePresentation`;
- best owner abstraction: the comparison morphism is the generic owner `colimit.post`, while the
  finite-presentation isomorphism criterion is the source-facing theorem in `SheafOfModules`;
- primitive data: a ring-valued sheaf `𝒪`, a finitely presented module sheaf `ℱ`, and a filtered
  diagram `𝒢`;
- derived API: the comparison morphism and its isomorphism criterion are reused directly here. -/

/- Lemma 18.27.11, core/canonical recall: the comparison morphism
`colim_λ ℋom_𝒪(ℱ, 𝒢_λ) ⟶ ℋom_𝒪(ℱ, colim_λ 𝒢_λ)` is the specialization
`colimit.post 𝒢 (ihom ℱ)` of the generic colimit comparison map. -/
recall colimit.post

/- Lemma 18.27.11, core/canonical recall: for finitely presented `ℱ`, the comparison morphism is
an isomorphism by
`SheafOfModules.isIso_internalHomColimitComparison_of_isFinitePresentation`. -/
recall isIso_internalHomColimitComparison_of_isFinitePresentation

end SheafOfModules

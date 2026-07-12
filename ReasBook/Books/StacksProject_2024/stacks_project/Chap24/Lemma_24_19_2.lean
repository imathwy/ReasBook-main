import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap24.Lemma_24_10_2
import StacksProject_2024.Chap24.Lemma_24_17_2
import StacksProject_2024.Chap24.Lemma_24_17_3

open SheafOfModules.RingedSite

noncomputable section

namespace SheafOfModules.RingedSite

-- Semantic search note: `lean_leansearch` only surfaced unrelated scheme-level open-immersion
-- restriction/pushforward owners, so the owner/API choice here was checked against the local
-- localized graded comparison in `Chap24/Lemma_24_10_2.lean` and the Chapter 24 DG tensor owners
-- in `Chap24/Lemma_24_17_2.lean` and `Chap24/Lemma_24_17_3.lean`.

/- Lemma 24.19.2
Recall: the localized lower-shriek and restriction owners are
`ringedSiteLocalizedExtensionByZero J 𝒪 U` and `ringedSiteLocalizedRestriction J 𝒪 U`, while the
Chapter 24 differential graded tensor product is carried by
`HasDifferentialGradedTensorHomAdjunction.tensor` on right modules and bimodules. The source
comparison
`j_! \mathcal M \otimes_{\mathcal A} \mathcal N
  \cong j_!(\mathcal M \otimes_{\mathcal A_U} \mathcal N|_U)`
as complexes is the differential-graded refinement of the graded comparison flagged in
`Lemma_24_10_2`; stating it faithfully still requires a localized differential graded
restriction/extension-plus-tensor owner that is not yet present in this workspace, so this item
stays as a recall block rather than a fake theorem shell. -/
recall ringedSiteLocalizedRestriction
recall ringedSiteLocalizedExtensionByZero
recall RightLinearEndomorphismDGAHom.toDifferentialGradedBimodule
recall HasDifferentialGradedTensorHomAdjunction.tensor

end SheafOfModules.RingedSite

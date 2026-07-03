import Mathlib
import StacksProject_2024.Chap18.Definition_18_6_1
import StacksProject_2024.Chap21.Definition_21_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Sheaf

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{max u v})]

-- Proof sketch: present the given morphism of ringed topoi by the ringed-site morphism `f`.
-- For any sheaf of sets `K` on the target, compute `H^q(K, f_* ℐ)` on the localized site. After
-- enlarging the site as in Lemma `18.7.2`, this becomes ordinary cohomology of the underlying
-- abelian sheaf of `ℐ` on a site where `f_*` is induced by precomposition. The resulting Čech
-- complexes agree with those for `ℐ`, and Lemma `21.12.3` gives vanishing of positive Čech
-- cohomology because `ℐ` is injective. Lemma `21.10.9` then upgrades that Čech vanishing to the
-- required higher-cohomology vanishing for every `K`.
/-- Lemma 21.14.1: for a morphism of ringed topoi, formalized here by a morphism of ringed sites
`f`, the pushforward `f_* \mathcal I` of an injective `\mathcal O_{\mathcal C}`-module sheaf
`\mathcal I` is totally acyclic on the target site. -/
theorem modulePushforward_isTotallyAcyclicOne_of_injective
    (ℐ : SheafOfModules X.structureSheaf) (hℐ : Injective ℐ) :
    IsTotallyAcyclicOne
      ((SheafOfModules.toSheaf Y.structureSheaf).obj
        ((SheafOfModules.pushforward f.structureSheafMap).obj ℐ)) := sorry

end RingedSite.Hom

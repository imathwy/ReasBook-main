import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap21.Definition_21_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Sheaf
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf Y.siteTopology AddCommGrpCat.{max u v})]

/- Domain-style sampling for Lemma 21.14.1:
- primary domain: acyclicity statements for sheaves of modules on ringed sites, expressed through
  the underlying abelian-sheaf owner `CategoryTheory.Sheaf.IsTotallyAcyclicOne`;
- sampled owner declarations:
  `CategoryTheory.Sheaf.IsTotallyAcyclicOne`,
  `RingedSite.Hom.modulePushforward`,
  `SheafOfModules.toSheaf`,
  `CategoryTheory.totallyAcyclicModule_isRightAcyclicForPushforward`;
- best owner abstraction: the Chapter 18 direct-image owner `f.modulePushforward`, with this file
  providing the source-facing bridge from an injective module sheaf to the acyclicity owner on the
  underlying abelian sheaf;
- primitive data: a morphism of ringed sites `f` and an injective module sheaf `ℐ`;
- derived API: the induced `IsTotallyAcyclicOne` instance for the underlying abelian sheaf of
  `f.modulePushforward.obj ℐ`.

This theorem's public surface intentionally omits
`[Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]`: that site hypothesis belongs
to proof routes used elsewhere in Chapter 21, but it is not part of the canonical
`IsTotallyAcyclicOne` owner data appearing in the conclusion.

Source/core/bridge triage:
- `source-facing`: the Stacks claim that direct image of an injective module sheaf is acyclic for
  all cohomology-over-a-sheaf functors on the target;
- `core/canonical`: `CategoryTheory.Sheaf.IsTotallyAcyclicOne` and `f.modulePushforward`;
- `bridge/view`: forgetting module structure via `SheafOfModules.toSheaf Y.structureSheaf`. -/

-- Proof sketch: present the given morphism of ringed topoi by the ringed-site morphism `f`.
-- For any sheaf of sets `K` on the target, compute `H^q(K, f_* ℐ)` on the localized site. After
-- enlarging the site as in Lemma `18.7.2`, this becomes ordinary cohomology of the underlying
-- abelian sheaf of `ℐ` on a site where `f_*` is induced by precomposition. The resulting Čech
-- complexes agree with those for `ℐ`, and Lemma `21.12.3` gives vanishing of positive Čech
-- cohomology because `ℐ` is injective. Lemma `21.10.9` then upgrades that Čech vanishing to the
-- required higher-cohomology vanishing for every `K`.
/-- Lemma 21.14.1: for a morphism of ringed topoi, formalized here by a morphism of ringed sites
`f`, the pushforward `f_* ℐ` of an injective `𝒪_X`-module sheaf `ℐ` is totally acyclic on the
target site `Y`. This is exposed as the canonical `IsTotallyAcyclicOne` instance on the
underlying abelian sheaf of `f_* ℐ`. -/
@[stacks 072Z]
instance modulePushforward_isTotallyAcyclicOne_of_injective
    (ℐ : SheafOfModules X.structureSheaf) [Injective ℐ] :
    IsTotallyAcyclicOne
      ((SheafOfModules.toSheaf Y.structureSheaf).obj (f.modulePushforward.obj ℐ)) := by
  sorry

end RingedSite.Hom

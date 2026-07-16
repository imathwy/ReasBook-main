import StacksProject_2024.stacks_project.Chap08.Lemma_8_10_3
import StacksProject_2024.stacks_project.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

/- Domain-style sampling for Situation 21.38.1:
- primary domain: ringed sites and the morphisms of topoi induced by cocontinuous functors of
  sites;
- sampled owner declarations:
  `RingedSite`,
  `RingedSite.ofRingSheaf`,
  `RingedSite.Hom`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`.
- best owner abstraction: the inherited ringed structure on the total category should be owned by a
  `RingedSite`, while the induced geometric morphism remains canonically owned by
  `P.p.morphismOfTopoiInOfCocontinuous`.
- primitive data: the inherited topology on `P.S` and the pulled-back ring sheaf
  `P.p.sheafPushforwardContinuous RingCat ...`;
- derived API: the direct canonical recall of the induced morphism of topoi and the corresponding
  ringed-site morphism `projectionRingedSiteHom X P`.

Source/core/bridge triage:
- `source-facing`: `inheritedRingedSite`;
- `core/canonical`: `RingedSite`, `RingedSite.Hom`, and
  `P.p.morphismOfTopoiInOfCocontinuous`;
- `bridge/view`: the specialization of
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage` to `P.p`. -/
-- Semantic search note: deferred `lean_leansearch` was unavailable in this runner, so the owner
-- choice here was verified against `Lemma_8_10_3` and the Chapter 7 topos API.

section

variable (X : RingedSite.{u, v}) (P : FibredCategoryOver X)
variable [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]

/-- Helper for Situation 21.38.1: the pulled-back ring-valued structure sheaf on the inherited
topology of the total category. -/
abbrev inheritedStructureSheaf :
    Sheaf (inheritedTopology X.siteTopology P) RingCat.{max u v} :=
  -- Name the pushed-forward structure sheaf once so later ringed-site packaging stays
  -- definitionally stable.
  (P.p.sheafPushforwardContinuous RingCat.{max u v}
    (inheritedTopology X.siteTopology P) X.siteTopology).obj X.structureSheaf

/-- Situation 21.38.1: the total category of a fibred category over a ringed site `X`, equipped
with the topology inherited from the base site and the structure sheaf pulled back from
`X.structureSheaf` along the projection `P.p`. This is the source ringed site for the induced
morphism of ringed topoi, and the companion `projectionRingedSiteHom X P` packages the
corresponding site-presented morphism of ringed topoi. -/
@[stacks 08P8]
abbrev inheritedRingedSite :
    RingedSite.{u, v} :=
  -- Package the inherited topology with the named pulled-back structure sheaf.
  RingedSite.ofRingSheaf
    (inheritedTopology X.siteTopology P)
    (inheritedStructureSheaf X P)

section

variable [IsMorphismOfSites (inheritedTopology X.siteTopology P) X.siteTopology P.p]

-- Route correction: package the projection directly on `RingedSite.Hom`; once the inherited
-- structure sheaf is named explicitly, its comparison map is definitionally the identity.
/-- Helper for Situation 21.38.1: the canonical projection from the base ringed site `X` to the
ringed site on the total category with inherited topology and pulled-back structure sheaf. -/
abbrev projectionRingedSiteHom :
    X ⟶ inheritedRingedSite X P where
  base := P.p
  isMorphismOfSites := ‹IsMorphismOfSites
    (inheritedTopology X.siteTopology P) X.siteTopology P.p›
  -- The target structure sheaf is exactly the pushed-forward source structure sheaf.
  structureSheafMap := 𝟙 (inheritedStructureSheaf X P)

/-- Helper for Situation 21.38.1: the underlying site functor of
`projectionRingedSiteHom X P` is `P.p`. -/
@[simp] theorem projectionRingedSiteHom_base :
    RingedSite.Hom.base (projectionRingedSiteHom X P) = P.p := by
  -- The bundled morphism was introduced with base functor `P.p`.
  rfl

end

end

end FibredCategoryOver
end CategoryTheory

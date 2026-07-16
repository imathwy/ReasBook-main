import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap07.Definition_7_15_1_Topoi
import stacks_proof.stacks_project.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v

/- Domain-style sampling for Definition 18.7.1:
- primary domain: ringed sites and ringed topoi presented by sites;
- sampled owner API:
  `RingedSite`,
  `RingedSite.Hom`,
  `Functor.morphismOfTopoiInOfContinuous`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `RingedSite.Hom.IsRingedEquivalence`;
- source/core/bridge triage:
  `source-facing`: a ringed topos presented by a site, and its site-presented morphisms;
  `core/canonical`: `RingedSite` for objects and `RingedSite.Hom` for morphisms;
  `bridge/view`: the induced underlying morphism of topoi, when the canonical sheaf-theoretic
  site-morphism hypotheses carried by `RingedSite.Hom.base` are read through the Chapter 7 owner
  `Functor.morphismOfTopoiInOfContinuous`, together with the stronger ringed bridge owner
  `RingedSite.Hom.IsRingedEquivalence`.

Primitive data separate cleanly as follows:
- object level: exactly the data already owned by `RingedSite`;
- morphism level: exactly the data already owned by `RingedSite.Hom`, namely a site morphism
  together with the induced map on structure sheaves into the canonical pushforward.

Accordingly, this item should recall the canonical owners `RingedSite` and `RingedSite.Hom`
directly. The underlying morphism of topoi is auxiliary bridge data and should be exposed through
the canonical Chapter 7 site-to-topos bridge, rather than by duplicating its hypotheses in a new
wrapper owner. -/

/- Definition 18.7.1: a ringed topos presented by a site is just a ringed site, i.e. a site
together with a sheaf of rings. -/
recall RingedSite

/- Definition 18.7.1: a morphism of ringed topoi presented by sites is the canonical owner
`RingedSite.Hom`, i.e. a morphism of sites together with the adjoint pushforward form
`\mathcal O_Y \to f_* \mathcal O_X` of the structure-sheaf map. -/
recall RingedSite.Hom

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}}

open scoped MorphismOfTopoiIn

/-- The underlying morphism of topoi attached to a morphism of ringed sites. This is the canonical
Chapter 7 site-to-topos bridge specialized to the site morphism `f.base`, so no extra wrapper
owner is needed around the already bundled `IsMorphismOfSites` data. The only extra input is the
canonical left-exactness instance for the sheaf pullback functor required by
`Functor.morphismOfTopoiInOfContinuous`. -/
noncomputable abbrev toMorphismOfTopoi (f : X ⟶ Y)
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)] :
    MorphismOfTopoiIn Y.siteTopology X.siteTopology :=
  f.base.morphismOfTopoiInOfContinuous Y.siteTopology X.siteTopology

@[simp] theorem toMorphismOfTopoi_pushforward
    (f : X ⟶ Y)
    [PreservesFiniteLimits
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)] :
    f.toMorphismOfTopoi _* =
      f.base.sheafPushforwardContinuous (Type (max u v)) Y.siteTopology X.siteTopology :=
  rfl

/-- The presented ringed topoi underlying `f` are equivalent: the underlying morphism of topoi is
an equivalence, and the structure-sheaf comparison is an isomorphism in the pushforward form
carried by `RingedSite.Hom`. Equivalently, the adjoint inverse-image form of the structure-sheaf
map is an isomorphism. -/
class IsRingedEquivalence (f : X ⟶ Y) : Prop where
  /-- The inverse-image functor of the canonical underlying morphism of topoi is an equivalence. -/
  inverseImage_isEquivalence :
    Functor.IsEquivalence
      (f.base.sheafPullback (Type (max u v)) Y.siteTopology X.siteTopology)
  /-- The structure-sheaf map of `f` is an isomorphism. -/
  structureSheafMap_isIso : IsIso f.structureSheafMap

attribute [instance] IsRingedEquivalence.inverseImage_isEquivalence
attribute [instance] IsRingedEquivalence.structureSheafMap_isIso

end RingedSite.Hom

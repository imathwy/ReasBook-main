import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap07.Definition_7_15_1_Topoi
import stacks_project.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/- Domain-style sampling for Definition 18.7.1:
- primary domain: ringed sites and ringed topoi presented by sites;
- sampled owner API:
  `RingedSite`,
  `RingedSite.Hom`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `RingedSite.Hom.IsToposEquivalence`,
  `RingedSite.Hom.IsRingedEquivalence`;
- source/core/bridge triage:
  `source-facing`: a ringed topos presented by a site, and its site-presented morphisms;
  `core/canonical`: `RingedSite` for objects and `RingedSite.Hom` for morphisms;
  `bridge/view`: the induced underlying morphism of topoi, when the canonical sheaf-theoretic
  hypotheses needed to build it are available, the bundled bridge owner
    `RingedSite.Hom.IsToposEquivalence`, the stronger ringed bridge owner
    `RingedSite.Hom.IsRingedEquivalence`, and the ring-sheaf pushforward attached to the base
    site morphism.

Primitive data separate cleanly as follows:
- object level: exactly the data already owned by `RingedSite`;
- morphism level: exactly the data already owned by `RingedSite.Hom`, namely a site morphism
  together with the induced map on structure sheaves into the canonical pushforward.

Accordingly, this item should recall the canonical owners `RingedSite` and `RingedSite.Hom`
directly. The underlying morphism of topoi is auxiliary bridge data, and any bridge structure must
reuse the canonical site-level owner rather than duplicating its primitive fields or introducing an
independent ring-sheaf pushforward. -/

/- Definition 18.7.1: a ringed topos presented by a site is just a ringed site, i.e. a site
together with a sheaf of rings. -/
recall RingedSite

/- Definition 18.7.1: a morphism of ringed topoi presented by sites is the canonical owner
`RingedSite.Hom`, i.e. a morphism of sites together with the adjoint pushforward form
`\mathcal O_Y \to f_* \mathcal O_X` of the structure-sheaf map. -/
recall RingedSite.Hom

namespace RingedSite.Hom

variable {X Y Z : RingedSite.{u, v}}

/-- The canonical pushforward functor on ring-valued sheaves attached to a morphism of ringed
sites. -/
abbrev ringPushforward (f : X ⟶ Y) :
    Sheaf X.siteTopology RingCat.{max u v} ⥤ Sheaf Y.siteTopology RingCat.{max u v} :=
  f.base.sheafPushforwardContinuous RingCat.{max u v} Y.siteTopology X.siteTopology

open scoped MorphismOfTopoiIn

/-- Bridge data ensuring that a morphism of ringed sites presents an underlying morphism of topoi
in a specified sheaf-value category. The underlying morphism of topoi uses the special case
`A = Type w`. -/
class HasToposMorphism (A : Type w) [Category A] (f : X ⟶ Y) : Prop where
  /-- The canonical pushforward on set-valued sheaves is a right adjoint. -/
  sheafPushforwardContinuous_isRightAdjoint :
    (f.base.sheafPushforwardContinuous A Y.siteTopology X.siteTopology).IsRightAdjoint
  /-- The canonical pullback on set-valued sheaves preserves finite limits. -/
  sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (f.base.sheafPullback A Y.siteTopology X.siteTopology)

attribute [instance] HasToposMorphism.sheafPushforwardContinuous_isRightAdjoint
attribute [instance] HasToposMorphism.sheafPullback_preservesFiniteLimits

/-- Explicit right-adjoint and left-exactness data package into the bundled bridge owner
`HasToposMorphism`. -/
instance instHasToposMorphismOfSheafFunctorData
    (A : Type w) [Category A] (f : X ⟶ Y)
    [(f.base.sheafPushforwardContinuous A Y.siteTopology X.siteTopology).IsRightAdjoint]
    [PreservesFiniteLimits (f.base.sheafPullback A Y.siteTopology X.siteTopology)] :
    HasToposMorphism A f where
  sheafPushforwardContinuous_isRightAdjoint := inferInstance
  sheafPullback_preservesFiniteLimits := inferInstance

/-- The underlying morphism of topoi attached to a morphism of ringed sites, whenever the
bundled bridge owner `HasToposMorphism` is available. This is a bridge/view from the source-facing
owner `RingedSite.Hom` to the canonical topos-level owner `MorphismOfTopoiIn`. -/
noncomputable abbrev toMorphismOfTopoi (f : X ⟶ Y) [HasToposMorphism (Type w) f] :
    MorphismOfTopoiIn.{u, u, v, v, w} Y.siteTopology X.siteTopology where
  inverseImageFunctor :=
    LeftExactFunctor.of (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)
  pushforward := f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology
  adjunction := f.base.sheafAdjunctionContinuous (Type w) Y.siteTopology X.siteTopology

@[simp] theorem toMorphismOfTopoi_pushforward
    (f : X ⟶ Y) [HasToposMorphism (Type w) f] :
    f.toMorphismOfTopoi _* =
      f.base.sheafPushforwardContinuous (Type w) Y.siteTopology X.siteTopology :=
  rfl

/-- The underlying morphism of topoi of `f` is an equivalence. This keeps the auxiliary
sheaf-theoretic hypotheses needed to build `f.toMorphismOfTopoi` internal to a single bridge
owner, so downstream theorem headers can state only the mathematically primary equivalence
hypothesis. -/
class IsToposEquivalence (f : X ⟶ Y) : Prop extends HasToposMorphism (Type (max u v)) f where
  /-- The inverse-image functor of the canonical underlying morphism of topoi is an equivalence. -/
  inverseImage_isEquivalence :
    Functor.IsEquivalence (f.toMorphismOfTopoi.inverseImage)

attribute [instance] IsToposEquivalence.inverseImage_isEquivalence

/-- The presented ringed topoi underlying `f` are equivalent: the underlying morphism of topoi is
an equivalence, and the structure-sheaf comparison is an isomorphism in the pushforward form
carried by `RingedSite.Hom`. Equivalently, the adjoint inverse-image form of the structure-sheaf
map is an isomorphism. -/
class IsRingedEquivalence (f : X ⟶ Y) : Prop extends IsToposEquivalence f where
  /-- The structure-sheaf map of `f` is an isomorphism. -/
  structureSheafMap_isIso : IsIso f.structureSheafMap

attribute [instance] IsRingedEquivalence.structureSheafMap_isIso

end RingedSite.Hom

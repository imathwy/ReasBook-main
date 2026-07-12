import StacksProject_2024.Chap04.Lemma_4_33_7
import StacksProject_2024.Chap07.Lemma_7_21_2
import StacksProject_2024.Chap07.Lemma_7_22_4
import StacksProject_2024.Chap07.Lemma_7_23_1
import StacksProject_2024.Chap07.Lemma_7_28_4
import StacksProject_2024.Chap18.Definition_18_7_1
import StacksProject_2024.Chap18.Lemma_18_20_1
import StacksProject_2024.Chap21.Situation_21_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u v

namespace CategoryTheory
namespace FibredCategoryOver

section

variable {X : RingedSite.{u, v}} (P : FibredCategoryOver X)
variable [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
variable [Functor.IsCocontinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
variable [IsMorphismOfSites (inheritedTopology X.siteTopology P) X.siteTopology P.p]

local notation "JP" => inheritedTopology X.siteTopology P

/- Domain-style sampling for Lemma 21.38.2:
- primary domain: localized morphisms of topoi induced by slice functors coming from a fibred
  category over a ringed site;
- sampled owner API:
  `RingedSite.Hom.localization`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward`,
  `Functor.sheafPushforwardContinuousComp'`;
- best owner abstraction: the localized projection `π_U` is already canonically owned by the
  localized ringed-site morphism `RingedSite.Hom.localization (projectionRingedSiteHom X P) U`,
  and its underlying geometric morphism is obtained by `toMorphismOfTopoi`. The section morphism
  is derived API from that owner, not primitive local data.

Source/core/bridge triage:
- `source-facing`: the existence of a section `σ` for the localized projection morphism of topoi;
- `core/canonical`: `RingedSite.Hom.localization`, `RingedSite.Hom.toMorphismOfTopoi`, and the
  Chapter 7 sheaf pushforward/pullback owners on the slice sites;
- `bridge/view`: the slice pullback right adjoint to `Over.post P.p`, used only to realize the
  section and identify `σ⁻¹` with `π_U _*`.

Primitive data are the projection morphism `projectionRingedSiteHom X P` and its localization at
`U`; the section morphism and the formula `σ⁻¹ = π_U _*` are derived theorem-level output. -/
/-- The canonical projection functor `Over.post (projectionRingedSiteHom X P).base` preserves
finite limits as soon as the source-facing slice functor `Over.post P.p` does. -/
instance projectionRingedSiteHom_overPost_preservesFiniteLimits (U : P.S)
    [PreservesFiniteLimits
      ((Over.post P.p).sheafPullback
        (Type (max u v))
        ((JP).over U)
        (X.siteTopology.over (P.p.obj U)))] :
    PreservesFiniteLimits
      ((Over.post (projectionRingedSiteHom X P).base).sheafPullback
        (Type (max u v))
        ((inheritedRingedSite X P).siteTopology.over U)
        (X.siteTopology.over ((projectionRingedSiteHom X P).base.obj U))) := by
  simpa [projectionRingedSiteHom, inheritedRingedSite]
    using (show PreservesFiniteLimits
      ((Over.post P.p).sheafPullback
        (Type (max u v))
        ((JP).over U)
        (X.siteTopology.over (P.p.obj U))) from inferInstance)

/-- The localized projection ringed-site morphism is continuous on the localized inherited site. -/
instance localizedProjection_isContinuous (U : P.S) :
    ((projectionRingedSiteHom X P).localization U).base.IsContinuous
      (((inheritedRingedSite X P).localization U).siteTopology)
      ((X.localization (P.p.obj U)).siteTopology) :=
  -- Reuse the owner theorem for localized morphisms of ringed sites directly.
  ((projectionRingedSiteHom X P).localization U).isMorphismOfSites.toIsContinuous

/-- The canonical localized projection preserves finite limits whenever the slice pullback along
`P.p` does. -/
instance localizedProjection_preservesFiniteLimits (U : P.S)
    [PreservesFiniteLimits
      ((Over.post P.p).sheafPullback
        (Type (max u v))
        ((JP).over U)
        (X.siteTopology.over (P.p.obj U)))] :
    PreservesFiniteLimits
      (((projectionRingedSiteHom X P).localization U).base.sheafPullback
        (Type (max u v))
        (((inheritedRingedSite X P).localization U).siteTopology)
        ((X.localization (P.p.obj U)).siteTopology)) := by
  -- The localized projection is definitionaly the localized ringed-site morphism.
  simpa [projectionRingedSiteHom, inheritedRingedSite, RingedSite.Hom.localization,
    RingedSite.localization] using
    (show PreservesFiniteLimits
      (((projectionRingedSiteHom X P).localization U).base.sheafPullback
        (Type (max u v))
        (((inheritedRingedSite X P).localization U).siteTopology)
        ((X.localization ((projectionRingedSiteHom X P).base.obj U)).siteTopology)) from
      RingedSite.Hom.localization_sheafPullback_preservesFiniteLimits
        (projectionRingedSiteHom X P) U)

section localizedProjectionSection

omit [Functor.IsContinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
  [Functor.IsCocontinuous P.p (inheritedTopology X.siteTopology P) X.siteTopology]
  [IsMorphismOfSites (inheritedTopology X.siteTopology P) X.siteTopology P.p]

/-- Helper for Lemma 21.38.2: the ambient arrow represented by a slice object over `p(U)`. -/
private abbrev localized_projection_over_hom
    (U : P.S) (A : Over (P.p.obj U)) :
    A.left ⟶ P.p.obj U :=
  A.hom

/-- Helper for Lemma 21.38.2: a morphism in the slice commutes with the normalized ambient arrows.
-/
private theorem localized_projection_over_hom_w
    (U : P.S) {A B : Over (P.p.obj U)} (g : A ⟶ B) :
    g.left ≫ localized_projection_over_hom P U B =
      localized_projection_over_hom P U A := by
  -- The normalized arrow is just `A.hom`, so the compatibility is exactly the slice equation.
  simpa [localized_projection_over_hom] using Over.w g

/-- Helper for Lemma 21.38.2: identify the canonical object of the fiber of `P.p` over
the codomain of `A`. -/
private abbrev localized_projection_section_fiber
    (U : P.S) (_A : Over (P.p.obj U)) :
    P.p.Fiber (P.p.obj U) :=
  Functor.Fiber.mk rfl

/-- Helper for Lemma 21.38.2: the chosen strongly cartesian arrow over `A.hom` with codomain
`U`. -/
-- Route correction: use the normalized ambient arrow `A.hom : A.left ⟶ P.p.obj U` directly,
-- so the chosen pullback lives over the fixed fiber object `Functor.Fiber.mk rfl`.
private abbrev localized_projection_section_arrow
    (U : P.S) (A : Over (P.p.obj U)) :
    (((canonicalPullbackChoice P.p).obj
        (localized_projection_over_hom P U A)
        (localized_projection_section_fiber P U A)).1 ⟶ U) :=
  (canonicalPullbackChoice P.p).map
    (localized_projection_over_hom P U A)
    (localized_projection_section_fiber P U A)

/-- Helper for Lemma 21.38.2: the object of `Over U` obtained by pulling `U` back along an object
of `Over (P.p.obj U)`. -/
private abbrev localized_projection_section_obj
    (U : P.S) (A : Over (P.p.obj U)) :
    Over U :=
  Over.mk (localized_projection_section_arrow P U A)

/-- Helper for Lemma 21.38.2: the chosen pullback arrow is strongly cartesian over `A.hom`. -/
private theorem localized_projection_section_arrow_isStronglyCartesian
    (U : P.S) (A : Over (P.p.obj U)) :
    P.p.IsStronglyCartesian
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) := by
  -- This is exactly the owner field carried by `canonicalPullbackChoice`.
  simpa [localized_projection_section_arrow] using
    (canonicalPullbackChoice P.p).isStronglyCartesian
      (localized_projection_over_hom P U A)
      (localized_projection_section_fiber P U A)

/-- Helper for Lemma 21.38.2: the chosen pullback arrow is also a lift of `A.hom`. -/
private theorem localized_projection_section_arrow_isHomLift
    (U : P.S) (A : Over (P.p.obj U)) :
    P.p.IsHomLift
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) := by
  -- A strongly cartesian arrow is, in particular, a lift of the same base morphism.
  exact (localized_projection_section_arrow_isStronglyCartesian P U A).toIsHomLift

/-- Helper for Lemma 21.38.2: the chosen strongly-cartesian universal property produces the map on
objects over a morphism in `Over (P.p.obj U)`. -/
-- This is the direct source-facing lift given by `IsStronglyCartesian.map`, with the lift input
-- for `A` supplied by the chosen pullback arrow's `IsHomLift` companion.
private noncomputable def localized_projection_section_lift
    (U : P.S) {A B : Over (P.p.obj U)} (g : A ⟶ B) :
    (localized_projection_section_obj P U A).left ⟶
      (localized_projection_section_obj P U B).left :=
  let hB :
      P.p.IsStronglyCartesian
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isStronglyCartesian P U B
  let hA :
      P.p.IsHomLift
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isHomLift P U A
  @Functor.IsStronglyCartesian.map _ _ _ _ P.p _ _ _ _
    (localized_projection_over_hom P U B)
    (localized_projection_section_arrow P U B)
    hB _ _ g.left
    (localized_projection_over_hom P U A)
    (localized_projection_over_hom_w P U g).symm
    (localized_projection_section_arrow P U A)
    hA

/-- Helper for Lemma 21.38.2: the chosen lift over `g : A ⟶ B` factors the pullback arrows
through the strongly cartesian arrow over `B.hom`. -/
-- This is exactly the factorization formula provided by `IsStronglyCartesian.fac` for the chosen
-- comparison lift.
private theorem localized_projection_section_lift_fac
    (U : P.S) {A B : Over (P.p.obj U)} (g : A ⟶ B) :
    localized_projection_section_lift P U g ≫
        localized_projection_section_arrow P U B =
      localized_projection_section_arrow P U A := by
  -- Read the chosen lift back through the strong-cartesian factorization owner.
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isStronglyCartesian P U B
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isStronglyCartesian P U A
  letI : P.p.IsHomLift
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isHomLift P U A
  simpa [localized_projection_section_lift] using
    (@Functor.IsStronglyCartesian.fac _ _ _ _ P.p _ _ _ _
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B)
      (localized_projection_section_arrow_isStronglyCartesian P U B)
      _ _ g.left
      (localized_projection_over_hom P U A)
      (localized_projection_over_hom_w P U g).symm
      (localized_projection_section_arrow P U A)
      (localized_projection_section_arrow_isHomLift P U A))

/-- Helper for Lemma 21.38.2: the chosen lift defines a morphism in the slice `Over U`. -/
private noncomputable def localized_projection_section_map
    (U : P.S) {A B : Over (P.p.obj U)} (g : A ⟶ B) :
    localized_projection_section_obj P U A ⟶
      localized_projection_section_obj P U B :=
  Over.homMk (localized_projection_section_lift P U g)
    (localized_projection_section_lift_fac P U g)

/-- Helper for Lemma 21.38.2: the section map attached to an identity morphism is the identity. -/
-- This is the slice-level form of `IsStronglyCartesian.map_self`.
private theorem localized_projection_section_lift_id
    (U : P.S) (A : Over (P.p.obj U)) :
    localized_projection_section_lift P U (𝟙 A) =
      𝟙 (localized_projection_section_obj P U A).left := by
  -- The identity lift is exactly the `map_self` owner for the chosen strongly cartesian arrow.
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isStronglyCartesian P U A
  letI : P.p.IsHomLift
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isHomLift P U A
  simpa [localized_projection_section_lift] using
    (Functor.IsStronglyCartesian.map_self P.p
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A))

/-- Helper for Lemma 21.38.2: the section lifts compose as expected. -/
-- This is the composition formula supplied by `IsStronglyCartesian.map_comp_map`.
private theorem localized_projection_section_lift_comp
    (U : P.S) {A B C : Over (P.p.obj U)} (g : A ⟶ B) (h : B ⟶ C) :
    localized_projection_section_lift P U (g ≫ h) =
      localized_projection_section_lift P U g ≫
        localized_projection_section_lift P U h := by
  -- Compose the owner-level comparison maps instead of reproving uniqueness in the total category.
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U C)
      (localized_projection_section_arrow P U C) :=
    localized_projection_section_arrow_isStronglyCartesian P U C
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isStronglyCartesian P U B
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isStronglyCartesian P U A
  letI : P.p.IsHomLift
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isHomLift P U B
  letI : P.p.IsHomLift
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isHomLift P U A
  symm
  simpa [localized_projection_section_lift] using
    (Functor.IsStronglyCartesian.map_comp_map P.p
      (localized_projection_over_hom P U C)
      (localized_projection_section_arrow P U C)
      (localized_projection_over_hom_w P U h).symm
      (localized_projection_over_hom_w P U g).symm
      (localized_projection_section_arrow P U B)
      (localized_projection_section_arrow P U A))

/-- Helper for Lemma 21.38.2: the morphism in `Over U` induced by an identity morphism downstairs
is the identity. -/
-- Reduce equality in `Over U` to equality of the underlying arrows.
private theorem localized_projection_section_map_id
    (U : P.S) (A : Over (P.p.obj U)) :
    localized_projection_section_map P U (𝟙 A) =
      𝟙 (localized_projection_section_obj P U A) := by
  -- Reduce equality in the slice to equality of the underlying ambient arrow.
  apply Over.OverMorphism.ext
  simpa [localized_projection_section_map] using
    localized_projection_section_lift_id P U A

/-- Helper for Lemma 21.38.2: the morphism in `Over U` induced by a composite morphism downstairs
is the composite of the induced morphisms. -/
-- Reduce equality in `Over U` to the ambient composition identity for the chosen lifts.
private theorem localized_projection_section_map_comp
    (U : P.S) {A B C : Over (P.p.obj U)} (g : A ⟶ B) (h : B ⟶ C) :
    localized_projection_section_map P U (g ≫ h) =
      localized_projection_section_map P U g ≫
        localized_projection_section_map P U h := by
  -- Reduce equality in the slice to the ambient lift-composition identity.
  apply Over.OverMorphism.ext
  simpa [localized_projection_section_map] using
    localized_projection_section_lift_comp P U g h

-- Proof sketch: send `A ⟶ P.p.obj U` to the chosen strongly cartesian pullback
-- `A ×_{P.p.obj U} U ⟶ U`, and send a morphism in the base slice to the unique lift between the
-- chosen pullbacks.
/-- Companion bridge for Lemma 21.38.2: the chosen pullback functor
`Over (P.p.obj U) ⥤ Over U` obtained from the canonical strongly cartesian lifts over `U`.
This is the slice-level section of `Over.post P.p` used to build the section of the localized
projection morphism of topoi. -/
noncomputable def localized_projection_section_functor
    (U : P.S) :
    Over (P.p.obj U) ⥤ Over U where
  obj := localized_projection_section_obj P U
  map := fun g ↦ localized_projection_section_map P U g
  map_id := localized_projection_section_map_id P U
  map_comp := fun g h ↦ localized_projection_section_map_comp P U g h

/-- Helper for Lemma 21.38.2: a morphism in the localized base slice lifts to the chosen
strongly cartesian pullback object over `U`. -/
private noncomputable def localized_projection_section_lift_from_post
    (U : P.S) {A : Over U} {B : Over (P.p.obj U)}
    (β : (Over.post P.p).obj A ⟶ B) :
    A.left ⟶ (localized_projection_section_obj P U B).left :=
  let hB :
      P.p.IsStronglyCartesian
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isStronglyCartesian P U B
  let hA : P.p.IsHomLift ((Over.post P.p).obj A).hom A.hom :=
    IsHomLift.of_fac P.p ((Over.post P.p).obj A).hom A.hom rfl rfl (by simp)
  -- Use the universal property of the chosen pullback object over `B.hom`.
  @Functor.IsStronglyCartesian.map _ _ _ _ P.p _ _ _ _
    (localized_projection_over_hom P U B)
    (localized_projection_section_arrow P U B)
    hB _ _ β.left
    ((Over.post P.p).obj A).hom
    (Over.w β).symm
    A.hom
    hA

/-- Helper for Lemma 21.38.2: the lifted arrow from the base slice factors through the chosen
pullback arrow over `B.hom`. -/
private theorem localized_projection_section_lift_from_post_fac
    (U : P.S) {A : Over U} {B : Over (P.p.obj U)}
    (β : (Over.post P.p).obj A ⟶ B) :
    localized_projection_section_lift_from_post P U β ≫
        localized_projection_section_arrow P U B =
      A.hom := by
  let hB :
      P.p.IsStronglyCartesian
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isStronglyCartesian P U B
  let hA : P.p.IsHomLift ((Over.post P.p).obj A).hom A.hom :=
    IsHomLift.of_fac P.p ((Over.post P.p).obj A).hom A.hom rfl rfl (by simp)
  -- Read back the lift through the factorization owner for the strongly cartesian arrow.
  simpa [localized_projection_section_lift_from_post] using
    (@Functor.IsStronglyCartesian.fac _ _ _ _ P.p _ _ _ _
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B)
      hB _ _ β.left
      ((Over.post P.p).obj A).hom
      (Over.w β).symm
      A.hom
      hA)

/-- Helper for Lemma 21.38.2: the lifted arrow from the base slice is itself a lift over the
underlying arrow `β.left`. -/
private theorem localized_projection_section_lift_from_post_isHomLift
    (U : P.S) {A : Over U} {B : Over (P.p.obj U)}
    (β : (Over.post P.p).obj A ⟶ B) :
    P.p.IsHomLift β.left (localized_projection_section_lift_from_post P U β) := by
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isStronglyCartesian P U B
  letI : P.p.IsHomLift ((Over.post P.p).obj A).hom A.hom :=
    by
      simpa using
        (IsHomLift.of_fac P.p ((Over.post P.p).obj A).hom A.hom rfl rfl (by simp) :
          P.p.IsHomLift ((Over.post P.p).obj A).hom A.hom)
  -- The universal-property comparison map returned by `map` lies over the chosen base arrow.
  dsimp [localized_projection_section_lift_from_post]
  infer_instance

/-- Helper for Lemma 21.38.2: a morphism in `Over (P.p.obj U)` induces a morphism into the chosen
pullback object in `Over U`. -/
private noncomputable def localized_projection_section_hom_from_post
    (U : P.S) {A : Over U} {B : Over (P.p.obj U)}
    (β : (Over.post P.p).obj A ⟶ B) :
    A ⟶ localized_projection_section_obj P U B :=
  Over.homMk
    (localized_projection_section_lift_from_post P U β)
    (localized_projection_section_lift_from_post_fac P U β)

/-- Helper for Lemma 21.38.2: the chosen lift lies over the downstairs slice morphism `g`. -/
-- The comparison map returned by `IsStronglyCartesian.map` is itself a lift over `g.left`.
private theorem localized_projection_section_lift_isHomLift
    (U : P.S) {A B : Over (P.p.obj U)} (g : A ⟶ B) :
    P.p.IsHomLift g.left (localized_projection_section_lift P U g) := by
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isStronglyCartesian P U B
  dsimp [localized_projection_section_lift]
  infer_instance

/-- Helper for Lemma 21.38.2: after applying `Over.post P.p`, the chosen section object has the
expected domain object in the base slice. -/
private theorem localized_projection_section_post_domain_eq
    (U : P.S) (A : Over (P.p.obj U)) :
    P.p.obj (localized_projection_section_obj P U A).left = A.left := by
  -- Read the source object of the chosen pullback arrow through the normalized hom-lift owner.
  letI : P.p.IsHomLift
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isHomLift P U A
  simpa [localized_projection_section_obj] using
    (IsHomLift.domain_eq P.p
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A))

/-- Helper for Lemma 21.38.2: the chosen section object becomes isomorphic to the original slice
object after applying `Over.post P.p`. -/
private noncomputable def localized_projection_section_post_component
    (U : P.S) (A : Over (P.p.obj U)) :
    ((Over.post P.p).obj (localized_projection_section_obj P U A)) ≅ A := by
  -- Package the domain transport and the normalized arrow equation into one `Over` isomorphism.
  letI : P.p.IsHomLift
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A) :=
    localized_projection_section_arrow_isHomLift P U A
  refine Over.isoMk (eqToIso (localized_projection_section_post_domain_eq P U A)) ?_
  simpa [localized_projection_section_obj, localized_projection_over_hom] using
    (IsHomLift.fac' P.p
      (localized_projection_over_hom P U A)
      (localized_projection_section_arrow P U A)).symm

/-- Helper for Lemma 21.38.2: a morphism into the chosen pullback object pushes forward to the
corresponding morphism in the localized base slice. -/
private noncomputable def localized_projection_section_post_hom
    (U : P.S) {A : Over U} {B : Over (P.p.obj U)}
    (γ : A ⟶ localized_projection_section_obj P U B) :
    (Over.post P.p).obj A ⟶ B :=
  (Over.post P.p).map γ ≫ (localized_projection_section_post_component P U B).hom

/-- Helper for Lemma 21.38.2: pushing the lifted morphism back down recovers the original
localized slice morphism. This is the verified half of the planned hom-set equivalence. -/
private theorem localized_projection_section_post_hom_from_post
    (U : P.S) {A : Over U} {B : Over (P.p.obj U)}
    (β : (Over.post P.p).obj A ⟶ B) :
    localized_projection_section_post_hom P U
        (localized_projection_section_hom_from_post P U β) =
      β := by
  let hB := localized_projection_section_post_domain_eq P U B
  have hlift :
      P.p.map (localized_projection_section_lift_from_post P U β) =
        β.left ≫ eqToHom hB.symm := by
    letI : P.p.IsHomLift β.left (localized_projection_section_lift_from_post P U β) :=
      localized_projection_section_lift_from_post_isHomLift P U β
    -- Normalize the codomain transport in the hom-lift owner for the constructed arrow.
    simpa [hB] using
      (IsHomLift.fac' P.p
        β.left
        (localized_projection_section_lift_from_post P U β))
  -- Reduce equality of slice morphisms to the underlying arrow in `X`.
  apply Over.OverMorphism.ext
  have hleft :
      (localized_projection_section_post_hom P U
          (localized_projection_section_hom_from_post P U β)).left =
        P.p.map (localized_projection_section_lift_from_post P U β) ≫ eqToHom hB := by
    simp [localized_projection_section_post_hom, localized_projection_section_hom_from_post,
      localized_projection_section_post_component]
  rw [hleft, hlift]
  simp [Category.assoc]

/-- Helper for Lemma 21.38.2: the two slice-level comparison maps are inverse on morphisms into
the chosen pullback object. -/
private theorem localized_projection_section_hom_from_post_post_hom
    (U : P.S) {A : Over U} {B : Over (P.p.obj U)}
    (γ : A ⟶ localized_projection_section_obj P U B) :
    localized_projection_section_hom_from_post P U
        (localized_projection_section_post_hom P U γ) =
      γ := by
  let β := localized_projection_section_post_hom P U γ
  letI : P.p.IsStronglyCartesian
      (localized_projection_over_hom P U B)
      (localized_projection_section_arrow P U B) :=
    localized_projection_section_arrow_isStronglyCartesian P U B
  let hB := localized_projection_section_post_domain_eq P U B
  have hA :
      P.p.IsHomLift ((Over.post P.p).obj A).hom A.hom :=
    IsHomLift.of_fac P.p ((Over.post P.p).obj A).hom A.hom rfl rfl (by simp)
  letI : P.p.IsHomLift β.left γ.left := by
    refine IsHomLift.of_fac P.p β.left γ.left rfl hB ?_
    simp [β, localized_projection_section_post_hom, localized_projection_section_post_component]
  have hγ :
      γ.left ≫ localized_projection_section_arrow P U B =
        A.hom := by
    simpa [localized_projection_section_obj] using Over.w γ
  have huniq : γ.left = localized_projection_section_lift_from_post P U β := by
    exact
      @Functor.IsStronglyCartesian.map_uniq _ _ _ _ P.p _ _ _ _
        (localized_projection_over_hom P U B)
        (localized_projection_section_arrow P U B)
        (localized_projection_section_arrow_isStronglyCartesian P U B)
        _ _
        β.left
        ((Over.post P.p).obj A).hom
        (Over.w β).symm
        A.hom
        hA
        γ.left
        (show P.p.IsHomLift β.left γ.left from inferInstance)
        hγ
  apply Over.OverMorphism.ext
  change localized_projection_section_lift_from_post P U β = γ.left
  simpa using huniq.symm

/-- Helper for Lemma 21.38.2: the chosen lift and pushforward constructions give the hom-set
equivalence underlying the slice adjunction `Over.post P.p ⊣ localized_projection_section_functor
P U`. -/
private noncomputable def localized_projection_section_homEquiv
    (U : P.S) (A : Over U) (B : Over (P.p.obj U)) :
    (((Over.post P.p).obj A ⟶ B) ≃
      (A ⟶ localized_projection_section_obj P U B)) where
  toFun := fun β ↦ localized_projection_section_hom_from_post P U β
  invFun := fun γ ↦ localized_projection_section_post_hom P U γ
  left_inv := by
    -- Proof comment: sending a base-slice map up to the chosen pullback and pushing it back down
    -- recovers the original map.
    intro β
    exact localized_projection_section_post_hom_from_post P U β
  right_inv := by
    -- Proof comment: the strong-cartesian universal property makes the lifted map unique.
    intro γ
    exact localized_projection_section_hom_from_post_post_hom P U γ

/-- Helper for Lemma 21.38.2: the `Over.post P.p` image of the section map is compatible with the
objectwise comparison isomorphisms. -/
private theorem localized_projection_section_post_map_transport
    (U : P.S) {A B : Over (P.p.obj U)} (g : A ⟶ B) :
    ((Over.post P.p).map (localized_projection_section_map P U g)).left ≫
        (localized_projection_section_post_component P U B).hom.left =
      (localized_projection_section_post_component P U A).hom.left ≫ g.left := by
  let hA := localized_projection_section_post_domain_eq P U A
  let hB := localized_projection_section_post_domain_eq P U B
  have hlift :
      P.p.map (localized_projection_section_lift P U g) =
        eqToHom hA ≫ g.left ≫ eqToHom hB.symm := by
    -- Route correction: normalize the base map of the chosen slice lift once via `IsHomLift.fac'`.
    letI : P.p.IsHomLift g.left (localized_projection_section_lift P U g) :=
      localized_projection_section_lift_isHomLift P U g
    simpa [hA, hB] using
      (IsHomLift.fac' P.p g.left (localized_projection_section_lift P U g))
  have hleft :
      ((Over.post P.p).map (localized_projection_section_map P U g)).left ≫
          (localized_projection_section_post_component P U B).hom.left =
        P.p.map (localized_projection_section_lift P U g) ≫ eqToHom hB := by
    -- Unfold the slice constructions so the comparison becomes a statement in the ambient category.
    simp [localized_projection_section_map, localized_projection_section_post_component]
  rw [hleft, hlift]
  simpa [localized_projection_section_post_component, hA, Category.assoc]

/-- Helper for Lemma 21.38.2: the chosen pullback functor on slice categories is right adjoint to
`Over.post P.p`. -/
private noncomputable def localized_projection_section_adjunction
    (U : P.S) :
    Over.post P.p ⊣ localized_projection_section_functor P U := by
  exact
    Adjunction.mkOfHomEquiv
      { homEquiv := localized_projection_section_homEquiv P U
        homEquiv_naturality_left_symm := by
          intro A' A B f g
          apply Over.OverMorphism.ext
          change
            P.p.map (f.left ≫ g.left) ≫
                (localized_projection_section_post_component P U B).hom.left =
              P.p.map f.left ≫
                (P.p.map g.left ≫
                  (localized_projection_section_post_component P U B).hom.left)
          rw [Functor.map_comp]
          simp [Category.assoc]
        homEquiv_naturality_right := by
          intro A B B' f g
          have hf :
              ((Over.post P.p).map (localized_projection_section_hom_from_post P U f)).left ≫
                  (localized_projection_section_post_component P U B).hom.left =
                f.left := by
            simpa [localized_projection_section_post_hom] using
              congrArg (fun h => h.left)
                (localized_projection_section_post_hom_from_post P U f)
          have hpost :
              localized_projection_section_post_hom P U
                  (localized_projection_section_hom_from_post P U f ≫
                    localized_projection_section_map P U g) =
                f ≫ g := by
            apply Over.OverMorphism.ext
            calc
              ((Over.post P.p).map
                    (localized_projection_section_hom_from_post P U f ≫
                      localized_projection_section_map P U g)).left ≫
                  (localized_projection_section_post_component P U B').hom.left =
                  ((Over.post P.p).map
                        (localized_projection_section_hom_from_post P U f)).left ≫
                      (((Over.post P.p).map
                            (localized_projection_section_map P U g)).left ≫
                        (localized_projection_section_post_component P U B').hom.left) := by
                    simp [Functor.map_comp, Category.assoc]
              _ = ((Over.post P.p).map
                      (localized_projection_section_hom_from_post P U f)).left ≫
                    ((localized_projection_section_post_component P U B).hom.left ≫ g.left) := by
                    rw [localized_projection_section_post_map_transport P U g]
              _ = (((Over.post P.p).map
                        (localized_projection_section_hom_from_post P U f)).left ≫
                      (localized_projection_section_post_component P U B).hom.left) ≫ g.left := by
                    simp [Category.assoc]
              _ = f.left ≫ g.left := by rw [hf]
          calc
            localized_projection_section_hom_from_post P U (f ≫ g) =
                localized_projection_section_hom_from_post P U
                  (localized_projection_section_post_hom P U
                    (localized_projection_section_hom_from_post P U f ≫
                      localized_projection_section_map P U g)) := by
                  rw [hpost]
            _ = localized_projection_section_hom_from_post P U f ≫
                  localized_projection_section_map P U g := by
                  simpa using
                    localized_projection_section_hom_from_post_post_hom P U
                      (localized_projection_section_hom_from_post P U f ≫
                        localized_projection_section_map P U g) }

/-- Helper for Lemma 21.38.2: the chosen pullback functor is continuous for the localized
topologies. -/
private instance localized_projection_sectionFunctor_isContinuous
    (U : P.S) :
    Functor.IsContinuous
      (localized_projection_section_functor P U)
      (X.siteTopology.over (P.p.obj U))
      ((JP).over U) := by
  exact
    (localized_projection_section_adjunction P U).isContinuous_of_isCocontinuous
      ((JP).over U)
      (X.siteTopology.over (P.p.obj U))

/-- Companion bridge for Lemma 21.38.2: the chosen pullback functor is a section of
`Over.post P.p`. This is the slice-level form of the source identity `p ∘ v = id`. -/
noncomputable def localized_projection_section_post_iso
    (U : P.S) :
    localized_projection_section_functor P U ⋙ Over.post P.p ≅ 𝟭 (Over (P.p.obj U)) :=
  -- Assemble the objectwise section comparison and discharge naturality through the single
  -- transport lemma above.
  NatIso.ofComponents
    (fun A ↦ localized_projection_section_post_component P U A)
    (by
      intro A B g
      apply Over.OverMorphism.ext
      simpa using localized_projection_section_post_map_transport P U g)

end localizedProjectionSection

-- Proof sketch: choose the slice pullback functor
-- `v : Over (P.p.obj U) ⥤ Over U` sending an arrow `V ⟶ P.p.obj U` to a chosen strongly
-- cartesian lift `V ×_{P.p.obj U} U ⟶ U`. This functor is right adjoint to `Over.post P.p`,
-- and it is continuous and cocontinuous for the localized topologies because coverings in the
-- inherited topology are generated by strongly cartesian morphisms. Apply Lemma `7.22.2` on the
-- localized sites to obtain a morphism of topoi `σ` whose inverse image is `π_{U,*}`,
-- and use the counit of the slice adjunction to identify `π_U ∘ σ` with the identity.
/-- Lemma 21.38.2: for `U : P.S`, the canonical localized projection morphism of topoi
`((projectionRingedSiteHom X P).localization U).toMorphismOfTopoi` admits a section morphism of topoi `σ`, and the
inverse-image functor of `σ` is the direct-image functor
`(((projectionRingedSiteHom X P).localization U).toMorphismOfTopoi) _*`. -/
-- The companion bridge above isolates the slice-level section of `Over.post P.p`; the remaining
-- proof step is to package that section through the Chapter 7 site-to-topos owners.
@[stacks 08P9]
theorem localized_projection_morphism_of_topoi_has_section
    (U : P.S)
    [HasWeakSheafify (X.siteTopology.over (P.p.obj U)) (Type (max u v))]
    [∀ Q : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.post P.p).op.HasLeftKanExtension Q]
    [PreservesFiniteLimits
      ((Over.post P.p).sheafPullback
        (Type (max u v))
        ((JP).over U)
        (X.siteTopology.over (P.p.obj U)))] :
    let π :
        MorphismOfTopoiIn
          (((inheritedRingedSite X P).localization U).siteTopology)
          ((X.localization (P.p.obj U)).siteTopology) :=
      ((projectionRingedSiteHom X P).localization U).toMorphismOfTopoi
    ∃ σ : MorphismOfTopoiIn
        ((X.localization (P.p.obj U)).siteTopology)
        (((inheritedRingedSite X P).localization U).siteTopology),
      MorphismOfTopoiIn.comp σ π =
          MorphismOfTopoiIn.id ((X.localization (P.p.obj U)).siteTopology) ∧
        σ⁻¹ = π _* := by
  let π :
      MorphismOfTopoiIn
        (((inheritedRingedSite X P).localization U).siteTopology)
        ((X.localization (P.p.obj U)).siteTopology) :=
    ((projectionRingedSiteHom X P).localization U).toMorphismOfTopoi
  let _ :
      ((localized_projection_section_functor P U).sheafPullback
        (Type (max u v))
        (X.siteTopology.over (P.p.obj U))
        ((JP).over U)).IsRightAdjoint :=
    sheafPullback_isRightAdjoint_of_continuous_leftAdjoint
      (u := localized_projection_section_functor P U)
      (w := Over.post P.p)
      (adj := localized_projection_section_adjunction P U)
      (J := X.siteTopology.over (P.p.obj U))
      (K := (JP).over U)
  let _ :
      PreservesFiniteLimits
        ((localized_projection_section_functor P U).sheafPullback
          (Type (max u v))
          (X.siteTopology.over (P.p.obj U))
          ((JP).over U)) :=
    inferInstance
  let σ :
      MorphismOfTopoiIn
        ((X.localization (P.p.obj U)).siteTopology)
        (((inheritedRingedSite X P).localization U).siteTopology) :=
    (localized_projection_section_functor P U).morphismOfTopoiInOfContinuous
      (X.siteTopology.over (P.p.obj U))
      ((JP).over U)
  refine ⟨σ, ?_, ?_⟩
  · sorry
  · rfl

end

end FibredCategoryOver
end CategoryTheory

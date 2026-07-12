import StacksProject_2024.Chap21.Definition_21_45_1
import StacksProject_2024.Chap18.Definition_18_13_1
import StacksProject_2024.Chap18.Lemma_18_20_1
import StacksProject_2024.Chap21.Lemma_21_19_1
import StacksProject_2024.Chap21.Lemma_21_20_4
import StacksProject_2024.Chap07.Lemma_7_14_10
import StacksProject_2024.Chap21.Lemma_21_45_2

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

universe u v

namespace RingedSite.Hom.ModuleDerived

open SheafOfModules.RingedSite
open _root_.RingedSite.DerivedCategory

section

/- Domain-style sampling for Lemma 21.45.3:
- primary domain: derived pullback on module sheaves over ringed sites and preservation of the
  intrinsic `m`-pseudo-coherence predicate;
- sampled owner declarations:
  `RingedSite.Hom.modulePullbackDerived`,
  `RingedSite.Hom.modulePullbackToDerived`,
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSite.DerivedCategory.IsMPseudoCoherent`;
- best owner abstraction: the pullback side should be stated directly through the bundled
  ringed-site morphism `f : X ⟶ Y` and its owner functor `modulePullbackDerived f`; the
  pseudo-coherence side is already owned by `RingedSite.DerivedCategory.IsMPseudoCoherent`;
- primitive data: the morphism `f : X ⟶ Y`, the derived object `E`, and the integer `m`;
- derived API: preservation of `m`-pseudo-coherence under `L(f)^*`.

Source/core/bridge triage:
- `source-facing`: derived pullback preserves `m`-pseudo-coherent objects;
- `core/canonical`: `modulePullbackDerived`, `ModuleCat`, `ModuleDerived`, and
  `RingedSite.DerivedCategory.IsMPseudoCoherent`;
- `bridge/view`: site-presented morphism data belongs in downstream bridge files that build a
  bundled morphism `f : X ⟶ Y`; it should not remain primitive in this owner theorem.
-/
variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasBinaryProducts X.carrier]
variable [HasBinaryProducts Y.carrier]

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y
local notation "DModY" => ModuleDerived Y

variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : Y, (localizedRestriction Y U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : Y, PreservesFiniteLimits (localizedRestriction Y U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [∀ U : Y, PreservesFiniteColimits (localizedRestriction Y U)]
variable [∀ U : X, HasBinaryProducts (X.localization U).carrier]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{max u v}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : X, ∀ V : X.localization U,
  (localizedRestriction (X.localization U) V).Additive]
variable [∀ U : X, ∀ V : X.localization U,
  PreservesFiniteLimits (localizedRestriction (X.localization U) V)]
variable [∀ U : X, ∀ V : X.localization U,
  PreservesFiniteColimits (localizedRestriction (X.localization U) V)]

variable [CategoryWithHomology ModX]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]
variable [∀ U : X, ∀ V : X.localization U,
  CategoryWithHomology (ModuleCat (((X.localization U).localization V)))]

variable [CategoryWithHomology ModY]
variable [∀ U : Y, CategoryWithHomology (ModuleCat (Y.localization U))]

variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(f^*).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

-- Proof comment: the source proof begins by covering any source object with pieces that map into
-- objects of the form `f.base.obj V`; this packages that purely site-theoretic reduction.
/-- Helper for Lemma 21.45.3: every object of the source site admits a cover by objects mapping to
objects in the image of `f.base`. -/
private lemma exists_source_cover_mapping_to_target
    (U : X) :
    ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      ∃ V : Y, Nonempty (I.Y ⟶ f.base.obj V) := by
  sorry

-- Proof comment: this is the target-side local witness supplied directly by the pseudo-coherence
-- criterion from Definition 21.45.1.
/-- Helper for Lemma 21.45.3: an `m`-pseudo-coherent target object admits strict-perfect
approximations after passing to a covering of any target object. -/
private lemma exists_target_cover_with_local_approximation
    (E : DModY) (m : ℤ) (hE : E.IsMPseudoCoherent m) (V : Y) :
    ∃ T : Y.siteTopology.Cover V, ∀ I : T.Arrow,
      HasStrictlyPerfectApproximationInDegree E I.Y m := by
  sorry

-- Proof comment: the same site-theoretic reduction used globally also works after localizing at
-- `V`; this is the source-faithful way to refine an object of `X/f(V)` by pieces mapping into
-- objects of `Y/V`.
/-- Helper for Lemma 21.45.3: every object of the localized source site `X/f(V)` admits a cover
by objects mapping to objects in the image of the localized morphism
`f.localization V : X/f(V) ⟶ Y/V`. -/
private lemma exists_source_cover_mapping_to_target_localization
    {V : Y} (U : X.localization (f.base.obj V)) :
    ∃ T : (X.localization (f.base.obj V)).siteTopology.Cover U, ∀ I : T.Arrow,
      ∃ W : Y.localization V, Nonempty (I.Y ⟶ (f.localization V).base.obj W) := by
  sorry

/-- Helper for Lemma 21.45.3: after fixing a target cover of `V`, the terminal object of the
source slice `X/f(V)` admits a refinement whose members map into chosen target cover charts. -/
private lemma exists_source_cover_mapping_to_target_cover_localization
    {V : Y} (Ttgt : Y.siteTopology.Cover V) :
    ∃ Tsrc : (X.localization (f.base.obj V)).siteTopology.Cover (Over.mk (𝟙 (f.base.obj V))),
      ∀ I : Tsrc.Arrow,
        ∃ J : Ttgt.Arrow, Nonempty (I.Y ⟶ (f.localization V).base.obj (Over.mk J.f)) := by
  -- Proof comment: this is the cover-alignment step from the source proof. One first covers the
  -- terminal object of `X/f(V)` by objects mapping into `Y/V`, then refines each target chart
  -- against the chosen cover of `V`.
  sorry

/-- Helper for Lemma 21.45.3: a strict-perfect approximation over a chosen target cover chart
pulls back to a strict-perfect approximation on any source chart mapping to it. -/
private lemma localized_pullback_witness_of_target_cover_arrow
    (E : DModY) (m : ℤ) {V : Y} {Ttgt : Y.siteTopology.Cover V} (J : Ttgt.Arrow)
    {Z : X.localization (f.base.obj V)}
    (σ : Z ⟶ (f.localization V).base.obj (Over.mk J.f))
    (hJ :
      HasStrictlyPerfectApproximationInDegree E J.Y m) :
    HasStrictlyPerfectApproximationInDegree
      ((localizedRestrictionDerived X (f.base.obj V)).obj ((L(f)^*).obj E))
      Z m := by
  -- Proof comment: this is the witness-level transport in the source proof. The missing bridge is
  -- the localized pullback comparison `j[f(V)]⁻¹ Lf^* ≅ L(f.localization V)^* j[V]⁻¹` together
  -- with the cone argument on the localized morphism.
  sorry

-- Proof comment: this is the source-faithful full-slice step after the outer cover reduction.
-- Once the chosen target cover is aligned with a source cover of the terminal slice object, the
-- final-object criterion from Lemma `21.45.2` closes the argument.
/-- Helper for Lemma 21.45.3: the derived pullback becomes `m`-pseudo-coherent on the full slice
`X/f(V)`. -/
private lemma localized_source_slice_isMPseudoCoherent
    (E : DModY) (m : ℤ) (hE : E.IsMPseudoCoherent m) (V : Y) :
    ((localizedRestrictionDerived X (f.base.obj V)).obj ((L(f)^*).obj E)).IsMPseudoCoherent m := by
  sorry

/-- Helper for Lemma 21.45.3: after proving pseudo-coherence on `X/V`, descend along a map
`ρ : U ⟶ V` by relocalizing once more. -/
private lemma localizedRestrictionDerived_isMPseudoCoherent_of_arrow
    (m : ℤ) {U V : X} (ρ : U ⟶ V) {K : ModuleDerived X}
    (hK : ((j[V]⁻¹).obj K).IsMPseudoCoherent m) :
    ((j[U]⁻¹).obj K).IsMPseudoCoherent m := by
  -- Proof comment: the source proof finishes by viewing `j[U]⁻¹ K` as the further restriction of
  -- `j[V]⁻¹ K` along the arrow `Over.mk ρ`.
  -- Route correction: use the witness-level relocalization equivalence
  -- `HasStrictlyPerfectApproximationInDegree.relocalization_iff` and then apply the local
  -- criterion from Definition `21.45.1` on the slice site `X/V`.
  have hrelocal := HasStrictlyPerfectApproximationInDegree.relocalization_iff ρ K m
  let _ := hrelocal
  let _ := hK
  sorry

/-- Helper for Lemma 21.45.3: once a source object maps into `f.base.obj V`, the localized derived
pullback is `m`-pseudo-coherent. -/
private lemma localized_piece_isMPseudoCoherent_of_maps_to_target
    (E : DModY) (m : ℤ) (hE : E.IsMPseudoCoherent m)
    {U : X} {V : Y} (_ρ : U ⟶ f.base.obj V) :
    ((j[U]⁻¹).obj ((L(f)^*).obj E)).IsMPseudoCoherent m := by
  sorry

-- Proof sketch: work locally on an arbitrary object of `X`. The hypothesis `E.IsMPseudoCoherent m`
-- supplies, after refining to a cover, strictly perfect approximations for the restrictions of
-- `E`. Pull those models back along `f`, use the definition of `modulePullbackDerived f` to
-- transport the comparison maps, and identify the resulting local objects with strictly perfect
-- approximations on `X`. This is exactly the local condition in Definition `21.45.1`.
/-- Lemma 21.45.3: for a morphism `f : X ⟶ Y` of ringed sites, if `E ∈ D(𝒪_Y)` is
`m`-pseudo-coherent, then its derived pullback `L(f)^* E` is `m`-pseudo-coherent in `D(𝒪_X)`. -/
@[stacks 08H4]
theorem IsMPseudoCoherent.pullback
    {E : DModY} {m : ℤ} (hE : E.IsMPseudoCoherent m) :
    ((L(f)^*).obj E).IsMPseudoCoherent m := by
  sorry

end

end RingedSite.Hom.ModuleDerived

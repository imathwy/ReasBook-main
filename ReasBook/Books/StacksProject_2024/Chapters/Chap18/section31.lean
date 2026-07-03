import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_31_1 (from Chap18) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

/- Domain-style sampling for Definition 18.31.1:
- primary domain: flat morphisms of ringed sites, expressed by exactness of inverse image on
  module sheaves;
- sampled owner declarations:
  `SheafOfModules.pullback`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `exactFunctor`;
- best owner abstraction: the source-facing owner should remain `RingedSite.Hom.IsFlat`, while the
  primitive canonical functor is `SheafOfModules.pullback f.structureSheafMap`;
- primitive data: a morphism of ringed sites `f`;
- derived API: the source-facing notation `f^*` and the constructor/reformulation lemmas exposing
  exactness of that canonical pullback functor via the class projection and `@[mk_iff]`.

Source/core/bridge triage:
- `source-facing`: `RingedSite.Hom.IsFlat`;
- `core/canonical`: `SheafOfModules.pullback f.structureSheafMap` with the exactness owner
  `exactFunctor`;
- `bridge/view`: the notation `f^*` for the canonical pullback functor. -/

/-- Pushforward on module sheaves along a morphism of ringed sites is a right adjoint. -/
-- Proof sketch: use the standard pullback-pushforward adjunction attached to the structure-sheaf
-- map; this instance is the minimal bridge needed so the canonical owner
-- `SheafOfModules.pullback f.structureSheafMap` is available in the ringed-site setting.
instance modulePushforward_isRightAdjoint :
    (SheafOfModules.pushforward f.structureSheafMap).IsRightAdjoint := sorry

/-- The inverse-image functor on module sheaves attached to a morphism of ringed sites. -/
noncomputable abbrev modulePullback :
    SheafOfModules.{max u v} Y.structureSheaf ⥤
      SheafOfModules.{max u v} X.structureSheaf :=
  SheafOfModules.pullback f.structureSheafMap

/- Source-facing notation for inverse image of module sheaves on ringed sites. -/
scoped syntax:max term:max "^*" : term

scoped macro_rules
  | `($f^*) => `(RingedSite.Hom.modulePullback $f)

/-- Definition 18.31.1: in the site-presented formalization used here, a morphism of ringed
sites is flat when the inverse-image functor on module sheaves attached to its structure-sheaf
map is exact, formalizing flatness of the ring map `f^\sharp`. -/
@[mk_iff isFlat_iff_pullback_exact]
class IsFlat : Prop where
  /-- Pullback on module sheaves preserves finite limits. -/
  pullback_exact :
    exactFunctor (SheafOfModules.{max u v} Y.structureSheaf)
      (SheafOfModules.{max u v} X.structureSheaf) (f^*)

open scoped RingedSite.Hom

end RingedSite.Hom

/-! ### Lemma_18_31_2 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 18.31.2:
- primary domain: exactness of inverse-image and pullback functors on sheaves and module sheaves;
- sampled canonical declarations:
  `exactFunctor`,
  `F.sheafPullback`,
  `RingedSite.Hom.modulePullback`,
  `RingedSite.Hom.IsFlat.pullback_exact`;
- best owner abstraction for part `(2)`: `RingedSite.Hom.IsFlat`.

Primitive-vs-derived split:
- primitive data: a morphism of ringed sites `f : X ⟶ Y` together with the flatness structure
  `[f.IsFlat]`;
- derived API: exactness of the canonical pullback functor on module sheaves, exposed by
  `RingedSite.Hom.IsFlat.pullback_exact` and written source-facing as exactness of `f^*`.

Source/core/bridge triage for part `(2)`:
- `source-facing`: exactness of pullback on module sheaves for a flat morphism of ringed topoi;
- `core/canonical`: `RingedSite.Hom.IsFlat.pullback_exact`;
- `bridge/view`: the notation `f^*` for the canonical module pullback functor.
-/

-- Proof sketch: exactness of the inverse-image functor on sheaves of sets is part of the
-- definition of a morphism of topoi, and the underlying sheaf of sets of the inverse image of an
-- abelian sheaf is computed by the same inverse-image functor; exactness on abelian sheaves
-- follows by transport across the forgetful comparison.
/-- Lemma 18.31.2 (1): for a site presentation of the underlying morphism of topoi
`f : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal C')`, the inverse-image functor on abelian
sheaves `f^{-1} : \mathrm{Ab}(\mathcal C') \to \mathrm{Ab}(\mathcal C)` is exact. -/
theorem ringedToposInverseImage_exact
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F J K]
    [RepresentablyFlat F]
    [HasSheafify J (Type u)] [HasSheafify K (Type u)]
    [∀ P : Cᵒᵖ ⥤ Type u, F.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ Dᵒᵖ ⥤ Type u)] :
    exactFunctor
      (Sheaf J AddCommGrpCat.{u})
      (Sheaf K AddCommGrpCat.{u})
      (F.sheafPullback AddCommGrpCat.{u} J K) := by
  rw [exactFunctor_iff]
  constructor
  · let _ :
        PreservesFiniteLimits
          (F.op.lan :
            (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{u}) :=
        inferInstance
    exact Functor.sheafPullbackConstruction.preservesFiniteLimits F AddCommGrpCat.{u} J K
  · let _ : (F.sheafPullback AddCommGrpCat.{u} J K).IsLeftAdjoint :=
        (F.sheafAdjunctionContinuous AddCommGrpCat.{u} J K).isLeftAdjoint
    infer_instance

/- Lemma 18.31.2 (2): for a flat morphism of ringed topoi, formalized by a flat morphism of
ringed sites `f`, the pullback functor on module sheaves `f^*` is exact. This is already the
canonical owner theorem `RingedSite.Hom.IsFlat.pullback_exact`. -/
recall IsFlat.pullback_exact

end RingedSite.Hom

/-! ### Definition_18_31_3 (from Chap18) -/
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC CommRingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf JC CommRingCat.{u}} {𝒪' : Sheaf JD CommRingCat.{u}}

local notation "X" => RingedSite.ofCommRingSheaf JC 𝒪
local notation "Y" => RingedSite.ofCommRingSheaf JD 𝒪'

/- Domain-style sampling for Definition 18.31.3:
- primary domain: relative flatness of a sheaf of modules along a morphism of ringed sites,
  expressed by restricting scalars along the inverse-image structure-sheaf map;
- sampled owner declarations:
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.restrictScalars`,
  `SheafOfModules.flat_over` from `Definition_17_20_3`;
- best owner abstraction: the source-facing owner should be the bundled morphism
  `f : RingedSite.Hom X Y`, where `X := RingedSite.ofCommRingSheaf JC 𝒪` and
  `Y := RingedSite.ofCommRingSheaf JD 𝒪'`; the inverse-image structure-sheaf map is only a thin
  bridge needed to restrict scalars;
- primitive data: the bundled ringed-site morphism `f : X ⟶ Y` and the `\mathcal O`-module `ℱ`;
- derived API: the inverse-image commutative structure-sheaf map of `f` and the relative
  flatness predicate `flatOver`.

Source/core/bridge triage:
- `source-facing`: the relative flatness predicate `flatOver f ℱ`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat` for a sheaf of modules over a fixed
  structure sheaf;
- `bridge/view`: the inverse-image structure-sheaf map
  `inverseImageStructureSheafMap f` and the resulting restricted module
  `((SheafOfModules.restrictScalars
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).map
        (inverseImageStructureSheafMap f))).obj ℱ)`,
  viewed as a module over `f^{-1}\mathcal O'`.
-/

local instance base_isContinuous (f : X ⟶ Y) : Functor.IsContinuous f.base JD JC :=
  f.isMorphismOfSites.toIsContinuous

private abbrev pushforwardCommRingMap
    (f : X ⟶ Y) :
    𝒪' ⟶ (f.base.sheafPushforwardContinuous CommRingCat.{u} JD JC).obj 𝒪 :=
  Functor.preimage (sheafCompose JD (forget₂ CommRingCat RingCat))
    (show ringSheaf JD 𝒪' ⟶
        ringSheaf JD ((f.base.sheafPushforwardContinuous CommRingCat.{u} JD JC).obj 𝒪) from
      f.structureSheafMap)

/-- The inverse-image form `f^{-1}\mathcal O_Y \to \mathcal O_X` of the structure-sheaf map of a
bundled morphism of ringed sites `f : X ⟶ Y`, in the commutative setting
`X = RingedSite.ofCommRingSheaf JC 𝒪` and `Y = RingedSite.ofCommRingSheaf JD 𝒪'`. -/
abbrev inverseImageStructureSheafMap
    (f : X ⟶ Y) :
    (f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪' ⟶ 𝒪 :=
  ((f.base.sheafAdjunctionContinuous CommRingCat.{u} JD JC).homEquiv _ _).symm
    (pushforwardCommRingMap f)

/-- Definition 18.31.3: for a morphism of ringed sites `f : X ⟶ Y`, an `\mathcal O_X`-module
`\mathcal F` is flat over `Y` when, after restricting scalars along the inverse-image
structure-sheaf map `f^{-1}\mathcal O_Y \to \mathcal O_X`, it is a flat
`f^{-1}\mathcal O_Y`-module. -/
abbrev flatOver
    (f : X ⟶ Y) (ℱ : ringedSiteModuleCategory JC 𝒪) : Prop :=
  IsFlat ((f.base.sheafPullback CommRingCat.{u} JD JC).obj 𝒪')
    ((SheafOfModules.restrictScalars
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).map
        (inverseImageStructureSheafMap f))).obj ℱ)

end RingedSite.Hom

/-! ### Lemma_18_31_4 (from Chap18) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 18.31.4:
- primary domain: pullback of internal-Hom sheaves along a flat morphism of ringed sites;
- sampled owner declarations:
  `CategoryTheory.expComparison`,
  `RingedSite.Hom.pullbackInternalHomComparison`,
  `RingedSite.Hom.(^*)`,
  `RingedSite.Hom.IsFlat`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction: the ambient owner is the pullback functor `(f^*)`; when the stronger
  Cartesian-closed comparison owner `CategoryTheory.expComparison` is available, the comparison of
  Remark 18.27.3 is its ringed-site bridge component. The source-facing theorem remains stated for
  that bridge because the generic mathlib owner currently carries extra ambient assumptions not
  present in the textbook statement;
- primitive data: a morphism of ringed sites `f` and module sheaves `ℱ 𝒢`;
- derived API: the statement that the source-facing comparison morphism is an isomorphism when
  `ℱ` is finitely presented and `f` is flat.

Source/core/bridge triage:
- `source-facing`: the isomorphism statement for the comparison morphism;
- `core/canonical`: `RingedSite.Hom.(^*)`, `RingedSite.Hom.IsFlat`,
  `SheafOfModules.IsFinitePresentation`, and, under the stronger generic comparison hypotheses,
  `CategoryTheory.expComparison`;
- `bridge/view`: `RingedSite.Hom.pullbackInternalHomComparison`. -/

variable {X Y : RingedSite} (f : X ⟶ Y)
variable [MonoidalCategory (SheafOfModules Y.structureSheaf)]
variable [MonoidalClosed (SheafOfModules Y.structureSheaf)]
variable [MonoidalCategory (SheafOfModules X.structureSheaf)]
variable [MonoidalClosed (SheafOfModules X.structureSheaf)]
variable [(f^*).Monoidal]

-- Proof sketch: the statement is local on `X`, so after localizing one may choose a finite free
-- presentation of `ℱ`. Flatness makes pullback exact, internal Hom is left exact in the first
-- variable, and for finite free sources the comparison map is visibly an isomorphism. Applying
-- these facts to the presentation diagram and using the five lemma gives the result.
--
-- API note: `pullbackInternalHomComparison` is the source-facing bridge/view of the ambient
-- pullback comparison; the generic owner `CategoryTheory.expComparison` in mathlib currently
-- requires additional Cartesian-closed comparison data that is not part of this textbook-facing
-- statement.
/-- Lemma 18.31.4: for a flat morphism of ringed sites
`f : (\mathcal C, \mathcal O_\mathcal C) \to (\mathcal D, \mathcal O_\mathcal D)` and
`\mathcal O_\mathcal D`-modules `\mathcal F`, `\mathcal G`, if `\mathcal F` is finitely
presented, then the canonical map of Remark 18.27.3
`f^*\mathcal H\!\mathit{om}_{\mathcal O_\mathcal D}(\mathcal F, \mathcal G) ⟶
\mathcal H\!\mathit{om}_{\mathcal O_\mathcal C}(f^*\mathcal F, f^*\mathcal G)`
is an isomorphism. -/
theorem isIso_pullbackInternalHomComparison
    (ℱ 𝒢 : SheafOfModules Y.structureSheaf) [ℱ.IsFinitePresentation] [IsFlat f] :
    IsIso (pullbackInternalHomComparison f ℱ 𝒢) := sorry

end RingedSite.Hom

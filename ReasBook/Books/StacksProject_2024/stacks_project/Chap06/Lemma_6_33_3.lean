import Mathlib
import StacksProject_2024.Chap06.Definition_6_15_1
import StacksProject_2024.Chap06.Glueing_data_for_sheaves_on_an_open_cover
import StacksProject_2024.Chap06.Lemma_6_21_6
import StacksProject_2024.Chap06.Lemma_6_15_2
import StacksProject_2024.Chap06.Lemma_6_33_2
import StacksProject_2024.Chap06.Lemma_6_33_4
import StacksProject_2024.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}}

local instance : HasLimits (Type w) := inferInstance
local instance : HasColimits (Type w) := inferInstance
local instance : PreservesLimits (forget (Type w)) := inferInstance
local instance : PreservesFilteredColimits (forget (Type w)) :=
  PreservesColimits.preservesFilteredColimits (forget (Type w))
local instance : (forget (Type w)).ReflectsIsomorphisms := inferInstance

/-- The open subspace attached to an inclusion `W ⊆ U`. -/
private abbrev openSubsetHomOfLE {W U : Opens X} (h : W ≤ U) :
    openSubsetSpace W ⟶ openSubsetSpace U :=
  (Opens.toTopCat X).map (homOfLE h)

private abbrev openSubsetRestrictionFunctor {W U : Opens X} (h : W ≤ U) :
    Opens (openSubsetSpace U) ⥤ Opens (openSubsetSpace W) :=
  Opens.map (openSubsetHomOfLE h)

/-- The inclusion `W ↪ U ↪ X` is the inclusion `W ↪ X`. -/
@[simp] private theorem openSubsetHomOfLE_comp_inclusion {W U : Opens X} (h : W ≤ U) :
    openSubsetHomOfLE h ≫ openSubsetInclusion U = openSubsetInclusion W :=
  rfl

/-- The map of open subspaces induced by an inclusion `W ⊆ U` is an open embedding. -/
private theorem openSubsetHomOfLE_isOpenEmbedding {W U : Opens X} (h : W ≤ U) :
    IsOpenEmbedding (openSubsetHomOfLE h) := by
  exact IsLocalHomeomorph.isOpenEmbedding_of_comp
    U.isOpenEmbedding.isLocalHomeomorph
    (by simpa [Function.comp, openSubsetHomOfLE_comp_inclusion] using W.isOpenEmbedding)
    (by continuity)

/-- The inclusion `U ∩ V ↪ U` is an open embedding. -/
private theorem openSubsetIntersectionLeftInclusion_isOpenEmbedding (U V : Opens X) :
    IsOpenEmbedding (openSubsetIntersectionLeftInclusion U V) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_left

/-- The inclusion `U ∩ V ↪ V` is an open embedding. -/
private theorem openSubsetIntersectionRightInclusion_isOpenEmbedding (U V : Opens X) :
    IsOpenEmbedding (openSubsetIntersectionRightInclusion U V) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_right

private theorem openSubsetTripleFirstInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleFirstInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_left)

private theorem openSubsetTripleSecondInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleSecondInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_right)

private theorem openSubsetTripleThirdInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleThirdInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_right

private theorem openSubsetTripleToPairLeftInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairLeftInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_left

private theorem openSubsetTripleToPairCenterInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairCenterInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding (inf_le_inf inf_le_right le_rfl)

private theorem openSubsetTripleToPairOuterInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairOuterInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) le_rfl)

variable {C : Type (w + 1)} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

variable {ι : Type u} {U : ι → Opens X}

private abbrev algebraicRestrictToOpen (U : Opens X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace U) :=
  U.isOpenEmbedding.sheafPullback C

private abbrev algebraicRestrictToPairLeft (U V : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) :=
  (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback C

private abbrev algebraicRestrictToPairRight (U V : Opens X) :
    TopCat.Sheaf C (openSubsetSpace V) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) :=
  (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback C

private abbrev algebraicRestrictToTripleFirst (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleFirstInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictToTripleSecond (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace V) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleSecondInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictToTripleThird (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace W) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleThirdInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictOverlapToTripleLeft (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairLeftInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictOverlapToTripleCenter (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairCenterInclusion_isOpenEmbedding U V W).sheafPullback C

private abbrev algebraicRestrictOverlapToTripleOuter (U V W : Opens X) :
    TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W)) :=
  (openSubsetTripleToPairOuterInclusion_isOpenEmbedding U V W).sheafPullback C

private theorem algebraicOpenSubsetRestriction_comp_eq
    {C : Type (w + 1)} [Category.{w} C] {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    ((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding hTW).sheafPullback C) =
      ((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).sheafPullback C) := by
  sorry

private noncomputable def algebraicOpenSubsetRestrictionCompIso
    {C : Type (w + 1)} [Category.{w} C] {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    ((openSubsetHomOfLE_isOpenEmbedding hWU).sheafPullback C) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding hTW).sheafPullback C) ≅
      ((openSubsetHomOfLE_isOpenEmbedding (hTW.trans hWU)).sheafPullback C) :=
  eqToIso (algebraicOpenSubsetRestriction_comp_eq hTW hWU)

private theorem algebraicGlobalRestriction_comp_eq
    {C : Type (w + 1)} [Category.{w} C] {W U : Opens X} (h : W ≤ U) :
    (U.isOpenEmbedding.sheafPullback C) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C) =
      (W.isOpenEmbedding.sheafPullback C) := by
  sorry

private noncomputable def algebraicGlobalRestrictionCompIso
    {C : Type (w + 1)} [Category.{w} C] {W U : Opens X} (h : W ≤ U) :
    (U.isOpenEmbedding.sheafPullback C) ⋙
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback C) ≅
      (W.isOpenEmbedding.sheafPullback C) :=
  eqToIso (algebraicGlobalRestriction_comp_eq h)

private noncomputable def algebraicRestrictToTripleFirstViaIJIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleFirst U V W :
      TopCat.Sheaf C (openSubsetSpace U) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft U V :
        TopCat.Sheaf C (openSubsetSpace U) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ⋙
        (algebraicRestrictOverlapToTripleLeft U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ U from inf_le_left)).symm

private noncomputable def algebraicRestrictToTripleSecondViaIJIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleSecond U V W :
      TopCat.Sheaf C (openSubsetSpace V) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight U V :
        TopCat.Sheaf C (openSubsetSpace V) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ⋙
        (algebraicRestrictOverlapToTripleLeft U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ V)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ V from inf_le_right)).symm

private noncomputable def algebraicRestrictToTripleSecondViaJKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleSecond U V W :
      TopCat.Sheaf C (openSubsetSpace V) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft V W :
        TopCat.Sheaf C (openSubsetSpace V) ⥤
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleCenter U V W :
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ V from inf_le_left)).symm

private noncomputable def algebraicRestrictToTripleThirdViaJKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleThird U V W :
      TopCat.Sheaf C (openSubsetSpace W) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight V W :
        TopCat.Sheaf C (openSubsetSpace W) ⥤
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleCenter U V W :
          TopCat.Sheaf C (openSubsetSpace (V ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ W from inf_le_right)).symm

private noncomputable def algebraicRestrictToTripleFirstViaIKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleFirst U V W :
      TopCat.Sheaf C (openSubsetSpace U) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairLeft U W :
        TopCat.Sheaf C (openSubsetSpace U) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleOuter U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ U from inf_le_left)).symm

private noncomputable def algebraicRestrictToTripleThirdViaIKIso
    (U V W : Opens X) :
    (algebraicRestrictToTripleThird U V W :
      TopCat.Sheaf C (openSubsetSpace W) ⥤
        TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) ≅
      (algebraicRestrictToPairRight U W :
        TopCat.Sheaf C (openSubsetSpace W) ⥤
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W))) ⋙
        (algebraicRestrictOverlapToTripleOuter U V W :
          TopCat.Sheaf C (openSubsetSpace (U ⊓ W)) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V ⊓ W))) :=
  (algebraicOpenSubsetRestrictionCompIso
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ W from inf_le_right)).symm

private noncomputable def algebraicGlobalRestrictionToPairViaLeftIso
    (U V : Opens X) :
    (algebraicRestrictToOpen (U ⊓ V) :
      TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ≅
      (algebraicRestrictToOpen U :
        TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace U)) ⋙
        (algebraicRestrictToPairLeft U V :
          TopCat.Sheaf C (openSubsetSpace U) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) :=
  (algebraicGlobalRestrictionCompIso
    (show U ⊓ V ≤ U from inf_le_left)).symm

private noncomputable def algebraicGlobalRestrictionToPairViaRightIso
    (U V : Opens X) :
    (algebraicRestrictToOpen (U ⊓ V) :
      TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) ≅
      (algebraicRestrictToOpen V :
        TopCat.Sheaf C X ⥤ TopCat.Sheaf C (openSubsetSpace V)) ⋙
        (algebraicRestrictToPairRight U V :
          TopCat.Sheaf C (openSubsetSpace V) ⥤
            TopCat.Sheaf C (openSubsetSpace (U ⊓ V))) :=
  (algebraicGlobalRestrictionCompIso
    (show U ⊓ V ≤ V from inf_le_right)).symm

local notation "algRestrictToOpen" => algebraicRestrictToOpen
local notation "algRestrictToPairLeft" => algebraicRestrictToPairLeft
local notation "algRestrictToPairRight" => algebraicRestrictToPairRight
local notation "algRestrictToTripleFirst" => algebraicRestrictToTripleFirst
local notation "algRestrictToTripleSecond" => algebraicRestrictToTripleSecond
local notation "algRestrictToTripleThird" => algebraicRestrictToTripleThird
local notation "algRestrictOverlapToTripleLeft" => algebraicRestrictOverlapToTripleLeft
local notation "algRestrictOverlapToTripleCenter" =>
  algebraicRestrictOverlapToTripleCenter
local notation "algRestrictOverlapToTripleOuter" =>
  algebraicRestrictOverlapToTripleOuter

private abbrev algebraicTripleOverlapHom12
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleFirst (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (algRestrictToTripleSecond (U i) (U j) (U k)).obj (localSheaf j) :=
  ((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).mapIso (overlapIso i j)).hom ≫
    ((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app (localSheaf j))

private abbrev algebraicTripleOverlapHom23
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleSecond (U i) (U j) (U k)).obj (localSheaf j) ⟶
      (algRestrictToTripleThird (U i) (U j) (U k)).obj (localSheaf k) :=
  ((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
    ((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).mapIso
      (overlapIso j k)).hom ≫
    ((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app (localSheaf k))

private abbrev algebraicTripleOverlapHom13
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (algRestrictToTripleFirst (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (algRestrictToTripleThird (U i) (U j) (U k)).obj (localSheaf k) :=
  ((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).mapIso (overlapIso i k)).hom ≫
    ((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app (localSheaf k))

/-
Domain-style sampling for Lemma 6.33.3:
- primary domain: sheaf descent on an open cover, specialized to sheaves valued in a category of
  algebraic structures;
- sampled owner declarations:
  `IsAlgebraicStructure`,
  `CategoryTheory.sheafCompose`,
  `SheafOpenCoverGlueing`,
  `SheafOpenCoverGlueing.Realizes`,
  `exists_sheaf_realizing_open_cover_glueing`;
- owner abstraction: the chapter owner remains `SheafOpenCoverGlueing U`, and the algebraic input
  data should only appear through a thin bridge to that owner;
- primitive data: the local `C`-valued sheaves, the pairwise overlap isomorphisms, the cocycle
  condition, and the covering hypothesis;
- derived API: the realization predicate and the existence theorem for a global realizing sheaf.

Source/core/bridge triage:
- `source-facing`: the primitive local sheaves, overlap isomorphisms, cocycle, and cover;
- `core/canonical`: `SheafOpenCoverGlueing U`;
  `bridge/view`: the private helper below that forgets along `F` and packages the resulting
  set-valued descent datum in the existing owner. -/
private abbrev algebraicToTypes (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U : Opens X) :
    TopCat.Sheaf C (openSubsetSpace U) ⥤ TopCat.Sheaf (Type w) (openSubsetSpace U) :=
  letI : PreservesLimits F := inferInstance
  letI : (Opens.grothendieckTopology (openSubsetSpace U)).HasSheafCompose F :=
    CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
      (Opens.grothendieckTopology (openSubsetSpace U))
  sheafCompose (Opens.grothendieckTopology (openSubsetSpace U)) F

private noncomputable def algebraicPairLeftToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    ((algRestrictToPairLeft U V ⋙ algebraicToTypes F (U ⊓ V)).obj ℱ) ≅
      ((algebraicToTypes F U ⋙
        (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  eqToIso rfl

private noncomputable def algebraicPairRightToTypesIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    ((algRestrictToPairRight U V ⋙ algebraicToTypes F (U ⊓ V)).obj ℱ) ≅
      ((algebraicToTypes F V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  eqToIso rfl

private noncomputable def algebraicLeftOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace U)) :
    (TopCat.Sheaf.pullback (Type w) (openSubsetIntersectionLeftInclusion U V)).obj
        ((algebraicToTypes F U).obj ℱ) ≅
      ((algebraicToTypes F U ⋙
          (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  ((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullbackIso (Type w)).app
    ((algebraicToTypes F U).obj ℱ)

private noncomputable def algebraicRightOwnerIso
    (F : C ⥤ Type w) [IsAlgebraicStructure C F] (U V : Opens X)
    (ℱ : TopCat.Sheaf C (openSubsetSpace V)) :
    ((algebraicToTypes F V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
      ℱ) ≅
      (TopCat.Sheaf.pullback (Type w) (openSubsetIntersectionRightInclusion U V)).obj
        ((algebraicToTypes F V).obj ℱ) :=
  (((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullbackIso (Type w)).app
    ((algebraicToTypes F V).obj ℱ)).symm

namespace AlgebraicSheafOpenCover

/-- The cocycle condition for pairwise overlap isomorphisms in a gluing datum of sheaves valued in
a category of algebraic structures on an open cover. -/
def CocycleCondition (U : ι → Opens X)
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j)) :
    Prop :=
  ∀ i j k : ι,
    algebraicTripleOverlapHom12 localSheaf overlapIso i j k ≫
      algebraicTripleOverlapHom23 localSheaf overlapIso i j k =
    algebraicTripleOverlapHom13 localSheaf overlapIso i j k

variable {F : C ⥤ Type w} [IsAlgebraicStructure C F] {U : ι → Opens X}

private noncomputable def toSheafOpenCoverGlueing
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    SheafOpenCoverGlueing U where
  localSheaf i := (algebraicToTypes F (U i)).obj (localSheaf i)
  overlapIso i j :=
    (algebraicLeftOwnerIso F (U i) (U j) (localSheaf i) ≪≫
      (algebraicPairLeftToTypesIso F (U i) (U j) (localSheaf i)).symm) ≪≫
      ((algebraicToTypes F (U i ⊓ U j)).mapIso (overlapIso i j)) ≪≫
      (algebraicPairRightToTypesIso F (U i) (U j) (localSheaf j) ≪≫
        algebraicRightOwnerIso F (U i) (U j) (localSheaf j))
  cocycle := by
    sorry
  isCover := hU

private abbrev realizationLeftHom
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (ℱ : TopCat.Sheaf C X) (φ : ∀ i : ι, (algRestrictToOpen (U i)).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (algRestrictToOpen (U i ⊓ U j)).obj ℱ ⟶
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) :=
  ((algebraicGlobalRestrictionToPairViaLeftIso (U i) (U j)).hom.app ℱ) ≫
    ((algRestrictToPairLeft (U i) (U j)).mapIso (φ i)).hom

private abbrev realizationRightHom
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (ℱ : TopCat.Sheaf C X) (φ : ∀ i : ι, (algRestrictToOpen (U i)).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (algRestrictToOpen (U i ⊓ U j)).obj ℱ ⟶
      (algRestrictToPairRight (U i) (U j)).obj (localSheaf j) :=
  ((algebraicGlobalRestrictionToPairViaRightIso (U i) (U j)).hom.app ℱ) ≫
    ((algRestrictToPairRight (U i) (U j)).mapIso (φ j)).hom

/-- A `C`-valued sheaf realizes an algebraic gluing datum if its restrictions recover the given
local sheaves and the induced overlap comparisons agree with the prescribed overlap
isomorphisms in `TopCat.Sheaf C`. -/
def Realizes
    (U : ι → Opens X)
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (ℱ : TopCat.Sheaf C X) : Prop :=
  ∃ φ : ∀ i : ι,
      ((U i).isOpenEmbedding.sheafPullback C).obj ℱ ≅ localSheaf i,
    ∀ i j : ι,
      realizationLeftHom localSheaf ℱ φ i j ≫ (overlapIso i j).hom =
        realizationRightHom localSheaf ℱ φ i j

end AlgebraicSheafOpenCover

-- Proof sketch: glue the underlying set-valued sheaves by Lemma 6.33.2, then transport the
-- algebraic structure on sections across the equalizer construction.
/-- Lemma 6.33.3: an algebraic gluing datum on an open cover is realized by a `C`-valued sheaf on
the ambient space. -/
theorem exists_algebraic_sheaf_of_open_cover_glueing
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    ∃ ℱ : TopCat.Sheaf C X, AlgebraicSheafOpenCover.Realizes U localSheaf overlapIso ℱ := by
  sorry

end

section

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

/-- Restricting the restriction of `𝒪` to `U` further to `W ⊆ U` gives the restriction of `𝒪`
directly to `W`. -/
private noncomputable def restrictedRingSheafPullbackIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj
        ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪) ≅
      (TopCat.Sheaf.pullback RingCat (openSubsetInclusion W)).obj 𝒪 :=
  let e :
      TopCat.Sheaf.pullback RingCat (openSubsetInclusion U) ⋙
          TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h) ≅
        TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h ≫ openSubsetInclusion U) :=
    (TopCat.Sheaf.pullbackComp (openSubsetHomOfLE h) (openSubsetInclusion U) :
      TopCat.Sheaf.pullback RingCat (openSubsetInclusion U) ⋙
          TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h) ≅
        TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h ≫ openSubsetInclusion U))
  e.app 𝒪 ≪≫
    eqToIso (congrArg
      (fun f ↦ (TopCat.Sheaf.pullback RingCat f).obj 𝒪)
      (openSubsetHomOfLE_comp_inclusion h))

/-- The canonical map of restricted ring sheaves attached to an inclusion `W ⊆ U`. -/
private noncomputable def restrictedRingSheafToPushforward
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪 ⟶
      ((openSubsetRestrictionFunctor h).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W))).obj
        ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion W)).obj 𝒪) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
      ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪)) ≫
    ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).mapIso
      (restrictedRingSheafPullbackIso 𝒪 h)).hom

/-- Restriction of a ring sheaf to an open subset, as a sheaf on the corresponding open
subspace. -/
abbrev ringSheafRestriction (𝒪 : TopCat.Sheaf RingCat X) (U : Opens X) :
    TopCat.Sheaf RingCat (openSubsetSpace U) :=
  (TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪

namespace TopCat

set_option quotPrecheck false in
scoped notation:80 𝒪:80 " |_ " U:80 =>
  ringSheafRestriction 𝒪 U

end TopCat

open scoped TopCat

/- Domain-style sampling for the module-valued restriction step:
- primary domain: inverse-image/restriction of sheaves of modules along open inclusions;
- sampled owner declarations: `SheafOfModules.pullback`, `SheafOfModules.pullbackComp`,
  `moduleSheafRestrictionToOpen`, `moduleSheafExtensionByZeroAdjunction`;
- owner abstraction: the core owner is `SheafOfModules.pullback`, while
  `moduleSheafRestrictionToOpen` is the chapter’s canonical open-immersion specialization;
- source/core/bridge triage: the source-facing surface is the restricted ring sheaf notation
  `𝒪 |_ U`; `SheafOfModules.pullback` is core/canonical; and the pairwise overlap restrictions
  below are thin bridge/view specializations for the named inclusions in the open-cover
  geometry. -/

private instance moduleSheafRestrictionPushforward_isRightAdjoint
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (SheafOfModules.pushforward (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint := by
  sorry

/- Restriction of sheaves of modules along an inclusion `W ⊆ U` of open subsets. -/
noncomputable abbrev moduleSheafRestriction
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ W) :=
  let _ :
      (SheafOfModules.pushforward (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint :=
    moduleSheafRestrictionPushforward_isRightAdjoint 𝒪 h
  SheafOfModules.pullback (restrictedRingSheafToPushforward 𝒪 h)

/-- Restriction of `𝒪|_U`-modules to `\mathcal O|_{U \cap V}` along the left inclusion
`U \cap V \subset U`. -/
noncomputable abbrev moduleSheafRestrictionToPairLeft
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V)) :=
  moduleSheafRestriction 𝒪 inf_le_left

/-- Restriction of `𝒪|_V`-modules to `\mathcal O|_{U \cap V}` along the right inclusion
`U \cap V \subset V`. -/
noncomputable abbrev moduleSheafRestrictionToPairRight
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    SheafOfModules (𝒪 |_ V) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V)) :=
  moduleSheafRestriction 𝒪 inf_le_right

private abbrev moduleRestrictToTripleFirst
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_left)

private abbrev moduleRestrictToTripleSecond
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ V) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_right)

private abbrev moduleRestrictToTripleThird
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ W) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 inf_le_right

private abbrev moduleRestrictOverlapToTripleLeft
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (U ⊓ V)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 inf_le_left

private abbrev moduleRestrictOverlapToTripleCenter
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (V ⊓ W)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 (inf_le_inf inf_le_right le_rfl)

private abbrev moduleRestrictOverlapToTripleOuter
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (U ⊓ W)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) le_rfl)

private theorem moduleSheafRestriction_comp_eq
    (𝒪 : TopCat.Sheaf RingCat X) {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    moduleSheafRestriction 𝒪 hWU ⋙ moduleSheafRestriction 𝒪 hTW =
      moduleSheafRestriction 𝒪 (hTW.trans hWU) := by
  sorry

private noncomputable def moduleSheafRestrictionCompIso
    (𝒪 : TopCat.Sheaf RingCat X) {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    moduleSheafRestriction 𝒪 hWU ⋙ moduleSheafRestriction 𝒪 hTW ≅
      moduleSheafRestriction 𝒪 (hTW.trans hWU) :=
  eqToIso (moduleSheafRestriction_comp_eq 𝒪 hTW hWU)

private theorem moduleSheafRestrictionToOpen_comp_eq
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    moduleSheafRestrictionToOpen U 𝒪 ⋙ moduleSheafRestriction 𝒪 h =
      moduleSheafRestrictionToOpen W 𝒪 := by
  sorry

private noncomputable def moduleSheafRestrictionToOpenCompIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    moduleSheafRestrictionToOpen U 𝒪 ⋙ moduleSheafRestriction 𝒪 h ≅
      moduleSheafRestrictionToOpen W 𝒪 :=
  eqToIso (moduleSheafRestrictionToOpen_comp_eq 𝒪 h)

private noncomputable def moduleRestrictToTripleFirstViaIJIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleFirst 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 U V ⋙ moduleRestrictOverlapToTripleLeft 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ U from inf_le_left)).symm

private noncomputable def moduleRestrictToTripleSecondViaIJIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleSecond 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 U V ⋙ moduleRestrictOverlapToTripleLeft 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ V from inf_le_right)).symm

private noncomputable def moduleRestrictToTripleSecondViaJKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleSecond 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 V W ⋙ moduleRestrictOverlapToTripleCenter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ V from inf_le_left)).symm

private noncomputable def moduleRestrictToTripleThirdViaJKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleThird 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 V W ⋙ moduleRestrictOverlapToTripleCenter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ W from inf_le_right)).symm

private noncomputable def moduleRestrictToTripleFirstViaIKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleFirst 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 U W ⋙ moduleRestrictOverlapToTripleOuter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ U from inf_le_left)).symm

private noncomputable def moduleRestrictToTripleThirdViaIKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleThird 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 U W ⋙ moduleRestrictOverlapToTripleOuter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ W from inf_le_right)).symm

private noncomputable def moduleRestrictionToPairViaLeftIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    moduleSheafRestrictionToOpen (U ⊓ V) 𝒪 ≅
      moduleSheafRestrictionToOpen U 𝒪 ⋙ moduleSheafRestrictionToPairLeft 𝒪 U V :=
  (moduleSheafRestrictionToOpenCompIso 𝒪
    (show U ⊓ V ≤ U from inf_le_left)).symm

private noncomputable def moduleRestrictionToPairViaRightIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    moduleSheafRestrictionToOpen (U ⊓ V) 𝒪 ≅
      moduleSheafRestrictionToOpen V 𝒪 ⋙ moduleSheafRestrictionToPairRight 𝒪 U V :=
  (moduleSheafRestrictionToOpenCompIso 𝒪
    (show U ⊓ V ≤ V from inf_le_right)).symm

private theorem moduleToAddCommGrpPairLeftRestriction_eq
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{w} (openSubsetIntersectionLeftInclusion U V)).obj
        ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) =
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
        ((moduleSheafRestrictionToPairLeft 𝒪 U V).obj ℱ) := by
  sorry

private noncomputable def moduleToAddCommGrpPairLeftRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    ((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
        ((moduleSheafRestrictionToPairLeft 𝒪 U V).obj ℱ) :=
  (((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullbackIso
      AddCommGrpCat.{w}).app ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ)).symm ≪≫
    eqToIso (moduleToAddCommGrpPairLeftRestriction_eq 𝒪 U V ℱ)

private theorem moduleToAddCommGrpPairRightRestriction_eq
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{w} (openSubsetIntersectionRightInclusion U V)).obj
        ((SheafOfModules.toSheaf (𝒪 |_ V)).obj ℱ) =
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
        ((moduleSheafRestrictionToPairRight 𝒪 U V).obj ℱ) := by
  sorry

private noncomputable def moduleToAddCommGrpPairRightRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) :
    ((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback
      AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf (𝒪 |_ V)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
        ((moduleSheafRestrictionToPairRight 𝒪 U V).obj ℱ) :=
  (((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullbackIso
      AddCommGrpCat.{w}).app ((SheafOfModules.toSheaf (𝒪 |_ V)).obj ℱ)).symm ≪≫
    eqToIso (moduleToAddCommGrpPairRightRestriction_eq 𝒪 U V ℱ)

variable (𝒪 : TopCat.Sheaf RingCat X)

private abbrev moduleTripleOverlapHom12
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleFirst 𝒪 (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (moduleRestrictToTripleSecond 𝒪 (U i) (U j) (U k)).obj (localSheaf j) :=
  ((moduleRestrictToTripleFirstViaIJIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((moduleRestrictOverlapToTripleLeft 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso i j)).hom ≫
    ((moduleRestrictToTripleSecondViaIJIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf j))

private abbrev moduleTripleOverlapHom23
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleSecond 𝒪 (U i) (U j) (U k)).obj (localSheaf j) ⟶
      (moduleRestrictToTripleThird 𝒪 (U i) (U j) (U k)).obj (localSheaf k) :=
  ((moduleRestrictToTripleSecondViaJKIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
    ((moduleRestrictOverlapToTripleCenter 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso j k)).hom ≫
    ((moduleRestrictToTripleThirdViaJKIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf k))

private abbrev moduleTripleOverlapHom13
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleFirst 𝒪 (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (moduleRestrictToTripleThird 𝒪 (U i) (U j) (U k)).obj (localSheaf k) :=
  ((moduleRestrictToTripleFirstViaIKIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((moduleRestrictOverlapToTripleOuter 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso i k)).hom ≫
    ((moduleRestrictToTripleThirdViaIKIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf k))

/-- The cocycle condition for pairwise overlap isomorphisms in a gluing datum of sheaves of
`𝒪`-modules on an open cover. -/
private abbrev moduleToTypes (𝒪 : TopCat.Sheaf RingCat X) (U : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤ TopCat.Sheaf (Type w) (openSubsetSpace U) :=
  letI : PreservesLimits (forget AddCommGrpCat.{w}) := inferInstance
  letI :
      (Opens.grothendieckTopology (openSubsetSpace U)).HasSheafCompose
        (forget AddCommGrpCat.{w}) :=
    CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
      (Opens.grothendieckTopology (openSubsetSpace U))
  SheafOfModules.toSheaf (𝒪 |_ U) ⋙
    sheafCompose (Opens.grothendieckTopology (openSubsetSpace U)) (forget AddCommGrpCat.{w})

private noncomputable def modulePairLeftToTypesIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    ((moduleSheafRestrictionToPairLeft 𝒪 U V ⋙ moduleToTypes 𝒪 (U ⊓ V)).obj ℱ) ≅
      ((moduleToTypes 𝒪 U ⋙
        (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  let e :=
    (sheafCompose (Opens.grothendieckTopology (openSubsetSpace (U ⊓ V)))
      (forget AddCommGrpCat.{w})).mapIso
      (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 U V ℱ).symm
  eqToIso rfl ≪≫ e ≪≫ eqToIso rfl

private noncomputable def modulePairRightToTypesIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) :
    ((moduleSheafRestrictionToPairRight 𝒪 U V ⋙ moduleToTypes 𝒪 (U ⊓ V)).obj ℱ) ≅
      ((moduleToTypes 𝒪 V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  let e :=
    (sheafCompose (Opens.grothendieckTopology (openSubsetSpace (U ⊓ V)))
      (forget AddCommGrpCat.{w})).mapIso
      (moduleToAddCommGrpPairRightRestrictionIso 𝒪 U V ℱ).symm
  eqToIso rfl ≪≫ e ≪≫ eqToIso rfl

private noncomputable def moduleLeftOwnerIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) := by
  letI : PreservesFilteredColimitsOfSize.{w, w, w, w, w + 1, w + 1}
      (forget (Type w)) := by
    exact PreservesColimits.preservesFilteredColimits (forget (Type w))
  exact ((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullbackIso (Type w)).app
    ((moduleToTypes 𝒪 U).obj ℱ)

private noncomputable def moduleRightOwnerIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) := by
  letI : PreservesFilteredColimitsOfSize.{w, w, w, w, w + 1, w + 1}
      (forget (Type w)) := by
    exact PreservesColimits.preservesFilteredColimits (forget (Type w))
  exact (((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullbackIso (Type w)).app
    ((moduleToTypes 𝒪 V).obj ℱ)).symm

namespace ModuleSheafOpenCover

def CocycleCondition (U : ι → Opens X)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j)) :
    Prop :=
  ∀ i j k : ι,
    moduleTripleOverlapHom12 𝒪 localSheaf overlapIso i j k ≫
      moduleTripleOverlapHom23 𝒪 localSheaf overlapIso i j k =
    moduleTripleOverlapHom13 𝒪 localSheaf overlapIso i j k

variable {𝒪 : TopCat.Sheaf RingCat X} {U : ι → Opens X}

noncomputable def toSheafOpenCoverGlueing
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : CocycleCondition 𝒪 U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    SheafOpenCoverGlueing U where
  localSheaf i := (moduleToTypes 𝒪 (U i)).obj (localSheaf i)
  overlapIso i j :=
    (moduleLeftOwnerIso 𝒪 (U i) (U j) (localSheaf i) ≪≫
      (modulePairLeftToTypesIso 𝒪 (U i) (U j) (localSheaf i)).symm) ≪≫
      ((moduleToTypes 𝒪 (U i ⊓ U j)).mapIso (overlapIso i j)) ≪≫
      (modulePairRightToTypesIso 𝒪 (U i) (U j) (localSheaf j) ≪≫
        moduleRightOwnerIso 𝒪 (U i) (U j) (localSheaf j))
  cocycle := by
    sorry
  isCover := hU

private abbrev realizationLeftHom
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (ℱ : SheafOfModules 𝒪)
    (φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (moduleSheafRestrictionToOpen (U i ⊓ U j) 𝒪).obj ℱ ⟶
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) :=
  ((moduleRestrictionToPairViaLeftIso 𝒪 (U i) (U j)).hom.app ℱ) ≫
    ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).mapIso (φ i)).hom

private abbrev realizationRightHom
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (ℱ : SheafOfModules 𝒪)
    (φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (moduleSheafRestrictionToOpen (U i ⊓ U j) 𝒪).obj ℱ ⟶
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j) :=
  ((moduleRestrictionToPairViaRightIso 𝒪 (U i) (U j)).hom.app ℱ) ≫
    ((moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).mapIso (φ j)).hom

/-- A sheaf of `𝒪`-modules realizes a module gluing datum if its restrictions recover the given
local module sheaves and the induced overlap comparisons agree with the prescribed overlap
isomorphisms in the categories of sheaves of `𝒪`-modules. -/
def Realizes
    (U : ι → Opens X)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (ℱ : SheafOfModules 𝒪) : Prop :=
  ∃ φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i,
    ∀ i j : ι,
      realizationLeftHom localSheaf ℱ φ i j ≫ (overlapIso i j).hom =
        realizationRightHom localSheaf ℱ φ i j

end ModuleSheafOpenCover

-- Proof sketch: the equalizer construction from Lemma 6.33.2 inherits the module structure over
-- each ring of sections, and the resulting sheaf of modules restricts back to the given local
-- module sheaves.
/-- Lemma 6.33.3 for modules: a gluing datum of sheaves of `𝒪`-modules on an open cover is
realized by a sheaf of `𝒪`-modules on the ambient space. -/
theorem exists_module_sheaf_of_open_cover_glueing
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    ∃ ℱ : SheafOfModules 𝒪, ModuleSheafOpenCover.Realizes U localSheaf overlapIso ℱ := by
  sorry

end

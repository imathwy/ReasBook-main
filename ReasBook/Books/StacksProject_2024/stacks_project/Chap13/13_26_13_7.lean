import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.«13_26_13_1»
import StacksProject_2024.Chap13.Lemma_13_26_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} {ℬ : Type u}
  [Category.{v} 𝒜] [Category.{v} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)] [Abelian (finiteFilteredObjectCat ℬ)]
  [HasDerivedCategory (GradedObject ℤ 𝒜)] [HasDerivedCategory (GradedObject ℤ ℬ)]
  [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
  [HasBinaryBiproducts (finiteFilteredObjectCat ℬ)]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (GradedObject ℤ ℬ) (up ℤ))]
  [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]
  [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat ℬ) (up ℤ))]

/- Domain-style sampling for 13.26.13.7:
- primary domain: bounded-below filtered derived functors and the compatibility of their graded
  pieces with ordinary bounded-below right derived functors;
- sampled owner declarations in this domain:
  `Functor.rightDerivedUnique`,
  `mapBoundedBelowHomotopyCategory`,
  `filteredBoundedDerivedGradedPieceFunctor`,
  `Functor.totalRightDerived`;
- best owner abstraction: `Functor.rightDerivedUnique`, specialized to the chapter owners
  `DF⁺`, the `p`-th graded-piece functors, the filtered right derived functor built by
  `Functor.totalRightDerived` on the canonical bounded-below homotopy lift
  `mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T)`, and the plain
  bounded-below right derived functor
  `(mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜))
    (boundedBelowHomotopyQuasiIso 𝒜)`;
- primitive data: the actual Chapter `13` source functor on `K⁺(Fil^f(𝒜))` obtained from the
  canonical homotopy lift of `T` and then taking the `p`-th graded piece on the target side,
  together with comparison maps exhibiting the two chapter composites as right derived functors
  of that concrete source functor;
- derived API: the comparison isomorphism and its factorization identity, already owned by
  `Functor.rightDerivedUnique` and `Functor.rightDerived_fac`.

Source/core/bridge triage:
- `source-facing`: the graded-piece comparison from `(13.26.13.7)`;
- `core/canonical`: `Functor.rightDerivedUnique`;
- `bridge/view`: the defining factorization identity `Functor.rightDerived_fac`.

This item is therefore not a new generic schema: it is the Chapter `13` specialization of the
canonical uniqueness theorem for right derived functors, built from the bounded-below filtered
homotopy lift from `13.26.13.1` and the graded-piece owner from `Lemma_13_26_12`. -/

section

variable (T : 𝒜 ⥤ₗ ℬ)

local instance : PreservesFiniteLimits T.obj :=
  T.property

local instance : PreservesBinaryBiproducts T.obj :=
  preservesBinaryBiproducts_of_preservesBinaryProducts T.obj

local instance : T.obj.Additive :=
  Functor.additive_of_preservesBinaryBiproducts T.obj

variable (p : ℤ)

local notation "W" => FQis⁺(𝒜)
local notation "QFiltA" => mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜
local notation "QFiltB" => mapBoundedBelowFilteredHomotopyToDerivedBelow ℬ
local notation "Tplus" => mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T)

variable [hRTFilt : Functor.HasRightDerivedFunctor (Tplus ⋙ QFiltB) W]

local instance : Functor.IsLocalization QFiltA W :=
  mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization

local notation "Qplus" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "QMapT" => mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj

variable [hRT : Functor.HasRightDerivedFunctor QMapT QisPlus]

local instance : Functor.IsLocalization Qplus QisPlus :=
  mapBoundedBelowHomotopyToDerivedBelow_isLocalization

local notation "GrA" => filteredBoundedDerivedGradedPieceFunctor 𝒜 p
local notation "GrB" => filteredBoundedDerivedGradedPieceFunctor ℬ p
local notation "QGrB" => filteredBoundedHomotopyToDerivedByGradedPiece ℬ p
local notation "GObjA" =>
  (finiteFilteredObjectAssociatedGradedFunctor 𝒜 ⋙
    GradedObject.eval p : finiteFilteredObjectCat 𝒜 ⥤ 𝒜)
local notation "GObjB" =>
  (finiteFilteredObjectAssociatedGradedFunctor ℬ ⋙
    GradedObject.eval p : finiteFilteredObjectCat ℬ ⥤ ℬ)
local notation "KGrA" =>
  mapBoundedBelowHomotopyCategory
    GObjA
local notation "GrSource" => Tplus ⋙ QGrB
local notation "RTFilt" =>
  @Functor.totalRightDerived _ _ _ _ _ _ (Tplus ⋙ QFiltB) QFiltA W inferInstance hRTFilt
local notation "RT" =>
  @Functor.totalRightDerived _ _ _ _ _ _ QMapT Qplus QisPlus inferInstance hRT
local notation "RTGr" => RTFilt ⋙ GrB
local notation "GrRT" => GrA ⋙ RT
local notation "IFiltIncl" =>
  mapBoundedBelowHomotopyCategory (filteredInjectiveInclusion 𝒜)
local notation "WIFilt" => W.inverseImage IFiltIncl

/-- Helper for 13.26.13.7: the graded source functor is the filtered right-derived source
followed by the bounded-below graded-piece owner on the target. -/
theorem graded_source_eq_filtered_then_gr :
    GrSource = (Tplus ⋙ QFiltB) ⋙ GrB := by
  -- Both sides are the same bounded-below graded-piece composite after unfolding the owner
  -- abbreviations from Lemma `13.26.12`.
  rfl

/-- Helper for 13.26.13.7: the ordinary bounded-below graded source on `𝒜` localizes through the
filtered derived category and then the bounded-below graded-piece functor. -/
theorem graded_localization_bridge :
    KGrA ⋙ Qplus = QFiltA ⋙ GrA := by
  -- This is the same bounded-below graded-piece functor viewed through the filtered and ordinary
  -- derived localization owners.
  rfl

/-- Helper for 13.26.13.7: the bounded-below graded source on `K⁺(Fil^f(ℬ))` is the filtered
localization followed by the bounded-below graded-piece owner on `DF⁺(ℬ)`. -/
theorem graded_target_eq_filtered_then_gr :
    QGrB = QFiltB ⋙ GrB := by
  -- This is the target-side specialization of the same definitional graded-piece bridge.
  rfl

/-- Helper for 13.26.13.7: the bounded-below graded-piece functor on `DF⁺(ℬ)` is already the
canonical right derived functor of the bounded-below graded source on `K⁺(Fil^f(ℬ))`. -/
theorem graded_piece_target_is_right_derived :
    Functor.IsRightDerivedFunctor GrB
      (eqToHom (graded_target_eq_filtered_then_gr (ℬ := ℬ) (p := p)))
      (FQis⁺(ℬ)) := by
  -- The target-side graded-piece source already inverts filtered quasi-isomorphisms, so the
  -- owner theorem `Functor.isRightDerivedFunctor_of_inverts` applies directly.
  simpa [graded_target_eq_filtered_then_gr] using
    (Functor.isRightDerivedFunctor_of_inverts (FQis⁺(ℬ)) GrB
      (eqToIso (graded_target_eq_filtered_then_gr (ℬ := ℬ) (p := p))).symm)

/-- Helper for 13.26.13.7: pulled-back filtered quasi-isomorphisms between filtered-injective
complexes are already isomorphisms. -/
theorem filtered_injective_quasi_iso_is_iso
    {X Y : K⁺(𝓘^f(𝒜))} (f : X ⟶ Y) (hf : WIFilt f) :
    IsIso f := by
  let F : K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜) := filteredInjectiveHomotopyToFilteredDerived 𝒜
  letI : Functor.IsEquivalence F := by
    simpa [F] using filteredInjectiveHomotopyToFilteredDerived_isEquivalence (𝒜 := 𝒜)
  letI : F.Full := (Functor.asEquivalence F).fullyFaithfulFunctor.full
  letI : F.Faithful := (Functor.asEquivalence F).fullyFaithfulFunctor.faithful
  have : IsIso (F.map f) := by
    -- The filtered derived localization inverts the underlying filtered quasi-isomorphism.
    change IsIso (QFiltA.map (IFiltIncl.map f))
    exact Localization.inverts QFiltA W _ hf
  exact isIso_of_fully_faithful F f

/-- Helper for 13.26.13.7: the filtered-injective inclusion induces a localized equivalence for
the bounded-below filtered quasi-isomorphism localizer. -/
theorem filtered_injective_localizer_isLocalizedEquivalence :
    (LocalizerMorphism.ofEq (W₁ := WIFilt) (W₂ := W) rfl).IsLocalizedEquivalence := by
  let Φ : LocalizerMorphism WIFilt W := LocalizerMorphism.ofEq rfl
  let F : K⁺(𝓘^f(𝒜)) ⥤ DF⁺(𝒜) := filteredInjectiveHomotopyToFilteredDerived 𝒜
  letI : Functor.IsEquivalence F := by
    simpa [F] using filteredInjectiveHomotopyToFilteredDerived_isEquivalence (𝒜 := 𝒜)
  have hWIFilt :
      WIFilt ≤ MorphismProperty.isomorphisms (K⁺(𝓘^f(𝒜))) := by
    intro X Y f hf
    -- On the filtered-injective source, pulled-back filtered quasi-isomorphisms are already
    -- isomorphisms.
    exact filtered_injective_quasi_iso_is_iso (𝒜 := 𝒜) f hf
  letI : Functor.IsLocalization F WIFilt :=
    Functor.IsLocalization.of_isEquivalence F WIFilt hWIFilt
  -- Both localizations are represented by the same equivalence into `DF⁺(𝒜)`.
  simpa [Φ, F, IFiltIncl] using
    (LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization
      (Φ := Φ)
      (L₂ := QFiltA))

/-- Helper for 13.26.13.7: the filtered-injective inclusion carries the right derivability
structure needed to test right-derived comparison maps on filtered-injective models. -/
theorem filtered_injective_localizer_right_derivability :
    (LocalizerMorphism.ofEq (W₁ := WIFilt) (W₂ := W) rfl).IsRightDerivabilityStructure := by
  let Φ : LocalizerMorphism WIFilt W := LocalizerMorphism.ofEq rfl
  letI : Φ.IsLocalizedEquivalence := by
    simpa [Φ] using filtered_injective_localizer_isLocalizedEquivalence
  -- A localized equivalence is automatically a right derivability structure.
  simpa [Φ] using (LocalizerMorphism.IsRightDerivabilityStructure.mk' Φ)

/-- Helper for 13.26.13.7: on the filtered-injective source, the filtered derived source functor
already sends pulled-back filtered quasi-isomorphisms to isomorphisms. -/
theorem filtered_injective_localizer_derives_filtered_source :
    (LocalizerMorphism.ofEq (W₁ := WIFilt) (W₂ := W) rfl).Derives (Tplus ⋙ QFiltB) := by
  intro X Y f hf
  -- On filtered-injective complexes, every pulled-back filtered quasi-isomorphism is already an
  -- isomorphism before applying the source functor.
  haveI : IsIso f := filtered_injective_quasi_iso_is_iso (𝒜 := 𝒜) f hf
  change IsIso ((Tplus ⋙ QFiltB).map (IFiltIncl.map f))
  infer_instance

/-- Helper for 13.26.13.7: the same filtered-injective bridge also derives the graded source
functor. -/
theorem filtered_injective_localizer_derives_graded_source :
    (LocalizerMorphism.ofEq (W₁ := WIFilt) (W₂ := W) rfl).Derives GrSource := by
  intro X Y f hf
  -- The source morphism is already an isomorphism in `K⁺(𝓘^f(𝒜))`, so every functor sends it to
  -- an isomorphism.
  haveI : IsIso f := filtered_injective_quasi_iso_is_iso (𝒜 := 𝒜) f hf
  change IsIso (GrSource.map (IFiltIncl.map f))
  infer_instance

/-- Helper for 13.26.13.7: naturality for the bounded-below homotopy lift of a natural
transformation. -/
private theorem mapBoundedBelowHomotopyNatTrans_naturality
    {𝒞 : Type u} {𝒟 : Type u}
    [Category.{v} 𝒞] [Category.{v} 𝒟] [Abelian 𝒞] [Abelian 𝒟]
    [HasDerivedCategory 𝒟]
    {F G : 𝒞 ⥤ 𝒟} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (K L : K⁺(𝒞)) (φ : K ⟶ L) :
    ObjectProperty.homMk
        ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj) ≫
      φ =
        φ ≫
          ObjectProperty.homMk
            ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app L.obj) := by
  -- The bounded-below lift lives in a full subcategory, so naturality is inherited from the
  -- ambient homotopy-category naturality of `NatTrans.mapHomotopyCategory`.
  ext
  simpa using NatTrans.naturality (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)) φ.1

/-- Helper for 13.26.13.7: the bounded-below homotopy lift of a natural transformation. -/
private abbrev mapBoundedBelowHomotopyNatTrans
    {𝒞 : Type u} {𝒟 : Type u}
    [Category.{v} 𝒞] [Category.{v} 𝒟] [Abelian 𝒞] [Abelian 𝒟]
    [HasDerivedCategory 𝒟]
    {F G : 𝒞 ⥤ 𝒟} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    mapBoundedBelowHomotopyCategory F ⟶
      mapBoundedBelowHomotopyCategory G :=
  NatTrans.mk
    (fun K ↦ ObjectProperty.homMk
      ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj))
    (mapBoundedBelowHomotopyNatTrans_naturality τ)

/-- Helper for 13.26.13.7: the induced bounded-below homotopy-to-derived comparison from the
underived graded-piece map. -/
private abbrev mapBoundedBelowHomotopyToDerivedNatTrans
    {𝒞 : Type u} {𝒟 : Type u}
    [Category.{v} 𝒞] [Category.{v} 𝒟] [Abelian 𝒞] [Abelian 𝒟]
    [HasDerivedCategory 𝒟]
    {F G : 𝒞 ⥤ 𝒟} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
      mapBoundedBelowHomotopyCategoryToDerivedBelow G :=
  -- Whisker the bounded-below homotopy lift with the ordinary localization `Qplus`.
  Functor.whiskerRight
    (mapBoundedBelowHomotopyNatTrans τ)
    (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒟) ⥤ D⁺(𝒟))

/-- Helper for 13.26.13.7: after identifying the mapped filtration stages with the images of the
original stages under `T`, the mapped stage inclusion is just `T.map` of the original stage
inclusion. -/
private theorem mapped_stageInclusion_underlyingIso_comm
    (X : finiteFilteredObjectCat 𝒜) (p : ℤ) :
    let eSucc := Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj (p + 1)).arrow)
    let eCurr := Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj p).arrow)
    (((mapFiniteFilteredObjectCat T).obj X).obj.filtration.stageInclusion p) ≫ eCurr.hom =
      eSucc.hom ≫ T.obj.map (X.obj.filtration.stageInclusion p) := by
  -- Proof comment: both morphisms become the same after composing with the ambient monomorphism
  -- `T(F^p X) ⟶ T(X)`, so we compare them in the ambient object `T(X.obj)`.
  dsimp
  apply (cancel_mono (T.obj.map (X.obj.filtration.obj p).arrow)).1
  calc
    ((((mapFiniteFilteredObjectCat T).obj X).obj.filtration.stageInclusion p) ≫
        (Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj p).arrow)).hom) ≫
          T.obj.map (X.obj.filtration.obj p).arrow
      = (((mapFiniteFilteredObjectCat T).obj X).obj.filtration.stageInclusion p) ≫
          (((mapFiniteFilteredObjectCat T).obj X).obj.filtration.obj p).arrow := by
            rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
    _ = (((mapFiniteFilteredObjectCat T).obj X).obj.filtration.obj (p + 1)).arrow := by
          simp [DecreasingFiltration.stageInclusion, Category.assoc]
    _ = (Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj (p + 1)).arrow)).hom ≫
          T.obj.map ((X.obj.filtration.obj (p + 1)).arrow) := by
            rw [Subobject.underlyingIso_hom_comp_eq_mk]
    _ = (Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj (p + 1)).arrow)).hom ≫
          T.obj.map (X.obj.filtration.stageInclusion p ≫ (X.obj.filtration.obj p).arrow) := by
            rw [show (X.obj.filtration.obj (p + 1)).arrow =
                X.obj.filtration.stageInclusion p ≫ (X.obj.filtration.obj p).arrow by
                simp [DecreasingFiltration.stageInclusion]]
    _ = ((Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj (p + 1)).arrow)).hom ≫
          T.obj.map (X.obj.filtration.stageInclusion p)) ≫
            T.obj.map (X.obj.filtration.obj p).arrow := by
              rw [Functor.map_comp]
              simp [Category.assoc]

/-- Helper for 13.26.13.7: after identifying mapped stages with the images of the original
stages under `T`, the mapped stage map is just `T.map` of the original stage map. -/
private theorem mapped_stageMap_underlyingIso_comm
    {X Y : finiteFilteredObjectCat 𝒜} (f : X ⟶ Y) (q : ℤ) :
    let eX := Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj q).arrow)
    let eY := Subobject.underlyingIso (T.obj.map (Y.obj.filtration.obj q).arrow)
    FilteredObject.Hom.stageMap (((mapFiniteFilteredObjectCat T).map f).1) q ≫ eY.hom =
      eX.hom ≫ T.obj.map (FilteredObject.Hom.stageMap f.1 q) := by
  -- Proof comment: compare both maps after composing with the ambient monomorphism
  -- `T(F^q Y) ⟶ T(Y)`, then use the stage-map commutativity relation on the mapped and
  -- unmapped filtered morphisms.
  dsimp
  apply (cancel_mono (T.obj.map (Y.obj.filtration.obj q).arrow)).1
  calc
    (FilteredObject.Hom.stageMap (((mapFiniteFilteredObjectCat T).map f).1) q ≫
        (Subobject.underlyingIso (T.obj.map (Y.obj.filtration.obj q).arrow)).hom) ≫
          T.obj.map (Y.obj.filtration.obj q).arrow
      = FilteredObject.Hom.stageMap (((mapFiniteFilteredObjectCat T).map f).1) q ≫
          (((mapFiniteFilteredObjectCat T).obj Y).obj.filtration.obj q).arrow := by
            rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
    _ = (((mapFiniteFilteredObjectCat T).obj X).obj.filtration.obj q).arrow ≫
          ((mapFiniteFilteredObjectCat T).map f).1.hom := by
            rw [FilteredObject.Hom.stageMap_comm]
    _ = (((mapFiniteFilteredObjectCat T).obj X).obj.filtration.obj q).arrow ≫
          T.obj.map f.1.hom := by
            rfl
    _ = ((Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj q).arrow)).hom ≫
          T.obj.map (X.obj.filtration.obj q).arrow) ≫
            T.obj.map f.1.hom := by
              rw [Subobject.underlyingIso_hom_comp_eq_mk]
    _ = (Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj q).arrow)).hom ≫
          (T.obj.map (X.obj.filtration.obj q).arrow ≫ T.obj.map f.1.hom) := by
            simp [Category.assoc]
    _ = (Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj q).arrow)).hom ≫
          T.obj.map ((X.obj.filtration.obj q).arrow ≫ f.1.hom) := by
            rw [← Functor.map_comp]
    _ = (Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj q).arrow)).hom ≫
          T.obj.map (FilteredObject.Hom.stageMap f.1 q ≫ (Y.obj.filtration.obj q).arrow) := by
            rw [FilteredObject.Hom.stageMap_comm]
    _ = ((Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj q).arrow)).hom ≫
          T.obj.map (FilteredObject.Hom.stageMap f.1 q)) ≫
            T.obj.map (Y.obj.filtration.obj q).arrow := by
              rw [Functor.map_comp]
              simp [Category.assoc]

/-- Helper for 13.26.13.7: the objectwise source comparison
`gr^p(TX) ⟶ T(gr^p X)` built from the cokernel universal property. -/
private noncomputable def finite_filtered_graded_piece_comparison_app
    (X : finiteFilteredObjectCat 𝒜) :
    ((mapFiniteFilteredObjectCat T ⋙ GObjB).obj X) ⟶ ((GObjA ⋙ T.obj).obj X) := by
  let eCurr := Subobject.underlyingIso (T.obj.map (X.obj.filtration.obj p).arrow)
  -- Proof comment: the source graded piece is a cokernel, so the comparison is determined by the
  -- transported quotient map from `T(F^p X)` to `T(gr^p X)`.
  refine cokernel.desc (((mapFiniteFilteredObjectCat T).obj X).obj.filtration.stageInclusion p)
    (eCurr.hom ≫ T.obj.map (cokernel.π (X.obj.filtration.stageInclusion p))) ?_
  -- Proof comment: after transporting the mapped stage inclusion, the relation is exactly the
  -- image under `T` of the defining cokernel relation for `gr^p X`.
  rw [Category.assoc, mapped_stageInclusion_underlyingIso_comm (T := T) (X := X) (p := p)]
  simp [Functor.map_comp, Category.assoc]

/-- Helper for 13.26.13.7: the underived comparison on finite filtered objects from the graded
piece of the filtered image to the image of the graded piece. -/
private theorem finite_filtered_graded_piece_comparison_naturality
    {X Y : finiteFilteredObjectCat 𝒜} (f : X ⟶ Y) :
    ((mapFiniteFilteredObjectCat T ⋙ GObjB).map f) ≫
        finite_filtered_graded_piece_comparison_app
          (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) Y =
      finite_filtered_graded_piece_comparison_app
          (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) X ≫
        ((GObjA ⋙ T.obj).map f) := by
  -- Proof comment: compare after precomposing with the source cokernel projection. The left side
  -- becomes the mapped graded-piece map followed by the quotient comparison, while the right side
  -- is the image under `T` of the original graded-piece map. The transported stage-map lemma
  -- identifies these two descriptions.
  apply (cancel_epi
    (cokernel.π (((mapFiniteFilteredObjectCat T).obj X).obj.filtration.stageInclusion p))).1
  simp only [Category.assoc, finite_filtered_graded_piece_comparison_app, Functor.comp_map,
    cokernel.π_desc]
  simp [GObjA, GObjB, Category.assoc, Functor.map_comp,
    mapped_stageMap_underlyingIso_comm]

/-- Helper for 13.26.13.7: the underived comparison on finite filtered objects from the graded
piece of the filtered image to the image of the graded piece. -/
noncomputable def finite_filtered_graded_piece_comparison :
    mapFiniteFilteredObjectCat T ⋙ GObjB ⟶ GObjA ⋙ T.obj := by
  refine NatTrans.mk
    (fun X ↦ finite_filtered_graded_piece_comparison_app
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) X) ?_
  intro X Y f
  -- Proof comment: this is exactly the objectwise naturality theorem proved above.
  exact finite_filtered_graded_piece_comparison_naturality
    (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) f

/-- Helper for 13.26.13.7: the graded underived source comparison is the natural transformation
from the graded piece of the filtered image to the image of the graded piece. -/
noncomputable def graded_source_comparison :
    GrSource ⟶ KGrA ⋙ QMapT :=
  -- Route correction: first reassociate the source so the comparison is a lift of the underived
  -- finite-filtered map, then re-associate back to the chapter target `KGrA ⋙ QMapT`.
  (Functor.associator
      Tplus
      (mapBoundedBelowHomotopyCategory GObjB)
      (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ℬ) ⥤ D⁺(ℬ))).hom ≫
    mapBoundedBelowHomotopyToDerivedNatTrans
      (finite_filtered_graded_piece_comparison
        (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)) ≫
    (Functor.associator
      KGrA
      (mapBoundedBelowHomotopyCategory T.obj)
      (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ℬ) ⥤ D⁺(ℬ))).inv

/-- Helper for 13.26.13.7: the explicit comparison from the graded source to `RTFilt ⋙ gr^p`. -/
noncomputable abbrev αgrComparison :
    GrSource ⟶ QFiltA ⋙ RTGr :=
  -- Rewrite the source through the target-side graded-piece owner before whiskering the filtered
  -- total-right-derived unit.
  (eqToHom (graded_source_eq_filtered_then_gr (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)) :
      GrSource ⟶ (Tplus ⋙ QFiltB) ⋙ GrB) ≫
    (Functor.whiskerRight
      ((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W)
      GrB :
        ((Tplus ⋙ QFiltB) ⋙ GrB) ⟶ QFiltA ⋙ RTFilt ⋙ GrB) ≫
    (Functor.associator QFiltA RTFilt GrB).hom

/-- Helper for 13.26.13.7: on filtered-injective models, the comparison toward `RTFilt ⋙ gr^p`
is an isomorphism. -/
theorem alphagrComparison_app_isIso_on_filtered_injective
    (X : K⁺(𝓘^f(𝒜))) :
    IsIso (((αgrComparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)).app (IFiltIncl.obj X))) := by
  let hΦ := filtered_injective_localizer_derives_filtered_source
    (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  have hUnit :
      IsIso ((((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W).app (IFiltIncl.obj X))) := by
    -- The filtered-injective model already computes the filtered right derived functor source.
    exact hΦ.isIso (((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W)) X
  -- After rewriting the source equality, the comparison is the whiskered filtered derived unit
  -- followed by the associator.
  have hWhisker :
      IsIso
        (((Functor.whiskerRight
            ((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W)
            GrB).app (IFiltIncl.obj X))) := by
    change IsIso
      (GrB.map (((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W).app (IFiltIncl.obj X)))
    infer_instance
  simpa [αgrComparison, graded_source_eq_filtered_then_gr] using
    (show IsIso
      ((((Functor.whiskerRight
            ((Tplus ⋙ QFiltB).totalRightDerivedUnit QFiltA W)
            GrB).app (IFiltIncl.obj X)) ≫
          (Functor.associator QFiltA RTFilt GrB).hom.app (IFiltIncl.obj X)) from
      infer_instance)

/-- Helper for 13.26.13.7: the composite `gr^p ⋙ RT` is a right derived functor of the same
graded source after transporting through the graded comparison. -/
noncomputable abbrev βgrComparison :
    GrSource ⟶ QFiltA ⋙ GrRT :=
  -- Route correction: this leg uses the actual graded comparison natural transformation rather
  -- than a false equality between the two underived source functors.
  graded_source_comparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) ≫
    (Functor.whiskerLeft KGrA
      ((mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).totalRightDerivedUnit Qplus
        QisPlus) :
        (KGrA ⋙ QMapT) ⟶ KGrA ⋙ Qplus ⋙ RT) ≫
    (Functor.associator KGrA Qplus RT).hom ≫
    (Functor.whiskerRight ((eqToHom (graded_localization_bridge (𝒜 := 𝒜) (p := p)) :
        KGrA ⋙ Qplus ⟶ QFiltA ⋙ GrA)) RT :
        KGrA ⋙ Qplus ⋙ RT ⟶ QFiltA ⋙ GrA ⋙ RT) ≫
    (Functor.associator QFiltA GrA RT).hom

/-- Helper for 13.26.13.7: if the `(p + 1)`-st filtration stage is already the whole object,
then the `p`-th graded piece vanishes. -/
private theorem graded_piece_isZero_of_succ_eq_top_for_label
    (X : FilteredObject 𝒜) (p : ℤ) (h : X.filtration (p + 1) = ⊤) :
    IsZero (gr^{p} X) := by
  have hp : X.filtration p = ⊤ := filtration_eq_top_of_le (X := X) (by omega) h
  letI : IsIso (X.filtration.obj p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hp
  letI : IsIso (X.filtration.obj (p + 1)).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  have hstage :
      X.filtration.stageInclusion p =
        (X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow := by
    -- Proof comment: compare both candidates after composing with the ambient monomorphism of
    -- the `p`-th stage.
    apply (cancel_mono (X.filtration.obj p).arrow).1
    calc
      X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow =
          (X.filtration.obj (p + 1)).arrow := by
            exact Subobject.ofLE_arrow _
      _ =
          ((X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow) ≫
            (X.filtration.obj p).arrow := by
              simp
  rw [hstage]
  letI : Epi ((X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow) := by
    infer_instance
  -- Proof comment: once the stage inclusion is an isomorphism, the graded piece is the
  -- cokernel of an epimorphism and therefore vanishes.
  simpa [FilteredObject.gradedPiece, DecreasingFiltration.gradedPiece] using
    (Limits.isZero_cokernel_of_epi
      ((X.filtration.obj (p + 1)).arrow ≫ inv (X.filtration.obj p).arrow))

/-- Helper for 13.26.13.7: if the `p`-th filtration stage is already zero, then the `p`-th
graded piece vanishes. -/
private theorem graded_piece_isZero_of_eq_bot_for_label
    (X : FilteredObject 𝒜) (p : ℤ) (h : X.filtration p = ⊥) :
    IsZero (gr^{p} X) := by
  have hp1 : X.filtration (p + 1) = ⊥ := filtration_eq_bot_of_le (X := X) (by omega) h
  let hzeroSucc : IsZero (F^{p + 1} X) := stage_isZero_of_eq_bot X (p + 1) hp1
  let hzero : IsZero (F^{p} X) := stage_isZero_of_eq_bot X p h
  letI : IsIso (X.filtration.stageInclusion p) := hzeroSucc.isIso hzero _
  -- Proof comment: both adjacent stages are zero, so the stage inclusion is an isomorphism and
  -- its cokernel vanishes.
  simpa [FilteredObject.gradedPiece, DecreasingFiltration.gradedPiece] using
    (Limits.isZero_cokernel_of_epi (X.filtration.stageInclusion p))

/-- Helper for 13.26.13.7: inside the interval window, the `p`-th graded piece of the
interval-split object is canonically the distinguished `p`-summand. -/
private noncomputable def interval_split_graded_piece_iso_component
    (a b : ℤ) (J : Set.Icc a b → 𝒜) (hp : p ∈ Set.Icc a b) :
    gr^{p} ((intervalSplitFilteredObject a b J).obj) ≅ J ⟨p, hp⟩ := by
  let X : FilteredObject 𝒜 := (intervalSplitFilteredObject a b J).obj
  let jp : Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J :=
    ⟨⟨p, hp⟩, le_rfl⟩
  let πp : F^{p} X ⟶ J ⟨p, hp⟩ :=
    (X.filtration.obj p).arrow ≫ biproduct.π J ⟨p, hp⟩
  let ip : J ⟨p, hp⟩ ⟶ F^{p} X :=
    biproduct.ι (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) jp
  let rp : F^{p} X ⟶ F^{p + 1} X :=
    (X.filtration.obj p).arrow ≫
      biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1)
  have hipπ : ip ≫ πp = 𝟙 _ := by
    -- Proof comment: the distinguished summand survives in `F^p` and the `p`-projection picks
    -- it out exactly.
    simp [ip, πp, jp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, Category.assoc]
  have hipr : ip ≫ rp = 0 := by
    -- Proof comment: the distinguished `p`-summand does not lie in the `(p + 1)`-tail.
    have hpfalse : ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
      omega
    simp [ip, rp, jp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype,
      hpfalse, Category.assoc]
  have hstageπ : X.filtration.stageInclusion p ≫ πp = 0 := by
    -- Proof comment: the next filtration stage only sees summands with index at least `p + 1`,
    -- so the `p`-projection kills it.
    have hpfalse : ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
      omega
    calc
      X.filtration.stageInclusion p ≫ πp
          = X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow ≫
              biproduct.π J ⟨p, hp⟩ := by
                simp [πp, Category.assoc]
      _ = (X.filtration.obj (p + 1)).arrow ≫ biproduct.π J ⟨p, hp⟩ := by
            rw [Subobject.ofLE_arrow]
      _ = 0 := by
            simp [X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, hpfalse]
  have hstager : X.filtration.stageInclusion p ≫ rp = 𝟙 _ := by
    -- Proof comment: projecting the `p`-tail onto the `(p + 1)`-tail is the canonical
    -- retraction of the tail inclusion.
    apply (cancel_mono (X.filtration.obj (p + 1)).arrow).1
    calc
      X.filtration.stageInclusion p ≫ rp ≫ (X.filtration.obj (p + 1)).arrow
          = X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow ≫
              biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
                (X.filtration.obj (p + 1)).arrow := by
                  simp [rp, Category.assoc]
      _ = (X.filtration.obj (p + 1)).arrow ≫
            biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
              (X.filtration.obj (p + 1)).arrow := by
                rw [Subobject.ofLE_arrow]
      _ = (X.filtration.obj (p + 1)).arrow := by
            simp [X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, Category.assoc]
  have htotal : πp ≫ ip + rp ≫ X.filtration.stageInclusion p = 𝟙 _ := by
    -- Proof comment: every summand of the `p`-tail is either the distinguished `p`-summand or
    -- already lies in the `(p + 1)`-tail, so these two projectors add up to the identity.
    apply (cancel_mono (X.filtration.obj p).arrow).1
    ext j
    by_cases hj : j = jp
    · subst hj
      have hpfalse : ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
        omega
      simp [πp, ip, rp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype,
        hpfalse, Category.assoc]
    · have hjne : j.1.1 ≠ p := by
        intro hEq
        apply hj
        ext
        simp [jp, hEq]
      have hjgt : p + 1 ≤ j.1.1 := by
        omega
      simp [πp, ip, rp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype,
        hj, hjgt, Category.assoc]
  let eStage : F^{p} X ≅ J ⟨p, hp⟩ ⊞ F^{p + 1} X :=
    { hom := biprod.lift πp rp
      inv := biprod.desc ip (X.filtration.stageInclusion p)
      hom_inv_id := by
        -- Proof comment: the two complementary projectors on the `p`-tail sum to the identity.
        apply (cancel_mono (X.filtration.obj p).arrow).1
        calc
          (biprod.lift πp rp ≫ biprod.desc ip (X.filtration.stageInclusion p)) ≫
              (X.filtration.obj p).arrow
              =
                (πp ≫ ip + rp ≫ X.filtration.stageInclusion p) ≫
                  (X.filtration.obj p).arrow := by
                    simp [Preadditive.add_comp, Category.assoc]
          _ = (X.filtration.obj p).arrow := by
                rw [htotal]
                simp
      inv_hom_id := by
        -- Proof comment: the distinguished summand and the tail inclusion give the two standard
        -- injections into the binary biproduct decomposition.
        ext
        · simp [hipπ, hstageπ, Category.assoc]
        · simp [hipr, hstager, Category.assoc] }
  let s : CokernelCofork (X.filtration.stageInclusion p) :=
    CokernelCofork.ofπ πp hstageπ
  have hs : IsColimit s := by
    -- Proof comment: after identifying `F^p` with `J_p ⊞ F^(p + 1)`, the stage inclusion is the
    -- standard coprojection `biprod.inr`, whose cokernel is the first projection `biprod.fst`.
    refine IsCokernel.ofIso
      (biprod.inr : F^{p + 1} X ⟶ J ⟨p, hp⟩ ⊞ F^{p + 1} X)
      (biprod.isCokernelInrCokernelFork (J ⟨p, hp⟩) (F^{p + 1} X))
      s
      (Iso.refl _)
      eStage.symm
      (Iso.refl _)
      ?_
      ?_
    · simp [eStage, Category.assoc]
    · simp [s, eStage, πp, Category.assoc]
  -- Proof comment: both the canonical cokernel and the explicit descended `p`-projection are
  -- cokernels of the same stage inclusion, so their points are canonically isomorphic.
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (X.filtration.stageInclusion p))
    hs

/-- Helper for 13.26.13.7: inside the interval, the `p`-th filtration stage of the split model
decomposes as the distinguished `p`-summand together with the `(p + 1)`-tail. -/
private theorem interval_split_stage_decomposition
    (a b : ℤ) (J : Set.Icc a b → 𝒜) (hp : p ∈ Set.Icc a b) :
    ∃ eStage :
        F^{p} ((intervalSplitFilteredObject a b J).obj) ≅
          J ⟨p, hp⟩ ⊞ F^{p + 1} ((intervalSplitFilteredObject a b J).obj),
      ((intervalSplitFilteredObject a b J).obj.filtration.stageInclusion p) ≫ eStage.hom =
        biprod.inr ∧
      eStage.hom ≫ biprod.fst =
        (((intervalSplitFilteredObject a b J).obj).filtration.obj p).arrow ≫
          biproduct.π J ⟨p, hp⟩ := by
  let X : FilteredObject 𝒜 := (intervalSplitFilteredObject a b J).obj
  let jp : Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J :=
    ⟨⟨p, hp⟩, le_rfl⟩
  let πp : F^{p} X ⟶ J ⟨p, hp⟩ :=
    (X.filtration.obj p).arrow ≫ biproduct.π J ⟨p, hp⟩
  let ip : J ⟨p, hp⟩ ⟶ F^{p} X :=
    biproduct.ι (Subtype.restrict (fun i : Set.Icc a b ↦ p ≤ i.1) J) jp
  let rp : F^{p} X ⟶ F^{p + 1} X :=
    (X.filtration.obj p).arrow ≫
      biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1)
  have hipπ : ip ≫ πp = 𝟙 _ := by
    -- Proof comment: the distinguished summand survives in `F^p` and the `p`-projection picks
    -- it out exactly.
    simp [ip, πp, jp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, Category.assoc]
  have hstageπ : X.filtration.stageInclusion p ≫ πp = 0 := by
    -- Proof comment: the next filtration stage only sees summands with index at least `p + 1`,
    -- so the `p`-projection kills it.
    have hpfalse : ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
      omega
    calc
      X.filtration.stageInclusion p ≫ πp
          = X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow ≫
              biproduct.π J ⟨p, hp⟩ := by
                simp [πp, Category.assoc]
      _ = (X.filtration.obj (p + 1)).arrow ≫ biproduct.π J ⟨p, hp⟩ := by
            rw [Subobject.ofLE_arrow]
      _ = 0 := by
            simp [X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, hpfalse]
  have hstager : X.filtration.stageInclusion p ≫ rp = 𝟙 _ := by
    -- Proof comment: projecting the `p`-tail onto the `(p + 1)`-tail is the canonical
    -- retraction of the tail inclusion.
    apply (cancel_mono (X.filtration.obj (p + 1)).arrow).1
    calc
      X.filtration.stageInclusion p ≫ rp ≫ (X.filtration.obj (p + 1)).arrow
          = X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow ≫
              biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
                (X.filtration.obj (p + 1)).arrow := by
                  simp [rp, Category.assoc]
      _ = (X.filtration.obj (p + 1)).arrow ≫
            biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1) ≫
              (X.filtration.obj (p + 1)).arrow := by
                rw [Subobject.ofLE_arrow]
      _ = (X.filtration.obj (p + 1)).arrow := by
            simp [X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype, Category.assoc]
  have htotal : πp ≫ ip + rp ≫ X.filtration.stageInclusion p = 𝟙 _ := by
    -- Proof comment: every summand of the `p`-tail is either the distinguished `p`-summand or
    -- already lies in the `(p + 1)`-tail, so these two projectors add up to the identity.
    apply (cancel_mono (X.filtration.obj p).arrow).1
    ext j
    by_cases hj : j = jp
    · subst hj
      have hpfalse : ¬ p + 1 ≤ (⟨p, hp⟩ : Set.Icc a b).1 := by
        omega
      simp [πp, ip, rp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype,
        hpfalse, Category.assoc]
    · have hjne : j.1.1 ≠ p := by
        intro hEq
        apply hj
        ext
        simp [jp, hEq]
      have hjgt : p + 1 ≤ j.1.1 := by
        omega
      simp [πp, ip, rp, X, intervalSplitFilteredObject_stage_arrow_eq_fromSubtype,
        hj, hjgt, Category.assoc]
  let eStageHom : F^{p} X ⟶ J ⟨p, hp⟩ ⊞ F^{p + 1} X :=
    biprod.lift πp rp
  let eStageInv : J ⟨p, hp⟩ ⊞ F^{p + 1} X ⟶ F^{p} X :=
    biprod.desc ip (X.filtration.stageInclusion p)
  have hHomInv : eStageHom ≫ eStageInv = 𝟙 _ := by
    -- Proof comment: the two complementary projectors on the `p`-tail sum to the identity.
    apply (cancel_mono (X.filtration.obj p).arrow).1
    calc
      (eStageHom ≫ eStageInv) ≫ (X.filtration.obj p).arrow
          = (πp ≫ ip + rp ≫ X.filtration.stageInclusion p) ≫
              (X.filtration.obj p).arrow := by
                simp [eStageHom, eStageInv, Preadditive.add_comp, Category.assoc]
      _ = (X.filtration.obj p).arrow := by
            rw [htotal]
            simp
  have hInvHom : eStageInv ≫ eStageHom = 𝟙 _ := by
    -- Proof comment: the distinguished summand and the tail inclusion are the standard
    -- injections for this binary biproduct decomposition.
    ext
    · simp [eStageHom, eStageInv, hipπ, hstageπ, Category.assoc]
    · simp [eStageHom, eStageInv, hstager, Category.assoc]
  let eStage : F^{p} X ≅ J ⟨p, hp⟩ ⊞ F^{p + 1} X :=
    ⟨eStageHom, eStageInv, hHomInv, hInvHom⟩
  have hStageInr :
      X.filtration.stageInclusion p ≫ eStage.hom = biprod.inr := by
    -- Proof comment: after the splitting, the next stage embeds as the right summand.
    ext
    · simp [eStage, eStageHom, hstageπ, Category.assoc]
    · simp [eStage, eStageHom, hstager, Category.assoc]
  have hStageFst :
      eStage.hom ≫ biprod.fst = πp := by
    -- Proof comment: the left biproduct projection is exactly the distinguished `p`-summand
    -- quotient map.
    simp [eStage, eStageHom, Category.assoc]
  refine ⟨eStage, ?_, ?_⟩
  · simpa [X] using hStageInr
  · simpa [X, πp] using hStageFst

/-- Helper for 13.26.13.7: the interval-split comparison is reduced to the inside-interval
identity-on-the-`p`-summand computation. -/
private theorem finite_filtered_graded_piece_comparison_app_isIso_on_interval_component
    (a b : ℤ) (J : Set.Icc a b → 𝒜) (hp : p ∈ Set.Icc a b) :
    IsIso
      (finite_filtered_graded_piece_comparison_app
        (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
        (intervalSplitFilteredObject a b J)) := by
  let X := intervalSplitFilteredObject a b J
  let Xf : FilteredObject 𝒜 := X.obj
  let Yf : FilteredObject ℬ := ((mapFiniteFilteredObjectCat T).obj X).obj
  let Jp : 𝒜 := J ⟨p, hp⟩
  obtain ⟨eStage, hStageInr, hStageFst⟩ :=
    interval_split_stage_decomposition (𝒜 := 𝒜) (p := p) a b J hp
  let πp : F^{p} Xf ⟶ Jp := eStage.hom ≫ biprod.fst
  let ip : Jp ⟶ F^{p} Xf := biprod.inl ≫ eStage.inv
  let rp : F^{p} Xf ⟶ F^{p + 1} Xf := eStage.hom ≫ biprod.snd
  have hipπ : ip ≫ πp = 𝟙 _ := by
    -- Proof comment: after the stage splitting, the left summand is the distinguished
    -- `p`-component.
    simp [ip, πp, Category.assoc]
  have hipr : ip ≫ rp = 0 := by
    -- Proof comment: the distinguished `p`-summand does not contribute to the tail component.
    simp [ip, rp, Category.assoc]
  have hstageπ : Xf.filtration.stageInclusion p ≫ πp = 0 := by
    -- Proof comment: the stage inclusion lands entirely in the right biproduct summand.
    calc
      Xf.filtration.stageInclusion p ≫ πp
          = (Xf.filtration.stageInclusion p ≫ eStage.hom) ≫ biprod.fst := by
              simp [πp, Category.assoc]
      _ = biprod.inr ≫ biprod.fst := by rw [hStageInr]
      _ = 0 := by simp
  have hstager : Xf.filtration.stageInclusion p ≫ rp = 𝟙 _ := by
    -- Proof comment: under the same splitting, the next stage is exactly the right summand.
    calc
      Xf.filtration.stageInclusion p ≫ rp
          = (Xf.filtration.stageInclusion p ≫ eStage.hom) ≫ biprod.snd := by
              simp [rp, Category.assoc]
      _ = biprod.inr ≫ biprod.snd := by rw [hStageInr]
      _ = 𝟙 _ := by simp
  have hHomLift : eStage.hom = biprod.lift πp rp := by
    -- Proof comment: the splitting is uniquely determined by its two biproduct projections.
    ext
    · simp [πp, Category.assoc]
    · simp [rp, Category.assoc]
  have hInvDesc : eStage.inv = biprod.desc ip (Xf.filtration.stageInclusion p) := by
    -- Proof comment: the inverse splitting is uniquely determined by the two standard
    -- inclusions.
    ext
    · simp [ip, Category.assoc]
    · simpa [hStageInr, Category.assoc]
  have htotal : πp ≫ ip + rp ≫ Xf.filtration.stageInclusion p = 𝟙 _ := by
    -- Proof comment: the left projection-plus-right projection recovers the identity on the
    -- `p`-stage.
    calc
      πp ≫ ip + rp ≫ Xf.filtration.stageInclusion p
          = biprod.lift πp rp ≫ biprod.desc ip (Xf.filtration.stageInclusion p) := by
              simp [Category.assoc]
      _ = 𝟙 _ := by simpa [hHomLift, hInvDesc] using eStage.hom_inv_id
  let eCurr := Subobject.underlyingIso (T.obj.map (Xf.filtration.obj p).arrow)
  let eSucc := Subobject.underlyingIso (T.obj.map (Xf.filtration.obj (p + 1)).arrow)
  let πsrc : F^{p} Yf ⟶ T.obj.obj Jp := eCurr.hom ≫ T.obj.map πp
  let isrc : T.obj.obj Jp ⟶ F^{p} Yf := T.obj.map ip ≫ eCurr.inv
  let rsrc : F^{p} Yf ⟶ F^{p + 1} Yf := eCurr.hom ≫ T.obj.map rp ≫ eSucc.inv
  have hStageMapped :
      Yf.filtration.stageInclusion p =
        eSucc.hom ≫ T.obj.map (Xf.filtration.stageInclusion p) ≫ eCurr.inv := by
    -- Proof comment: after transporting the mapped stages back to `T(F^p X)` and
    -- `T(F^{p + 1} X)`, the mapped stage inclusion is just `T.map` of the original one.
    apply (cancel_mono eCurr.hom).1
    simpa [Yf, eCurr, eSucc, Category.assoc] using
      mapped_stageInclusion_underlyingIso_comm (T := T) (X := X) (p := p)
  have hisrcπ : isrc ≫ πsrc = 𝟙 _ := by
    -- Proof comment: the mapped left summand still projects isomorphically onto `T(J_p)`.
    simp [isrc, πsrc, hipπ, Functor.map_comp, Category.assoc]
  have hisrcr : isrc ≫ rsrc = 0 := by
    -- Proof comment: the mapped distinguished summand still misses the mapped tail.
    simp [isrc, rsrc, hipr, Functor.map_comp, Category.assoc]
  have hstageπsrc : Yf.filtration.stageInclusion p ≫ πsrc = 0 := by
    -- Proof comment: the mapped stage inclusion is `T.map` of the original stage inclusion, so
    -- the same cokernel relation holds after transport.
    calc
      Yf.filtration.stageInclusion p ≫ πsrc
          = eSucc.hom ≫ T.obj.map (Xf.filtration.stageInclusion p) ≫
              T.obj.map πp := by
                simp [πsrc, hStageMapped, Category.assoc]
      _ = eSucc.hom ≫ T.obj.map (Xf.filtration.stageInclusion p ≫ πp) := by
            rw [← Functor.map_comp]
            simp [Category.assoc]
      _ = 0 := by simp [hstageπ]
  have hstagersrc : Yf.filtration.stageInclusion p ≫ rsrc = 𝟙 _ := by
    -- Proof comment: after the same transport, the mapped next stage is again the right
    -- biproduct summand.
    calc
      Yf.filtration.stageInclusion p ≫ rsrc
          = eSucc.hom ≫ T.obj.map (Xf.filtration.stageInclusion p) ≫
              T.obj.map rp ≫ eSucc.inv := by
                simp [rsrc, hStageMapped, Category.assoc]
      _ = eSucc.hom ≫ T.obj.map (Xf.filtration.stageInclusion p ≫ rp) ≫ eSucc.inv := by
            rw [← Functor.map_comp]
            simp [Category.assoc]
      _ = 𝟙 _ := by simp [hstager]
  have htotalsrc : πsrc ≫ isrc + rsrc ≫ Yf.filtration.stageInclusion p = 𝟙 _ := by
    -- Proof comment: transporting the splitting through `T` and the underlying-stage isomorphisms
    -- preserves the complementary projector identity.
    calc
      πsrc ≫ isrc + rsrc ≫ Yf.filtration.stageInclusion p
          = eCurr.hom ≫ T.obj.map (πp ≫ ip + rp ≫ Xf.filtration.stageInclusion p) ≫
              eCurr.inv := by
                simp [πsrc, isrc, rsrc, hStageMapped, Functor.map_comp, Category.assoc,
                  Preadditive.comp_add, Preadditive.add_comp]
      _ = 𝟙 _ := by simp [htotal]
  let eStageSrcHom : F^{p} Yf ⟶ T.obj.obj Jp ⊞ F^{p + 1} Yf :=
    biprod.lift πsrc rsrc
  let eStageSrcInv : T.obj.obj Jp ⊞ F^{p + 1} Yf ⟶ F^{p} Yf :=
    biprod.desc isrc (Yf.filtration.stageInclusion p)
  have hStageSrcHomInv : eStageSrcHom ≫ eStageSrcInv = 𝟙 _ := by
    -- Proof comment: the mapped complementary projectors still add up to the identity.
    calc
      eStageSrcHom ≫ eStageSrcInv
          = πsrc ≫ isrc + rsrc ≫ Yf.filtration.stageInclusion p := by
              simp [eStageSrcHom, eStageSrcInv, Category.assoc]
      _ = 𝟙 _ := htotalsrc
  have hStageSrcInvHom : eStageSrcInv ≫ eStageSrcHom = 𝟙 _ := by
    -- Proof comment: the mapped distinguished summand and mapped tail give the standard
    -- injections into the binary biproduct decomposition.
    ext
    · simp [eStageSrcHom, eStageSrcInv, hisrcπ, hstageπsrc, Category.assoc]
    · simp [eStageSrcHom, eStageSrcInv, hstagersrc, Category.assoc]
  let eStageSrc : F^{p} Yf ≅ T.obj.obj Jp ⊞ F^{p + 1} Yf :=
    ⟨eStageSrcHom, eStageSrcInv, hStageSrcHomInv, hStageSrcInvHom⟩
  have hStageSrcInr :
      Yf.filtration.stageInclusion p ≫ eStageSrc.hom = biprod.inr := by
    -- Proof comment: under the mapped splitting, the next mapped stage is still the right
    -- biproduct summand.
    ext
    · simp [eStageSrc, eStageSrcHom, hstageπsrc, Category.assoc]
    · simp [eStageSrc, eStageSrcHom, hstagersrc, Category.assoc]
  have hStageSrcFst :
      eStageSrc.hom ≫ biprod.fst = πsrc := by
    -- Proof comment: the left mapped biproduct projection is exactly the source-side quotient
    -- map toward `T(J_p)`.
    simp [eStageSrc, eStageSrcHom, Category.assoc]
  let sTarget : CokernelCofork (Xf.filtration.stageInclusion p) :=
    CokernelCofork.ofπ πp hstageπ
  have hsTarget : IsColimit sTarget := by
    -- Proof comment: after the stage splitting, the target-side cokernel is the standard
    -- cokernel of `biprod.inr`.
    refine IsCokernel.ofIso
      (biprod.inr : F^{p + 1} Xf ⟶ Jp ⊞ F^{p + 1} Xf)
      (biprod.isCokernelInrCokernelFork Jp (F^{p + 1} Xf))
      sTarget
      (Iso.refl _)
      eStage.symm
      (Iso.refl _)
      ?_
      ?_
    · simpa [Category.assoc] using hStageInr
    · simpa [sTarget, hStageFst, πp, Category.assoc] using hStageFst
  let eTarget : gr^{p} Xf ≅ Jp :=
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (Xf.filtration.stageInclusion p))
      hsTarget
  have hTargetComp :
      cokernel.π (Xf.filtration.stageInclusion p) ≫ eTarget.hom = πp := by
    -- Proof comment: the canonical target graded-piece isomorphism is characterized by the
    -- explicit `p`-projection onto the distinguished summand.
    simpa [eTarget, sTarget, πp] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel (Xf.filtration.stageInclusion p))
        hsTarget
        WalkingParallelPair.one
  let sSource : CokernelCofork (Yf.filtration.stageInclusion p) :=
    CokernelCofork.ofπ πsrc hstageπsrc
  have hsSource : IsColimit sSource := by
    -- Proof comment: the mapped source-side cokernel is likewise the standard cokernel of the
    -- right biproduct injection after transporting along the stage isomorphisms.
    refine IsCokernel.ofIso
      (biprod.inr : F^{p + 1} Yf ⟶ T.obj.obj Jp ⊞ F^{p + 1} Yf)
      (biprod.isCokernelInrCokernelFork (T.obj.obj Jp) (F^{p + 1} Yf))
      sSource
      (Iso.refl _)
      eStageSrc.symm
      (Iso.refl _)
      ?_
      ?_
    · simpa [Category.assoc] using hStageSrcInr
    · simpa [sSource, hStageSrcFst, πsrc, Category.assoc] using hStageSrcFst
  let eSource : gr^{p} Yf ≅ T.obj.obj Jp :=
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (Yf.filtration.stageInclusion p))
      hsSource
  have hSourceComp :
      cokernel.π (Yf.filtration.stageInclusion p) ≫ eSource.hom = πsrc := by
    -- Proof comment: the source-side graded-piece isomorphism is characterized by the mapped
    -- `p`-projection after the transported splitting.
    simpa [eSource, sSource, πsrc] using
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsCokernel (Yf.filtration.stageInclusion p))
        hsSource
        WalkingParallelPair.one
  have hTargetMapComp :
      T.obj.map (cokernel.π (Xf.filtration.stageInclusion p)) ≫
          (Functor.mapIso T.obj eTarget).hom =
        T.obj.map πp := by
    -- Proof comment: applying `T` to the target-side cokernel characterization transports the
    -- same explicit projection formula to `ℬ`.
    simpa [Functor.map_comp] using congrArg (fun f ↦ T.obj.map f) hTargetComp
  have hCompare :
      finite_filtered_graded_piece_comparison_app
          (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) X ≫
        (Functor.mapIso T.obj eTarget).hom =
      eSource.hom := by
    -- Proof comment: after precomposing with the source cokernel projection, both morphisms are
    -- the same transported quotient map `πsrc`.
    apply (cancel_epi (cokernel.π (Yf.filtration.stageInclusion p))).1
    calc
      cokernel.π (Yf.filtration.stageInclusion p) ≫
          (finite_filtered_graded_piece_comparison_app
            (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) X ≫
              (Functor.mapIso T.obj eTarget).hom)
          =
        (eCurr.hom ≫ T.obj.map (cokernel.π (Xf.filtration.stageInclusion p))) ≫
          (Functor.mapIso T.obj eTarget).hom := by
            simp [finite_filtered_graded_piece_comparison_app, X, Xf, Yf, eCurr, Category.assoc]
      _ = eCurr.hom ≫ T.obj.map πp := by
            rw [Category.assoc, hTargetMapComp]
      _ = πsrc := by
            simp [πsrc]
      _ = cokernel.π (Yf.filtration.stageInclusion p) ≫ eSource.hom := by
            rw [hSourceComp]
  -- Proof comment: postcomposing the comparison with the target-side component isomorphism gives
  -- the source-side component isomorphism, so the comparison itself is an isomorphism.
  rw [isIso_comp_right_iff
    (finite_filtered_graded_piece_comparison_app
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) X)
    ((Functor.mapIso T.obj eTarget).hom)]
  rw [hCompare]
  infer_instance

/-- Helper for 13.26.13.7: the underived comparison is an isomorphism on the interval-split
control object. -/
private theorem finite_filtered_graded_piece_comparison_app_isIso_on_interval_split
    (a b : ℤ) (J : Set.Icc a b → 𝒜) :
    IsIso
      (finite_filtered_graded_piece_comparison_app
        (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
        (intervalSplitFilteredObject a b J)) := by
  by_cases hp : p ∈ Set.Icc a b
  · -- Proof comment: inside the interval, the remaining work is the explicit quotient
    -- computation identifying both graded pieces with the `p`-th summand.
    exact finite_filtered_graded_piece_comparison_app_isIso_on_interval_component
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) a b J hp
  · have hp' : p < a ∨ b < p := by
      -- Proof comment: being outside the interval means we are either strictly to the left or
      -- strictly to the right of the finite window.
      by_contra h
      push_neg at h
      exact hp ⟨h.1, h.2⟩
    rcases hp' with hpa | hbp
    · let X := intervalSplitFilteredObject a b J
      have htopTarget :
          X.obj.filtration (p + 1) = ⊤ := by
        -- Proof comment: to the left of the interval, the `(p + 1)`-tail already contains every
        -- summand of the interval biproduct.
        apply (Subobject.isIso_arrow_iff_eq_top _).1
        rw [intervalSplitFilteredObject_stage_arrow_eq_fromSubtype]
        let g := biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1)
        refine ⟨⟨g, biproduct.fromSubtype_toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1), ?_⟩⟩
        ext i
        have hi : p + 1 ≤ i.1 := by omega
        simp [g, hi]
      have hzeroTarget :
          IsZero (gr^{p} X.obj) :=
        graded_piece_isZero_of_succ_eq_top_for_label X.obj p htopTarget
      have htopSource :
          (((mapFiniteFilteredObjectCat T).obj X).obj).filtration (p + 1) = ⊤ := by
        -- Proof comment: the mapped `(p + 1)`-stage is represented by `T` applied to the same
        -- split mono, so it is still the top stage.
        apply (Subobject.isIso_arrow_iff_eq_top _).1
        change IsIso (T.obj.map (X.obj.filtration.obj (p + 1)).arrow)
        rw [intervalSplitFilteredObject_stage_arrow_eq_fromSubtype]
        let g := biproduct.toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1)
        let f := biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1)
        have hf : IsIso f := by
          refine ⟨⟨g, biproduct.fromSubtype_toSubtype J (fun i : Set.Icc a b ↦ p + 1 ≤ i.1), ?_⟩⟩
          ext i
          have hi : p + 1 ≤ i.1 := by omega
          simp [f, g, hi]
        infer_instance
      have hzeroSource :
          IsZero
            (gr^{p} (((mapFiniteFilteredObjectCat T).obj X).obj)) :=
        graded_piece_isZero_of_succ_eq_top_for_label
          (((mapFiniteFilteredObjectCat T).obj X).obj) p htopSource
      letI :
          IsZero ((mapFiniteFilteredObjectCat T ⋙ GObjB).obj X) := by
        simpa [GObjB] using hzeroSource
      letI :
          IsZero ((GObjA ⋙ T.obj).obj X) := by
        simpa [GObjA, Functor.comp_obj] using Functor.map_isZero T.obj
          (show IsZero (GObjA.obj X) by simpa [GObjA] using hzeroTarget)
      infer_instance
    · let X := intervalSplitFilteredObject a b J
      have hbotTarget :
          X.obj.filtration p = ⊥ := by
        -- Proof comment: to the right of the interval, no interval summand survives in the
        -- `p`-tail, so the stage is zero.
        apply (Subobject.mk_eq_bot_iff_zero).2
        rw [intervalSplitFilteredObject_stage_arrow_eq_fromSubtype]
        ext i
        have hi : ¬ p ≤ i.1 := by omega
        simp [hi]
      have hzeroTarget :
          IsZero (gr^{p} X.obj) :=
        graded_piece_isZero_of_eq_bot_for_label X.obj p hbotTarget
      have hbotSource :
          (((mapFiniteFilteredObjectCat T).obj X).obj).filtration p = ⊥ := by
        -- Proof comment: the mapped `p`-stage is represented by `T` applied to the zero tail
        -- inclusion, hence it is again the zero stage.
        apply (Subobject.mk_eq_bot_iff_zero).2
        change T.obj.map (X.obj.filtration.obj p).arrow = 0
        rw [intervalSplitFilteredObject_stage_arrow_eq_fromSubtype]
        ext i
        have hi : ¬ p ≤ i.1 := by omega
        simp [hi]
      have hzeroSource :
          IsZero
            (gr^{p} (((mapFiniteFilteredObjectCat T).obj X).obj)) :=
        graded_piece_isZero_of_eq_bot_for_label
          (((mapFiniteFilteredObjectCat T).obj X).obj) p hbotSource
      letI :
          IsZero ((mapFiniteFilteredObjectCat T ⋙ GObjB).obj X) := by
        simpa [GObjB] using hzeroSource
      letI :
          IsZero ((GObjA ⋙ T.obj).obj X) := by
        simpa [GObjA, Functor.comp_obj] using Functor.map_isZero T.obj
          (show IsZero (GObjA.obj X) by simpa [GObjA] using hzeroTarget)
      infer_instance

/-- Helper for 13.26.13.7: the underived comparison is an isomorphism on every filtered
injective finite filtered object. -/
private theorem finite_filtered_graded_piece_comparison_app_isIso_of_filtered_injective
    (I : 𝓘^f(𝒜)) :
    IsIso
      (finite_filtered_graded_piece_comparison_app
        (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) I.obj) := by
  obtain ⟨a, b, J, e, hJ⟩ :=
    (isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject (I := I.obj)).1 I.property
  let η := finite_filtered_graded_piece_comparison
    (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  have hSplit :
      IsIso
        (finite_filtered_graded_piece_comparison_app
          (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
          (intervalSplitFilteredObject a b J)) :=
    finite_filtered_graded_piece_comparison_app_isIso_on_interval_split
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) a b J
  have hNat := NatTrans.naturality η e.hom
  -- Proof comment: conjugate the interval-split comparison across the presentation isomorphism
  -- `e : I.obj ≅ intervalSplitFilteredObject a b J`.
  rw [isIso_comp_right_iff
    (η.app I.obj)
    (((GObjA ⋙ T.obj).map e.hom))] at hNat ⊢
  simpa using
    (show IsIso (((mapFiniteFilteredObjectCat T ⋙ GObjB).map e.hom) ≫
        η.app (intervalSplitFilteredObject a b J)) from inferInstance)

/-- Helper for 13.26.13.7: the objectwise filtered-injective comparison upgrades to a natural
isomorphism on the filtered-injective source. -/
private noncomputable def filtered_injective_finite_filtered_graded_piece_comparison_iso :
    filteredInjectiveInclusion 𝒜 ⋙ mapFiniteFilteredObjectCat T ⋙ GObjB ≅
      filteredInjectiveInclusion 𝒜 ⋙ GObjA ⋙ T.obj := by
  refine NatIso.ofComponents
    (fun I ↦ asIso
      (finite_filtered_graded_piece_comparison_app
        (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) I.obj)) ?_
  intro I J f
  -- Proof comment: the naturality square is the same one already proved for the ambient
  -- comparison, specialized along the filtered-injective inclusion.
  simpa using
    (finite_filtered_graded_piece_comparison_naturality
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) f.1)

/-- Helper for 13.26.13.7: the graded source comparison is an isomorphism on bounded-below
filtered-injective complexes. -/
private theorem graded_source_comparison_app_isIso_on_filtered_injective
    (X : K⁺(𝓘^f(𝒜))) :
    IsIso
      (((graded_source_comparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)).app
        (IFiltIncl.obj X))) := by
  let τ :=
    filtered_injective_finite_filtered_graded_piece_comparison_iso
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  have hMid :
      IsIso
        (((mapBoundedBelowHomotopyToDerivedNatTrans τ.hom).app X)) := by
    -- Proof comment: the bounded-below homotopy lift sends the filtered-injective objectwise
    -- natural isomorphism to an isomorphism on each filtered-injective complex.
    infer_instance
  -- Proof comment: `graded_source_comparison` is exactly this lifted comparison, up to the two
  -- canonical associator isomorphisms.
  simpa [graded_source_comparison, IFiltIncl, τ, Functor.comp_obj] using
    (show IsIso
      (((Functor.associator
            IFiltIncl
            (mapBoundedBelowHomotopyCategory (mapFiniteFilteredObjectCat T ⋙ GObjB))
            (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ℬ) ⥤ D⁺(ℬ))).hom.app X) ≫
        ((mapBoundedBelowHomotopyToDerivedNatTrans τ.hom).app X) ≫
        ((Functor.associator
            (mapBoundedBelowHomotopyCategory
              (filteredInjectiveInclusion 𝒜 ⋙ GObjA))
            (mapBoundedBelowHomotopyCategory T.obj)
            (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ℬ) ⥤ D⁺(ℬ))).inv.app X)) from
      inferInstance)

theorem betagrComparison_app_isIso_on_filtered_injective
    (X : K⁺(𝓘^f(𝒜))) :
    IsIso (((βgrComparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)).app (IFiltIncl.obj X))) := by
  let J : K⁺ᵢ(𝒜) := (filteredInjectiveGradedPieceHomotopyFunctor 𝒜 p).obj X
  have hsource :
      IsIso
        (((graded_source_comparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)).app
          (IFiltIncl.obj X))) :=
    graded_source_comparison_app_isIso_on_filtered_injective
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) X
  have hcomp :
      QMapT.ComputesRightDerivedAt QisPlus (KinjIncl.obj J) := by
    -- Proof comment: the graded-piece complex of a bounded-below filtered-injective complex is a
    -- bounded-below injective complex, so it computes the ordinary right derived functor of `T`.
    simpa [J, KinjIncl] using
      (boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := QMapT) (I := boundedBelowInjectiveHomotopyCat.toInjectivePlus J))
  have hunit :
      IsIso
        (((mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).totalRightDerivedUnit
          Qplus QisPlus).app (KinjIncl.obj J)) := by
    -- Proof comment: convert the computation statement to the canonical total-right-derived unit
    -- criterion.
    exact (Functor.computesRightDerivedAt_iff
      (F := QMapT) (S := QisPlus) (X := KinjIncl.obj J)).1 hcomp
  have htail :
      IsIso
        ((((Functor.whiskerLeft KGrA
              ((mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).totalRightDerivedUnit
                Qplus QisPlus)).app (IFiltIncl.obj X)) ≫
            (Functor.associator KGrA Qplus RT).hom.app (IFiltIncl.obj X)) ≫
          ((Functor.whiskerRight
              ((eqToHom (graded_localization_bridge (𝒜 := 𝒜) (p := p)) :
                KGrA ⋙ Qplus ⟶ QFiltA ⋙ GrA)) RT).app (IFiltIncl.obj X)) ≫
          (Functor.associator QFiltA GrA RT).hom.app (IFiltIncl.obj X)) := by
    -- Proof comment: on a filtered-injective model, the tail of `βgrComparison` is exactly the
    -- ordinary bounded-below unit component at the graded-piece injective complex `J`.
    simpa [graded_localization_bridge (𝒜 := 𝒜) (p := p),
      filteredInjectiveHomotopyToFilteredDerived_gr_comm (𝒜 := 𝒜) p,
      IFiltIncl, KinjIncl, J, Functor.comp_obj] using hunit
  -- Proof comment: after isolating the graded-source comparison from the ordinary injective unit,
  -- both factors are isomorphisms on filtered-injective test objects.
  simpa [βgrComparison] using
    (show IsIso
      ((((graded_source_comparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)).app
            (IFiltIncl.obj X)) ≫
          ((((Functor.whiskerLeft KGrA
                ((mapBoundedBelowHomotopyCategoryToDerivedBelow T.obj).totalRightDerivedUnit
                  Qplus QisPlus)).app (IFiltIncl.obj X)) ≫
              (Functor.associator KGrA Qplus RT).hom.app (IFiltIncl.obj X)) ≫
            ((Functor.whiskerRight
                ((eqToHom (graded_localization_bridge (𝒜 := 𝒜) (p := p)) :
                  KGrA ⋙ Qplus ⟶ QFiltA ⋙ GrA)) RT).app (IFiltIncl.obj X)) ≫
            (Functor.associator QFiltA GrA RT).hom.app (IFiltIncl.obj X))) from
      inferInstance)

/-- Helper for 13.26.13.7: the composite `RTFilt ⋙ gr^p` is a right derived functor of the
graded source `GrSource`. -/
theorem rtgr_is_rightDerived :
    Functor.IsRightDerivedFunctor RTGr
      (αgrComparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)) W := by
  let _ := filtered_injective_localizer_right_derivability (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  let hΦ := filtered_injective_localizer_derives_graded_source
    (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  -- Route correction: the filtered-injective localizer reduces the right-derived witness to the
  -- explicit comparison on filtered-injective models, where the whiskered filtered unit is an
  -- isomorphism.
  exact hΦ.isRightDerivedFunctor_of_isIso
    (αgrComparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p))
    (fun X ↦ alphagrComparison_app_isIso_on_filtered_injective
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) X)

/-- Helper for 13.26.13.7: the composite `gr^p ⋙ RT` is a right derived functor of the same
graded source after transporting through the graded comparison. -/
theorem grrt_is_rightDerived :
    Functor.IsRightDerivedFunctor GrRT
      (βgrComparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)) W := by
  let _ := filtered_injective_localizer_right_derivability (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  let hΦ := filtered_injective_localizer_derives_graded_source
    (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  -- Route correction: after making `graded_source_comparison` explicit, the filtered-injective
  -- criterion reduces this right-derived witness to the concrete comparison isomorphism on
  -- filtered-injective test objects.
  exact hΦ.isRightDerivedFunctor_of_isIso
    (βgrComparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p))
    (fun X ↦ betagrComparison_app_isIso_on_filtered_injective
      (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p) X)

/- Canonical owner recall: the graded-piece comparison in `13.26.13.7` is the specialized
uniqueness isomorphism for right derived functors. -/
recall Functor.rightDerivedUnique

/- 13.26.13.7: taking the `p`-th graded piece commutes with the filtered right derived functor
via the canonical comparison isomorphism between the two Chapter `13` right derived functors of
the same source functor on `K⁺(Fil^f(𝒜))`. -/
/- Implementation lemma for 13.26.13.7: the graded-piece comparison is the chapter specialization
of `Functor.rightDerivedUnique`. The public entry is the `def`
`graded_filtered_rightDerived_iso`, with the right-derived assumptions carried only by the ambient
instance context. -/
private theorem graded_filtered_rightDerived_iso_aux :
    RTGr ≅ GrRT := by
  let αgr : GrSource ⟶ QFiltA ⋙ RTGr := αgrComparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  let βgr : GrSource ⟶ QFiltA ⋙ GrRT := βgrComparison (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  letI : Functor.IsRightDerivedFunctor RTGr αgr W := by
    -- The `RTGr` leg is now reduced to the explicit comparison `αgr`.
    simpa [αgr] using rtgr_is_rightDerived (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  letI : Functor.IsRightDerivedFunctor GrRT βgr W := by
    -- The `GrRT` leg is now reduced to the filtered-injective test encoded in `βgr`.
    simpa [βgr] using grrt_is_rightDerived (𝒜 := 𝒜) (ℬ := ℬ) (T := T) (p := p)
  exact (RTGr).rightDerivedUnique GrRT αgr βgr W

/-- 13.26.13.7: taking the `p`-th graded piece commutes with the filtered right derived functor
via the canonical uniqueness isomorphism between the two Chapter `13` right derived functors of
the same source functor. -/
noncomputable def graded_filtered_rightDerived_iso :
    RTGr ≅ GrRT :=
  graded_filtered_rightDerived_iso_aux

end

end

end CategoryTheory

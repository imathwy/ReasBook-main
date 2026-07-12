import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap13.Lemma_13_11_6
import StacksProject_2024.Chap13.Lemma_13_14_16
import StacksProject_2024.Chap13.Lemma_13_14_15
import StacksProject_2024.Chap13.Lemma_13_15_2
import StacksProject_2024.Chap13.Lemma_13_20_2
import StacksProject_2024.Chap17.Lemma_17_20_2
import StacksProject_2024.Chap20.«20_3_0_4»
import StacksProject_2024.Chap20.Global_sections_module_owners_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open RingedSpace.Hom
open CategoryTheory.ObjectProperty
open TopologicalSpace
open DerivedCategory.TStructure
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- Naturality for the bounded-below homotopy-category lift of a natural transformation. -/
private theorem mapBoundedBelowHomotopyNatTrans_naturality
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (K L : K⁺(𝒜)) (φ : K ⟶ L) :
    (mapBoundedBelowHomotopyCategory F).map φ ≫
        ObjectProperty.homMk
          ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app L.obj) =
      ObjectProperty.homMk
          ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj) ≫
        (mapBoundedBelowHomotopyCategory G).map φ := by
  ext
  simpa using ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).naturality φ.hom)

/-- The bounded-below homotopy-category lift of a natural transformation. -/
private noncomputable def mapBoundedBelowHomotopyNatTrans
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    CategoryTheory.mapBoundedBelowHomotopyCategory F ⟶
      CategoryTheory.mapBoundedBelowHomotopyCategory G :=
  NatTrans.mk
    (fun K ↦
      ObjectProperty.homMk ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj))
    (mapBoundedBelowHomotopyNatTrans_naturality τ)

/-- The induced natural transformation on bounded-below homotopy-to-derived functors. -/
private noncomputable def mapBoundedBelowHomotopyToDerivedNatTrans
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    {F G : 𝒜 ⥤ ℬ} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
      CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow G :=
  Functor.whiskerRight
    (mapBoundedBelowHomotopyNatTrans τ)
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow : K⁺(ℬ) ⥤ D⁺(ℬ))

/-- Helper for Lemma 20.17.1: the bounded-below homotopy lift of a composite is natural in the
source complex. -/
private theorem mapBoundedBelowHomotopyCategoryCompHom_naturality
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K L : K⁺(A)) (φ : K ⟶ L) :
    (CategoryTheory.mapBoundedBelowHomotopyCategory (F ⋙ G)).map φ ≫
      ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).hom.app L.obj) =
        ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).hom.app K.obj) ≫
          (CategoryTheory.mapBoundedBelowHomotopyCategory F ⋙
            CategoryTheory.mapBoundedBelowHomotopyCategory G).map φ := by
  ext
  simpa using (Functor.mapHomotopyCategoryCompIso F G).hom.naturality φ.hom

/-- Helper for Lemma 20.17.1: the bounded-below homotopy lift of a composite functor. -/
private noncomputable def mapBoundedBelowHomotopyCategoryCompHom
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    CategoryTheory.mapBoundedBelowHomotopyCategory (F ⋙ G) ⟶
      CategoryTheory.mapBoundedBelowHomotopyCategory F ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategory G :=
  NatTrans.mk
    (fun K ↦ ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).hom.app K.obj))
    (mapBoundedBelowHomotopyCategoryCompHom_naturality F G)

/-- Helper for Lemma 20.17.1: the inverse bounded-below homotopy lift of a composite is natural
in the source complex. -/
private theorem mapBoundedBelowHomotopyCategoryCompInv_naturality
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K L : K⁺(A)) (φ : K ⟶ L) :
    (CategoryTheory.mapBoundedBelowHomotopyCategory F ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategory G).map φ ≫
      ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).inv.app L.obj) =
        ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).inv.app K.obj) ≫
          (CategoryTheory.mapBoundedBelowHomotopyCategory (F ⋙ G)).map φ := by
  ext
  simpa using (Functor.mapHomotopyCategoryCompIso F G).inv.naturality φ.hom

/-- Helper for Lemma 20.17.1: the inverse bounded-below homotopy lift of a composite functor. -/
private noncomputable def mapBoundedBelowHomotopyCategoryCompInv
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    CategoryTheory.mapBoundedBelowHomotopyCategory F ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategory G ⟶
      CategoryTheory.mapBoundedBelowHomotopyCategory (F ⋙ G) :=
  NatTrans.mk
    (fun K ↦ ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso F G).inv.app K.obj))
    (mapBoundedBelowHomotopyCategoryCompInv_naturality F G)

/-- Helper for Lemma 20.17.1: the bounded-below homotopy lift of a composite has the expected
inverse. -/
private theorem mapBoundedBelowHomotopyCategoryComp_hom_inv_id
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapBoundedBelowHomotopyCategoryCompHom F G ≫
      mapBoundedBelowHomotopyCategoryCompInv F G =
        𝟙 (CategoryTheory.mapBoundedBelowHomotopyCategory (F ⋙ G)) := by
  ext K
  simpa using (Functor.mapHomotopyCategoryCompIso F G).hom_inv_id_app K.obj

/-- Helper for Lemma 20.17.1: the inverse bounded-below homotopy lift of a composite has the
expected inverse. -/
private theorem mapBoundedBelowHomotopyCategoryComp_inv_hom_id
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    mapBoundedBelowHomotopyCategoryCompInv F G ≫
      mapBoundedBelowHomotopyCategoryCompHom F G =
        𝟙 (CategoryTheory.mapBoundedBelowHomotopyCategory F ⋙
          CategoryTheory.mapBoundedBelowHomotopyCategory G) := by
  ext K
  simpa using (Functor.mapHomotopyCategoryCompIso F G).inv_hom_id_app K.obj

/-- Helper for Lemma 20.17.1: applying the bounded-below homotopy lift to a composite is
canonically isomorphic to composing the two bounded-below lifts. -/
private noncomputable def mapBoundedBelowHomotopyCategoryCompIso
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    CategoryTheory.mapBoundedBelowHomotopyCategory (F ⋙ G) ≅
      CategoryTheory.mapBoundedBelowHomotopyCategory F ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategory G where
  hom := mapBoundedBelowHomotopyCategoryCompHom F G
  inv := mapBoundedBelowHomotopyCategoryCompInv F G
  hom_inv_id := mapBoundedBelowHomotopyCategoryComp_hom_inv_id F G
  inv_hom_id := mapBoundedBelowHomotopyCategoryComp_inv_hom_id F G

/-- Helper for Lemma 20.17.1: the bounded-below homotopy-to-derived functor of a composite is
canonically isomorphic to the iterated bounded-below functor. -/
private noncomputable abbrev mapBoundedBelowHomotopyCategoryToDerivedBelowCompIso
    {A B C : Type u} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow (F ⋙ G) ≅
      CategoryTheory.mapBoundedBelowHomotopyCategory F ⋙
        CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow G :=
  Functor.isoWhiskerRight
    (mapBoundedBelowHomotopyCategoryCompIso F G)
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow : K⁺(C) ⥤ D⁺(C)) ≪≫
    Functor.associator
      (CategoryTheory.mapBoundedBelowHomotopyCategory F)
      (CategoryTheory.mapBoundedBelowHomotopyCategory G)
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow : K⁺(C) ⥤ D⁺(C))

/-- Helper for Lemma 20.17.1: after forgetting the bounded-below restriction, the image of a
morphism under `mapBoundedBelowHomotopyCategory F` is the ordinary homotopy-category image of the
ambient morphism. -/
private theorem mapBoundedBelowHomotopyCategory_map_eq
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive]
    {X Y : K⁺(𝒜)} (s : X ⟶ Y) :
    ((HomotopyCategory.plus ℬ).ι.map ((mapBoundedBelowHomotopyCategory F).map s)) =
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map ((HomotopyCategory.plus 𝒜).ι.map s)) := by
  -- Proof comment: the bounded-below functor is obtained by restricting the ambient homotopy
  -- functor to the bounded-below full subcategory.
  simp [mapBoundedBelowHomotopyCategory]

/-- Helper for Lemma 20.17.1: exact additive functors send bounded-below quasi-isomorphisms to
bounded-below quasi-isomorphisms. -/
private theorem exactFunctor_maps_boundedBelowQuasiIso
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    {X Y : K⁺(𝒜)} (s : X ⟶ Y) (hs : Qis⁺(𝒜) s) :
    Qis⁺(ℬ) ((mapBoundedBelowHomotopyCategory F).map s) := by
  have hsAmbient :
      HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ) ((HomotopyCategory.plus 𝒜).ι.map s) := hs
  have hsOut : QuasiIso (((HomotopyCategory.plus 𝒜).ι.map s).out) := by
    exact
      (HomotopyCategory.quotient_map_mem_quasiIso_iff
        (C := 𝒜)
        (c := ComplexShape.up ℤ)
        (f := ((HomotopyCategory.plus 𝒜).ι.map s).out)).1
        (by simpa [HomotopyCategory.quotient_map_out] using hsAmbient)
  let _ : F.PreservesHomology := by
    infer_instance
  let _ : QuasiIso (((HomotopyCategory.plus 𝒜).ι.map s).out) := hsOut
  have hMapped :
      QuasiIso
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((HomotopyCategory.plus 𝒜).ι.map s).out))) := by
    infer_instance
  change
    HomotopyCategory.quasiIso ℬ (ComplexShape.up ℤ)
      ((HomotopyCategory.plus ℬ).ι.map ((mapBoundedBelowHomotopyCategory F).map s))
  rw [mapBoundedBelowHomotopyCategory_map_eq (F := F) s]
  rw [← HomotopyCategory.quotient_map_out
    (((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.plus 𝒜).ι.map s))),
    HomotopyCategory.quotient_map_mem_quasiIso_iff]
  simpa using hMapped

section BaseChange

/- Domain-style sampling for Lemma 20.17.1:
- primary domain: bounded-below derived base change for module sheaves on ringed spaces in a
  commutative square;
- sampled owner declarations:
  `Functor.totalRightDerived`,
  `Functor.rightDerivedNatTrans`,
  `Functor.rightDerivedCompComparison`,
  `RingedSpace.Hom.IsFlat.pullback_exact`;
- best owner abstraction:
  `source-facing`: the bounded-below flat base-change morphism
    `g^* Rf_* ℱ ⟶ Rf'_* (g')^* ℱ`;
  `core/canonical`: the bounded-below specialization of `Functor.totalRightDerived` for module
    pushforward, together with the Chapter 13 owners `Functor.rightDerivedNatTrans` and
    `Functor.rightDerivedCompComparison`;
  `bridge/view`: the underived base-change natural transformation and the two comparison maps
    `R(g^* ∘ f_*) ⟶ g^* ∘ Rf_*` and `R(f'_* ∘ (g')^*) ⟶ Rf'_* ∘ R(g')^*`.

Primitive-vs-derived split:
- primitive data: the underived pullback and pushforward functors on module sheaves and the
  commutative-square witness `sq : CommSq g' f' f g`;
- derived API: the source and target composite objects `g^* Rf_* ℱ` and `Rf'_* (g')^* ℱ`, the
  derived lift of the underived base-change transformation on composite owners, and the
  comparison isomorphisms supplied by flatness.

This refinement uses the canonical bounded-below pushforward owner from Chapter `13`,
namely the direct `Functor.totalRightDerived` specialization for `f _*`, and the canonical
bounded-below pullback and pushforward owners from Chapter `13`. The source-facing theorem is
kept on those bounded-below owners directly, rather than exporting a second public bridge from the
unbounded Chapter `20` pullback owner back to `D⁺`. This keeps the item faithful to Lemma
`20.17.1` while avoiding new public data built from private bounded-below bridge proofs. -/

variable {X X' S S' : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModXPrime" => RingedSpace.Modules X'
local notation "ModS" => RingedSpace.Modules S
local notation "ModSPrime" => RingedSpace.Modules S'
local notation "DModX" => D⁺(ModX)
local notation "DModXPrime" => D⁺(ModXPrime)
local notation "DModS" => D⁺(ModS)
local notation "DModSPrime" => D⁺(ModSPrime)
local notation "QisX" => Qis⁺(ModX)
local notation "QisXPrime" => Qis⁺(ModXPrime)
local notation "QisS" => Qis⁺(ModS)
local notation "QisSPrime" => Qis⁺(ModSPrime)
local notation "QX" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModX) ⥤ DModX)
local notation "QXPrime" =>
  (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModXPrime) ⥤ DModXPrime)
local notation "QS" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModS) ⥤ DModS)
local notation "QSPrime" =>
  (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModSPrime) ⥤ DModSPrime)

attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

local instance : EnoughInjectives ModX :=
  by
    let _ : IsGrothendieckAbelian.{u} ModX := sheafModules_isGrothendieckAbelian X
    infer_instance

local instance : EnoughInjectives ModXPrime :=
  by
    let _ : IsGrothendieckAbelian.{u} ModXPrime := sheafModules_isGrothendieckAbelian X'
    infer_instance

local instance : EnoughInjectives ModS :=
  by
    let _ : IsGrothendieckAbelian.{u} ModS := sheafModules_isGrothendieckAbelian S
    infer_instance

local instance : EnoughInjectives ModSPrime :=
  by
    let _ : IsGrothendieckAbelian.{u} ModSPrime := sheafModules_isGrothendieckAbelian S'
    infer_instance

/-- The source object `Lg^* Rf_* ℱ` for bounded-below derived base change. -/
noncomputable abbrev boundedBelowDerivedBaseChangeSource
    (f : X ⟶ S) (g : S' ⟶ S) (ℱ : DModX) :
    DModSPrime :=
  (Functor.totalRightDerived
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
      QS
      QisS).obj (Rf_[f] ℱ)

/-- The target object `R(f')_* L(g')^* ℱ` for bounded-below derived base change. -/
noncomputable abbrev boundedBelowDerivedBaseChangeTarget
    (g' : X' ⟶ X) (f' : X' ⟶ S') (ℱ : DModX) :
    DModSPrime :=
  Rf_[f'] ((Functor.totalRightDerived
      (mapBoundedBelowHomotopyCategory (g'^*) ⋙ QXPrime)
      QX
      QisX).obj ℱ)

/-- The source-facing target alias `R(f')_* (g')^* ℱ` for bounded-below base change.

Formally this is the canonical bounded-below derived target
`R(f')_* L(g')^* ℱ`. In flat situations, Lemma `13.16.9` computes the derived pullback by the
underived pullback, so downstream flat base-change statements can use this shorter source-facing
name instead of the longer derived target owner. -/
noncomputable abbrev boundedBelowFlatBaseChangeTarget
    (g' : X' ⟶ X) (f' : X' ⟶ S') (ℱ : DModX) :
    DModSPrime :=
  boundedBelowDerivedBaseChangeTarget g' f' ℱ

section

variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)

local notation "Rf" =>
  modulePushforwardDerivedPlus f

local notation "Rf'" =>
  modulePushforwardDerivedPlus f'

local notation "Lg" =>
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
    QS
    QisS

local notation "Lg'" =>
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategory (g'^*) ⋙ QXPrime)
    QX
    QisX

local notation "Rgf" =>
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategory (f _*) ⋙
      mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
    QX
    QisX

local notation "Rf'g'" =>
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategory (g'^*) ⋙
      mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))
    QX
    QisX

local notation "sourceComparison" =>
  Functor.rightDerivedCompComparison
    QisX
    QisS
    (mapBoundedBelowHomotopyCategory (f _*))
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))

local notation "targetComparison" =>
  Functor.rightDerivedCompComparison
    QisX
    QisXPrime
    (mapBoundedBelowHomotopyCategory (g'^*))
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))

-- These eight existence instances are the direct Chapter 13 owner instances for additive
-- pushforward, pullback, their underived composites, and the two mixed comparison owners on
-- bounded-below module complexes.
local instance :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f _*))
      QisX :=
  inferInstance

local instance :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))
      QisXPrime :=
  inferInstance

local instance :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
      QisS :=
  inferInstance

local instance :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (g'^*))
      QisX :=
  inferInstance

/-- Helper for Lemma 20.17.1: a bounded-below homotopy object with injective terms defines a
bounded-below injective complex. -/
private abbrev boundedBelowInjectiveHomotopyToInjectivePlus
    (K : K⁺(ModX))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n)) :
    CochainComplex.InjectivePlus ModX :=
  ⟨⟨K.obj.as, K.property⟩, hK⟩

/-- The bounded-below right derived functor of `f_*` followed by the canonical bounded-below
derived-category localization functor exists. -/
local instance modulePushforward_then_localization_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        QS)
      QisX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor
        (mapBoundedBelowHomotopyCategory (f _*) ⋙
          QS)
        QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        QS)
  infer_instance

/-- The bounded-below pushforward followed by localization is pointwise right derived when the
source category has enough injectives. -/
local instance modulePushforward_then_localization_hasPointwiseRightDerivedFunctor :
    Functor.HasPointwiseRightDerivedFunctor
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        QS)
      QisX :=
  CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
    (mapBoundedBelowHomotopyCategory (f _*) ⋙
      QS)

/-- The bounded-below right derived functor of `(g')^*` followed by the canonical bounded-below
derived-category localization functor exists. -/
local instance modulePullback_then_localization_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategory (g'^*) ⋙
        QXPrime)
      QisX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor
        (mapBoundedBelowHomotopyCategory (g'^*) ⋙
          QXPrime)
        QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (mapBoundedBelowHomotopyCategory (g'^*) ⋙
        QXPrime)
  infer_instance

/-- The bounded-below right derived functor of `f_*` followed by the bounded-below derived
pullback along `g` exists. -/
local instance :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow ((f _*) ⋙ (g^*)))
      QisX :=
  inferInstance

/-- The bounded-below right derived functor of `f_*` followed by the bounded-below derived
pullback along `g` exists. -/
local instance modulePushforward_then_derivedPullback_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
      QisX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor
        (mapBoundedBelowHomotopyCategory (f _*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
        QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
  infer_instance

/-- The bounded-below composite `f_*` followed by derived pullback along `g` is pointwise right
derived when the source category has enough injectives. -/
local instance modulePushforward_then_derivedPullback_hasPointwiseRightDerivedFunctor :
    Functor.HasPointwiseRightDerivedFunctor
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
      QisX :=
  CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
    (mapBoundedBelowHomotopyCategory (f _*) ⋙
      mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))

/-- The bounded-below right derived functor of `(g')^*` followed by the bounded-below derived
pushforward along `f'` exists. -/
local instance :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow ((g'^*) ⋙ (f' _*)))
      QisX :=
  inferInstance

/-- The bounded-below right derived functor of `(g')^*` followed by the bounded-below derived
pushforward along `f'` exists. -/
local instance modulePullback_then_derivedPushforward_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategory (g'^*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))
      QisX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor
        (mapBoundedBelowHomotopyCategory (g'^*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))
        QisX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (mapBoundedBelowHomotopyCategory (g'^*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))
  infer_instance

-- Route correction: replace the componentwise adjunction transport, which timed out at
-- `underivedBaseChangeApp_naturality`, by the canonical pullback square and its mate.
/-- Helper for Lemma 20.17.1: the inverse-image square attached to the commutative base-change
diagram. This packages the pullback transport once so the mate construction can supply
underived naturality automatically. -/
private noncomputable abbrev underivedBaseChangePullbackSquare
    (sq : CommSq g' f' f g) :
    CategoryTheory.TwoSquare (g^*) (f^*) (f'^*) (g'^*) := by
  -- Proof comment: `TwoSquare` unfolds to a natural transformation from `g^* ⋙ f'^*` to
  -- `f^* ⋙ g'^*`, and the usual pullback-composition isomorphisms provide that bridge.
  change (g^* ⋙ f'^*) ⟶ (f^* ⋙ g'^*)
  exact
    (SheafOfModules.pullbackComp
      (RingedSpace.Hom.toRingCatSheafHom g)
      (RingedSpace.Hom.toRingCatSheafHom f')).hom ≫
    (eqToIso (congrArg RingedSpace.Hom.pullback sq.w.symm)).hom ≫
    (SheafOfModules.pullbackComp
      (RingedSpace.Hom.toRingCatSheafHom f)
      (RingedSpace.Hom.toRingCatSheafHom g')).inv

/-- The underived module-level base-change transformation
`g^* f_* ⟶ f'_* (g')^*` attached to the commutative square. -/
private noncomputable abbrev underivedBaseChangeNatTrans
    (sq : CommSq g' f' f g) :
    (f _* ⋙ g^*) ⟶ (g'^* ⋙ f' _*) :=
  -- Proof comment: the base-change map is the mate of the inverse-image square across
  -- `f^* ⊣ f_*` and `f'^* ⊣ f'_*`, so no separate componentwise naturality proof is needed.
  (CategoryTheory.mateEquiv
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom f))
      (SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom f'))
      (underivedBaseChangePullbackSquare g' f' f g sq)).natTrans

/-- The underived base-change transformation after passing to bounded-below derived owners. -/
private noncomputable def underivedBaseChangeToDerivedNatTrans
    (sq : CommSq g' f' f g) :
    mapBoundedBelowHomotopyCategoryToDerivedBelow ((f _*) ⋙ (g^*)) ⟶
      mapBoundedBelowHomotopyCategoryToDerivedBelow ((g'^*) ⋙ (f' _*)) :=
  mapBoundedBelowHomotopyToDerivedNatTrans
    (underivedBaseChangeNatTrans g' f' f g sq)

/-- The derived lift of the underived bounded-below base-change transformation between the two
composite-derived owners. -/
private noncomputable def underivedBaseChangeDerivedComparisonNatTrans
    (sq : CommSq g' f' f g) :
    mapBoundedBelowHomotopyCategory (f _*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*) ⟶
      mapBoundedBelowHomotopyCategory (g'^*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*) :=
  (mapBoundedBelowHomotopyCategoryToDerivedBelowCompIso (f _*) (g^*)).inv ≫
    underivedBaseChangeToDerivedNatTrans g' f' f g sq ≫
      (mapBoundedBelowHomotopyCategoryToDerivedBelowCompIso (g'^*) (f' _*)).hom

/-- The derived lift of the underived bounded-below base-change transformation between the two
composite-derived owners. -/
private noncomputable def compositeDerivedBaseChangeNatTrans
    (sq : CommSq g' f' f g) :
    Rgf ⟶
      Rf'g' :=
  Functor.rightDerivedNatTrans
    Rgf
    Rf'g'
    (Functor.totalRightDerivedUnit
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
      QX
      QisX)
    (Functor.totalRightDerivedUnit
      (mapBoundedBelowHomotopyCategory (g'^*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))
      QX
      QisX)
    QisX
    (underivedBaseChangeDerivedComparisonNatTrans g' f' f g sq)

/-- The canonical comparison `R(g^* ∘ f_*) ⟶ g^* ∘ Rf_*`. -/
private noncomputable abbrev baseChangeSourceComparison :
    Rgf ⟶
      Rf ⋙ Lg :=
  Functor.rightDerivedDesc
    Rgf
    (Functor.totalRightDerivedUnit
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
      QX
      QisX)
    QisX
    (Rf ⋙ Lg)
    (whiskerLeft
        (mapBoundedBelowHomotopyCategory (f _*))
        (Functor.totalRightDerivedUnit
          (mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
          QS
          QisS) ≫
      (Functor.associator
        (mapBoundedBelowHomotopyCategory (f _*))
        QS
        Lg).hom ≫
      whiskerRight
        (Functor.totalRightDerivedUnit
          (mapBoundedBelowHomotopyCategory (f _*) ⋙ QS)
          QX
          QisX)
        Lg ≫
      (Functor.associator QX Rf Lg).hom)

/-- The canonical comparison `R(f'_* ∘ (g')^*) ⟶ Rf'_* ∘ R(g')^*`. -/
private noncomputable abbrev baseChangeTargetComparison :
    Rf'g' ⟶
      Lg' ⋙ Rf' :=
  Functor.rightDerivedDesc
    Rf'g'
    (Functor.totalRightDerivedUnit
      (mapBoundedBelowHomotopyCategory (g'^*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))
      QX
      QisX)
    QisX
    (Lg' ⋙ Rf')
    (whiskerLeft
        (mapBoundedBelowHomotopyCategory (g'^*))
        (Functor.totalRightDerivedUnit
          (mapBoundedBelowHomotopyCategoryToDerivedBelow (f' _*))
          QXPrime
          QisXPrime) ≫
      (Functor.associator
        (mapBoundedBelowHomotopyCategory (g'^*))
        QXPrime
        Rf').hom ≫
      whiskerRight
        (Functor.totalRightDerivedUnit
          (mapBoundedBelowHomotopyCategory (g'^*) ⋙ QXPrime)
          QX
          QisX)
        Rf' ≫
      (Functor.associator QX Lg' Rf').hom)

/-- Helper for Lemma 20.17.1: when `g` is flat, the bounded-below derived-unit for `g^*` is an
isomorphism on every bounded-below complex because exact pullback already inverts
quasi-isomorphisms. -/
private theorem pullbackDerivedUnit_isIso_of_flat
    [RingedSpace.Hom.IsFlat g] (K : K⁺(ModS)) :
    IsIso
      (((mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
        QS
        QisS).app K) := by
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (g^*) :=
    ((CategoryTheory.exactFunctor_iff (g^*)).1 (IsFlat.pullback_exact g)).1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (g^*) :=
    ((CategoryTheory.exactFunctor_iff (g^*)).1 (IsFlat.pullback_exact g)).2
  have hInverts :
      MorphismProperty.IsInvertedBy
        QisS
        (mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)) := by
    intro X Y s hs
    have hsMapped :
        Qis⁺(ModSPrime) ((mapBoundedBelowHomotopyCategory (g^*)).map s) :=
      exactFunctor_maps_boundedBelowQuasiIso (F := g^*) s hs
    change
      IsIso
        ((mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModSPrime) ⥤ D⁺(ModSPrime)).map
          ((mapBoundedBelowHomotopyCategory (g^*)).map s))
    exact
      Localization.inverts
        (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModSPrime) ⥤ D⁺(ModSPrime))
        (Qis⁺(ModSPrime))
        ((mapBoundedBelowHomotopyCategory (g^*)).map s)
        hsMapped
  have hUnit :
      IsIso
        ((mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
          QS
          QisS) := by
    exact
      Functor.isIso_of_isRightDerivedFunctor_of_inverts
        ((mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerived
          QS
          QisS)
        ((mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
          QS
          QisS)
        hInverts
  let _ :
      IsIso
        ((mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
          QS
          QisS) := hUnit
  infer_instance

/-- Helper for Lemma 20.17.1: naturality transports invertibility of the source comparison
component along a bounded-below quasi-isomorphism. -/
private theorem baseChangeSourceComparison_app_isIso_of_quasiIso
    {K L : K⁺(ModX)} (φ : K ⟶ L)
    (hφ : QisX φ)
    (hL : IsIso ((baseChangeSourceComparison f g).app ((QX).obj L))) :
    IsIso ((baseChangeSourceComparison f g).app ((QX).obj K)) := by
  have hQφ : IsIso ((QX).map φ) := Localization.inverts QX QisX φ hφ
  have hcod : IsIso ((Rf ⋙ Lg).map ((QX).map φ)) := by
    infer_instance
  have hcomp :
      IsIso (((baseChangeSourceComparison f g).app ((QX).obj K)) ≫
        ((Rf ⋙ Lg).map ((QX).map φ))) := by
    rw [← (baseChangeSourceComparison f g).naturality ((QX).map φ)]
    infer_instance
  exact
    (isIso_comp_right_iff
      ((baseChangeSourceComparison f g).app ((QX).obj K))
      ((Rf ⋙ Lg).map ((QX).map φ))).1 hcomp

/-- Helper for Lemma 20.17.1: naturality transports invertibility of the source comparison
component along an isomorphism in `D⁺(ModX)`. -/
private theorem baseChangeSourceComparison_app_isIso_of_iso
    {Y Z : DModX} (e : Y ≅ Z)
    (hZ : IsIso ((baseChangeSourceComparison f g).app Z)) :
    IsIso ((baseChangeSourceComparison f g).app Y) := by
  have hcod : IsIso ((Rf ⋙ Lg).map e.hom) := by
    infer_instance
  have hcomp :
      IsIso (((baseChangeSourceComparison f g).app Y) ≫ ((Rf ⋙ Lg).map e.hom)) := by
    rw [← (baseChangeSourceComparison f g).naturality e.hom]
    infer_instance
  exact
    (isIso_comp_right_iff
      ((baseChangeSourceComparison f g).app Y)
      ((Rf ⋙ Lg).map e.hom)).1 hcomp

/-- Helper for Lemma 20.17.1: the source comparison is invertible on a bounded-below injective
replacement. -/
private theorem baseChangeSourceComparison_app_isIso_of_boundedBelowInjective
    [RingedSpace.Hom.IsFlat g]
    (K : K⁺(ModX))
    (hK : ∀ n : ℤ, Injective (K.obj.as.X n)) :
    IsIso ((baseChangeSourceComparison f g).app ((QX).obj K)) := by
  let J : CochainComplex.InjectivePlus ModX :=
    boundedBelowInjectiveHomotopyToInjectivePlus (K := K) hK
  let X : K⁺(ModX) := (HomotopyCategory.Plus.quotient ModX).obj J
  have hComputeComposite :
      (mapBoundedBelowHomotopyCategory (f _*) ⋙
        mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).ComputesRightDerivedAt
        QisX
        X := by
    simpa [X, J, boundedBelowInjectiveHomotopyToInjectivePlus] using
      (CategoryTheory.boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := mapBoundedBelowHomotopyCategory (f _*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
        (I := J))
  have hαComposite :
      IsIso
        (((mapBoundedBelowHomotopyCategory (f _*) ⋙
            mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
          QX
          QisX).app X) := by
    have hCanonical :
        IsIso
          (((mapBoundedBelowHomotopyCategory (f _*) ⋙
              mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
            (Qis⁺(ModX)).Q
            QisX).app X) := by
      exact
        (Functor.computesRightDerivedAt_iff
          (F := mapBoundedBelowHomotopyCategory (f _*) ⋙
            mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
          (S := QisX)
          (X := X)).1 hComputeComposite
    let _ :
        ((mapBoundedBelowHomotopyCategory (f _*) ⋙
            mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerived
          (Qis⁺(ModX)).Q
          QisX).IsRightDerivedFunctor
          ((mapBoundedBelowHomotopyCategory (f _*) ⋙
              mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
            (Qis⁺(ModX)).Q
            QisX)
          QisX := by
      infer_instance
    exact
      (LocalizerMorphism.isIso_iff_of_isRightDerivabilityStructure
        (Φ := LocalizerMorphism.id QisX)
        (L₁ := (Qis⁺(ModX)).Q)
        (L₂ := QX)
        (F := mapBoundedBelowHomotopyCategory (f _*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
        (F₁ := (mapBoundedBelowHomotopyCategory (f _*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerived
            (Qis⁺(ModX)).Q
            QisX)
        (α₁ := (mapBoundedBelowHomotopyCategory (f _*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
            (Qis⁺(ModX)).Q
            QisX)
        (F₂ := (mapBoundedBelowHomotopyCategory (f _*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerived
            QX
            QisX)
        (α₂ := (mapBoundedBelowHomotopyCategory (f _*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
            QX
            QisX)
        X).1 hCanonical
  have hComputePushforward :
      (mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).ComputesRightDerivedAt
        QisX
        X := by
    simpa [X, J, boundedBelowInjectiveHomotopyToInjectivePlus] using
      (CategoryTheory.boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (F := mapBoundedBelowHomotopyCategory (f _*) ⋙ QS)
        (I := J))
  have hαPushforward :
      IsIso
        (((mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerivedUnit
          QX
          QisX).app X) := by
    have hCanonical :
        IsIso
          (((mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerivedUnit
            (Qis⁺(ModX)).Q
            QisX).app X) := by
      exact
        (Functor.computesRightDerivedAt_iff
          (F := mapBoundedBelowHomotopyCategory (f _*) ⋙ QS)
          (S := QisX)
          (X := X)).1 hComputePushforward
    let _ :
        ((mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerived
          (Qis⁺(ModX)).Q
          QisX).IsRightDerivedFunctor
          ((mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerivedUnit
            (Qis⁺(ModX)).Q
            QisX)
          QisX := by
      infer_instance
    exact
      (LocalizerMorphism.isIso_iff_of_isRightDerivabilityStructure
        (Φ := LocalizerMorphism.id QisX)
        (L₁ := (Qis⁺(ModX)).Q)
        (L₂ := QX)
        (F := mapBoundedBelowHomotopyCategory (f _*) ⋙ QS)
        (F₁ := (mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerived
          (Qis⁺(ModX)).Q
          QisX)
        (α₁ := (mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerivedUnit
          (Qis⁺(ModX)).Q
          QisX)
        (F₂ := (mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerived
          QX
          QisX)
        (α₂ := (mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerivedUnit
          QX
          QisX)
        X).1 hCanonical
  have hαPullback :
      IsIso
        (((mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
          QS
          QisS).app ((mapBoundedBelowHomotopyCategory (f _*)).obj X)) := by
    exact
      pullbackDerivedUnit_isIso_of_flat
        (g := g)
        ((mapBoundedBelowHomotopyCategory (f _*)).obj X)
  let βG :
      mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*) ⟶ QS ⋙ Lg :=
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
      QS
      QisS
  let βF :
      mapBoundedBelowHomotopyCategory (f _*) ⋙ QS ⟶ QX ⋙ Rf :=
    (mapBoundedBelowHomotopyCategory (f _*) ⋙ QS).totalRightDerivedUnit
      QX
      QisX
  have hfac :
      (((mapBoundedBelowHomotopyCategory (f _*) ⋙
            mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
          QX
          QisX).app X) ≫
          ((baseChangeSourceComparison f g).app ((QX).obj X)) =
        (((Functor.whiskerLeft
            (mapBoundedBelowHomotopyCategory (f _*))
            βG).app X) ≫
            (Functor.associator
              (mapBoundedBelowHomotopyCategory (f _*))
              QS
              Lg).hom.app X) ≫
          ((Functor.whiskerRight βF Lg).app X) ≫
            (Functor.associator QX Rf Lg).hom.app X := by
    -- Proof comment: this is the standard factorization of the right-derived composition
    -- comparison specialized to `f_*` and `g^*`.
    simpa [X, baseChangeSourceComparison, βG, βF, Category.assoc] using
      (Functor.rightDerived_fac_app
        (RF := Rgf)
        (α := (mapBoundedBelowHomotopyCategory (f _*) ⋙
          mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
            QX QisX)
        (W := QisX)
        (G := Rf ⋙ Lg)
        (β := (Functor.whiskerLeft
            (mapBoundedBelowHomotopyCategory (f _*))
            βG) ≫
          (Functor.associator
            (mapBoundedBelowHomotopyCategory (f _*))
            QS
            Lg).hom ≫
          Functor.whiskerRight βF Lg ≫
          (Functor.associator QX Rf Lg).hom)
        X)
  have htail :
      IsIso
        ((((Functor.whiskerLeft
              (mapBoundedBelowHomotopyCategory (f _*))
              βG).app X) ≫
            (Functor.associator
              (mapBoundedBelowHomotopyCategory (f _*))
              QS
              Lg).hom.app X) ≫
          ((Functor.whiskerRight βF Lg).app X) ≫
            (Functor.associator QX Rf Lg).hom.app X) := by
    have hWhiskerLeft :
        IsIso
          ((Functor.whiskerLeft
            (mapBoundedBelowHomotopyCategory (f _*))
            βG).app X) := by
      simpa [βG] using hαPullback
    have hWhiskerRight :
        IsIso ((Functor.whiskerRight βF Lg).app X) := by
      change IsIso
        ((Functor.totalRightDerived
          (mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*))
          QS
          QisS).map (βF.app X))
      let _ : IsIso (βF.app X) := hαPushforward
      infer_instance
    let _ :
        IsIso
          ((Functor.whiskerLeft
            (mapBoundedBelowHomotopyCategory (f _*))
            βG).app X) := hWhiskerLeft
    let _ :
        IsIso ((Functor.whiskerRight βF Lg).app X) := hWhiskerRight
    let _ :
        IsIso
          ((Functor.associator
            (mapBoundedBelowHomotopyCategory (f _*))
            QS
            Lg).hom.app X) := by
      infer_instance
    let _ :
        IsIso ((Functor.associator QX Rf Lg).hom.app X) := by
      infer_instance
    have hFirstTwo :
        IsIso
          (((Functor.whiskerLeft
                (mapBoundedBelowHomotopyCategory (f _*))
                βG).app X) ≫
              (Functor.associator
                (mapBoundedBelowHomotopyCategory (f _*))
                QS
                Lg).hom.app X) := by
      let ab :=
        ((Functor.whiskerLeft
          (mapBoundedBelowHomotopyCategory (f _*))
          βG).app X) ≫
          (Functor.associator
            (mapBoundedBelowHomotopyCategory (f _*))
            QS
            Lg).hom.app X
      have hcompRight :
          IsIso
            (ab ≫ CategoryTheory.inv ((Functor.associator
                  (mapBoundedBelowHomotopyCategory (f _*))
                  QS
                  Lg).hom.app X)) := by
        dsimp [ab]
        simpa [Category.assoc] using hWhiskerLeft
      exact
        (isIso_comp_right_iff ab
          (CategoryTheory.inv ((Functor.associator
            (mapBoundedBelowHomotopyCategory (f _*))
            QS
            Lg).hom.app X))).1 hcompRight
    have hFirstThree :
        IsIso
          ((((Functor.whiskerLeft
                  (mapBoundedBelowHomotopyCategory (f _*))
                  βG).app X) ≫
                (Functor.associator
                  (mapBoundedBelowHomotopyCategory (f _*))
                  QS
                  Lg).hom.app X) ≫
              ((Functor.whiskerRight βF Lg).app X)) := by
      let abc :=
        (((Functor.whiskerLeft
            (mapBoundedBelowHomotopyCategory (f _*))
            βG).app X) ≫
          (Functor.associator
            (mapBoundedBelowHomotopyCategory (f _*))
            QS
            Lg).hom.app X) ≫
          ((Functor.whiskerRight βF Lg).app X)
      have hcompRight :
          IsIso
            (abc ≫
                CategoryTheory.inv ((Functor.whiskerRight βF Lg).app X)) := by
        dsimp [abc]
        simpa [Category.assoc] using hFirstTwo
      exact
        (isIso_comp_right_iff abc
          (CategoryTheory.inv ((Functor.whiskerRight βF Lg).app X))).1 hcompRight
    let _ :
        IsIso
          ((((Functor.whiskerLeft
                  (mapBoundedBelowHomotopyCategory (f _*))
                  βG).app X) ≫
                (Functor.associator
                  (mapBoundedBelowHomotopyCategory (f _*))
                  QS
                  Lg).hom.app X) ≫
              ((Functor.whiskerRight βF Lg).app X)) := hFirstThree
    have hNormalized :
        IsIso
          (βG.app ((mapBoundedBelowHomotopyCategory (f _*)).obj X) ≫
            ((mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerived
              mapBoundedBelowHomotopyToDerivedBelow
              Qis⁺(ModS)).map
              (βF.app X)) := by
      simpa [Category.assoc] using hFirstThree
    let normalized :=
      βG.app ((mapBoundedBelowHomotopyCategory (f _*)).obj X) ≫
        ((mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerived
          mapBoundedBelowHomotopyToDerivedBelow
          Qis⁺(ModS)).map
          (βF.app X)
    let _ : IsIso normalized := by
      simpa [normalized] using hNormalized
    have hNormalizedComp :
        IsIso (normalized ≫ (Functor.associator QX Rf Lg).hom.app X) := by
      have hcompRight :
          IsIso
            ((normalized ≫ (Functor.associator QX Rf Lg).hom.app X) ≫
              CategoryTheory.inv ((Functor.associator QX Rf Lg).hom.app X)) := by
        simpa [normalized, Category.assoc] using hNormalized
      exact
        (isIso_comp_right_iff
          (normalized ≫ (Functor.associator QX Rf Lg).hom.app X)
          (CategoryTheory.inv ((Functor.associator QX Rf Lg).hom.app X))).1 hcompRight
    simpa [normalized, Category.assoc] using hNormalizedComp
  have hcomp :
      IsIso
        ((((mapBoundedBelowHomotopyCategory (f _*) ⋙
              mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
            QX
            QisX).app X) ≫
            ((baseChangeSourceComparison f g).app ((QX).obj X))) := by
    rw [hfac]
    exact htail
  let _ :
      IsIso
        (((mapBoundedBelowHomotopyCategory (f _*) ⋙
            mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
          QX
          QisX).app X) := hαComposite
  have hX :
      IsIso ((baseChangeSourceComparison f g).app ((QX).obj X)) :=
    (isIso_comp_left_iff
      (((mapBoundedBelowHomotopyCategory (f _*) ⋙
            mapBoundedBelowHomotopyCategoryToDerivedBelow (g^*)).totalRightDerivedUnit
          QX
          QisX).app X)
      ((baseChangeSourceComparison f g).app ((QX).obj X))).1 hcomp
  let _ : IsIso ((baseChangeSourceComparison f g).app ((QX).obj X)) := hX
  simpa [X, J, boundedBelowInjectiveHomotopyToInjectivePlus] using
    (inferInstance : IsIso ((baseChangeSourceComparison f g).app ((QX).obj X)))

/-- Helper for Lemma 20.17.1: the source comparison is invertible on every bounded-below derived
object once `g` is flat. -/
private theorem baseChangeSourceComparison_app_isIso
    [RingedSpace.Hom.IsFlat g]
    (ℱ : DModX) :
    IsIso ((baseChangeSourceComparison f g).app ℱ) := by
  letI : Functor.EssSurj QX := mapBoundedBelowHomotopyToDerivedBelow_essSurj (𝒜 := ModX)
  let K : K⁺(ModX) := Functor.objPreimage QX ℱ
  rcases exists_quasiIso_to_boundedBelowInjective (𝒜 := ModX) K with ⟨K', s, hK', hs⟩
  have hK' :
      IsIso ((baseChangeSourceComparison f g).app ((QX).obj K')) :=
    baseChangeSourceComparison_app_isIso_of_boundedBelowInjective
      (f := f) (g := g) K' hK'
  have hK :
      IsIso ((baseChangeSourceComparison f g).app ((QX).obj K)) :=
    baseChangeSourceComparison_app_isIso_of_quasiIso
      (f := f) (g := g) s (by simpa [boundedBelowHomotopyQuasiIso] using hs) hK'
  exact
    baseChangeSourceComparison_app_isIso_of_iso
      (f := f)
      (g := g)
      (Functor.objObjPreimageIso QX ℱ).symm
      hK

/-- Helper for Lemma 20.17.1: the canonical bounded-below base-change candidate obtained by
inverting the source comparison. -/
private noncomputable def boundedBelowDerivedBaseChangeCandidate
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : CommSq g' f' f g) [RingedSpace.Hom.IsFlat g] (ℱ : DModX) :
    boundedBelowDerivedBaseChangeSource f g ℱ ⟶
      boundedBelowDerivedBaseChangeTarget g' f' ℱ :=
  let hIso : IsIso ((baseChangeSourceComparison f g).app ℱ) :=
    baseChangeSourceComparison_app_isIso (f := f) (g := g) ℱ
  @CategoryTheory.inv _ _ _ _ ((baseChangeSourceComparison f g).app ℱ) hIso ≫
    (compositeDerivedBaseChangeNatTrans g' f' f g sq).app ℱ ≫
      (baseChangeTargetComparison g' f').app ℱ

/-- The canonical specification predicate for a bounded-below derived base-change morphism in the
commutative square `sq : CommSq g' f' f g`. -/
def IsBoundedBelowDerivedBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : CommSq g' f' f g) (ℱ : DModX)
    (η : boundedBelowDerivedBaseChangeSource f g ℱ ⟶
      boundedBelowDerivedBaseChangeTarget g' f' ℱ) : Prop :=
  (baseChangeSourceComparison f g).app ℱ ≫ η =
    (compositeDerivedBaseChangeNatTrans g' f' f g sq).app ℱ ≫
      (baseChangeTargetComparison g' f').app ℱ

/-- The source-facing target-alias specialization of `IsBoundedBelowDerivedBaseChangeMap` for a
commutative square `sq : CommSq g' f' f g`, whose target is written as `R(f')_* (g')^* ℱ`. -/
def IsBoundedBelowFlatBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : CommSq g' f' f g) (ℱ : DModX)
    (η : boundedBelowDerivedBaseChangeSource f g ℱ ⟶
      boundedBelowFlatBaseChangeTarget g' f' ℱ) : Prop :=
  IsBoundedBelowDerivedBaseChangeMap g' f' f g sq ℱ η

/-- Helper for Lemma 20.17.1: the canonical candidate obtained by inverting the source
comparison satisfies the defining base-change equation. -/
private theorem boundedBelowDerivedBaseChangeCandidate_spec
    (sq : CommSq g' f' f g)
    [RingedSpace.Hom.IsFlat g]
    (ℱ : DModX) :
    IsBoundedBelowDerivedBaseChangeMap g' f' f g sq ℱ
      (boundedBelowDerivedBaseChangeCandidate g' f' f g sq ℱ) := by
  letI : IsIso ((baseChangeSourceComparison f g).app ℱ) :=
    baseChangeSourceComparison_app_isIso (f := f) (g := g) ℱ
  -- Proof comment: expand the specification once and cancel the source comparison component with
  -- its inverse.
  simpa [IsBoundedBelowDerivedBaseChangeMap, boundedBelowDerivedBaseChangeCandidate,
    Category.assoc] using
    (IsIso.hom_inv_id_assoc
      ((baseChangeSourceComparison f g).app ℱ)
      ((compositeDerivedBaseChangeNatTrans g' f' f g sq).app ℱ ≫
        (baseChangeTargetComparison g' f').app ℱ))

/-- Uniqueness for bounded-below derived base-change morphisms satisfying the canonical owner
predicate of Lemma `20.17.1`. -/
theorem eq_of_boundedBelowDerivedBaseChange_eq
    (sq : CommSq g' f' f g)
    [RingedSpace.Hom.IsFlat g]
    (ℱ : DModX)
    {η₁ η₂ : boundedBelowDerivedBaseChangeSource f g ℱ ⟶
      boundedBelowDerivedBaseChangeTarget g' f' ℱ}
    (hη₁ : IsBoundedBelowDerivedBaseChangeMap g' f' f g sq ℱ η₁)
    (hη₂ : IsBoundedBelowDerivedBaseChangeMap g' f' f g sq ℱ η₂) :
    η₁ = η₂ := by
  letI : IsIso ((baseChangeSourceComparison f g).app ℱ) :=
    baseChangeSourceComparison_app_isIso (f := f) (g := g) ℱ
  -- Proof comment: rewrite both specifications by precomposing with the inverse source
  -- comparison, so both maps become the same canonical composite.
  have hη₁' :
      η₁ = boundedBelowDerivedBaseChangeCandidate g' f' f g sq ℱ := by
    simpa [boundedBelowDerivedBaseChangeCandidate, Category.assoc] using
      congrArg
        (fun t ↦ CategoryTheory.inv ((baseChangeSourceComparison f g).app ℱ) ≫ t)
        hη₁
  have hη₂' :
      η₂ = boundedBelowDerivedBaseChangeCandidate g' f' f g sq ℱ := by
    simpa [boundedBelowDerivedBaseChangeCandidate, Category.assoc] using
      congrArg
        (fun t ↦ CategoryTheory.inv ((baseChangeSourceComparison f g).app ℱ) ≫ t)
        hη₂
  exact hη₁'.trans hη₂'.symm

/-- Uniqueness for the flat base-change specialization of Lemma `20.17.1`, whose target is written
as `R(f')_* (g')^* ℱ`. -/
theorem eq_of_boundedBelowFlatBaseChange_eq
    (sq : CommSq g' f' f g)
    [RingedSpace.Hom.IsFlat g]
    (ℱ : DModX)
    {η₁ η₂ : boundedBelowDerivedBaseChangeSource f g ℱ ⟶
      boundedBelowFlatBaseChangeTarget g' f' ℱ}
    (hη₁ : IsBoundedBelowFlatBaseChangeMap g' f' f g sq ℱ η₁)
    (hη₂ : IsBoundedBelowFlatBaseChangeMap g' f' f g sq ℱ η₂) :
    η₁ = η₂ := by
  simpa [IsBoundedBelowFlatBaseChangeMap, boundedBelowFlatBaseChangeTarget] using
    (eq_of_boundedBelowDerivedBaseChange_eq g' f' f g sq ℱ hη₁ hη₂)

/- Lemma 20.17.1: for a commutative square of ringed spaces
`X' --g'--> X`, `S' --g--> S` with vertical maps `f' : X' ⟶ S'` and `f : X ⟶ S`, if `g` is
flat, then every bounded-below derived object `ℱ ∈ D⁺(ModX)` has a unique bounded-below
base-change morphism `Lg^* Rf_* ℱ ⟶ R(f')_* L(g')^* ℱ` satisfying
`IsBoundedBelowDerivedBaseChangeMap g' f' f g sq ℱ`. -/
@[stacks 02N7]
theorem existsUnique_boundedBelowDerivedBaseChangeMap
    (sq : CommSq g' f' f g)
    [RingedSpace.Hom.IsFlat g]
    (ℱ : DModX) :
    ∃! η : boundedBelowDerivedBaseChangeSource f g ℱ ⟶
        boundedBelowDerivedBaseChangeTarget g' f' ℱ,
      IsBoundedBelowDerivedBaseChangeMap g' f' f g sq ℱ η := by
  refine
    ⟨boundedBelowDerivedBaseChangeCandidate g' f' f g sq ℱ,
      boundedBelowDerivedBaseChangeCandidate_spec g' f' f g sq ℱ,
      ?_⟩
  intro η hη
  exact
    eq_of_boundedBelowDerivedBaseChange_eq
      (g' := g')
      (f' := f')
      (f := f)
      (g := g)
      (sq := sq)
      (ℱ := ℱ)
      (η₁ := η)
      (η₂ := boundedBelowDerivedBaseChangeCandidate g' f' f g sq ℱ)
      hη
      (boundedBelowDerivedBaseChangeCandidate_spec g' f' f g sq ℱ)

/-- Lemma 20.17.1, source-facing target-alias specialization: `ℱ ∈ D⁺(ModX)` has a unique
bounded-below base-change morphism `Lg^* Rf_* ℱ ⟶ R(f')_* (g')^* ℱ`. In flat situations this is
the usual textbook target spelling. -/
@[stacks 02N7]
theorem existsUnique_boundedBelowFlatBaseChangeMap
    (sq : CommSq g' f' f g)
    [RingedSpace.Hom.IsFlat g]
    (ℱ : DModX) :
    ∃! η : boundedBelowDerivedBaseChangeSource f g ℱ ⟶
        boundedBelowFlatBaseChangeTarget g' f' ℱ,
      IsBoundedBelowFlatBaseChangeMap g' f' f g sq ℱ η := by
  simpa [IsBoundedBelowFlatBaseChangeMap, boundedBelowFlatBaseChangeTarget] using
    (existsUnique_boundedBelowDerivedBaseChangeMap g' f' f g sq ℱ)

end

end BaseChange

end AlgebraicGeometry.RingedSpace

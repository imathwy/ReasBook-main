import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_49_1 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/- 
Domain-style sampling for Definition 20.49.1:
- primary domain: perfect complexes and perfect derived `\mathcal O_X`-modules on a ringed space;
- sampled owner declarations:
  `moduleDerivedRestrictionToOpen`,
  `DerivedCategory.IsMPseudoCoherent`,
  `CochainComplex.IsStrictlyPerfect`,
  `DerivedCategory.IsPerfect` from Chapter 15;
- best owner abstraction: `CochainComplex.IsPerfect` remains the source-facing complex predicate,
  while the derived notion should be owned intrinsically by `DerivedCategory (RingedSpace.Modules X)`
  through local strictly perfect models after restriction to opens, not by a chosen global
  representative complex;
- primitive data: an open cover together with strictly perfect local models and local
  quasi-isomorphisms/isomorphisms on the restricted objects;
- derived API: bridge lemmas comparing the intrinsic derived predicate with perfect
  representatives.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsPerfect` and `DerivedCategory.IsPerfect`;
- `core/canonical`: `moduleDerivedRestrictionToOpen` and `CochainComplex.IsStrictlyPerfect`;
- `bridge/view`: representative-based existence theorems for perfect complexes.
-/
namespace AlgebraicGeometry.RingedSpace

local instance instModuleSheafRestrictionToOpenAdditive
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (U : Opens X) :
    (_root_.moduleSheafRestrictionToOpen U 𝒪).Additive := sorry

local instance instModuleSheafRestrictionToOpenPreservesFiniteLimits
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (U : Opens X) :
    PreservesFiniteLimits (_root_.moduleSheafRestrictionToOpen U 𝒪) := sorry

local instance instModuleSheafRestrictionToOpenPreservesFiniteColimits
    {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (U : Opens X) :
    PreservesFiniteColimits (_root_.moduleSheafRestrictionToOpen U 𝒪) := sorry

variable {X : TopCat.{u}} {𝒪 : X.Sheaf RingCat.{u}}

private abbrev OpenComplex (V : Opens X) :=
  CochainComplex (SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} V.inclusion').obj 𝒪)) ℤ

/-- Definition 20.49.1 (1): a complex of `\mathcal O_X`-modules is perfect if there is an open
covering of `X` such that on each member of the cover its restriction is quasi-isomorphic to a
strictly perfect complex. -/
def CochainComplex.IsPerfect (E : CochainComplex (SheafOfModules 𝒪) ℤ) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X),
    iSup U = ⊤ ∧
      ∀ i : ι, ∃ Ei : OpenComplex (U i),
        ∃ α : Ei ⟶
            (((_root_.moduleSheafRestrictionToOpen (U i) 𝒪).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E),
          CochainComplex.IsStrictlyPerfect Ei ∧ QuasiIso α

-- Proof sketch: unfold `CochainComplex.IsPerfect`; this is exactly the local strict-perfect
-- presentation condition from the definition, expressed using the restriction functor to open
-- subspaces and the standard predicate `QuasiIso` for quasi-isomorphisms of complexes.
/-- A complex of `\mathcal O_X`-modules is perfect exactly when it is locally quasi-isomorphic to
a strictly perfect complex. -/
theorem cochainComplex_isPerfect_iff
    (E : CochainComplex (SheafOfModules 𝒪) ℤ) :
    CochainComplex.IsPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X),
        iSup U = ⊤ ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ α : Ei ⟶
                (((_root_.moduleSheafRestrictionToOpen (U i) 𝒪).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj E),
              CochainComplex.IsStrictlyPerfect Ei ∧ QuasiIso α :=
  Iff.rfl

namespace DerivedCategory

local notation "DMod" => DerivedCategory (SheafOfModules 𝒪)

/-- Definition 20.49.1 (2): an object of `D(\mathcal O_X)` is perfect if some open covering of
`X` carries strictly perfect models for its restrictions in the derived categories of the open
subspaces. -/
def IsPerfect (E : DMod) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X),
    iSup U = ⊤ ∧
      ∀ i : ι, ∃ Ei : OpenComplex (U i),
        ∃ _ : DerivedCategory.Q.obj Ei ≅
            ((_root_.moduleSheafRestrictionToOpen (U i) 𝒪).mapDerivedCategory).obj E,
          CochainComplex.IsStrictlyPerfect Ei

-- Proof sketch: unfold `DerivedCategory.IsPerfect`; the statement is exactly the existence of a
-- open cover on which the restricted derived object is represented by strictly perfect
-- complexes.
/-- Unfolding `DerivedCategory.IsPerfect` gives the intrinsic open-cover condition by strictly
perfect local models in the restricted derived categories. -/
theorem isPerfect_iff
    (E : DMod) :
    IsPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X),
        iSup U = ⊤ ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ _ : DerivedCategory.Q.obj Ei ≅
                ((_root_.moduleSheafRestrictionToOpen (U i) 𝒪).mapDerivedCategory).obj E,
              CochainComplex.IsStrictlyPerfect Ei :=
  Iff.rfl

-- Proof sketch: a perfect representative gives strictly perfect local models after restricting the
-- representative complex to the chosen open cover, while conversely local strictly perfect models
-- for the restricted derived object can be transported to any chosen representative complex.
/-- A derived `\mathcal O_X`-module is perfect exactly when it admits a perfect representative
complex. This is a bridge theorem from the intrinsic owner `DerivedCategory.IsPerfect` to chosen
representatives. -/
theorem isPerfect_iff_exists_perfect_representative
    (E : DMod) :
    IsPerfect E ↔
      ∃ K : CochainComplex (SheafOfModules 𝒪) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          CochainComplex.IsPerfect K := by
  sorry

end DerivedCategory
end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_2 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "Q" =>
  (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DModX)

-- Proof sketch: apply the representative bridge from Definition `20.49.1`; the given perfect
-- complex `K` already supplies the chosen representative required there.
/-- Lemma 20.49.2 (1): a perfect representative complex determines a perfect object of
`D(\mathcal O_X)`. -/
theorem derived_isPerfect_of_perfect_representative
    (E : DModX) (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (e : E ≅ Q.obj K) (hK : CochainComplex.IsPerfect K) :
    DerivedCategory.IsPerfect E := sorry

-- Proof sketch: unpack the perfect representative supplied by `DerivedCategory.IsPerfect E`,
-- obtaining a perfect complex `L` with `E ≅ Q.obj L`. Compose this isomorphism with the chosen
-- representation `E ≅ Q.obj K` and transport perfection across the induced isomorphism between
-- `Q.obj L` and `Q.obj K`; by the local definition of `CochainComplex.IsPerfect`, the complex `K`
-- inherits the same strictly perfect local presentation.
/-- Lemma 20.49.2 (2): if `E` is a perfect object of `D(\mathcal O_X)`, then every cochain
complex representing `E` is perfect. -/
theorem representing_complex_isPerfect_of_derived_isPerfect
    (E : DModX) (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (e : E ≅ Q.obj K) (hE : DerivedCategory.IsPerfect E) :
    CochainComplex.IsPerfect K := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_3 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/-- The pullback of the structure sheaf of `X` to the open subspace cut out by `U`. -/
abbrev openSubspaceRingCatSheaf (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  (TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X)

/-- An `\mathcal O_U`-module is finite free if it is isomorphic to a finite free module sheaf on
the open subspace `U`. -/
def IsFiniteFreeOnOpenSubspace {U : Opens X.carrier}
    (ℱ : openSubspaceModuleCategory X U) : Prop :=
  ∃ I : Type u, Finite I ∧
    Nonempty (ℱ ≅ (SheafOfModules.free.{u} I : openSubspaceModuleCategory X U))

-- Proof sketch: unfold `IsFiniteFreeOnOpenSubspace`.
/-- Unfolding `IsFiniteFreeOnOpenSubspace` gives the existence of a finite basis for the module
sheaf on the open subspace. -/
theorem isFiniteFreeOnOpenSubspace_iff {U : Opens X.carrier}
    (ℱ : openSubspaceModuleCategory X U) :
    IsFiniteFreeOnOpenSubspace ℱ ↔
      ∃ I : Type u, Finite I ∧
        Nonempty (ℱ ≅ (SheafOfModules.free.{u} I : openSubspaceModuleCategory X U)) := sorry

/-- An `\mathcal O_U`-module is finite locally free if some open cover of `U` trivializes it by
finite free module sheaves. -/
def IsFiniteLocallyFreeOnOpenSubspace {U : Opens X.carrier}
    (ℱ : openSubspaceModuleCategory X U) : Prop :=
  ∃ (ι : Type u) (V : ι → Opens U),
    iSup V = ⊤ ∧
      ∀ i : ι, ∃ I : Type u, Finite I ∧
        Nonempty
          (ℱ.over (V i) ≅
            (SheafOfModules.free.{u} I :
              SheafOfModules ((openSubspaceRingCatSheaf X U).over (V i))))

-- Proof sketch: unfold `IsFiniteLocallyFreeOnOpenSubspace`.
/-- Unfolding `IsFiniteLocallyFreeOnOpenSubspace` gives a covering of the open subspace on which
the module becomes finite free. -/
theorem isFiniteLocallyFreeOnOpenSubspace_iff {U : Opens X.carrier}
    (ℱ : openSubspaceModuleCategory X U) :
    IsFiniteLocallyFreeOnOpenSubspace ℱ ↔
      ∃ (ι : Type u) (V : ι → Opens U),
        iSup V = ⊤ ∧
          ∀ i : ι, ∃ I : Type u, Finite I ∧
            Nonempty
              (ℱ.over (V i) ≅
                (SheafOfModules.free.{u} I :
                  SheafOfModules ((openSubspaceRingCatSheaf X U).over (V i)))) := sorry

namespace DerivedCategory

/-- An object of `D(\mathcal O_X)` admits a finite-locally-free representative on an open cover
if, after restricting to each member of some open cover, it is represented by a bounded complex
whose terms are finite locally free `\mathcal O`-modules on that open subspace. -/
def HasFiniteLocallyFreeRepresentativeOnOpenCover (E : DModX) : Prop :=
  ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
    ∃ _ : E ≅ DerivedCategory.Q.obj K,
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        iSup U = ⊤ ∧
              ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
                ∃ _ : DerivedCategory.Q.obj Ei ≅
                    DerivedCategory.Q.obj ((moduleComplexRestrictionToOpen X (U i)).obj K),
                  (∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b) ∧
                    ∀ j : ℤ, IsFiniteLocallyFreeOnOpenSubspace (Ei.X j)

-- Proof sketch: unfold `HasFiniteLocallyFreeRepresentativeOnOpenCover`.
/-- Unfolding `HasFiniteLocallyFreeRepresentativeOnOpenCover` gives the open-cover criterion by
bounded complexes of finite locally free modules. -/
theorem hasFiniteLocallyFreeRepresentativeOnOpenCover_iff
    (E : DModX) :
    HasFiniteLocallyFreeRepresentativeOnOpenCover E ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          ∃ (ι : Type u) (U : ι → Opens X.carrier),
            iSup U = ⊤ ∧
              ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
                ∃ _ : DerivedCategory.Q.obj Ei ≅
                    DerivedCategory.Q.obj ((moduleComplexRestrictionToOpen X (U i)).obj K),
                  (∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b) ∧
                    ∀ j : ℤ, IsFiniteLocallyFreeOnOpenSubspace (Ei.X j) := sorry

/-- An object of `D(\mathcal O_X)` admits a finite-free representative on an open cover if,
after restricting to each member of some open cover, it is represented by a bounded complex whose
terms are finite free `\mathcal O`-modules on that open subspace. -/
def HasFiniteFreeRepresentativeOnOpenCover (E : DModX) : Prop :=
  ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
    ∃ _ : E ≅ DerivedCategory.Q.obj K,
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        iSup U = ⊤ ∧
              ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
                ∃ _ : DerivedCategory.Q.obj Ei ≅
                    DerivedCategory.Q.obj ((moduleComplexRestrictionToOpen X (U i)).obj K),
                  (∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b) ∧
                    ∀ j : ℤ, IsFiniteFreeOnOpenSubspace (Ei.X j)

-- Proof sketch: unfold `HasFiniteFreeRepresentativeOnOpenCover`.
/-- Unfolding `HasFiniteFreeRepresentativeOnOpenCover` gives the open-cover criterion by bounded
complexes of finite free modules. -/
theorem hasFiniteFreeRepresentativeOnOpenCover_iff
    (E : DModX) :
    HasFiniteFreeRepresentativeOnOpenCover E ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          ∃ (ι : Type u) (U : ι → Opens X.carrier),
            iSup U = ⊤ ∧
              ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
                ∃ _ : DerivedCategory.Q.obj Ei ≅
                    DerivedCategory.Q.obj ((moduleComplexRestrictionToOpen X (U i)).obj K),
                  (∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b) ∧
                    ∀ j : ℤ, IsFiniteFreeOnOpenSubspace (Ei.X j) := sorry

-- Proof sketch: `(1) → (2)` uses Lemma `20.49.2` to choose a perfect representative and then
-- applies Lemma `17.14.6` termwise on the open subspaces, using the local-ring hypothesis on
-- stalks. `(2) → (3)` refines the cover so that each finite locally free term becomes finite free
-- on smaller opens. `(3) → (1)` applies Lemma `20.49.2` again, since a bounded complex of finite
-- free modules is in particular strictly perfect on each member of the chosen cover.
/-- Lemma 20.49.3: for an object `E` of `D(\mathcal O_X)` on a ringed space whose stalk rings are
local, the following are equivalent: `E` is perfect, `E` is locally represented by bounded
complexes of finite locally free modules, and `E` is locally represented by bounded complexes of
finite free modules. -/
theorem perfect_tfae_exists_cover_termwise_finiteLocallyFree_exists_cover_termwise_finiteFree
    (E : DModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    ([ IsPerfect E
      , HasFiniteLocallyFreeRepresentativeOnOpenCover E
      , HasFiniteFreeRepresentativeOnOpenCover E
      ] : List Prop).TFAE := sorry

end DerivedCategory
end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_4 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: work locally using the `(a - 1)`-pseudo-coherent approximation by a strictly
-- perfect complex inducing cohomology isomorphisms in degrees `≥ a`. The cone is then a shift of
-- a kernel sheaf in degree `a - 1`. Derived tensoring with arbitrary modules and using the
-- tor-amplitude bound in `[a, b]` shows the corresponding cokernel sheaf is flat by Lemma
-- `20.26.16`; by Modules, Lemma `17.18.3` it is locally a direct summand of a finite free sheaf,
-- so the local truncation is again strictly perfect and represents `E`.
/-- Lemma 20.49.4: if an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` and is
`(a - 1)`-pseudo-coherent, with `a ≤ b`, then `E` is perfect. -/
theorem isPerfect_of_hasTorAmplitudeIn_of_isMPseudoCoherent
    (E : DMod) (a b : ℤ) (hab : a ≤ b)
    (hamp : HasTorAmplitudeIn E a b)
    (hpc : IsMPseudoCoherent E (a - 1)) :
    DerivedCategory.IsPerfect E := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_5 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
variable [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, HasCountableCoproducts (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, MonoidalCategory (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, MonoidalPreadditive (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, HasColimits (openSubspaceModuleCategory X U)]
variable [∀ U : Opens X.carrier, (curriedTensor (openSubspaceModuleCategory X U)).Additive]
variable [∀ U : Opens X.carrier,
  ∀ ℱ : openSubspaceModuleCategory X U,
    ((curriedTensor (openSubspaceModuleCategory X U)).obj ℱ).Additive]
variable [∀ U : Opens X.carrier,
  ∀ (ℱ 𝒢 : CochainComplex (openSubspaceModuleCategory X U) ℤ),
    CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (openSubspaceModuleCategory X U))]
variable [∀ U : Opens X.carrier,
  CategoryWithHomology (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  HasCountableCoproducts (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  MonoidalCategory (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  MonoidalPreadditive (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  HasColimits (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  (curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding))).Additive]
variable [∀ U : Opens X.carrier,
  ∀ ℱ : RingedSpace.Modules (X.restrict U.isOpenEmbedding),
    ((curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding))).obj ℱ).Additive]
variable [∀ U : Opens X.carrier,
  ∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules (X.restrict U.isOpenEmbedding)) ℤ),
    CochainComplex.HasMapBifunctor ℱ 𝒢
      (curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding)))]

/-- A complex on an open subspace is strictly perfect when it is bounded and each term is a
retract of a finite free module sheaf. -/
def CochainComplex.IsStrictlyPerfectRelativeToOpen {U : Opens X.carrier}
    (K : CochainComplex (openSubspaceModuleCategory X U) ℤ) : Prop :=
  (∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b) ∧
    ∀ j : ℤ, ∃ I : Type u, Finite I ∧
      Nonempty
        (Retract (K.X j) (SheafOfModules.free.{u} I : openSubspaceModuleCategory X U))

namespace DerivedCategory

local notation "DMod" => DerivedCategory (Modules X)
local notation "OpenComplex" U => CochainComplex (openSubspaceModuleCategory X U) ℤ

/-- A derived `\mathcal O_X`-module has a local strictly perfect presentation when it is
represented on some open cover by quasi-isomorphisms from strictly perfect complexes. -/
def HasLocalStrictlyPerfectPresentation (E : DMod) : Prop :=
  ∃ K : CochainComplex (Modules X) ℤ,
    ∃ _ : E ≅ ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DMod).obj K),
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        iSup U = ⊤ ∧
          ∀ i : ι, ∃ Ki : OpenComplex (U i),
            ∃ α : Ki ⟶
                (((moduleRestrictionToOpen X (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  K),
              CochainComplex.IsStrictlyPerfectRelativeToOpen Ki ∧ QuasiIso α

/-- A derived `\mathcal O_X`-module has a local pseudo-coherent presentation when one chosen
representative admits, for every degree bound `m`, a local strictly perfect approximation that is
cohomologically an isomorphism above `m` and an epimorphism in degree `m`. -/
def HasLocalPseudoCoherentPresentation (E : DMod) : Prop :=
  ∃ K : CochainComplex (Modules X) ℤ,
    ∃ _ : E ≅ ((DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DMod).obj K),
      ∀ m : ℤ,
        ∃ (ι : Type u) (U : ι → Opens X.carrier),
          iSup U = ⊤ ∧
            ∀ i : ι, ∃ Ki : OpenComplex (U i),
              ∃ α : Ki ⟶
                  (((moduleRestrictionToOpen X (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                    K),
                CochainComplex.IsStrictlyPerfectRelativeToOpen Ki ∧
                  (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
                    Epi (HomologicalComplex.homologyMap α m)

-- Proof sketch: if `E` has a local strictly perfect presentation, then those local models give
-- pseudo-coherent approximations in every degree and finite tor amplitude on each open by the
-- strictly perfect case. Conversely, refine to an open cover with bounded tor amplitude, use the
-- pseudo-coherent presentations in degree `a - 1`, and apply the local perfection criterion of
-- the source proof on each member of the cover.
/-- Lemma 20.49.5: for an object `E` of `D(\mathcal O_X)`, perfection is equivalent to being
pseudo-coherent and locally of finite tor dimension. -/
theorem perfect_iff_pseudoCoherent_and_locallyHasFiniteTorDimension
    (E : DMod) :
    HasLocalStrictlyPerfectPresentation E ↔
      HasLocalPseudoCoherentPresentation E ∧ LocallyHasFiniteTorDimension E := sorry

end DerivedCategory

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_6 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePullback (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived (f : X ⟶ Y) [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions on `Y`, use preservation of K-flatness by pullback,
-- and invoke the universal property of the total left derived functor.
/-- Pullback on homotopy categories admits a total left derived functor. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for module pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) \to D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive] :
    DModY ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DModY)
    (ModuleQis Y)

-- Proof sketch: combine the characterization of perfect objects by pseudo-coherence and local
-- finite tor dimension with Lemmas `20.47.3` and `20.48.4`, which show that derived pullback
-- preserves these two properties. Then apply the same characterization on `X`.
/-- Lemma 20.49.6: let `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` be a morphism of ringed
spaces and let `E` be an object of `D(\mathcal O_Y)`. If `E` is perfect in `D(\mathcal O_Y)`,
then the derived pullback `Lf^*E` is perfect in `D(\mathcal O_X)`. -/
theorem modulePullbackDerived_isPerfect
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive]
    (E : DModY) (hE : DerivedCategory.IsPerfect E) :
    DerivedCategory.IsPerfect ((modulePullbackDerived f).obj E) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_7 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: combine Lemma `20.49.5`, which characterizes perfect objects by
-- pseudo-coherence and local finite tor dimension, with Lemma `20.47.4 (1)` for the
-- pseudo-coherent part and Lemma `20.48.6 (1)` for the tor-amplitude part on each member of a
-- local open cover.
/-- Lemma 20.49.7 (1): let `(X, \mathcal O_X)` be a ringed space and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O_X)`. If `K` and `L` are
perfect, then `M` is perfect. -/
theorem isPerfect_obj₃_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₂ : DerivedCategory.IsPerfect T.obj₂) :
    DerivedCategory.IsPerfect T.obj₃ := sorry

-- Proof sketch: use Lemma `20.49.5` to reduce perfectness to pseudo-coherence plus local finite
-- tor dimension; then apply Lemma `20.47.4 (2)` and Lemma `20.48.6 (2)` to the distinguished
-- triangle and reassemble the two conditions.
/-- Lemma 20.49.7 (2): let `(X, \mathcal O_X)` be a ringed space and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O_X)`. If `K` and `M` are
perfect, then `L` is perfect. -/
theorem isPerfect_obj₂_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : DerivedCategory.IsPerfect T.obj₁) (h₃ : DerivedCategory.IsPerfect T.obj₃) :
    DerivedCategory.IsPerfect T.obj₂ := sorry

-- Proof sketch: again reduce via Lemma `20.49.5`, then use Lemma `20.47.4 (3)` for
-- pseudo-coherence and Lemma `20.48.6 (3)` for the local tor-amplitude bounds to propagate
-- perfectness to the first vertex.
/-- Lemma 20.49.7 (3): let `(X, \mathcal O_X)` be a ringed space and let
`K \to L \to M \to K[1]` be a distinguished triangle in `D(\mathcal O_X)`. If `L` and `M` are
perfect, then `K` is perfect. -/
theorem isPerfect_obj₁_of_distinguishedTriangle
    (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₂ : DerivedCategory.IsPerfect T.obj₂) (h₃ : DerivedCategory.IsPerfect T.obj₃) :
    DerivedCategory.IsPerfect T.obj₁ := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_8 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: by Lemma `20.49.5`, it is enough to prove that `K ⊗^L L` is pseudo-coherent and
-- locally of finite tor dimension. Lemma `20.47.5 (2)` gives pseudo-coherence of the derived
-- tensor product of pseudo-coherent objects, and Lemma `20.48.7` gives finite tor-amplitude after
-- tensoring; applying Lemma `20.49.5` again yields perfection.
/-- Lemma 20.49.8: let `(X, \mathcal O_X)` be a ringed space. If `K` and `L` are perfect objects
of `D(\mathcal O_X)`, then so is `K \otimes_{\mathcal O_X}^{\mathbf L} L`. -/
theorem tensor_isPerfect_of_isPerfect
    (K L : DMod) (hK : DerivedCategory.IsPerfect K) (hL : DerivedCategory.IsPerfect L) :
    DerivedCategory.IsPerfect (K ⊗ L) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_9 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: apply Lemma `20.49.5` to rewrite perfection of `K ⊞ L` as pseudo-coherence plus
-- local finite tor dimension, then use Lemmas `20.47.6 (3)` and `20.48.8 (1)` to descend these
-- two properties to `K`, and finally reassemble them with Lemma `20.49.5`.
/-- Lemma 20.49.9 (1): if `K ⊞ L` is a perfect object of `D(\mathcal O_X)`, then `K` is
perfect. -/
theorem isPerfect_left_of_biprod
    (K L : DModX) (hKL : DerivedCategory.IsPerfect (K ⊞ L)) :
    DerivedCategory.IsPerfect K := sorry

-- Proof sketch: as in part `(1)`, use Lemma `20.49.5` to pass to pseudo-coherence and local
-- finite tor dimension, then apply Lemmas `20.47.6 (4)` and `20.48.8 (2)` to the right summand
-- and conclude again via Lemma `20.49.5`.
/-- Lemma 20.49.9 (2): if `K ⊞ L` is a perfect object of `D(\mathcal O_X)`, then `L` is
perfect. -/
theorem isPerfect_right_of_biprod
    (K L : DModX) (hKL : DerivedCategory.IsPerfect (K ⊞ L)) :
    DerivedCategory.IsPerfect L := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_10 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

local notation "DModU" => DerivedCategory (openSubspaceModuleCategory X U)

-- Proof sketch: by Lemma `20.33.6 (2)`, the support hypothesis identifies `Rj_* E` with
-- extension by zero from `U`. Perfectness is local on `X`: on `U` this extension restricts to
-- `E`, hence is perfect, while on the open complement of the closed image of `T` it vanishes.
/-- Lemma 20.49.10: let `j : U ↪ X` be an open subspace of a ringed space and let `E` be a
perfect object of `D(\mathcal O_U)`. If the cohomology sheaves of `E` are supported on a subset
`T ⊆ U` whose image is closed in `X`, then `Rj_* E` is a perfect object of `D(\mathcal O_X)`. -/
theorem isPerfect_pushforwardFromOpen_of_isPerfect_of_cohomologySupported
    {T : Set X.carrier} (hT_closed : IsClosed T)
    (hTU : T ⊆ (U : Set X.carrier))
    (E : DModU)
    (hE_perfect : DerivedCategory.IsPerfect E)
    (hE_support : moduleDerivedCohomologySupportedOn
      ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))
      E
      (Subtype.val ⁻¹' T)) :
    DerivedCategory.IsPerfect ((moduleDerivedPushforwardFromOpen U).obj E) :=
  by
    sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_49_11 (from Chap20) -/
open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The degree-`i` cohomology `\mathcal O_X`-module of a derived `\mathcal O_X`-module `E`. -/
abbrev derivedCohomologyModule (X : RingedSpace.{u}) (E : ModuleDerived X) (i : ℤ) :
    (RingedSpace.Modules X) :=
  (DerivedCategory.homologyFunctor (Modules X) i).obj E

/-- The underlying type-valued presheaf of an `\mathcal O_X`-module. -/
abbrev underlyingPresheaf (X : RingedSpace.{u}) (ℱ : (RingedSpace.Modules X)) :
    TopCat.Presheaf (Type u) X :=
  ℱ.val.presheaf ⋙ forget Ab

/-- The stalk of an `\mathcal O_X`-module, regarded as an underlying type. -/
abbrev stalkType (X : RingedSpace.{u}) (ℱ : (RingedSpace.Modules X)) (x : X) : Type u :=
  TopCat.Presheaf.stalk (underlyingPresheaf X ℱ) x

/-- The stalk of an `\mathcal O_X`-module inherits its additive group structure. -/
instance stalkAddCommGroup (X : RingedSpace.{u}) (ℱ : (RingedSpace.Modules X)) (x : X) :
    AddCommGroup (stalkType X ℱ x) := sorry

/-- The stalk of an `\mathcal O_X`-module carries its natural `\mathcal O_{X, x}`-module
structure. -/
instance stalkModule (X : RingedSpace.{u}) (ℱ : (RingedSpace.Modules X)) (x : X) :
    Module (X.presheaf.stalk x) (stalkType X ℱ x) := sorry

/-- The stalk of the degree-`i` cohomology module of `E` at `x`, viewed as a type over the stalk
ring `\mathcal O_{X, x}`. -/
abbrev derivedCohomologyStalk (E : ModuleDerived X) (i : ℤ) (x : X) : Type u :=
  stalkType X (derivedCohomologyModule X E i) x

/-- The degree-`i` cohomology stalk of `E` at `x` is finite free over `\mathcal O_{X, x}`. -/
def cohomologyStalkIsFiniteFree (E : ModuleDerived X) (i : ℤ) (x : X) : Prop :=
  Module.Free (X.presheaf.stalk x) (derivedCohomologyStalk E i x) ∧
    Module.Finite (X.presheaf.stalk x) (derivedCohomologyStalk E i x)

/-- The set of points where every cohomology stalk of `E` is finite free over the corresponding
stalk ring. -/
def finiteFreeCohomologyStalkLocus (E : ModuleDerived X) : Set X :=
  {x | ∀ i : ℤ, cohomologyStalkIsFiniteFree E i x}

/-- The restriction of every cohomology sheaf of `E` to the open subspace `U` is finite locally
free, expressed by local triviality inside `U`. -/
def cohomologyIsFiniteLocallyFreeOnOpen (E : ModuleDerived X) (U : Opens X.carrier) : Prop :=
  ∀ i : ℤ, ∀ x : X, x ∈ U →
    ∃ V : Opens X.carrier, x ∈ V ∧ V ≤ U ∧
      ∃ I : Type u, Finite I ∧
        Nonempty ((derivedCohomologyModule X E i).over V ≅ SheafOfModules.free.{u} I)

-- Proof sketch: represent `E` locally by a strictly perfect complex. At a point whose cohomology
-- stalks are all finite free, apply Lemma `17.11.7` to make the top cohomology locally free and
-- Lemma `20.46.5` to split off the top term locally; then shorten the strict-perfect complex and
-- iterate on its length.
/-- Lemma 20.49.11: for a perfect derived `\mathcal O_X`-module on a ringed space whose stalk
rings are local, the locus where every cohomology stalk is a finite free `\mathcal O_{X, x}`-
module is open. -/
theorem isOpen_finiteFreeCohomologyStalkLocus
    (E : ModuleDerived X) (hperfect : DerivedCategory.IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsOpen (finiteFreeCohomologyStalkLocus E) := sorry

/-- The open subset where every cohomology stalk of `E` is finite free. -/
def finiteFreeCohomologyStalkOpen
    (E : ModuleDerived X) (hperfect : DerivedCategory.IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) : Opens X.carrier :=
  ⟨finiteFreeCohomologyStalkLocus E, isOpen_finiteFreeCohomologyStalkLocus E hperfect hlocal⟩

-- Proof sketch: every point of the locus admits, by the same local splitting argument as in the
-- source proof, a neighborhood on which the restricted cohomology sheaves are finite locally free
-- in all degrees; these neighborhoods lie inside the locus and cover the open subset above.
/-- On the finite-free cohomology-stalk locus of a perfect complex, all cohomology sheaves become
finite locally free after restriction. -/
theorem cohomologyIsFiniteLocallyFreeOnOpen_finiteFreeCohomologyStalkOpen
    (E : ModuleDerived X) (hperfect : DerivedCategory.IsPerfect E)
    (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    cohomologyIsFiniteLocallyFreeOnOpen E (finiteFreeCohomologyStalkOpen E hperfect hlocal) :=
  sorry

-- Proof sketch: a locally free trivialization on an open neighborhood inside `U` makes each
-- cohomology stalk finite free at points of that neighborhood. Applying this to every degree
-- shows that each point of `U` belongs to the locus by definition.
/-- Any open subset on which all cohomology sheaves of `E` are finite locally free is contained
in the finite-free cohomology-stalk locus. -/
theorem subset_finiteFreeCohomologyStalkLocus_of_cohomologyIsFiniteLocallyFreeOnOpen
    (E : ModuleDerived X) (U : Opens X.carrier)
    (hU : cohomologyIsFiniteLocallyFreeOnOpen E U) :
    (U : Set X) ⊆ finiteFreeCohomologyStalkLocus E := sorry

end

end AlgebraicGeometry.RingedSpace

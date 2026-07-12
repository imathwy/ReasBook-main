import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Shift.Quotient
import Mathlib.CategoryTheory.Triangulated.Functor
import StacksProject_2024.Chap20.Definition_20_26_14_Core

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 20.26.14 (derived exactness layer):
- primary domain: fixed-right-factor derived tensoring on `D(𝒪_X)`;
- sampled owner declarations:
  `derivedTensorProduct`,
  `derivedTensorProductCounit`,
  `Functor.CommShift`,
  `NatTrans.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: `Definition_20_26_14_Core` already owns the source-facing derived tensor
  product and its left-derived-functor API; this file only adds the heavier shift-compatibility
  and triangulated-exactness companions on that canonical owner.

Source/core/bridge triage:
- `source-facing`: the derived tensor product owner `derivedTensorProduct`;
- `core/canonical`: the imported core file providing the derived-functor construction and counit;
- `bridge/view`: the shift-counit comparison maps identifying the two shifted left-derived-functor
  structures needed to package `Functor.CommShift` on `derivedTensorProduct`.

Primitive vs derived:
- primitive data: the fixed right factor `ℱ : D(𝒪_X)` and the imported owner
  `derivedTensorProduct ℱ`;
- derived API: the `CommShift` and `IsTriangulated` instance surface. -/

variable {X : RingedSpace.{u}}
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : RingedSpace.Modules X, ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

/-- Helper for Definition 20.26.14: the category of `𝒪_X`-modules on a ringed space is abelian. -/
local instance abelianModules20_26_14 : Abelian (RingedSpace.Modules X) := inferInstance

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "Complexes" => CochainComplex (RingedSpace.Modules X) ℤ
local notation "KMod" => HomotopyCategory (RingedSpace.Modules X) (up ℤ)
local notation "Q" =>
  (HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ) : Complexes ⥤ KMod)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- Helper for Definition 20.26.14: the quotient-lift tensor owner on `K(𝒪_X)` before
postcomposing with `Qh`. -/
private noncomputable abbrev derivedTensorSourceHomotopyOwner
    (K : Complexes) :
    KMod ⥤ KMod :=
  CategoryTheory.Quotient.lift
    (homotopic (RingedSpace.Modules X) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙ Q)
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h
          (𝟙 K)
          (curriedTensor (RingedSpace.Modules X))
          (up ℤ)))

/-- Helper for Definition 20.26.14: the public source functor is the homotopy owner followed by
the derived-category localization functor `Qh`. -/
private theorem derivedTensorSourceHomotopyFunctorOfComplex_eq_owner_comp_qh
    (K : Complexes) :
    derivedTensorSourceHomotopyFunctorOfComplex K =
      derivedTensorSourceHomotopyOwner (X := X) K ⋙ Qh := by
  rfl

/-- Helper for Definition 20.26.14: the homotopy owner is the strict quotient factorization of
the fixed-right tensor functor followed by the homotopy quotient. -/
private theorem derivedTensorSourceHomotopyOwner_comp_quotient
    (K : Complexes) :
    Q ⋙ derivedTensorSourceHomotopyOwner (X := X) K =
      (((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙ Q := by
  -- Proof comment: this is the defining strict factorization property of `Quotient.lift`.
  simpa [derivedTensorSourceHomotopyOwner] using
    (CategoryTheory.Quotient.lift_spec
      (r := homotopic (RingedSpace.Modules X) (up ℤ))
      ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙ Q)
      (fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 K)
            (curriedTensor (RingedSpace.Modules X))
            (up ℤ))))

/-- Helper for Definition 20.26.14: the homotopy-level tensor owner already commutes with shifts
before passing to the derived category. -/
private noncomputable instance derivedTensorSourceHomotopyOwner_commShift
    (K : Complexes) :
    (derivedTensorSourceHomotopyOwner (X := X) K).CommShift ℤ := by
  let F : Complexes ⥤ KMod :=
    (((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙ Q
  let _ : F.CommShift ℤ := by
    infer_instance
  -- Proof comment: expose the owner exactly as the quotient lift of the fixed-right tensor
  -- functor, so the localization shift API applies to that owner directly.
  change
    (CategoryTheory.Quotient.lift
      (homotopic (RingedSpace.Modules X) (up ℤ))
      F
      (fun _ _ _ _ ⟨h⟩ ↦
        HomotopyCategory.eq_of_homotopy _ _
          (HomologicalComplex.mapBifunctorMapHomotopy₁ h
            (𝟙 K)
            (curriedTensor (RingedSpace.Modules X))
            (up ℤ)))).CommShift ℤ
  infer_instance

private noncomputable instance derivedTensorSourceHomotopyFunctorOfComplex_commShift
    (K : Complexes) :
    (derivedTensorSourceHomotopyFunctorOfComplex K).CommShift ℤ := by
  let F : Complexes ⥤ KMod :=
    (((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj K) ⋙ Q
  let _ : F.CommShift ℤ := by
    infer_instance
  -- Proof comment: keep the source owner in the direct quotient-lift spelling so the generic
  -- localization shift API can recognize it without an additional normalization bridge.
  let hComm :
      (((CategoryTheory.Quotient.lift
        (homotopic (RingedSpace.Modules X) (up ℤ))
        F
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h
              (𝟙 K)
              (curriedTensor (RingedSpace.Modules X))
              (up ℤ)))) ⋙ Qh).CommShift ℤ) := by
    infer_instance
  simpa [derivedTensorSourceHomotopyFunctorOfComplex] using hComm

private noncomputable instance derivedTensorSourceFunctor_commShift
    (ℱ : DMod) :
    (derivedTensorSourceFunctor ℱ).CommShift ℤ := by
  simpa [derivedTensorSourceFunctor] using
    (derivedTensorSourceHomotopyFunctorOfComplex_commShift
      ((DerivedCategory.Q : Complexes ⥤ DMod).objPreimage ℱ))

/-- Helper for Definition 20.26.14: whiskering the forward map of `Functor.leftDerivedNatIso`
by the localization functor and then composing with the target counit recovers the source
comparison morphism. -/
private theorem leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit
    {A B H : Type*} [Category A] [Category B] [Category H]
    {L : A ⥤ B} {W : MorphismProperty A} [L.IsLocalization W]
    {F F' : A ⥤ H} {LF LF' : B ⥤ H}
    {α : L ⋙ LF ⟶ F} {α' : L ⋙ LF' ⟶ F'}
    [LF.IsLeftDerivedFunctor α W] [LF'.IsLeftDerivedFunctor α' W]
    (e : F' ≅ F) :
    Functor.whiskerLeft L (Functor.leftDerivedNatIso LF' LF α' α W e).hom ≫ α =
      α' ≫ e.hom := by
  -- Proof comment: expand `leftDerivedNatIso` to the underlying `leftDerivedNatTrans`, then use
  -- the defining factorization identity of the left-derived comparison.
  simpa [Functor.leftDerivedNatIso] using
    (Functor.leftDerivedNatTrans_fac LF' LF α' α W e.hom)

/-- The derived tensor product endofunctor `- ⊗^L ℱ` commutes with shifts. -/
noncomputable instance derivedTensorProduct_commShift
    (ℱ : DMod) :
    (derivedTensorProduct ℱ).CommShift ℤ := by
  -- Proof comment: the generic `totalLeftDerived` instance supplies the derived shift
  -- compatibility once the source owner has its shift structure.
  -- TODO: either recover the missing `CommShift` instance on
  -- `((derivedTensorSourceFunctor ℱ).totalLeftDerived Qh Qis)` from the exact owner API used in
  -- Chapter 21, or build the explicit shifted left-derived witness described by Agent C's plan.
  sorry

/- The defining counit of the left-derived-functor owner is compatible with the shift structures
on the source and target functors exhibited above. -/
/-- The canonical counit `Qh ⋙ derivedTensorProduct ℱ ⟶ derivedTensorSourceFunctor ℱ` commutes
with shifts. -/
noncomputable instance derivedTensorProductCounit_commShift
    (ℱ : DMod) :
    NatTrans.CommShift (derivedTensorProductCounit ℱ) ℤ := by
  -- Proof comment: recall the canonical total-left-derived counit rather than reproving shift
  -- compatibility for the chapter-local counit wrapper.
  -- TODO: after `derivedTensorProduct_commShift` is rebuilt in the correct owner spelling,
  -- rewrite `derivedTensorProductCounit ℱ` back to `totalLeftDerivedCounit` through a small
  -- definitional bridge and reuse the standard counit `CommShift` instance.
  sorry

-- Proof sketch: the homotopy-category tensor functor with fixed right factor is triangulated, and
-- its total left derived functor on `D(𝒪_X)` inherits triangulated exactness.
/-- The derived tensor product endofunctor on `D(𝒪_X)` is exact in the triangulated sense. -/
noncomputable instance derivedTensorProduct_isTriangulated
    (ℱ : DMod) :
    (derivedTensorProduct ℱ).IsTriangulated := by
  -- Proof comment: once normalized to the canonical total left-derived owner, triangulated
  -- exactness comes from the generic derived-functor API.
  -- TODO: once the public `CommShift` instance is in place in the canonical owner spelling,
  -- normalize `derivedTensorProduct ℱ` to `totalLeftDerived` and let the generic exact-functor
  -- API close the triangulatedness goal.
  sorry

end AlgebraicGeometry.RingedSpace

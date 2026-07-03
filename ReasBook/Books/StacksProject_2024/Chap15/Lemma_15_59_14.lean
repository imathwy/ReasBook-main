import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import StacksProject_2024.Chap13.Remark_13_10_9
import StacksProject_2024.Chap15.Lemma_15_58_3
import StacksProject_2024.Chap15.Definition_15_59_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory
open BraidedCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable [∀ (K₁ K₂ : CochainComplex (ModuleCat R) ℤ),
  CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat R))]

/- Domain-style sampling for Lemma 15.59.14:
- primary domain: monoidal localization of the homotopy category of cochain complexes, and its
  comparison with the derived tensor product on `D(R)`;
- sampled owner declarations:
  `homotopyCategory_moduleCat_symmetric_category`,
  `LocalizedMonoidal`,
  `Functor.totalLeftDerived`,
  `derivedTensorProduct`;
- best owner abstraction: the canonical owner of commutativity for derived tensor product is the
  symmetric monoidal structure on `DerivedCategory (ModuleCat R)` induced from the symmetric
  monoidal structure on `HomotopyCategory (ModuleCat R) (up ℤ)`, with the notation
  `K ⊗[R]^L L` as the source-facing bridge to the owner tensor;
- primitive vs. derived:
  primitive data are the symmetric monoidal structure on `K(R)` from Lemma `15.58.3`, the
  monoidal stability of quasi-isomorphisms, and the localized monoidal tensor on `D(R)`;
  the tensor-vs-derived-tensor comparison and the commutativity statement below are derived API;
- source/core/bridge triage:
  `source-facing`: the canonical commutativity of `K ⊗[R]^L L`;
  `core/canonical`: the `MonoidalCategory`/`SymmetricCategory` instances on `D(R)`;
  `bridge/view`: the comparison theorem identifying the localized tensor object with
  `K ⊗[R]^L L`;
- layer: this file is a `bridge/view` owner for the source-facing derived-tensor symmetry, so it
  should reuse the localized symmetric-monoidal owner directly rather than keep a parallel
  standalone existence theorem. -/

local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

-- Proof sketch: quasi-isomorphisms in `K(R)` are detected on homology, tensoring in the homotopy
-- category comes from the symmetric monoidal tensor product on complexes from Lemma `15.58.3`,
-- and tensoring two quasi-isomorphisms again yields a quasi-isomorphism.
/-- Quasi-isomorphisms in the homotopy category `K(R)` are stable under tensor product. -/
private theorem homotopyCategory_quasiIso_isMonoidal :
    (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)).IsMonoidal := by
  sorry

/-- The monoidal category structure on `D(R)` obtained by localizing the tensor product on the
homotopy category `K(R)`. -/
noncomputable instance : MonoidalCategory DMod := by
  let _ : (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  change MonoidalCategory
    (LocalizedMonoidal Qh Qis (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KMod))))
  infer_instance

-- Proof sketch: localize the symmetric monoidal structure on `K(R)` along quasi-isomorphisms,
-- using the preceding monoidal stability theorem.
/-- The derived category `D(R)` inherits the symmetric monoidal structure obtained by localizing
the tensor product on `K(R)`. -/
noncomputable instance : SymmetricCategory DMod := by
  let _ : (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  change SymmetricCategory
    (LocalizedMonoidal Qh Qis (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KMod))))
  infer_instance

noncomputable instance : (DerivedCategory.Qh : KMod ⥤ DMod).Monoidal := by
  let _ : (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance :
      (Localization.Monoidal.toMonoidalCategory
        Qh
        Qis
        (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KMod)))).Monoidal)

private noncomputable def derivedCategory_tensorLeftComparisonIso
    (L : DMod) :
    Qh ⋙ MonoidalCategory.tensorLeft L ≅
      MonoidalCategory.tensorRight (tensorRightRepresentative L) ⋙ Qh := by
  exact
    Functor.isoWhiskerLeft Qh
        ((tensoringLeft DMod).mapIso
          (tensorRightRepresentativeIso L)).symm ≪≫
      Functor.Monoidal.commTensorLeft Qh
        (tensorRightRepresentative L) ≪≫
      Functor.isoWhiskerRight
        (tensorLeftIsoTensorRight (tensorRightRepresentative L))
        Qh

-- Proof sketch: the comparison isomorphism identifies `tensorLeft L` with a localization of the
-- underived tensor functor, and that source functor is already inverted on quasi-isomorphisms.
private noncomputable instance derivedCategory_tensorLeft_isLeftDerived
    (L : DMod) :
    (MonoidalCategory.tensorLeft L).IsLeftDerivedFunctor
      (derivedCategory_tensorLeftComparisonIso L).hom Qis := by
  simpa using
    (Functor.isLeftDerivedFunctor_of_inverts Qis (MonoidalCategory.tensorLeft L)
      (derivedCategory_tensorLeftComparisonIso L))

private noncomputable def tensorLeftIsoDerivedTensorProduct
    (L : DMod) :
    MonoidalCategory.tensorLeft L ≅ derivedTensorProduct L := by
  let F : KMod ⥤ DMod :=
    MonoidalCategory.tensorRight (tensorRightRepresentative L) ⋙ Qh
  let _ : F.HasLeftDerivedFunctor Qis := tensorRightCompQh_hasLeftDerivedFunctor L
  let G : DMod ⥤ DMod :=
    F.totalLeftDerived Qh Qis
  let e : MonoidalCategory.tensorLeft L ≅ G :=
    Functor.leftDerivedNatIso
      (MonoidalCategory.tensorLeft L)
      G
      (derivedCategory_tensorLeftComparisonIso L).hom
      (Functor.totalLeftDerivedCounit
        F
        Qh
        Qis)
      Qis
      (Iso.refl F)
  simpa [F, G, derivedTensorProduct] using e

-- Proof sketch: the localized tensor product on `D(R)` is the total left derived functor of
-- tensoring with a fixed right factor in `K(R)`, hence agrees with the source-facing derived tensor
-- product notation from Definition `15.59.13`.
/-- The localized tensor product on `D(R)` is canonically isomorphic to the source-facing derived
tensor product `K ⊗[R]^L L`. -/
noncomputable def derivedCategory_tensorObj_iso_derivedTensorProduct
    (K L : DMod) :
    K ⊗ L ≅ (derivedTensorProduct L).obj K :=
  β_ K L ≪≫ (tensorLeftIsoDerivedTensorProduct L).app K

/-- The fixed-right-factor tensor functor on `D(R)` is canonically isomorphic to the source-facing
derived tensor product functor `- ⊗[R]^L L`. -/
noncomputable def tensoringRightIsoDerivedTensorProduct
    (L : DMod) :
    (tensoringRight DMod).obj L ≅ derivedTensorProduct L :=
  NatIso.ofComponents
    (fun K ↦ derivedCategory_tensorObj_iso_derivedTensorProduct K L)
    (fun {_ _} _ ↦ by
      sorry)

@[simp] theorem tensoringRightIsoDerivedTensorProduct_hom_app (L K : DMod) :
    (tensoringRightIsoDerivedTensorProduct L).hom.app K =
      (derivedCategory_tensorObj_iso_derivedTensorProduct K L).hom :=
  rfl

@[simp] theorem tensoringRightIsoDerivedTensorProduct_inv_app (L K : DMod) :
    (tensoringRightIsoDerivedTensorProduct L).inv.app K =
      (derivedCategory_tensorObj_iso_derivedTensorProduct K L).inv :=
  rfl

-- Proof sketch: compare both derived-tensor objects with the owner tensor `K ⊗ L` on `D(R)`, and
-- then apply the braiding isomorphism of the symmetric monoidal structure on `D(R)`.
/-- Lemma 15.59.14: for derived `R`-complexes `K^•` and `L^•`, the derived tensor products
`K^• \otimes_R^{\mathbf L} L^•` and `L^• \otimes_R^{\mathbf L} K^•` are canonically isomorphic,
functorially in both complexes, with the chain-level symmetry using the sign `(-1)^(pq)` on
`K^p ⊗_R L^q`. -/
noncomputable def derivedTensorProduct_comm (K L : DMod) :
    (derivedTensorProduct L).obj K ≅ (derivedTensorProduct K).obj L :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct K L).symm ≪≫
    β_ K L ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct L K

end

end CategoryTheory

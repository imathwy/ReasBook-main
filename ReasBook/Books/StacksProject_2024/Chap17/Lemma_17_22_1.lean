import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

/-
Domain-style sampling for Lemma 17.22.1:
- primary domain: tensor/internal-Hom calculus in braided monoidal closed categories of
  `\mathcal O_X`-modules;
- inspected owner declarations:
  notation `A ⟶[C] B`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`,
  `MonoidalCategory.tensorLeftTensor`,
  `CategoryTheory.ihom.adjunction`,
  `CategoryTheory.Adjunction.rightAdjointUniq`,
- owner abstraction: the canonical internal-Hom owner
  `MonoidalClosed.internalHomAdjunction₂`, whose objectwise surface is the notation
  `A ⟶[C] B`; the braided tensor-left comparison is only a bridge from the Stacks tensor order
  to that owner;
- primitive data: the ambient monoidal-closed structure and the modules `ℱ`, `𝒢`, `ℋ`;
- derived API: the textbook objectwise isomorphism
  `((ℱ ⊗ 𝒢) ⟶[ModX] ℋ) ≅ (ℱ ⟶[ModX] (𝒢 ⟶[ModX] ℋ))` and its companion naturality lemmas.

Source/core/bridge triage:
- `source-facing`: the textbook objectwise isomorphism
  `internalHomTensorIso ℱ 𝒢 ℋ`, together with its functoriality in `ℱ`, `𝒢`, and `ℋ`;
- `core/canonical`: notation `A ⟶[C] B` and `MonoidalClosed.internalHomAdjunction₂`;
- `bridge/view`: the braided tensor-left comparison built from `tensorLeftTensor` and
  `rightAdjointUniq`.

The public surface should therefore stay at the textbook object level and reuse the canonical
internal-Hom owner directly, while the functor-level right-adjoint-uniqueness comparison remains a
thin private bridge. -/
namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [BraidedCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
set_option quotPrecheck false in
local notation A " ⟶[ModX] " B:10 => ((ihom A).obj B)

private noncomputable def internalHomTensorNatIso
    (ℱ 𝒢 : ModX) :
    ihom (ℱ ⊗ 𝒢) ≅ ihom 𝒢 ⋙ ihom ℱ :=
  Adjunction.rightAdjointUniq
    (ihom.adjunction (ℱ ⊗ 𝒢))
    (((ihom.adjunction ℱ).comp (ihom.adjunction 𝒢)).ofNatIsoLeft
      (((MonoidalCategory.tensoringLeft (RingedSpace.Modules X)).mapIso (β_ ℱ 𝒢)) ≪≫
        MonoidalCategory.tensorLeftTensor 𝒢 ℱ).symm)

/-- Lemma 17.22.1: for `\mathcal O_X`-modules `ℱ`, `𝒢`, and `ℋ`, the internal Hom out of
`ℱ ⊗ 𝒢` is canonically isomorphic to the iterated internal Hom. On the theorem surface this is
attached directly to the canonical internal-Hom owner
`MonoidalClosed.internalHomAdjunction₂`. -/
noncomputable def internalHomTensorIso
    (ℱ 𝒢 ℋ : ModX) :
    ((ℱ ⊗ 𝒢) ⟶[ModX] ℋ) ≅ (ℱ ⟶[ModX] (𝒢 ⟶[ModX] ℋ)) :=
  (internalHomTensorNatIso ℱ 𝒢).app ℋ

private theorem internalHomTensorNatIso_natural_in_first_variable
    {ℱ ℱ' 𝒢 : ModX} (f : ℱ ⟶ ℱ') :
    MonoidalClosed.pre (f ⊗ₘ 𝟙 𝒢) ≫ (internalHomTensorNatIso ℱ 𝒢).hom =
      (internalHomTensorNatIso ℱ' 𝒢).hom ≫
        Functor.whiskerLeft (ihom 𝒢) (MonoidalClosed.pre f) := sorry

private theorem internalHomTensorNatIso_natural_in_second_variable
    {ℱ 𝒢 𝒢' : ModX} (g : 𝒢 ⟶ 𝒢') :
    MonoidalClosed.pre (𝟙 ℱ ⊗ₘ g) ≫ (internalHomTensorNatIso ℱ 𝒢).hom =
      (internalHomTensorNatIso ℱ 𝒢').hom ≫
        Functor.whiskerRight (MonoidalClosed.pre g) (ihom ℱ) := sorry

/-- Lemma 17.22.1 is contravariantly functorial in the first variable `ℱ`, objectwise at `ℋ`. -/
theorem internalHomTensorIso_natural_in_first_variable
    {ℱ ℱ' 𝒢 ℋ : ModX} (f : ℱ ⟶ ℱ') :
    (MonoidalClosed.pre (f ⊗ₘ 𝟙 𝒢)).app ℋ ≫
        (internalHomTensorIso ℱ 𝒢 ℋ).hom =
      (internalHomTensorIso ℱ' 𝒢 ℋ).hom ≫
        (MonoidalClosed.pre f).app (𝒢 ⟶[ModX] ℋ) := by
  simpa using
    NatTrans.congr_app (internalHomTensorNatIso_natural_in_first_variable f) ℋ

/-- Lemma 17.22.1 is contravariantly functorial in the second variable `𝒢`, objectwise at `ℋ`. -/
theorem internalHomTensorIso_natural_in_second_variable
    {ℱ 𝒢 𝒢' ℋ : ModX} (g : 𝒢 ⟶ 𝒢') :
    (MonoidalClosed.pre (𝟙 ℱ ⊗ₘ g)).app ℋ ≫
        (internalHomTensorIso ℱ 𝒢 ℋ).hom =
      (internalHomTensorIso ℱ 𝒢' ℋ).hom ≫
        (ihom ℱ).map ((MonoidalClosed.pre g).app ℋ) := by
  simpa using
    NatTrans.congr_app (internalHomTensorNatIso_natural_in_second_variable g) ℋ

/-- Lemma 17.22.1 is functorial in the third variable `ℋ`. -/
theorem internalHomTensorIso_natural_in_third_variable
    (ℱ 𝒢 : ModX) {ℋ ℋ' : ModX} (h : ℋ ⟶ ℋ') :
    (ihom (ℱ ⊗ 𝒢)).map h ≫ (internalHomTensorIso ℱ 𝒢 ℋ').hom =
      (internalHomTensorIso ℱ 𝒢 ℋ).hom ≫
        (ihom 𝒢 ⋙ ihom ℱ).map h :=
  (internalHomTensorNatIso ℱ 𝒢).hom.naturality h

end AlgebraicGeometry.RingedSpace

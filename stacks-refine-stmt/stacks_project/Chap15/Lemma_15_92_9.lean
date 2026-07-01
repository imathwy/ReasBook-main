import Mathlib
import stacks_project.Chap10.Lemma_10_24_5
import stacks_project.Chap15.Lemma_15_74_1
import stacks_project.Chap15.Lemma_15_92_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "Cpx" => CochainComplex (ModuleCat A) ℤ
local notation "single₀" => (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ) : ModuleCat A ⥤ DMod)

private abbrev singleZeroCpx (M : ModuleCat A) : Cpx :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M

private noncomputable instance : (DerivedCategory.Q : Cpx ⥤ DMod).Monoidal := by
  change (((HomotopyCategory.quotient (ModuleCat A) (up ℤ)) ⋙
      (DerivedCategory.Qh : HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DMod))).Monoidal
  infer_instance

section Monoidal

local instance : MonoidalCategory DMod := inferInstance

private noncomputable abbrev localizationAwayTensorLinearEquiv
    (f g : A) :
    Localization.Away f ⊗[A] Localization.Away g ≃ₗ[A] Localization.Away (f * g) :=
  ((LocalizedModule.equivTensorProduct (Submonoid.powers f) (Localization.Away g)).symm.restrictScalars A) ≪≫ₗ
    awayMulLinearEquiv g f A ≪≫ₗ
      awayEqLinearEquiv A (mul_comm g f)

private noncomputable abbrev localizationAwayTensorModuleIso
    (f g : A) :
    ModuleCat.of A (Localization.Away f ⊗[A] Localization.Away g) ≅
      ModuleCat.of A (Localization.Away (f * g)) :=
  (localizationAwayTensorLinearEquiv f g).toModuleIso

private theorem singleZeroTensorComplex_eq_tensorObj
    (M N : ModuleCat A) :
    singleZeroCpx (ModuleCat.of A ((↑M) ⊗[A] ↑N)) =
      HomologicalComplex.tensorObj (singleZeroCpx M) (singleZeroCpx N) := by
  sorry

private noncomputable def singleZeroDerivedTensorModuleIso
    (M N : ModuleCat A) :
    ((single₀).obj M ⊗[A]^L (single₀).obj N) ≅
      (single₀).obj (ModuleCat.of A ((↑M) ⊗[A] ↑N)) :=
  ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (ModuleCat.of A ((↑M) ⊗[A] ↑N))).symm) ≪≫
    (DerivedCategory.Q.mapIso (eqToIso (singleZeroTensorComplex_eq_tensorObj M N))) ≪≫
      (Functor.Monoidal.μIso (DerivedCategory.Q : Cpx ⥤ DMod) (singleZeroCpx M) (singleZeroCpx N)).symm ≪≫
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M) ⊗ᵢ
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app N)) ≪≫
          derivedCategory_tensorObj_iso_derivedTensorProduct ((single₀).obj M) ((single₀).obj N)).symm

private noncomputable def localizationAwayTensorIso
    (f g : A) :
    ((single₀).obj (ModuleCat.of A (Localization.Away f)) ⊗[A]^L
      (single₀).obj (ModuleCat.of A (Localization.Away g))) ≅
      (single₀).obj (ModuleCat.of A (Localization.Away (f * g))) :=
  singleZeroDerivedTensorModuleIso
      (ModuleCat.of A (Localization.Away f))
      (ModuleCat.of A (Localization.Away g)) ≪≫
    (single₀).mapIso (localizationAwayTensorModuleIso f g)

/- Domain-style sampling for Lemma 15.92.9:
- primary domain: localization-away objects `T(K, f)` in the closed monoidal derived category
  `D(A)`;
- sampled owner declarations:
  `CategoryTheory.DerivedCategory.localizationAwayT`,
  `CategoryTheory.derivedInternalHomTensorIso`,
  `awayMulLinearEquiv`,
  `CategoryTheory.DerivedCategory.localizationAwayT_isDerivedLimit`,
  `CategoryTheory.derivedInternalHom_comp`;
- best owner abstraction: the chapter owner `localizationAwayT H f K` for the textbook object
  `T(K, f)`;
- primitive data: `H : RHomPkg`, `f g : A`, and `K : DMod`;
- derived API: the product-localization comparison below.

Layer triage:
- `source-facing`: `localizationAwayT_mul`;
- `core/canonical`: `localizationAwayT H f K` and the currying comparison
  `derivedInternalHomTensorIso`;
- `bridge/view`: the identification of iterated away localizations with localization away from
  `f * g`, concretely routed through the module-side owner `awayMulLinearEquiv` on
  `Localization.Away g` and then transported to degree-zero objects in `D(A)`, expressed as an
  object-level `Iso`. -/

-- Proof sketch: combine the tensor-Hom currying comparison from Lemma `15.74.1` with the
-- module-side owner `awayMulLinearEquiv` identifying iterated away localization with
-- localization away from `f * g`, transported to the degree-zero objects `A_f`, `A_g`, and
-- `A_{fg}` in `D(A)`.
/-- The canonical comparison morphism
`T(T(K, g), f) ⟶ T(K, fg)` obtained by currying together the two localization-away internal-Hom
owners and then identifying the degree-zero localized tensor factor with `A_{fg}[0]`. -/
private noncomputable def localizationAwayT_mul_hom
    (H : RHomPkg) (f g : A) (K : DMod) :
    localizationAwayT H f (localizationAwayT H g K) ⟶ localizationAwayT H (f * g) K :=
  (derivedInternalHomTensorIso H
      ((single₀).obj (ModuleCat.of A (Localization.Away f)))
      ((single₀).obj (ModuleCat.of A (Localization.Away g)))
      K).hom ≫
    derivedInternalHomMap H (localizationAwayTensorIso f g).inv (𝟙 K)

private theorem localizationAwayT_mul_hom_isIso
    (H : RHomPkg) (f g : A) (K : DMod) :
    IsIso (localizationAwayT_mul_hom H f g K) := by
  sorry

/-- Lemma 15.92.9: the textbook localization-away object satisfies
`T(T(K, g), f) ≃ T(K, fg)`. This is the owner-level form of the iterated derived internal-Hom
comparison for the degree-zero localization objects `A_f`, `A_g`, and `A_{fg}`. -/
noncomputable abbrev localizationAwayT_mul
    (H : RHomPkg) (f g : A) (K : DMod) :
    localizationAwayT H f (localizationAwayT H g K) ≅ localizationAwayT H (f * g) K := by
  letI := localizationAwayT_mul_hom_isIso H f g K
  exact asIso (localizationAwayT_mul_hom H f g K)

end Monoidal

end

end CategoryTheory.DerivedCategory

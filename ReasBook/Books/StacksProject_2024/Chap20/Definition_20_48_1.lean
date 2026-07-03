import Mathlib
import StacksProject_2024.Chap20.Definition_20_26_14
import StacksProject_2024.Chap20.Lemma_20_32_2
import StacksProject_2024.Chap20.Lemma_20_32_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AlgebraicGeometry.RingedSpace

section

/-
Domain-style sampling for Definition 20.48.1:
- primary domain: tor-amplitude and finite tor dimension in `D(\mathcal O_X)`;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionToOpenDerived`,
  `AlgebraicGeometry.RingedSpace.restrictedModuleDerivedOnOpen`,
  `CategoryTheory.HasTorAmplitudeIn`,
  `CategoryTheory.HasFiniteTorDimension`;
- best owner abstraction: the source-facing owners in this file are the ringed-space predicates
  `HasTorAmplitudeIn`, `HasFiniteTorDimension`, and `LocallyHasFiniteTorDimension`; the tensor
  construction and the passage to open subspaces are already canonically owned upstream.

Source/core/bridge triage:
- `source-facing`: the ringed-space tor-dimension predicates from Definition 20.48.1;
- `core/canonical`: `derivedTensorProduct`;
- `bridge/view`: restriction to open subspaces via `moduleRestrictionToOpenDerived` and
  `restrictedModuleDerivedOnOpen`.

Primitive vs derived:
- primitive data: the derived object `E`, interval bounds `a, b`, and the restricted objects on an
  open cover;
- derived API: local finite tor dimension on an open cover and the module-specialization
  predicate.
-/

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

local notation "ModX" => (RingedSpace.Modules X)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor ModX
/-- Definition 20.48.1 (1): an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]`
if for every `\mathcal O_X`-module `\mathcal F`, the derived tensor product
`E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` has vanishing homology outside `[a, b]`. -/
def HasTorAmplitudeIn (E : DMod) (a b : ℤ) : Prop :=
  ∀ (ℱ : ModX) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((H i).obj ((derivedTensorProduct ((single0).obj ℱ)).obj E))

-- Proof sketch: unfold `HasTorAmplitudeIn`; it is exactly the defining homology-vanishing
-- condition for `E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` outside the interval
-- `[a, b]`.
/-- An object of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` exactly when derived tensoring
with every degree-zero module sheaf has vanishing homology outside `[a, b]`. -/
theorem hasTorAmplitudeIn_iff (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ (ℱ : ModX) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((H i).obj ((derivedTensorProduct ((single0).obj ℱ)).obj E)) := Iff.rfl

/-- Definition 20.48.1 (2): an object of `D(\mathcal O_X)` has finite tor dimension if it has
tor-amplitude in some finite interval `[a, b]`. -/
def HasFiniteTorDimension (E : DMod) : Prop :=
  ∃ a b : ℤ, HasTorAmplitudeIn E a b

-- Proof sketch: unfold `HasFiniteTorDimension`; it is exactly the existence of a finite
-- tor-amplitude interval.
/-- An object of `D(\mathcal O_X)` has finite tor dimension exactly when it has tor-amplitude in
some finite interval. -/
theorem hasFiniteTorDimension_iff (E : DMod) :
    HasFiniteTorDimension E ↔ ∃ a b : ℤ, HasTorAmplitudeIn E a b :=
  Iff.rfl

section LocalTorDimension

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

private abbrev HasFiniteTorDimensionOnOpen (U : Opens X.carrier) (E : DMod) : Prop :=
  HasFiniteTorDimension (restrictedModuleDerivedOnOpen U E)

/-- Definition 20.48.1 (3): an object of `D(\mathcal O_X)` locally has finite tor dimension if
there is an open covering of `X` on whose members its restriction has finite tor dimension. -/
def LocallyHasFiniteTorDimension (E : DMod) : Prop :=
  ∃ (ι : Type v) (U : ι → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i, HasFiniteTorDimensionOnOpen (U i) E

-- Proof sketch: unfold `LocallyHasFiniteTorDimension`; it is exactly the existence of an indexed
-- open cover on which the restricted derived object has finite tor dimension.
end LocalTorDimension

/-- Definition 20.48.1 (4): an `\mathcal O_X`-module `\mathcal F` has tor dimension at most `d`
if its degree-zero derived object `\mathcal F[0]` has tor-amplitude in `[-d, 0]`. -/
def ModuleHasTorDimensionLE (ℱ : ModX) (d : ℕ) : Prop :=
  HasTorAmplitudeIn ((single0).obj ℱ) (-((d : ℤ))) 0

-- Proof sketch: unfold `ModuleHasTorDimensionLE`; it is exactly the tor-amplitude condition for
-- the degree-zero derived object `\mathcal F[0]` with bounds `[-d, 0]`.
/-- An `\mathcal O_X`-module has tor dimension at most `d` exactly when its degree-zero derived
object has tor-amplitude in `[-d, 0]`. -/
theorem moduleHasTorDimensionLE_iff (ℱ : ModX) (d : ℕ) :
    ModuleHasTorDimensionLE ℱ d ↔
      HasTorAmplitudeIn ((single0).obj ℱ) (-((d : ℤ))) 0 := Iff.rfl

end

end AlgebraicGeometry.RingedSpace

import Mathlib
import stacks_project.Chap18.Lemma_18_19_2
import stacks_project.Chap21.Lemma_21_20_4

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false
set_option linter.unusedSectionVars false

namespace SheafOfModules.RingedSite

section

variable (X : RingedSite.{u, v})

local notation "Mod" => RingedSite.Hom.ModuleCat X
local notation "DMod" => RingedSite.Hom.ModuleDerived X
local notation "H" => DerivedCategory.homologyFunctor Mod
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

variable [Abelian Mod]
variable [CategoryWithHomology Mod]
variable (hMon : MonoidalCategoryStruct DMod)

local instance instMonoidalCategoryStructDMod : MonoidalCategoryStruct DMod := hMon

private abbrev tensorSingle0 (E : DMod) (ℱ : Mod) : DMod :=
  E ⊗ ((single0).obj ℱ)

/- Domain-style sampling for Definition 21.46.1:
- primary domain: tor-amplitude and local tor dimension in the derived category of modules on a
  ringed site;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSite.localization`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `RingedSite.ofCommRingSheaf`;
- best owner abstraction: the source-facing predicates `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`, `LocallyHasFiniteTorDimension`, and `ModuleHasTorDimensionLE` depend
  only on the ambient ringed site `X`, so their owner-level parameters should be `ModuleCat X`,
  `ModuleDerived X`, `X.siteTopology.Cover`, and `X.localization U` rather than a chosen site
  presentation `(C, J, 𝒪)`;
- primitive data: an object of `D(\mathcal O_X)`, interval bounds, and degree-zero module inputs;
- derived API: the finite-tor-dimension and module-level specializations, plus the localized
  specialization below.

Source/core/bridge triage:
- `source-facing`: the tor-amplitude, finite-tor-dimension, and module tor-dimension predicates;
- `core/canonical`: `RingedSite.Hom.ModuleCat`, `RingedSite.Hom.ModuleDerived`, and, for the local
  variant below, `RingedSite.localization` and `RingedSite.Hom.localizedRestrictionDerived`;
- `bridge/view`: a site presentation `X = RingedSite.ofCommRingSheaf J 𝒪`, which should specialize
  the ambient-owner formulation rather than own a parallel local-finite-tor-dimension API. -/

/-- Definition 21.46.1 (1): an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` if
for every `\mathcal O_X`-module `\mathcal F`, the derived tensor product
`E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` has vanishing homology outside `[a, b]`. -/
def HasTorAmplitudeIn (E : DMod) (a b : ℤ) : Prop :=
  ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((H i).obj (tensorSingle0 X E ℱ))

-- Proof sketch: unfold `HasTorAmplitudeIn`; it is exactly the defining homology-vanishing
-- condition for `E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` outside the interval
-- `[a, b]`.
/-- An object of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` exactly when derived tensoring
with every degree-zero `\mathcal O_X`-module has vanishing homology outside `[a, b]`. -/
theorem hasTorAmplitudeIn_iff (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn X E a b ↔
      ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((H i).obj (tensorSingle0 X E ℱ)) :=
  Iff.rfl

/-- Definition 21.46.1 (2): an object of `D(\mathcal O_X)` has finite tor dimension if it has
tor-amplitude in some interval `[a, b]`. -/
def HasFiniteTorDimension (E : DMod) : Prop :=
  ∃ a b : ℤ, HasTorAmplitudeIn X E a b

-- Proof sketch: unfold `HasFiniteTorDimension`; this is definitionally the existence of a
-- tor-amplitude interval.
/-- An object of `D(\mathcal O_X)` has finite tor dimension exactly when it has tor-amplitude in
some interval `[a, b]`. -/
theorem hasFiniteTorDimension_iff (E : DMod) :
    HasFiniteTorDimension X E ↔ ∃ a b : ℤ, HasTorAmplitudeIn X E a b :=
  Iff.rfl

/-- Definition 21.46.1 (4): an `\mathcal O_X`-module `\mathcal F` has tor dimension at most `d`
if its degree-zero derived object `\mathcal F[0]` has tor-amplitude in `[-d, 0]`. -/
def ModuleHasTorDimensionLE (ℱ : Mod) (d : ℕ) : Prop :=
  HasTorAmplitudeIn X ((single0).obj ℱ) (-((d : ℤ))) 0

-- Proof sketch: unfold `ModuleHasTorDimensionLE`; it is exactly the tor-amplitude condition for
-- the degree-zero derived object `\mathcal F[0]` with bounds `[-d, 0]`.
/-- An `\mathcal O_X`-module has tor dimension at most `d` exactly when its degree-zero derived
object has tor-amplitude in `[-d, 0]`. -/
theorem moduleHasTorDimensionLE_iff (ℱ : Mod) (d : ℕ) :
    ModuleHasTorDimensionLE X ℱ d ↔
      HasTorAmplitudeIn X ((single0).obj ℱ) (-((d : ℤ))) 0 :=
  Iff.rfl

end

section

variable (X : RingedSite.{u, v})

local notation "DMod" => RingedSite.Hom.ModuleDerived X

variable [Abelian (RingedSite.Hom.ModuleCat X)]
variable [CategoryWithHomology (RingedSite.Hom.ModuleCat X)]
variable [∀ U : X, Abelian (RingedSite.Hom.ModuleCat (X.localization U))]
variable [∀ U : X, CategoryWithHomology (RingedSite.Hom.ModuleCat (X.localization U))]
variable [∀ U : X, MonoidalCategoryStruct (RingedSite.Hom.ModuleDerived (X.localization U))]
variable [∀ U : X, (RingedSite.Hom.localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (RingedSite.Hom.localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (RingedSite.Hom.localizedRestriction X U)]

/-- Definition 21.46.1 (3): an object `E` of `D(\mathcal O)` locally has finite tor dimension if
for every object `U` there is a covering of `U` on whose members the restriction of `E` has
finite tor dimension. -/
def LocallyHasFiniteTorDimension (E : DMod) : Prop :=
  ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    HasFiniteTorDimension (X.localization I.Y)
      ((RingedSite.Hom.localizedRestrictionDerived X I.Y).obj E)

-- Proof sketch: unfold `LocallyHasFiniteTorDimension`; this is exactly the coveringwise
-- restriction condition saying that each object admits a cover on whose members the restricted
-- derived object has finite tor dimension.
/-- An object of `D(\mathcal O)` locally has finite tor dimension exactly when each object of the
site admits a covering on whose members the restriction has finite tor dimension. -/
theorem locallyHasFiniteTorDimension_iff (E : DMod) :
    LocallyHasFiniteTorDimension X E ↔
      ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        HasFiniteTorDimension (X.localization I.Y)
          ((RingedSite.Hom.localizedRestrictionDerived X I.Y).obj E) :=
  Iff.rfl

end

end SheafOfModules.RingedSite

import StacksProject_2024.Chap21.Lemma_21_19_1_core

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

open RingedSite.Hom

/-- Any index strictly below the left endpoint lies outside the interval `[a, b]`. -/
lemma not_mem_Icc_of_lt_left {a b i : ℤ} (hi : i < a) : i ∉ Set.Icc a b := by
  intro hmem
  exact (not_lt_of_ge hmem.1 hi).elim

section

variable {X : RingedSite.{u, v}}

local notation "Mod" => ModuleCat X
local notation "DMod" => ModuleDerived X
local notation "H" => DerivedCategory.homologyFunctor Mod
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

local instance moduleCatHasDerivedCategory : HasDerivedCategory Mod :=
  HasDerivedCategory.standard Mod

variable [CategoryWithHomology Mod]
variable [MonoidalCategory (ModuleDerived X)]

/- Domain-style sampling for Definition 21.46.1 (core layer):
- primary domain: tor-amplitude and finite tor dimension in the derived category of modules on a
  ringed site;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `MonoidalCategory (ModuleDerived X)`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: the source-facing predicates `HasTorAmplitudeIn`,
  `HasTorAmplitudeGE`, `HasFiniteTorDimension`, and `ModuleHasTorDimensionLE` depend only on the
  ambient ringed site `X`, so they belong in the core owner layer over `ModuleCat X` and
  `ModuleDerived X`, independent of the later localized covering API;
- primitive data: an object of `D(\mathcal O_X)`, interval bounds, and degree-zero module inputs;
- derived API: the finite-tor-dimension and module-level specializations.

Source/core/bridge triage:
- `source-facing`: the tor-amplitude, finite-tor-dimension, and module tor-dimension predicates;
- `core/canonical`: `RingedSite.Hom.ModuleCat`, `RingedSite.Hom.ModuleDerived`, and the homology
  functor, degree-zero embedding, and ambient tensor object on `ModuleDerived X`;
- `bridge/view`: the local finite-tor-dimension predicate is downstream derived API and belongs in
  `Definition_21_46_1.lean`, not in this primitive owner file. -/

/-- Definition 21.46.1 (1): an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` if
for every `\mathcal O_X`-module `\mathcal F`, the derived tensor product
`E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` has vanishing homology outside `[a, b]`. -/
def HasTorAmplitudeIn (E : DMod) (a b : ℤ) : Prop :=
  ∀ (ℱ : Mod) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((H i).obj (E ⊗ (single0).obj ℱ))

/-- An object of `D(\mathcal O_X)` has tor-amplitude in `[a, ∞]` if tensoring with any
degree-zero `\mathcal O_X`-module produces an object lying in degrees `≥ a`. -/
def HasTorAmplitudeGE (E : DMod) (a : ℤ) : Prop :=
  ∀ ℱ : Mod, (E ⊗ (single0).obj ℱ).IsGE a

/-- Definition 21.46.1 (2): an object of `D(\mathcal O_X)` has finite tor dimension if it has
tor-amplitude in some interval `[a, b]`. -/
def HasFiniteTorDimension (E : DMod) : Prop :=
  ∃ a b : ℤ, HasTorAmplitudeIn E a b

/-- Definition 21.46.1 (4): an `\mathcal O_X`-module `\mathcal F` has tor dimension at most `d`
if its degree-zero derived object `\mathcal F[0]` has tor-amplitude in `[-d, 0]`. -/
def ModuleHasTorDimensionLE (ℱ : Mod) (d : ℕ) : Prop :=
  HasTorAmplitudeIn ((single0).obj ℱ) (-(d : ℤ)) 0

end

section

variable {X : RingedSite.{u, v}}

local notation "Mod" => ModuleCat X
local notation "DMod" => ModuleDerived X
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

variable [MonoidalCategory (ModuleDerived X)]

/-- Tor-amplitude in a finite interval `[a, b]` implies lower tor-amplitude in `[a, ∞]`. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeGE
    {E : DMod} {a b : ℤ}
    (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeGE E a := by
  letI : HasDerivedCategory Mod := HasDerivedCategory.standard Mod
  simp only [HasTorAmplitudeGE]
  intro ℱ
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact hE ℱ i (not_mem_Icc_of_lt_left hi)

/-- Tor-amplitude in a fixed finite interval implies finite tor dimension. -/
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {E : DMod} {a b : ℤ}
    (hE : HasTorAmplitudeIn E a b) :
    HasFiniteTorDimension E :=
  ⟨a, b, hE⟩

end

end SheafOfModules.RingedSite

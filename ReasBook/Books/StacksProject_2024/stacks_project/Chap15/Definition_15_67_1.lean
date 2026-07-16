import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DMod" => DerivedCategory Mod
local notation "H" => homologyFunctor Mod
private abbrev single₀ : Mod ⥤ DMod := DerivedCategory.singleFunctor Mod (0 : ℤ)

/- Domain-style sampling for Definition 15.67.1:
- primary domain: tor-amplitude and finite tor dimension in the derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  `DerivedTensorProduct` notation `⊗[R]^L`,
  `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: this file is the `source-facing` owner for the tor-amplitude and
  finite-tor-dimension predicates on `D(R)`, while the derived tensor product itself is already
  canonically owned upstream by `derivedTensorProduct` and its notation;
- primitive vs. derived:
  primitive data are the derived object `K`, the interval bounds `a, b`, and the test module
  `M : ModuleCat R`;
  derived API is the existential finite-tor-dimension predicate and the module-level
  specializations;
- unlike projective and injective dimension, there is no separate upstream module-level canonical
  flat/tor-dimension invariant already available in mathlib or earlier Chapter 15 files, so the
  module predicates remain source-facing owners here rather than wrappers around a stricter owner;
- source/core/bridge triage:
  `source-facing`: `HasTorAmplitudeIn`, `HasFiniteTorDimension`;
  `core/canonical`: `derivedTensorProduct`, `⊗[R]^L`, `DerivedCategory.singleFunctor`, and `H`;
  `bridge/view`: the degree-zero embedding `(single₀).obj M : D(R)` of an `R`-module together with
    the module-level specializations `ModuleHasTorDimensionLE` and
    `ModuleHasFiniteTorDimension`. -/

/-- Definition 15.67.1 (1): an object `K` of `D(R)` has tor-amplitude in `[a, b]` if for every
`R`-module `M`, the homology of `K \otimes_R^{\mathbf L} M[0]` vanishes outside the interval
`[a, b]`. -/
def HasTorAmplitudeIn (K : DMod) (a b : ℤ) : Prop :=
  ∀ (M : Mod) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((H i).obj (K ⊗[R]^L (single₀.obj M)))

/-- Definition 15.67.1 (2): an object of `D(R)` has finite tor dimension if it has tor-amplitude
in some finite interval `[a, b]`. -/
def HasFiniteTorDimension (K : DMod) : Prop :=
  ∃ a b : ℤ, HasTorAmplitudeIn K a b

/-- An object of `D(R)` has finite tor dimension exactly when it has tor-amplitude in some finite
interval `[a, b]`. -/
theorem hasFiniteTorDimension_iff (K : DMod) :
    HasFiniteTorDimension K ↔ ∃ a b : ℤ, HasTorAmplitudeIn K a b :=
  Iff.rfl

/-- Tor-amplitude in a fixed finite interval implies finite tor dimension. -/
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {K : DMod} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) :
    HasFiniteTorDimension K :=
  ⟨a, b, hK⟩

/-- Definition 15.67.1 (3): an `R`-module `M` has tor dimension at most `d` if the degree-zero
derived object `M[0]` has tor-amplitude in `[-d, 0]`. -/
abbrev ModuleHasTorDimensionLE (M : Mod) (d : ℕ) : Prop :=
  HasTorAmplitudeIn (single₀.obj M) (-(d : ℤ)) 0

/-- Definition 15.67.1 (4): an `R`-module has finite tor dimension if its degree-zero derived
object has finite tor dimension in `D(R)`. -/
abbrev ModuleHasFiniteTorDimension (M : Mod) : Prop :=
  HasFiniteTorDimension (single₀.obj M)

-- Proof sketch: this is the one-sided version of `HasTorAmplitudeIn`, phrased through the
-- canonical `t`-structure owner `IsGE`.
/-- An object of `D(R)` has tor-amplitude in `[a, ∞]` if tensoring with any degree-zero
`R`-module produces an object lying in degrees `≥ a`. -/
def HasTorAmplitudeGE (K : DMod) (a : ℤ) : Prop :=
  ∀ M : ModuleCat R, (K ⊗[R]^L (single₀.obj M)).IsGE a

/-- Finite-interval tor-amplitude in `[a, b]` implies lower tor-amplitude in `[a, ∞]`. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeGE {K : DMod} {a b : ℤ}
    (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeGE K a := by
  -- Proof comment: below `a`, the interval condition for `HasTorAmplitudeIn` already forces
  -- vanishing of the tested tensor homology.
  intro M
  rw [isGE_iff]
  intro i hi
  exact hK M i fun hmem ↦ (not_lt_of_ge hmem.1 hi).elim

-- Proof sketch: unfold `HasTorAmplitudeGE` and rewrite `IsGE` by the standard homology
-- vanishing criterion.
/-- An object of `D(R)` has tor-amplitude in `[a, ∞]` exactly when tensoring with any degree-zero
`R`-module has vanishing homology in every degree `< a`. -/
theorem hasTorAmplitudeGE_iff
    (K : DMod) (a : ℤ) :
    HasTorAmplitudeGE K a ↔
      ∀ (M : ModuleCat R) (i : ℤ), i < a →
        IsZero ((H i).obj (K ⊗[R]^L (single₀).obj M)) := by
  simp [HasTorAmplitudeGE, isGE_iff]

end

end CategoryTheory

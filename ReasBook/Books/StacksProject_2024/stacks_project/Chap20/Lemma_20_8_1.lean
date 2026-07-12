import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap20.«20_11_0_1»
import StacksProject_2024.Chap21.Lemma_21_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.8.1:
- primary domain: restriction maps on sections of an injective `𝒪_X`-module over nested
  opens of a ringed space;
- sampled owner declarations:
  `injective_module_restriction_surjective_of_mono`,
  `RingedSpace.Modules`,
  `homOfLE`;
- best owner abstraction: the general site-level owner
  `injective_module_restriction_surjective_of_mono`;
- primitive data: an injective object `ℐ : X.Modules` and an inclusion `hU'U : U' ≤ U`,
  equivalently the canonical monomorphism `homOfLE hU'U : U' ⟶ U`;
- derived API: surjectivity of the restriction map on sections from `U` to `U'`.

Source/core/bridge triage:
- `source-facing`: the explicit surjectivity statement on nested opens from the textbook;
- `core/canonical`: the project-level site theorem
  `injective_module_restriction_surjective_of_mono`;
- `bridge/view`: specialize that owner to the site of opens of the ringed space and the mono
  `homOfLE hU'U`. -/

variable {X : RingedSpace.{u}} {U' U : Opens X}

-- Proof sketch: specialize the project's site-level surjectivity theorem
-- `injective_module_restriction_surjective_of_mono` to the canonical mono
-- `homOfLE hU'U : U' ⟶ U`.
/-- Lemma 20.8.1: if `ℐ` is an injective `𝒪_X`-module and `U' ⊆ U` are open subsets of `X`,
then the restriction map `ℐ(U) ⟶ ℐ(U')` is surjective. -/
@[stacks 01EA]
theorem module_sections_restriction_surjective_of_injective
    (ℐ : X.Modules) (hℐ : Injective ℐ) (hU'U : U' ≤ U) :
    Function.Surjective
      (((SheafOfModules.forget X.ringCatSheaf).obj ℐ).map (homOfLE hU'U).op) :=
  injective_module_restriction_surjective_of_mono (homOfLE hU'U) ℐ hℐ

/-- The underlying additive sheaf of an injective `𝒪_X`-module has surjective restriction maps
along inclusions of opens. -/
theorem underlying_module_sections_restriction_surjective_of_injective
    (ℐ : X.Modules) (hℐ : Injective ℐ) (hU'U : U' ≤ U) :
    Function.Surjective (((moduleUnderlyingSheaf X).obj ℐ).presheaf.map (homOfLE hU'U).op) := by
  simpa [moduleUnderlyingSheaf] using
    module_sections_restriction_surjective_of_injective ℐ hℐ hU'U

end AlgebraicGeometry.RingedSpace

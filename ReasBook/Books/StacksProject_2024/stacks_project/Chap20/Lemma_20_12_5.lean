import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import StacksProject_2024.Chap20.«20_2_0_4»
import StacksProject_2024.Chap20.«20_11_0_1»
import StacksProject_2024.Chap20.Lemma_20_12_3
import StacksProject_2024.Chap20.Lemma_20_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(f _*).Additive]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]

local notation "JY" => Opens.grothendieckTopology Y.carrier

/- Domain-style sampling for Lemma 20.12.5:
- primary domain: higher direct images of `𝒪_X`-modules on ringed spaces and their
  underlying additive sheaves;
- sampled owner declarations:
  `R^{p}_[f](ℱ)`,
  `moduleUnderlyingSheaf`,
  `higherCohomology_isZero_of_module_isFlasque`,
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- best owner abstraction: the source-facing higher direct image object
  `R^{p}_[f](ℱ)`, with the canonical underlying-sheaf bridge `moduleUnderlyingSheaf X`
  supplying the flasque hypothesis;
- primitive data: `f : X ⟶ Y`, a module `ℱ : X.Modules`, a flasqueness hypothesis on the
  underlying additive sheaf, and a positive degree `p`;
- derived API: vanishing of the higher direct image object `R^p f_* ℱ`.

Source/core/bridge triage:
- `source-facing`: the vanishing statement for the positive higher direct image of a flasque
  module;
- `core/canonical`: `f _*` and its right derived functors;
- `bridge/view`: `moduleUnderlyingSheaf X` for the underlying additive sheaf on which flasqueness
  is stated.
-/

private theorem higherDirectImageModule_underlyingSheaf_isZero_of_flasque
    (ℱ : RingedSpace.Modules X)
    (hℱ : TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℱ))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((moduleUnderlyingSheaf Y).obj (R^{p}_[f](ℱ))) := by
  rcases
      higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology
        f ℱ p with ⟨e⟩
  exact e.isZero_iff.2
    ((presheafToSheaf JY AddCommGrpCat.{u}).map_isZero
      (Functor.isZero _ fun U ↦
        higherCohomology_isZero_of_module_isFlasque ℱ hℱ
          ((Opens.map f.hom.base).obj (unop U)) p hp))

/-- Lemma 20.12.5: if an `𝒪_X`-module on a ringed space is flasque, then every positive
higher direct image `R^{p}_[f](ℱ)` is zero. -/
@[stacks 09T0]
theorem higherDirectImageModule_isZero_of_flasque
    (ℱ : RingedSpace.Modules X)
    (hℱ : TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℱ))
    (p : ℕ) (hp : 0 < p) :
    IsZero (R^{p}_[f](ℱ)) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply (moduleUnderlyingSheaf Y).map_injective
  simpa using
    (IsZero.iff_id_eq_zero _).1
      (higherDirectImageModule_underlyingSheaf_isZero_of_flasque f ℱ hℱ p hp)

/-- Typeclass form of Lemma 20.12.5: a flasque `𝒪_X`-module has zero positive higher direct
image. -/
instance instIsZeroHigherDirectImageModuleOfFlasque
    (ℱ : RingedSpace.Modules X) (p : ℕ)
    [hℱ : TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℱ)] [hp : Fact (0 < p)] :
    IsZero (R^{p}_[f](ℱ)) :=
  higherDirectImageModule_isZero_of_flasque f ℱ hℱ p hp.out

end AlgebraicGeometry.RingedSpace

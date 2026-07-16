import StacksProject_2024.stacks_project.Chap20.«20_2_0_4»
import StacksProject_2024.stacks_project.Chap20.Lemma_20_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.13.3:
- primary domain: comparison between cohomology of `𝒪_X`-modules on a ringed space and
  cohomology of their underlying abelian sheaves, both over an open subset and under higher
  direct image;
- sampled owner declarations:
  `moduleUnderlyingSheaf`,
  `moduleCohomologyAtOpen`,
  `underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology`,
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- best owner abstraction: the public source-facing statements here are `bridge/view` results over
  the chapter owner `moduleUnderlyingSheaf`; the open-cohomology comparison is governed by the
  localized ringed-site cohomology owner
  `underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology`, while the higher-direct-image
  comparison sits over the ringed-site owner
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- primitive data: a ringed space, an `𝒪_X`-module `ℱ`, an open subset or a morphism of
  ringed spaces, and a cohomological degree;
- derived API: the underlying additive sheaf `moduleUnderlyingSheaf`, open cohomology
  `moduleCohomologyAtOpen`, and the higher direct images obtained from right derived pushforward.

Source/core/bridge triage:
- `source-facing`: the two ringed-space comparison statements numbered in Lemma `20.13.3`;
- `core/canonical`: `moduleUnderlyingSheaf`, the localized-site comparison
  `underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology`, and the ringed-site owner
  `higherDirectImage_underlyingSheaf_is_sheafification_of_objectwise_cohomology`;
- `bridge/view`: the theorems below, which keep the Stacks ringed-space surface while reusing the
  canonical underlying-sheaf owner instead of raw `SheafOfModules.toSheaf` composites.
-/

section OpenCohomology

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions X.Modules]

-- Proof sketch: compute `H^i(U, ℱ)` as the `i`-th right derived functor of the sections
-- functor `Γ(U, -)` on `𝒪_X`-modules, then forget the `Γ(U, 𝒪_X)`-
-- module structure. The same injective resolution, viewed through `moduleUnderlyingSheaf X`,
-- computes the abelian-sheaf cohomology group on `U`.
/-- Lemma 20.13.3 (1): for an open subset `U ⊆ X`, the degree-`i` cohomology of an
`𝒪_X`-module `ℱ` computed in the category of `𝒪_X`-modules agrees, after forgetting the module
structure, with the degree-`i` cohomology of the underlying abelian sheaf of `ℱ` on `U`. -/
@[stacks 01F1]
theorem moduleCohomologyAtOpen_underlying_isomorphic_underlyingSheafCohomology
    (ℱ : X.Modules) (U : Opens X.carrier) (i : ℕ) :
    IsIsomorphic
      ((forget₂ (ModuleCat (X.presheaf.obj (op U))) AddCommGrpCat).obj
        (moduleCohomologyAtOpen U ℱ i))
      (((moduleUnderlyingSheaf X).obj ℱ).H' i U) := by
  exact ⟨eqToIso (moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology U ℱ i)⟩

end OpenCohomology

section HigherDirectImage

variable [HasInjectiveResolutions X.Modules]
variable [HasInjectiveResolutions
  (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

-- Proof sketch: forget an injective resolution of `ℱ` in `(RingedSpace.Modules X)` to an
-- injective resolution of the underlying abelian sheaf, use Remark `20.13.2` to identify the
-- section complexes termwise, and then apply Lemma `20.7.3` to identify the resulting right
-- derived direct images.
/-- Lemma 20.13.3 (2): for a morphism of ringed spaces `f : X ⟶ Y`, the degree-`i` higher direct
image of an `𝒪_X`-module `ℱ`, viewed as an abelian sheaf on `Y`, agrees with the degree-`i`
higher direct image of the underlying abelian sheaf of `ℱ`. -/
@[stacks 01F1]
theorem higherDirectImageModule_underlyingSheaf_isomorphic_higherDirectImageAbelianSheaf
    (f : X ⟶ Y)
    [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).Additive]
    (ℱ : X.Modules) (i : ℕ) :
    IsIsomorphic
      ((moduleUnderlyingSheaf Y).obj (R^{i}_[f](ℱ)))
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).rightDerived i).obj
        ((moduleUnderlyingSheaf X).obj ℱ)) := by
  sorry

end HigherDirectImage

end AlgebraicGeometry.RingedSpace

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap06.Definition_6_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

/-- The `i`-th higher direct image of a sheaf of modules along a morphism of ringed spaces. -/
abbrev higherDirectImageModule {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(f _*).Additive]
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    (ℱ : RingedSpace.Modules X) (i : ℕ) :
    RingedSpace.Modules Y :=
  ((f _*).rightDerived i).obj ℱ

/- Lean surface notation for the higher direct image `R^i f_*(ℱ)` on ringed spaces. -/
scoped macro:max "R^{" i:term "}_[" f:term "](" F:term ")" : term =>
  `(@higherDirectImageModule _ _ $f _ _ $F $i)

end AlgebraicGeometry.RingedSpace.Hom

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for 20.2.0.4:
- primary domain: higher direct images of `𝒪_X`-modules on ringed spaces, computed from
  injective resolutions;
- sampled owner declarations:
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`,
  `f _*`;
- best owner abstraction:
  `core/canonical`: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
  `source-facing`: the higher direct image module `R^i f_* ℱ`, written here as
    `((f _*).rightDerived i).obj ℱ`;
  `bridge/view`: the specialization of `isoRightDerivedObj` to module pushforward on ringed
    spaces;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y`, an `𝒪_X`-module
  `ℱ : RingedSpace.Modules X`, a chosen injective resolution `I : InjectiveResolution ℱ`, and a
  cohomological degree `i : ℕ`;
- derived API: the canonical comparison
  `R^i f_* ℱ ≅ H^i(f_* I^•)` in the module category of `Y`.

This file is therefore `bridge/view`: it should not stop at the ambient abelian-category recall,
but instead expose the source-facing module pushforward specialization of the canonical
injective-resolution computation.
-/

/- 20.2.0.4: the `i`th higher direct image module is computed by taking the `i`th cohomology
object of the pushforward of an injective resolution. This is the ringed-space/module
specialization of the canonical comparison `R^i F(X) ≅ H^i(F(I^•))`. -/
recall CategoryTheory.InjectiveResolution.isoRightDerivedObj

section

variable {X Y : RingedSpace.{u}}
variable (f : X ⟶ Y)
variable [(f _*).Additive]
variable [HasInjectiveResolutions (RingedSpace.Modules X)]

/-- 20.2.0.4: the higher direct image module computed from a chosen injective resolution is
isomorphic to the degree-`i` homology object of the pushed-forward resolution. -/
@[stacks 0715]
theorem higherDirectImageModule_isomorphic_to_homology_pushforward_of_injectiveResolution
    (ℱ : RingedSpace.Modules X) (I : InjectiveResolution ℱ) (i : ℕ) :
    IsIsomorphic
      (R^{i}_[f](ℱ))
      ((HomologicalComplex.homologyFunctor
        (RingedSpace.Modules Y) (ComplexShape.up ℕ) i).obj
          (((f _*).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  exact ⟨I.isoRightDerivedObj (f _*) i⟩

end

end AlgebraicGeometry.RingedSpace

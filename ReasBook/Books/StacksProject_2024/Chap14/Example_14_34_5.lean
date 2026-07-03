import Mathlib
import StacksProject_2024.Chap14.Definition_14_26_6

open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open AlgebraicTopology
open scoped Simplicial

universe u

noncomputable section

namespace CategoryTheory

variable (A : CommRingCat.{u})

/- Domain-style sampling for Example 14.34.5:
- primary domain: the polynomial `A`-algebra resolution of an `A`-algebra as an augmented
  simplicial object in `Under A`, together with its forgetful views to sets and to `A`-modules;
- sampled same-kind owner declarations:
  `Arrow.augmentedCechNerve`,
  `SimplicialObject.Augmented`,
  `commAlgCatEquivUnder`,
  `AlternatingFaceMapComplex.ε`;
- best owner abstraction: the source-facing owner is the augmented Čech nerve of the counit
  `A[B] ⟶ B` in `Under A`; the forgetful functors to sets and to `A`-modules are bridge/view data
  derived from that owner, not primary public owners;
- primitive vs. derived split:
  primitive data are the counit `A[B] ⟶ B` and its canonical augmented Čech nerve in `Under A`;
  derived API is the underlying augmented simplicial set, the underlying augmented simplicial
  `A`-module, and the homotopy/quasi-isomorphism properties of their augmentations.

Source/core/bridge triage:
- `source-facing`: the augmented polynomial `A`-algebra resolution of `B` in `Under A`;
- `core/canonical`: `Arrow.augmentedCechNerve`, `commAlgCatEquivUnder`, and the canonical
  forgetful functors from `CommAlgCat A`;
- `bridge/view`: the whiskered forgetful images of the source-facing owner in `Type u` and
  `ModuleCat A`. -/

/-- The augmented simplicial polynomial `A`-algebra resolution of `B`, given by the augmented Čech
nerve of the counit `A[B] ⟶ B` in `Under A`. -/
abbrev polynomialAlgebraAugmentedResolution (B : Under A) :
    SimplicialObject.Augmented (Under A) :=
  (Arrow.mk ((Under.costarAdjForget A).counit.app B)).augmentedCechNerve

private abbrev polynomialAlgebraForgetToModule : Under A ⥤ ModuleCat A :=
  (commAlgCatEquivUnder A).inverse ⋙
    forget₂ (CommAlgCat A) (AlgCat A) ⋙
      forget₂ (AlgCat A) (ModuleCat A)

/-- The augmented simplicial set obtained from
`polynomialAlgebraAugmentedResolution A B` by forgetting to underlying sets. -/
abbrev polynomialAlgebraAugmentedUnderlyingSet (B : Under A) :
    SimplicialObject.Augmented (Type u) :=
  (whiskeringObj (Under A) (Type u) (Under.forget A ⋙ forget CommRingCat)).obj
    (polynomialAlgebraAugmentedResolution A B)

/-- The augmented simplicial `A`-module obtained from
`polynomialAlgebraAugmentedResolution A B` by forgetting the algebra structure. -/
abbrev polynomialAlgebraAugmentedModuleResolution (B : Under A) :
    SimplicialObject.Augmented (ModuleCat A) :=
  (whiskeringObj (Under A) (ModuleCat A) (polynomialAlgebraForgetToModule A)).obj
    (polynomialAlgebraAugmentedResolution A B)

-- Proof sketch: the counit map `A[B] ⟶ B` is split by the unit of the adjunction, so its
-- augmented Cech nerve has an extra degeneracy. After forgetting to sets, this gives a simplicial
-- homotopy equivalence for the augmentation of the underlying simplicial set.
/-- Example 14.34.5: for a commutative ring `A` and a commutative `A`-algebra `B`, the
augmentation of the underlying simplicial set of `polynomialAlgebraAugmentedResolution A B`
admits a simplicial homotopy inverse. -/
theorem polynomialAlgebraResolutionForgetAugmentation_isHomotopyEquivalence
    (B : Under A) :
    IsHomotopyEquivalence (polynomialAlgebraAugmentedUnderlyingSet A B).hom := sorry

-- Proof sketch: the extra degeneracy on the augmented Cech nerve survives under the forgetful
-- functor `Under A ⥤ ModuleCat A`. Applying the standard extra-degeneracy argument for
-- alternating-face-map complexes yields a quasi-isomorphism to the complex concentrated in degree
-- `0` at the underlying `A`-module of `B`.
/-- The augmentation of the alternating face map complex of
`polynomialAlgebraAugmentedResolution A B`, after forgetting to `A`-modules, is a
quasi-isomorphism to the complex concentrated in degree `0` at `B`. -/
theorem polynomialAlgebraResolutionAlternatingFaceMapComplex_quasiIso
    (B : Under A) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (polynomialAlgebraAugmentedModuleResolution A B)) :=
  sorry

end CategoryTheory

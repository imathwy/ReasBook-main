import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap18.Lemma_18_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for pullback and tensor product of sheaves of modules on a ringed space:
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.Hom.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `CategoryTheory.Functor.Monoidal.μIso`,
  `Definition_6_26_1`'s notation `f^*`;
- best owner abstraction:
  for a morphism of ringed spaces `f`, the source-facing pullback-tensor comparison is the
  canonical monoidal comparison isomorphism `CategoryTheory.Functor.Monoidal.μIso` specialized to
  the pullback owner `f^*`;
- primitive data:
  a morphism of ringed spaces `f : X ⟶ Y` and module sheaves `ℱ 𝒢 : Y.Modules`;
- derived API:
  the canonical isomorphism `(CategoryTheory.Functor.Monoidal.μIso (f^*) ℱ 𝒢).symm`.

Layer triage:
- `source-facing`: the pullback-tensor comparison for a fixed morphism of ringed spaces;
- `core/canonical`: the owner pullback functor `f^*` together with
  `CategoryTheory.Functor.Monoidal.μIso`;
- `bridge/view`: specialization of that monoidal comparison to `f^*`.
-/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [MonoidalCategory Y.Modules]
variable [MonoidalCategory X.Modules]
variable [Functor.Monoidal (RingedSpace.Hom.pullback f)]
variable (ℱ 𝒢 : Y.Modules)

/- Lemma 17.16.4: pullback of the tensor product of two `\mathcal O_Y`-modules is canonically
isomorphic to the tensor product of their pullbacks. This is the canonical monoidal comparison
isomorphism specialized to the pullback owner `f^*`. -/
noncomputable abbrev pullbackTensorIso :
    (RingedSpace.Hom.pullback f).obj (ℱ ⊗ 𝒢) ≅
      ((RingedSpace.Hom.pullback f).obj ℱ ⊗ (RingedSpace.Hom.pullback f).obj 𝒢) :=
  (Functor.Monoidal.μIso (RingedSpace.Hom.pullback f) ℱ 𝒢).symm

end AlgebraicGeometry.RingedSpace

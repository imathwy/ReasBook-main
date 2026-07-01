import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap18.Lemma_18_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Functor.OplaxMonoidal
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for pullback and tensor product of sheaves of modules on a ringed space:
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.Hom.pullback`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `CategoryTheory.Functor.OplaxMonoidal.δ`,
  `Lemma_18_26_2`'s `IsIso (δ fStar ℱ 𝒢)` owner instance;
- best owner abstraction:
  for a morphism of ringed spaces `f`, the source-facing pullback-tensor comparison is the
  canonical oplax-monoidal comparison morphism `δ (f^*) ℱ 𝒢`; its isomorphism is already supplied
  by the Chapter 18 owner instance, so the public surface here should recall that comparison and
  its canonical `asIso` bridge directly instead of restating a generic monoidal-functor tensorator;
- primitive data:
  a morphism of ringed spaces `f : X ⟶ Y` and module sheaves `ℱ 𝒢 : Y.Modules`;
- derived API:
  the comparison morphism `δ (f^*) ℱ 𝒢` and the resulting isomorphism `asIso (δ (f^*) ℱ 𝒢)`.

Layer triage:
- `source-facing`: the pullback-tensor comparison for a fixed morphism of ringed spaces;
- `core/canonical`: the owner pullback functor `f^*` together with the oplax-monoidal comparison
  morphism `CategoryTheory.Functor.OplaxMonoidal.δ`;
- `bridge/view`: the isomorphism `asIso (δ (f^*) ℱ 𝒢)` obtained from the established Chapter 18
  `IsIso` instance.
-/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable (ℱ 𝒢 : Y.Modules)

/- Lemma 17.16.4: pullback of the tensor product of two `\mathcal O_Y`-modules is canonically
isomorphic to the tensor product of their pullbacks. In the project owner API this is the
canonical pullback-tensor comparison morphism for `f^*`. -/
#check δ (f^*) ℱ 𝒢

/- Companion bridge: the source-facing isomorphism itself is the canonical `asIso` of that
comparison morphism. -/
#check asIso (δ (f^*) ℱ 𝒢)

end AlgebraicGeometry.RingedSpace

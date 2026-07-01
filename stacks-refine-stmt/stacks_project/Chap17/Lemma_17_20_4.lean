import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap17.Definition_17_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.20.4:
- primary domain: exactness of pullback followed by tensoring with a sheaf that is flat over the
  target ringed space in the canonical relative-flatness sense;
- sampled owner declarations:
  `SheafOfModules.flat_over`,
  `SheafOfModules.RingedSite.IsFlat`,
  `f^*`,
  `sheafModuleTensorRightFunctor`,
  `exactFunctor`;
- owner abstraction: the source-facing flatness hypothesis should reuse
  `SheafOfModules.flat_over ℱ f` as the canonical relative-flatness owner on the restricted
  `f^{-1}\mathcal O_Y`-module, while the functor part should reuse the canonical pullback owner
  `f^*` and the existing tensor owner `sheafModuleTensorRightFunctor`;
- primitive data: a morphism `f : X ⟶ Y` and a sheaf `ℱ : (RingedSpace.Modules X)`;
- derived API: the exactness theorem for the canonical composite functor
  `f^* ⋙ sheafModuleTensorRightFunctor ℱ`.

Source/core/bridge triage:
- `source-facing`: exactness of `𝒢 ↦ f^*𝒢 ⊗ ℱ` under the hypothesis that `ℱ` is flat over `Y`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`, `f^*`,
  `sheafModuleTensorRightFunctor`, and `exactFunctor`;
- `bridge/view`: `SheafOfModules.flat_over` and the composite pullback-then-tensor functor used
  directly in the theorem.
-/

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "ModX" => X.Modules
local notation "ModY" => Y.Modules

-- Proof sketch: rewrite the textbook functor as
-- `𝒢 ↦ f^{-1}𝒢 ⊗_{f^{-1}\mathcal O_Y} ℱ`. The inverse-image functor on abelian sheaves is exact,
-- and the relative-flatness instance on `ℱ` is exactly the flatness needed for tensoring with
-- `ℱ` over `f^{-1}\mathcal O_Y` to preserve short exact sequences; combining these gives exactness of the
-- composite functor.
/-- Lemma 17.20.4: if `f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `\mathcal F` is an `\mathcal O_X`-module flat over `Y`, then the functor
`\mathcal G \mapsto f^* \mathcal G \otimes_{\mathcal O_X} \mathcal F` from
`Mod(\mathcal O_Y)` to `Mod(\mathcal O_X)` is exact. -/
theorem ringedSpaceModulePullbackTensor_exact_of_flatOverTarget
    (f : X ⟶ Y) (ℱ : ModX) [SheafOfModules.flat_over ℱ f] :
    exactFunctor ModY ModX (f^* ⋙ sheafModuleTensorRightFunctor ℱ) := sorry

end AlgebraicGeometry.RingedSpace

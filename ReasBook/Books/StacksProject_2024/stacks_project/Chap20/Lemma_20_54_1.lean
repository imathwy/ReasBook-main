import StacksProject_2024.Chap12.Lemma_12_29_1
import StacksProject_2024.Chap17.Lemma_17_18_2
import StacksProject_2024.Chap18.Example_18_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [BraidedCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (𝟙_ ModX : ModX)
local notation "LocallyDirectSummand" =>
  @IsLocallyDirectSummandOfFiniteFree _ _ (Opens.grothendieckTopology X) _ X.sheaf

/- Domain-style sampling for Lemma 20.54.1:
- primary domain: tensoring sheaves of `𝒪_X`-modules with a finite locally free factor
  and preservation of injective objects;
- sampled owner declarations:
  `Functor.PreservesInjectiveObjects`,
  `tensorLeftAdjunction`,
  `BraidedCategory.exactPairing_swap`,
  the `ExactPairing ((ihom ℰ).obj 𝒪X) ℰ` instance from Example 18.29.1;
- best owner abstraction: the source-facing theorem remains the injectivity statement for
  `ℰ ⊗ ℐ`, while its proof passes through the canonical criterion
  `Functor.PreservesInjectiveObjects` for the tensor endofunctor `tensorLeft ℰ`, derived from the
  exact-pairing owner attached to the finite locally free sheaf `ℰ`;
- primitive data: the ambient module category `(RingedSpace.Modules X)` and the finite locally free sheaf
  `ℰ`, expressed through the Chapter 17 ringed-space owner `SheafOfModules.IsFiniteLocallyFree`;
- derived API: the companion instance
  `(tensorLeft ℰ).PreservesInjectiveObjects` together with the source-facing specialization to
  `ℰ ⊗ ℐ`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that `ℰ ⊗ ℐ` is injective when `ℰ` is finite locally
  free and `ℐ` is injective;
- `core/canonical`: `Functor.PreservesInjectiveObjects`, `tensorLeftAdjunction`, and the exact
  pairing `ExactPairing ((ihom ℰ).obj 𝒪X) ℰ`;
- `bridge/view`: the swapped exact pairing
  `BraidedCategory.exactPairing_swap ((ihom ℰ).obj 𝒪X) ℰ`, which makes `tensorLeft ℰ`
  itself the right adjoint owner. -/

/-- Tensoring on the left by a finite locally free `𝒪_X`-module preserves injective
objects. -/
instance tensorLeft_preservesInjectiveObjects_of_isFiniteLocallyFree
    (ℰ : ModX) [ℰ.IsFiniteLocallyFree] :
    (tensorLeft ℰ).PreservesInjectiveObjects := by
  let dual : ModX := (ihom ℰ).obj 𝒪X
  let _ : LocallyDirectSummand ℰ :=
    SheafOfModules.isFiniteLocallyFree_to_isLocallyDirectSummandOfFiniteFree ℰ
  let _ : ExactPairing dual ℰ := inferInstance
  let _ : ExactPairing ℰ dual :=
    BraidedCategory.exactPairing_swap dual ℰ
  let _ : PreservesLimits (tensorLeft dual) :=
    (tensorLeftAdjunction dual ℰ).rightAdjoint_preservesLimits
  let hExact : exactFunctor ModX ModX (tensorLeft dual) :=
    (CategoryTheory.ExactFunctor.of (tensorLeft dual)).property
  simpa using
    CategoryTheory.preservesInjectiveObjects_of_exact_leftAdjoint
      (tensorLeftAdjunction ℰ dual) hExact

/-- Lemma 20.54.1: if `X` is a ringed space, `ℐ` is an injective `𝒪_X`-module, and `ℰ` is a
finite locally free `𝒪_X`-module, then `ℰ ⊗ ℐ` is injective. -/
@[stacks 01E7]
theorem moduleTensor_injective_of_isFiniteLocallyFree
    (ℰ ℐ : ModX) [ℰ.IsFiniteLocallyFree] (hℐ : Injective ℐ) :
    Injective (ℰ ⊗ ℐ) := by
  simpa using (tensorLeft ℰ).injective_obj_of_injective hℐ

end AlgebraicGeometry.RingedSpace

import Mathlib
import stacks_project.Chap17.Definition_17_14_1
import stacks_project.Chap17.Example_17_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [BraidedCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 20.54.1:
- primary domain: tensoring sheaves of `\mathcal O_X`-modules with a finite locally free factor
  and preservation of injective objects;
- sampled owner declarations:
  `Functor.PreservesInjectiveObjects`,
  `tensorRightAdjunction`,
  `BraidedCategory.tensorLeftIsoTensorRight`,
  the `ExactPairing ((ihom ℰ).obj (𝟙_ ModX)) ℰ` instance from Example 17.18.1;
- best owner abstraction: `Functor.PreservesInjectiveObjects` for the canonical tensor endofunctor
  `tensorLeft ℰ`, derived from the exact-pairing owner attached to the finite locally free sheaf
  `ℰ`;
- primitive data: the ambient module category `(RingedSpace.Modules X)` and the finite locally free sheaf
  `ℰ`;
- derived API: preservation of injective objects by `tensorLeft ℰ`, and the source-facing
  specialization to `ℰ ⊗ ℐ`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that `ℰ ⊗ \mathcal I` is injective when `ℰ` is finite
  locally free and `\mathcal I` is injective;
- `core/canonical`: `Functor.PreservesInjectiveObjects`, `tensorRightAdjunction`, and the exact
  pairing `ExactPairing ((ihom ℰ).obj (𝟙_ ModX)) ℰ`;
- `bridge/view`: the braided identification of left and right tensoring used to move from the
  canonical right-adjoint owner to the source-facing left-tensor statement. -/

/-- Tensoring on the left by a finite locally free sheaf preserves injective objects. -/
instance tensorLeft_preservesInjectiveObjects_of_isFiniteLocallyFree
    (ℰ : ModX) [ℰ.IsFiniteLocallyFree] :
    (tensorLeft ℰ).PreservesInjectiveObjects := by
  let dual := (ihom ℰ).obj (𝟙_ ModX)
  letI : ExactPairing dual ℰ := by
    simpa [dual] using
      (inferInstance : ExactPairing ((ihom ℰ).obj (𝟙_ ModX)) ℰ)
  letI : PreservesLimits (tensorLeft dual) :=
    (tensorLeftAdjunction dual ℰ).rightAdjoint_preservesLimits
  letI : (tensorLeft dual).PreservesMonomorphisms := inferInstance
  letI : (tensorRight dual).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms.of_iso (BraidedCategory.tensorLeftIsoTensorRight dual)
  letI : (tensorRight ℰ).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (tensorRightAdjunction dual ℰ)
  refine ⟨fun hℐ ↦ ?_⟩
  exact Injective.of_iso
    ((BraidedCategory.tensorLeftIsoTensorRight ℰ).symm.app _)
    ((tensorRight ℰ).injective_obj_of_injective hℐ)

/-- Lemma 20.54.1: if `X` is a ringed space, `ℐ` is an injective `\mathcal O_X`-module, and `ℰ`
is a finite locally free `\mathcal O_X`-module, then `ℰ \otimes_{\mathcal O_X} ℐ` is injective. -/
theorem moduleTensor_injective_of_isFiniteLocallyFree
    (ℰ ℐ : ModX) [ℰ.IsFiniteLocallyFree] (hℐ : Injective ℐ) :
    Injective (ℰ ⊗ ℐ) :=
  (tensorLeft ℰ).injective_obj_of_injective hℐ

end AlgebraicGeometry.RingedSpace

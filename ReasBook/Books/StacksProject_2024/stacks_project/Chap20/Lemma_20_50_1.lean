import Mathlib.Tactic.Recall
import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap15.Lemma_15_58_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ

variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : RingedSpace.Modules X, ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (RingedSpace.Modules X),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ ℱ : RingedSpace.Modules X,
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X))
    ((curriedTensor (RingedSpace.Modules X)).obj ℱ)]
variable [∀ ℱ : RingedSpace.Modules X,
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X))
    ((curriedTensor (RingedSpace.Modules X)).flip.obj ℱ)]

/- Domain-style sampling for Lemma 20.50.1:
- primary domain: symmetric monoidal structures on cochain complexes, specialized to
  `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `MonoidalCategory (CochainComplex C ℤ)`,
  `BraidedCategory (CochainComplex C ℤ)`,
  `SymmetricCategory (CochainComplex C ℤ)`,
  `SymmetricCategory.ofFaithful`;
- best owner abstraction: the core owner is the ambient typeclass
  `SymmetricCategory CpxX`, supplied in the project by Chapter 15's generic
  cochain-complex construction;
- primitive vs. derived: the primitive data are the monoidal and symmetric structures on
  `Modules X`
  together with the tensor exactness hypotheses needed to build the complex tensor product. The
  symmetric structure on `CpxX` is derived owner API and should therefore be used directly,
  not reintroduced through a local wrapper or witness declaration.

Source/core/bridge triage:
- `source-facing`: Lemma 20.50.1, the ringed-space specialization of the tensor symmetry on
  complexes of modules;
- `core/canonical`: the chapter owner instance `SymmetricCategory (CochainComplex C ℤ)` from
  Lemma 15.58.1;
- `bridge/view`: the specialization from a general preadditive symmetric monoidal category `C` to
  `Modules X`.

This item is check-only. The earlier local wrapper duplicated the Chapter 15 owner without adding
new source-facing mathematics, so the file should expose the canonical owner specialization
directly.
-/

/- Lemma 20.50.1: cochain complexes of `𝒪_X`-modules on a ringed space form a symmetric monoidal
category for the total-complex tensor product; this is the Chapter 15 owner
`cochainComplexSymmetricCategory`, specialized in this file to `CpxX`. -/
recall cochainComplexSymmetricCategory

/- Specialized check for Lemma 20.50.1 on cochain complexes of `𝒪_X`-modules. -/
example : SymmetricCategory CpxX := inferInstance

end

end AlgebraicGeometry.RingedSpace

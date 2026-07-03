import Mathlib
import StacksProject_2024.Chap15.Lemma_15_58_1
import StacksProject_2024.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ ℱ : (RingedSpace.Modules X),
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X)) ((curriedTensor (RingedSpace.Modules X)).obj ℱ)]
variable [∀ ℱ : (RingedSpace.Modules X),
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X)) ((curriedTensor (RingedSpace.Modules X)).flip.obj ℱ)]

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ

/- Domain-style sampling for Lemma 20.50.1:
- primary domain: symmetric monoidal structures on cochain complexes, specialized to
  `\mathcal O_X`-modules on a ringed space;
- sampled owner declarations:
  `MonoidalCategory (CochainComplex C ℤ)`,
  `BraidedCategory (CochainComplex C ℤ)`,
  `SymmetricCategory (CochainComplex C ℤ)`,
  `SymmetricCategory.ofFaithful`;
- best owner abstraction: the core owner is the ambient typeclass
  `SymmetricCategory (CochainComplex (RingedSpace.Modules X) ℤ)`, supplied in the project by Chapter 15's generic
  cochain-complex construction;
- primitive vs. derived: the primitive data are the monoidal and symmetric structures on
  `(RingedSpace.Modules X)`
  together with the tensor exactness hypotheses needed to build the complex tensor product. The
  symmetric structure on `CpxX` is derived owner API and should therefore be recalled directly,
  not reintroduced through a local wrapper or witness declaration.

Source/core/bridge triage:
- `source-facing`: Lemma 20.50.1, the ringed-space specialization of the tensor symmetry on
  complexes of modules;
- `core/canonical`: the chapter owner instance `SymmetricCategory (CochainComplex C ℤ)` from
  Lemma 15.58.1;
- `bridge/view`: the specialization from a general preadditive symmetric monoidal category `C` to
  `(RingedSpace.Modules X)`.
-/

/- Lemma 20.50.1: the category of complexes of `\mathcal O_X`-modules on a ringed space carries
the symmetric monoidal structure whose tensor product is the total complex
`\mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X} \mathcal G^\bullet)`. In Lean, this is
the canonical `SymmetricCategory` instance on `CochainComplex (RingedSpace.Modules X) ℤ`, inherited from
the generic Chapter 15 owner for cochain complexes in any suitable symmetric monoidal preadditive
category. -/
#synth SymmetricCategory CpxX

end

end AlgebraicGeometry.RingedSpace

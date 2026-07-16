import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap06.RingedSpaceModuleCore
import StacksProject_2024.stacks_project.Chap18.Lemma_18_27_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (CochainComplex (X.Modules) ℤ)]
variable [BraidedCategory (CochainComplex (X.Modules) ℤ)]
variable [MonoidalClosed (CochainComplex (X.Modules) ℤ)]

local notation "CpxX" => CochainComplex (X.Modules) ℤ

/- Domain-style sampling for Lemma 20.41.1:
- primary domain: internal-Hom complexes and tensor-Hom currying for cochain complexes of
  `𝒪_X`-modules;
- inspected owner declarations:
  `MonoidalClosed.internalHomTensorIso`,
  `K ⟹ L`,
  the standard closed-monoidal notation `K ⟹ L`;
- best owner abstraction:
  the canonical owner is `MonoidalClosed.internalHomTensorIso`, displayed here on the ringed-space
  complex category `CpxX` through the standard internal-Hom notation `K ⟹ L`;
- primitive data:
  the ambient ringed site and the three cochain complexes;
- derived API:
  the source-facing ringed-space specialization of the currying isomorphism.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.1 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: `MonoidalClosed.internalHomTensorIso`;
- `bridge/view`: the opens-site specialization, restated directly on
  `CochainComplex (X.Modules) ℤ`.

The target file therefore belongs at the `bridge/view` layer and should directly reuse the
Chapter 18 closed-monoidal owner theorem instead of rebuilding a parallel ringed-space
internal-Hom complex, its differential, or an extra wrapper isomorphism locally. -/

/- Lemma 20.41.1: for cochain complexes `𝒦^•`, `𝓛^•`, and `𝓜^•` of `𝒪_X`-modules on a ringed
space `(X, 𝒪_X)`, the iterated internal-Hom complex `𝒦^• ⟹ (𝓛^• ⟹ 𝓜^•)` is canonically
isomorphic to the internal-Hom complex `((𝒦^• ⊗ 𝓛^•) ⟹ 𝓜^•)`. In the project API this is the
generic owner theorem `MonoidalClosed.internalHomTensorIso`, specialized to the ringed-space
complex category `CpxX` coming from the canonical site of opens of `X`. -/
recall CategoryTheory.MonoidalClosed.internalHomTensorIso

/- Specialized check for Lemma 20.41.1 on cochain complexes of `𝒪_X`-modules. -/
#check
  (internalHomTensorIso :
    ∀ K L M : CpxX, K ⟹ (L ⟹ M) ≅ (K ⊗ L) ⟹ M)

end

end AlgebraicGeometry.RingedSpace

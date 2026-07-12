import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap13.Remark_13_10_9

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [Preadditive X.Modules]
variable [HasZeroObject X.Modules]
variable [HasBinaryBiproducts X.Modules]
variable [MonoidalCategory X.Modules]
variable [(curriedTensor X.Modules).Additive]
variable [∀ ℱ : X.Modules, ((curriedTensor X.Modules).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex X.Modules ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor X.Modules)]

/-
Domain-style sampling for Lemma 20.26.1:
- primary domain: triangulated fixed-factor tensor-totalization functors on homotopy categories of
  cochain complexes in a preadditive monoidal category;
- sampled owner declarations:
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the Chapter 13 owner instances on the fixed-factor homotopy tensor
  functors attached to a bilinear bifunctor;
- primitive data here: only the ringed-space tensor bifunctor `curriedTensor X.Modules` and a
  fixed complex `𝒢`;
- derived API here: the inherited `CommShift` and `IsTriangulated` structures on the induced
  homotopy-category endofunctors.

Source/core/bridge triage:
- `source-facing`: the two exact fixed-factor tensor-totalization endofunctors on
  `K(𝒪_X)`;
- `core/canonical`: `Functor.map₂CochainComplex`, `Functor.mapHomotopyCategory`,
  `Functor.CommShift`, and `Functor.IsTriangulated`, already owned by
  `stacks_project/Chap13/Remark_13_10_9.lean`;
- `bridge/view`: the specialization from the general bilinear owner theorem to
  `curriedTensor X.Modules`.

This file therefore should expose only the source-facing ringed-space specializations, with no
local duplicate exactness witnesses. -/

variable (𝒢 : CochainComplex X.Modules ℤ)

/- Lemma 20.26.1: for a fixed complex `𝒢^•` of `𝒪_X`-modules on a ringed space `(X, 𝒪_X)`, the
homotopy-category functor `ℱ^• ↦ Tot (𝒢^• ⊗_{𝒪_X} ℱ^•)` is the canonical owner
`((curriedTensor X.Modules).map₂CochainComplex.obj 𝒢).mapHomotopyCategory (up ℤ)`, hence carries
the inherited shift compatibility and triangulated exactness from Remark `13.10.9`. -/
#check
  (inferInstance :
    (((curriedTensor X.Modules).map₂CochainComplex.obj 𝒢).mapHomotopyCategory
      (up ℤ)).CommShift ℤ)

#check
  (inferInstance :
    (((curriedTensor X.Modules).map₂CochainComplex.obj 𝒢).mapHomotopyCategory
      (up ℤ)).IsTriangulated)

/- Lemma 20.26.1: after fixing the same complex `𝒢^•` in the right factor, the homotopy-category
functor `ℱ^• ↦ Tot (ℱ^• ⊗_{𝒪_X} 𝒢^•)` is the canonical owner
`((curriedTensor X.Modules).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory (up ℤ)`, so it
likewise carries the inherited shift compatibility and triangulated exactness from Remark
`13.10.9`. -/
#check
  (inferInstance :
    (((curriedTensor X.Modules).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory
      (up ℤ)).CommShift ℤ)

#check
  (inferInstance :
    (((curriedTensor X.Modules).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory
      (up ℤ)).IsTriangulated)

end

end AlgebraicGeometry.RingedSpace

import Mathlib
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Lemma_18_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-
Domain-style sampling for Lemma 17.16.2:
- primary domain: sheaf tensor products of modules over the structure sheaf of a ringed space,
  built from the ambient sheaf-of-rings tensor product and module-sheafification functor;
- inspected owner declarations:
  `RingedSpace.ringCatSheaf`,
  `_root_.moduleTensor`,
  `_root_.moduleSheafification`,
  `_root_.moduleSheafificationTensorComparison`,
  `_root_.moduleSheafificationTensorIso`;
- best owner abstraction:
  the core/canonical owner is the site-level sheaf-of-rings API on
  `SheafOfModules (ringSheaf (Opens.grothendieckTopology X) X.sheaf)`, while the ringed-space
  surface is `SheafOfModules (RingedSpace.ringCatSheaf X)`;
- primitive data:
  two presheaves of `\mathcal O_X`-modules;
- derived API:
  the ringed-space specialization of the canonical tensor-sheafification comparison and its
  associated isomorphism.

Layer triage:
- `source-facing`: the canonical isomorphism between the tensor product of the sheafifications and
  the sheafification of the presheaf tensor product;
- `core/canonical`: the Chapter 18 owners `_root_.moduleTensor` and `_root_.moduleSheafification`;
- `bridge/view`: the specialization from a sheaf of commutative rings to the structure sheaf
  `X.sheaf`.
-/

/- Lemma 17.16.2: for presheaves of `\mathcal O_X`-modules `ℱ'` and `𝒢'`, the tensor product of
their sheafifications is canonically identified with the sheafification of their presheaf tensor
product. This is the ringed-space specialization of
`_root_.moduleSheafificationTensorIso`. -/
#check
  (moduleSheafificationTensorIso X.sheaf :
    ∀ (ℱ' 𝒢' : PresheafOfModules (RingedSpace.ringCatSheaf X).obj),
      (moduleSheafification X.sheaf).obj ℱ' ⊗ (moduleSheafification X.sheaf).obj 𝒢' ≅
        (moduleSheafification X.sheaf).obj (PresheafOfModules.Monoidal.tensorObj ℱ' 𝒢'))

end AlgebraicGeometry.RingedSpace

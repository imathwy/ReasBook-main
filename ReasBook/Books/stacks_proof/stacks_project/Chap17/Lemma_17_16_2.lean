import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Sites.Monoidal
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap18.Lemma_18_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory TopologicalSpace
open Functor.OplaxMonoidal

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [MonoidalCategory X.Modules]

/- Domain-style sampling for Lemma 17.16.2:
- primary domain: sheaf tensor products of modules over the structure sheaf of a ringed space,
  built from the ambient sheaf-of-rings tensor product and module-sheafification functor;
- inspected owner declarations:
  `RingedSpace.ringCatSheaf`,
  `_root_.moduleSheafification`,
  `Functor.OplaxMonoidal.δ`;
- best owner abstraction:
  the core/canonical owner is the Chapter 18 tensor/sheafification isomorphism
  `asIso (δ (_root_.moduleSheafification X.sheaf) _ _)`, and the present file is only its ringed-space
  specialization;
- primitive data:
  two presheaves of `\mathcal O_X`-modules;
- derived API:
  none beyond the direct specialization of the owner isomorphism.

Layer triage:
- `source-facing`: the canonical isomorphism between the tensor product of the sheafifications and
  the sheafification of the presheaf tensor product;
- `core/canonical`: `Functor.OplaxMonoidal.δ` on `_root_.moduleSheafification X.sheaf`;
- `bridge/view`: the specialization from a general sheaf of commutative rings to the structure
  sheaf `X.sheaf`.
-/

/- Lemma 17.16.2: for presheaves of `\mathcal O_X`-modules `ℱ'` and `𝒢'`, the tensor product of
their sheafifications is canonically identified with the sheafification of their presheaf tensor
product. This item is the direct ringed-space specialization of the Chapter 18 owner
`Functor.OplaxMonoidal.δ`. -/
#check (Functor.OplaxMonoidal.δ
  (_root_.moduleSheafification (J := Opens.grothendieckTopology X) X.sheaf))

end AlgebraicGeometry.RingedSpace

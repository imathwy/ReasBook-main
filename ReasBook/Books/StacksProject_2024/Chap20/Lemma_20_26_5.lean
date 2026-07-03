import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Definition_20_26_2
import StacksProject_2024.Chap15.Lemma_15_59_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (K L : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor ((RingedSpace.Modules X)))]

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O_X`-modules and their totalized tensor
  product;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.tensorObj_isKFlat_of_isKFlat`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction: the owner is the predicate `K.IsKFlat` on the complex itself, and the
  tensor product is the canonical monoidal tensor `K ⊗ L` on cochain complexes;
- primitive vs derived: the primitive data are only the complexes `K`, `L`, and their K-flatness
  hypotheses. The tensor complex `K ⊗ L` is derived from the ambient monoidal structure, so no
  extra wrapper data should appear in the public API.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of the tensor-closure statement for K-flat
  complexes;
- `core/canonical`: the owner theorem `CochainComplex.tensorObj_isKFlat_of_isKFlat`;
- `bridge/view`: the specialization of that owner theorem to `(RingedSpace.Modules X)`. -/

/- Lemma 20.26.5: if `\mathcal K^\bullet` and `\mathcal L^\bullet` are K-flat complexes of
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, then the totalized tensor product
`\mathrm{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal L^\bullet)` is K-flat. This is
exactly the specialization of the canonical owner theorem
`CochainComplex.tensorObj_isKFlat_of_isKFlat` to `(RingedSpace.Modules X)`. -/
recall CochainComplex.tensorObj_isKFlat_of_isKFlat

end AlgebraicGeometry.RingedSpace

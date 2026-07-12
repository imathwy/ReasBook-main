import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_59_4

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `𝒪_X`-modules and their totalized tensor
  product;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.tensorObj_isKFlat_of_isKFlat`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction: the owner is the predicate `K.IsKFlat` on the complex itself, and the
  tensor product complex is the canonical derived object `HomologicalComplex.tensorObj K L`;
- primitive vs derived: the primitive data are only the complexes `K`, `L`, and their K-flatness
  hypotheses. The tensor complex is derived from the ambient monoidal structure, so no extra
  wrapper data should appear in the public API.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of the tensor-closure statement for K-flat
  complexes;
- `core/canonical`: the owner theorem `CochainComplex.tensorObj_isKFlat_of_isKFlat`;
- `bridge/view`: the specialization of that owner theorem to `(RingedSpace.Modules X)`. -/

/- Lemma 20.26.5: if `𝒦^•` and `𝓛^•` are K-flat complexes of `𝒪_X`-modules on a ringed space
`(X, 𝒪_X)`, then the totalized tensor product `Tot (𝒦^• ⊗_{𝒪_X} 𝓛^•)` is K-flat. This is
exactly the specialization of the canonical owner theorem
`CochainComplex.tensorObj_isKFlat_of_isKFlat` to `RingedSpace.Modules X`. -/
recall CochainComplex.tensorObj_isKFlat_of_isKFlat

end AlgebraicGeometry.RingedSpace

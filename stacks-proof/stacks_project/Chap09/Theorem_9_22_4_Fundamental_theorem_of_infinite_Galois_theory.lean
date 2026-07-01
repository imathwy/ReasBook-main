import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]

/- Domain-style sampling for Theorem 9.22.4:
- primary domain: infinite Galois theory and the Krull-topological Galois correspondence;
- sampled owner declarations:
  `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`,
  `InfiniteGalois.fixedField_bot`,
  `InfiniteGalois.isOpen_iff_finite`,
  `InfiniteGalois.normal_iff_isGalois`;
- best owner abstraction: the order isomorphism
  `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`, whose primitive data are the canonical
  maps `IntermediateField.fixingSubgroup` and `IntermediateField.fixedField`;
- derived API: the `K = L^G` clause, the open-subgroup/finite-extension criterion, and the
  normal-subgroup/Galois-subextension criterion are theorem-level consequences of that owner.

Source/core/bridge triage:
- `source-facing`: the infinite Galois correspondence between intermediate fields and closed
  subgroups, together with its standard corollaries;
- `core/canonical`: `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`;
- `bridge/view`: the companion theorems `InfiniteGalois.fixedField_bot`,
  `InfiniteGalois.isOpen_iff_finite`, and `InfiniteGalois.normal_iff_isGalois`.

This item is a pure canonical recall: there is no extra source-facing wrapper to keep once the
owner declaration is identified. -/

/- Theorem 9.22.4 (Fundamental theorem of infinite Galois theory): for a Galois extension `L/K`,
with `Gal(L/K)` equipped with its canonical profinite topology, the infinite Galois correspondence
is the order isomorphism
`InfiniteGalois.IntermediateFieldEquivClosedSubgroup : IntermediateField K L ≃o
    (ClosedSubgroup Gal(L/K))ᵒᵈ`,
sending an intermediate field `M` to the closed subgroup `M.fixingSubgroup` of `Gal(L/K)` and a
closed subgroup `H` to the fixed field `IntermediateField.fixedField H`. -/
recall InfiniteGalois.IntermediateFieldEquivClosedSubgroup

/- Companion recall: the textbook equality `K = L^G` for `G = Gal(L/K)` is encoded by the infinite
Galois theorem `InfiniteGalois.fixedField_bot`, which states that the fixed field of the whole
Galois group, namely `IntermediateField.fixedField ⊤`, is the bottom intermediate field. -/
recall InfiniteGalois.fixedField_bot

/- Companion recall: under the infinite Galois correspondence, the finite intermediate fields are
exactly those whose fixing subgroup is open; this is `InfiniteGalois.isOpen_iff_finite`. -/
recall InfiniteGalois.isOpen_iff_finite

/- Companion recall: under the infinite Galois correspondence, normal closed subgroups correspond
exactly to intermediate fields that are Galois over the base field; this is
`InfiniteGalois.normal_iff_isGalois`. -/
recall InfiniteGalois.normal_iff_isGalois

end

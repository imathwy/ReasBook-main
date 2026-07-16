import stacks_proof.stacks_project.Chap09.Definition_9_21_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/- Domain-style sampling for Theorem 9.21.7:
- primary domain: finite Galois correspondence between intermediate fields and subgroups of
  `Gal(L / K)`;
- sampled owner declarations:
  `IsGalois.intermediateFieldEquivSubgroup`,
  `IsGalois.fixedField_top`,
  `IsGalois.of_fixedField_normal_subgroup`,
  `IsGalois.fixingSubgroup_normal_of_isGalois`;
- best owner abstraction: the finite Galois correspondence is owned by the order isomorphism
  `IsGalois.intermediateFieldEquivSubgroup`;
- primitive data: a finite-dimensional Galois extension `L / K`;
- derived API: the fixed field of the whole Galois group and the two normal/Galois directions of
  the correspondence are already exposed upstream as owner theorems and instances.

Layer triage:
- `source-facing`: the finite fundamental theorem identifying intermediate fields with subgroups of
  `Gal(L / K)`;
- `core/canonical`: `IsGalois.intermediateFieldEquivSubgroup`;
- `bridge/view`: `IsGalois.fixedField_top`,
  `IsGalois.of_fixedField_normal_subgroup`,
  `IsGalois.fixingSubgroup_normal_of_isGalois`.

This file should therefore stay a pure recall surface. A local restatement of the correspondence,
or a local bundled theorem for the normal-subgroup criterion, would only duplicate the canonical
owner API already used in the chapter. -/

/- Theorem 9.21.7 (Fundamental theorem of Galois theory): for a finite Galois extension `L/K`,
the canonical Galois correspondence is the order isomorphism
`IsGalois.intermediateFieldEquivSubgroup`, which identifies intermediate fields `M` with
subgroups `M.fixingSubgroup` of `Gal(L / K)` and sends a subgroup `H` to its fixed field
`fixedField H`. -/
recall IsGalois.intermediateFieldEquivSubgroup

/- Companion recall: the textbook equality `K = L^G` for `G = Gal(L/K)` is the canonical theorem
`IsGalois.fixedField_top`, which identifies the fixed field of the whole Galois group with the
bottom intermediate field. -/
recall IsGalois.fixedField_top

/- Companion recalls: under the finite Galois correspondence, a normal subgroup
`H ≤ Gal(L / K)` cuts out a Galois intermediate field `fixedField H` by
`IsGalois.of_fixedField_normal_subgroup`, and conversely an intermediate field `M` that is Galois
over `K` has normal fixing subgroup by `IsGalois.fixingSubgroup_normal_of_isGalois`. -/
recall IsGalois.of_fixedField_normal_subgroup

recall IsGalois.fixingSubgroup_normal_of_isGalois

end

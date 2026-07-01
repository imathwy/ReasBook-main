import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u

/- Domain-style sampling for the Baire category theorem in topological additive groups:
- primary domain: Baire spaces for complete topological additive groups with a countably generated
  neighborhood filter at `0`
- owner declarations inspected: `BaireSpace`, `dense_iInter_of_isOpen`,
  `BaireSpace.of_completelyPseudoMetrizable`, `uniformity_eq_comap_nhds_zero'`,
  `IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`
- best owner abstraction: `BaireSpace`

Layer triage:
- `source-facing`: the complete first-countable topological additive-group specialization of the
  Stacks lemma, restated at the source-faithful local countability-at-`0` level
- `core/canonical`: `BaireSpace` together with `dense_iInter_of_isOpen`
- `bridge/view`: the canonical right-uniform-space route from `uniformity_eq_comap_nhds_zero'`,
  countable generation of `𝓝 0`, and completeness to complete pseudometrizability, hence to
  `BaireSpace`

Primitive data is only the family `U : ℕ+ → Set M` together with the proofs that each `U n` is
open and dense. The countably generated uniformity, complete pseudometrizability, and resulting
`BaireSpace` structure are derived API from the canonical owner abstraction, so this file should
package that bridge once and then reuse the canonical Baire-space declarations directly. -/

section

variable {M : Type u} [TopologicalSpace M] [AddGroup M] [IsTopologicalAddGroup M]
  [(𝓝 (0 : M)).IsCountablyGenerated]
  [@CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)]
variable {U : ℕ+ → Set M}

/-- A complete topological additive group with countably generated `𝓝 0` is a Baire space. This
is the chapter-level bridge from the Stacks hypotheses to the canonical `BaireSpace` owner. -/
instance baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup : BaireSpace M := by
  letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  letI : CompleteSpace M := ‹@CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M)›
  haveI : (uniformity M).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero']
    exact Filter.comap.isCountablyGenerated _ _
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace M := inferInstance
  infer_instance

attribute [instance 100] baireSpace_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup

/-- Lemma 15.36.3 (Baire category theorem): in a complete topological additive group whose
neighborhood filter at `0` is countably generated, the intersection of countably many open dense
subsets is dense. This is the source-facing specialization of the canonical Baire-space theorem,
so the linear-topology hypothesis from the surrounding Stacks context is intentionally omitted from
the statement. -/
theorem dense_iInter_open_of_complete_countablyGenerated_nhds_zero_topologicalAddGroup
    (hU_open : ∀ n, IsOpen (U n)) (hU_dense : ∀ n, Dense (U n)) : Dense (⋂ n, U n) :=
  dense_iInter_of_isOpen hU_open hU_dense

end

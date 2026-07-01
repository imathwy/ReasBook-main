import Mathlib.Tactic.Recall
import stacks_project.Chap12.«12_23_5_1»
import stacks_project.Chap12.Lemma_12_24_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [Abelian 𝒜]
  [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]

namespace FilteredComplex

/- Domain-style sampling for 12.24.6.1:
- primary domain: filtration-stage inequalities for a differential in a filtered cochain complex;
- declarations inspected in the project owner API:
  `DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next`,
  `FilteredComplex.cohomologyCycleStep`,
  `FilteredComplex.eventualCycleStep`,
  `FilteredComplex.weakConvergenceCriterion`;
- best owner abstraction:
  `DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next`;
- primitive data: the differential `K.d n (n + 1)` and the source and target filtrations
  `(K.X n).filtration`, `(K.X (n + 1)).filtration`;
- derived API: the source-facing filtered-complex specialization
  `cohomologyCycleStep K n p ≤ eventualCycleStep K n p`;
- source/core/bridge triage:
  `source-facing`: equation `(12.24.6.1)` for a filtered complex;
  `core/canonical`: the two-filtration owner inequality on a morphism;
  `bridge/view`: the consecutive-degree specialization obtained by instantiating that owner theorem
    with the differential of `K`.

This item adds no new owner-level mathematics, so the refinement keeps only a direct recall of the
owner theorem and its filtered-complex specialization, rather than a parallel local theorem. -/

/- Equation `(12.24.6.1)` uses the canonical owner theorem
`DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next`; this
file only recalls that statement and specializes it to the differential of a filtered complex. -/
recall DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next

variable (K : FilteredComplex 𝒜) (n p : ℤ)

/- Equation `(12.24.6.1)` is the `bridge/view` specialization of the owner theorem to consecutive
degrees of the filtered complex. The anonymous example below is the fully elaborated filtered-
complex instance of `cohomologyCycleStep K n p ≤ eventualCycleStep K n p`, which keeps
elaboration stable while still reusing the owner theorem directly. -/
example :
    ((kernelSubobject ((K.d n (n + 1)).hom) ⊓ (K.X n).filtration.obj p) ⊔
        (K.X n).filtration.obj (p + 1)) ≤
      ⨅ r : ℕ,
        (((K.X n).filtration.obj p ⊓
              (Subobject.pullback ((K.d n (n + 1)).hom)).obj
                ((K.X (n + 1)).filtration.obj (p + r))) ⊔
            (K.X n).filtration.obj (p + 1)) := by
  exact
    DecreasingFiltration.kernel_inf_stage_sup_next_le_iInf_pullback_target_stage_sup_next
      ((K.d n (n + 1)).hom)
      (K.X n).filtration
      (K.X (n + 1)).filtration
      p

end FilteredComplex

end CategoryTheory

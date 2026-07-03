import StacksProject_2024.Chap12.Lemma_12_24_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

namespace DecreasingFiltration

variable {C : Type u} [Category.{v} C]
variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasImages C] [HasCoproducts C]
  [InitialMonoClass C]
variable {X Y : C}

/- Domain-style sampling for 12.24.6.2:
- primary domain: boundary-stage inequalities for a morphism between filtered objects, specialized
  later to consecutive differentials in a filtered cochain complex;
- declarations inspected in the project owner API:
  `DecreasingFiltration`,
  `FilteredComplex.eventualBoundaryStep`,
  `FilteredComplex.cohomologyBoundaryStep`,
  `imageSubobject_comp_le`;
- best owner abstraction:
  the morphism-level filtration inequality below in `DecreasingFiltration`;
- primitive data: a morphism `f : X ⟶ Y`, decreasing filtrations `F` on `X` and `G` on `Y`, and
  a stage index `p`;
- derived API: the filtered-complex specialization
  `FilteredComplex.eventualBoundaryStep K n p ≤ FilteredComplex.cohomologyBoundaryStep K n p`;
- source/core/bridge triage:
  `source-facing`: equation `(12.24.6.2)` for a filtered complex;
  `core/canonical`: the owner theorem
    `iSup_inf_image_prev_stage_sup_next_le_image_inf_stage_sup_next`;
  `bridge/view`: the consecutive-degree specialization to the differential of `K`.

The filtered-complex inequality is therefore refined through the morphism-level owner theorem,
rather than by keeping a hand-expanded local proof at the complex level. -/

-- Proof sketch: each summand in the supremum is bounded by
-- `imageSubobject f ⊓ G^p + G^{p+1}`. The `G^{p+1}` term is already on the right, and the image
-- term is controlled by `imageSubobject_comp_le` because the image of
-- `F^{p-r+1} X ⟶ X ⟶ Y` factors through the image of `f`.
/-- Core/canonical owner: for a morphism `f : X ⟶ Y` between filtered objects, the supremum of the
subobjects `(G^p Y ∩ im(F^{p-r+1} X ⟶ Y)) + G^{p+1} Y` is contained in
`im(f) ∩ G^p Y + G^{p+1} Y`. -/
theorem iSup_inf_image_prev_stage_sup_next_le_image_inf_stage_sup_next
    (f : X ⟶ Y) (F : DecreasingFiltration X) (G : DecreasingFiltration Y) (p : ℤ) :
    (⨆ r : ℕ, (G.obj p ⊓ imageSubobject ((F.obj (p - r + 1)).arrow ≫ f)) ⊔ G.obj (p + 1)) ≤
      (imageSubobject f ⊓ G.obj p) ⊔ G.obj (p + 1) := by
  refine iSup_le fun r ↦ sup_le ?_ le_sup_right
  refine le_sup_of_le_left ?_
  refine le_inf ?_ inf_le_left
  exact inf_le_right.trans (imageSubobject_comp_le _ _)

end DecreasingFiltration

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜]

namespace FilteredComplex

/- Domain-style sampling for 12.24.6.2:
- primary domain: boundary-stage inequalities for a differential in a filtered cochain complex;
- declarations inspected in the project owner API:
  `DecreasingFiltration.iSup_inf_image_prev_stage_sup_next_le_image_inf_stage_sup_next`,
  `FilteredComplex.eventualBoundaryStep`,
  `FilteredComplex.cohomologyBoundaryStep`,
  `FilteredComplex.weakConvergenceCriterion`;
- best owner abstraction:
  the morphism-level owner theorem
    `DecreasingFiltration.iSup_inf_image_prev_stage_sup_next_le_image_inf_stage_sup_next`;
- primitive data: a filtered complex `K`, a cohomological degree `n`, and a filtration index `p`;
- derived API: the source-facing inequality `(12.24.6.2)`;
- source/core/bridge triage:
  `source-facing`: equation `(12.24.6.2)` for a filtered complex;
  `core/canonical`: the owner theorem on a filtered morphism;
  `bridge/view`: the consecutive-degree specialization
    `eventualBoundaryStep K n p ≤ cohomologyBoundaryStep K n p`.

This item keeps only the source-facing filtered-complex specialization of the canonical
filtered-morphism theorem, deleting the previous hand-expanded local copy. -/

/-- Equation `(12.24.6.2)`: for a filtered complex, the eventual boundary representative is
contained in the intrinsic boundary representative for the `p`-th graded piece of
`H^n(K^•)`. -/
theorem eventualBoundaryStep_le_cohomologyBoundaryStep
    (K : FilteredComplex 𝒜) (n p : ℤ) :
    eventualBoundaryStep K n p ≤ cohomologyBoundaryStep K n p := by
  simpa [eventualBoundaryStep, cohomologyBoundaryStep] using
    DecreasingFiltration.iSup_inf_image_prev_stage_sup_next_le_image_inf_stage_sup_next
      ((K.d (n - 1) n).hom)
      ((K.X (n - 1)).filtration)
      ((K.X n).filtration)
      p

end FilteredComplex

end CategoryTheory

import stacks_project.Chap13.Definition_13_11_3
import stacks_project.Chap13.Lemma_13_12_5
import stacks_project.Chap13.Lemma_13_36_1
import stacks_project.Chap15.Lemma_15_79_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.ObjectProperty
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.80.1:
- primary domain: ghost maps in the derived category `D(R)`, detected by the canonical homology
  functor family and combined along finite chains of composable arrows;
- sampled owner declarations:
  `H^i`,
  `ComposableArrows`,
  `objectGeneratedStage_eq_iSup_intervalStages`,
  `exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero`;
- best owner abstraction: the source-facing stage condition should use the Chapter 13 owner
  `⟨ringSingle⟩_n`, the chain itself is canonically a `ComposableArrows`, and the stepwise
  vanishing mechanism is already owned upstream by
  `exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero`; the stage hypothesis should be
  converted only through the Chapter 13 interval-stage bridge, not through a new local ghost
  wrapper;
- primitive vs. derived:
  primitive data are the stage-membership hypothesis on the leftmost object and the degreewise
  vanishing of each arrow under all cohomology functors;
  derived API is the vanishing of the total composite, obtained by converting the stage
  hypothesis through the interval-stage bridge and then applying the owner-level truncation
  factorization from Lemma `13.12.5`.

Source/core/bridge triage:
- `source-facing`: the ghost hypothesis and the zero-composite conclusion;
- `core/canonical`: `⟨ringSingle⟩_n`, `ComposableArrows`, `H^i`,
  `exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero`;
- `bridge/view`: `objectGeneratedStage_eq_iSup_intervalStages`, used only to pass from the
  source-facing stage hypothesis to the canonical bounded-support owner. -/

-- Proof sketch: use `objectGeneratedStage_eq_iSup_intervalStages` only as a bridge from
-- `X.left ∈ ⟨ringSingle⟩_n` to an interval-stage presentation with explicit cohomological
-- support. After shifting so that the support interval starts in degree `0`, apply
-- `exists_factor_through_truncGE_of_stepwise_homologyMap_eq_zero`; the resulting factorization
-- passes through a truncation object that vanishes because the shifted source has cohomology
-- supported in fewer than `n` consecutive degrees. Undo the shift to obtain `X.hom = 0`.
/-- Lemma 15.80.1: if the leftmost object of a chain of composable morphisms in `D(R)` lies in
`⟨R[0]⟩_n` and every arrow is ghost, then the composite of the chain is zero. -/
theorem ghost_composite_zero_of_mem_objectGeneratedStage
    {n : ℕ+} {X : ComposableArrows DMod n}
    (hX : (⟨ringSingle⟩_n) X.left)
    (hghost : ∀ j (hj : j < n) (i : ℤ), (H^i).map (X.arrow j hj).hom = 0) :
    X.hom = 0 := sorry

end

end CategoryTheory

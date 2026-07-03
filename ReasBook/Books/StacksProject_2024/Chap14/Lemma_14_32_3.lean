import Mathlib
import StacksProject_2024.Chap14.Lemma_14_20_3
import StacksProject_2024.Chap14.Lemma_14_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial
open SSet.modelCategoryQuillen

universe u

/- Domain-style sampling for Lemma 14.32.3:
- primary domain: simplicial-set trivial Kan fibrations for augmented Čech nerve maps.
- sampled owner declarations:
  `CategoryTheory.Arrow.augmentedCechNerve`,
  `CategoryTheory.CechNerveTerminalFrom.iso`,
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.pullback_snd`,
  `trivialKanFibration_of_bijective_below_of_surjective_of_coskeletal`.
- best owner abstraction:
  the source-facing map is the canonical augmentation
  `(Arrow.mk f).augmentedCechNerve.hom`, and the target property “trivial Kan fibration” is the
  owner predicate `I.rlp`.
- primitive-vs-derived split:
  primitive data: only the function `f : A → B` and the surjectivity hypothesis `hf`;
  derived API: the augmented Čech nerve map, its comparison with the pullback of the coordinatewise
  map on `0`-coskeleta, and the base-change closure of `I.rlp`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the augmentation from the simplicial set of iterated
  fibre products of a surjective map is a trivial Kan fibration;
- `core/canonical`: `Arrow.augmentedCechNerve` for the augmentation object and `I.rlp` for the
  lifting property;
- `bridge/view`: identify the augmentation as the pullback of the coordinatewise map
  `cechNerveTerminalFrom A ⟶ cechNerveTerminalFrom B` along the diagonal map
  `const B ⟶ cechNerveTerminalFrom B`, then apply
  `trivialKanFibration_of_bijective_below_of_surjective_of_coskeletal` at `n = 0` and
  `I.rlp.pullback_snd`.

There is no exact upstream theorem with this source-facing interface, so the correct refinement is
to keep the theorem and express its proof route entirely through these canonical owners, rather than
introducing any local wrapper around the pullback comparison or the lifting-property owner. -/

-- Proof sketch: identify the simplicial set `U` from Example 14.3.5 with the Čech nerve of the
-- arrow `f : A ⟶ B`. Via `CechNerveTerminalFrom.iso`, the coordinatewise map
-- `cechNerveTerminalFrom A ⟶ cechNerveTerminalFrom B` is the `0`-coskeletal comparison attached to
-- `f`, so `trivialKanFibration_of_bijective_below_of_surjective_of_coskeletal` at `n = 0`
-- shows
-- it lies in `I.rlp`. The augmented Čech nerve map `(Arrow.mk f).augmentedCechNerve.hom` is the
-- pullback of that coordinatewise map along the diagonal map from the constant simplicial set on
-- `B`, hence `I.rlp.pullback_snd` gives the result.
/-- The boundary of a positive-dimensional simplex contains all vertices, so the inclusion on
`0`-simplices is bijective. -/
private theorem boundary_zero_bijective (n : ℕ) :
    Function.Bijective ((∂Δ[n + 1].ι).app (op ⦋0⦌)) := by
  constructor
  · intro x y h
    exact Subtype.ext h
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    intro hs
    have hcard := Fintype.card_le_of_surjective _ hs
    simp at hcard

/-- Lemma 14.32.3: if `f : A → B` is surjective, then the augmentation from the simplicial set
whose `n`-simplices are the `(n + 1)`-fold fibre products `A ×[B] ⋯ ×[B] A`, canonically
formalized as the augmented Čech nerve map `(Arrow.mk f).augmentedCechNerve.hom`, to the constant
simplicial set on `B` is a trivial Kan fibration. -/
theorem trivialKanFibration_cechNerveAugmentation_of_surjective
    {A B : Type u} (f : A → B) (hf : Function.Surjective f) :
    I.rlp ((Arrow.mk f).augmentedCechNerve.hom) := by
  apply boundaryInclusions_rlp_of_zero_surjective_and_boundary_lifting
  · intro b
    sorry
  · intro n
    sorry

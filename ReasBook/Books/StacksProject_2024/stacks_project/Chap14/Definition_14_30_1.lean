import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Simplicial
open SSet.modelCategoryQuillen

universe u

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Definition 14.30.1:
- primary domain: simplicial-set lifting properties in the Quillen model structure.
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I`,
  `CategoryTheory.MorphismProperty.rlp`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `HomotopicalAlgebra.Fibration`.
- owner abstraction: `SSet.modelCategoryQuillen.I.rlp`.
- primitive data: the right lifting property against the boundary inclusions `∂Δ[n].ι`.
- derived API: the textbook split into surjectivity on `0`-simplices and positive-dimensional
  boundary filling.

Source/core/bridge triage:
- `source-facing`: the textbook split into degree-zero surjectivity and positive-dimensional
  boundary filling;
- `core/canonical`: `I.rlp`;
- `bridge/view`: thin source-facing consequences and reconstruction lemmas relating the textbook
  split description to `I.rlp`.

This item should therefore expose `I.rlp` as the main owner and keep the textbook formulation only
through thin companion theorems, rather than a large conjunction-shaped wrapper. -/

/- Definition 14.30.1: a map of simplicial sets is a trivial Kan fibration precisely when it has
the right lifting property with respect to the boundary inclusions `∂Δ[n].ι`, i.e. when it
belongs to `SSet.modelCategoryQuillen.I.rlp`. -/
#check (I.rlp f : Prop)

/-- Every morphism in `I.rlp` lifts against each boundary inclusion `∂Δ[n].ι`. -/
theorem boundaryInclusions_rlp_hasLiftingProperty (n : ℕ) (hf : I.rlp f) :
    HasLiftingProperty (∂Δ[n].ι) f :=
  hf _ (boundary_ι_mem_I n)

/-- Bridge/view companion to Definition 14.30.1: a morphism in `I.rlp` is surjective on
`0`-simplices. This is the source-facing reformulation of lifting against `∂Δ[0].ι`. -/
theorem boundaryInclusions_rlp_zero_surjective
    (hf : I.rlp f) :
    Function.Surjective (f.app (op ⦋0⦌)) := sorry

/-- Source-facing reconstruction of `I.rlp` from surjectivity on `0`-simplices and fillers for
all positive-dimensional boundaries. -/
theorem boundaryInclusions_rlp_of_zero_surjective_and_boundary_lifting
    (h0 : Function.Surjective (f.app (op ⦋0⦌)))
    (hboundary : ∀ n : ℕ, HasLiftingProperty (∂Δ[n + 1].ι) f) :
    I.rlp f := sorry

/-- Bundled source-facing restatement of Definition 14.30.1. The owner-level predicate `I.rlp f`
is equivalent to the textbook split into surjectivity on `0`-simplices and fillers for all
positive-dimensional boundaries. -/
theorem boundaryInclusions_rlp_iff_zero_surjective_and_boundary_lifting :
    I.rlp f ↔
      Function.Surjective (f.app (op ⦋0⦌)) ∧
        ∀ n : ℕ, HasLiftingProperty (∂Δ[n + 1].ι) f := sorry

/- Companion recall: every isomorphism of simplicial sets has the boundary-inclusion right lifting
property, via the canonical owner theorem `I.rlp_of_isIso`. -/
#check I.rlp_of_isIso

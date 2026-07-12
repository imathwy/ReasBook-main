import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
variable [∀ n : ℕ, HasWidePullback.{0} f.right
  (fun _ : Fin (n + 1) ↦ f.left) (fun _ ↦ f.hom)]

/- Domain-style sampling for Example 14.3.5:
- primary domain: Čech nerves of arrows in a category with the required iterated wide pullbacks;
- sampled owner declarations:
  `Arrow.cechNerve`,
  `Arrow.augmentedCechNerve`,
  `SimplicialObject.cechNerve`,
  `SimplicialObject.augmentedCechNerve`;
- best owner abstraction: the source-facing object here is the arrow-level simplicial object
  `f.cechNerve`; the augmentation to the codomain is additional derived structure carried by
  `f.augmentedCechNerve`;
- primitive data: only the arrow `f` together with the wide-pullback existence assumptions needed
  by the canonical owner;
- derived API: the augmented companion `f.augmentedCechNerve`, the functorial construction
  `SimplicialObject.cechNerve`, the augmented functorial package
  `SimplicialObject.augmentedCechNerve`, and the degreewise wide-pullback face/degeneracy
  description coming from the owner definition.

Source/core/bridge triage:
- `source-facing`: the simplicial object `f.cechNerve` with `n`-simplices the `(n + 1)`-fold
  fibre product of `f.left` over `f.right`;
- `core/canonical`: the same mathlib owner `Arrow.cechNerve`;
- `bridge/view`: the augmented companion `Arrow.augmentedCechNerve` and the functorial packages
  `SimplicialObject.cechNerve` and `SimplicialObject.augmentedCechNerve`.

This file introduces no additional primitive data beyond the mathlib owner, so the correct
refinement is direct canonical use of `f.cechNerve`, with the augmentation recorded only as its
derived companion `f.augmentedCechNerve` rather than as a parallel local wrapper. -/

/- Example 14.3.5: for a morphism `f : Y ⟶ X` such that all iterated fibre products of `Y` over
`X` exist, the canonical simplicial object with `n`-simplices the `(n + 1)`-fold fibre product of
`Y` over `X` is `f.cechNerve`. In degree `0` one gets `Y`, in degree `1` one gets the self-fibre
product `Y ×[X] Y`, the two face maps are the projections, and the unique degeneracy is the
diagonal. -/
#check (f.cechNerve : SimplicialObject C)

/- Companion recall: the canonical owner declaration for this example is
`CategoryTheory.Arrow.cechNerve`. -/
recall cechNerve

/- Bridge/view: the augmentation to the constant simplicial object on `X` is the canonical derived
companion `f.augmentedCechNerve`. -/
#check (f.augmentedCechNerve : SimplicialObject.Augmented C)

/- Companion recall: the canonical augmented companion is
`CategoryTheory.Arrow.augmentedCechNerve`. -/
recall augmentedCechNerve

end CategoryTheory.Arrow

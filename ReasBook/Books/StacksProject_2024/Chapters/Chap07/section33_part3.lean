import Mathlib
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
import Mathlib.CategoryTheory.Sites.Point.Presheaf
import Mathlib.Tactic.Recall
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sober

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_7_33_8 (from Chap07) -/
namespace CategoryTheory

/- Domain-style sampling for Example 7.33.8:
- primary domain: points of the chaotic site `(C, ⊥)` and the induced fiber functor on
  presheaves;
- sampled owner declarations:
  `GrothendieckTopology.pointBot`,
  `GrothendieckTopology.pointBotPresheafFiberIso`,
  `GrothendieckTopology.pointBotFunctor`,
  `GrothendieckTopology.pointsBot`;
- source/core/bridge triage:
  `source-facing`: the point of the chaotic topology attached to `U₀` and the description of its
    fiber functor as evaluation at `U₀`;
  `core/canonical`: `GrothendieckTopology.pointBot` together with
    `GrothendieckTopology.pointBotPresheafFiberIso`;
  `bridge/view`: the presheaf-topos identification behind the fiber functor, already packaged by
    the owner isomorphism rather than by a local wrapper.

The primitive data are only the object `U₀ : C` and the ambient category. The evaluation
description of the corresponding presheaf fiber functor is derived API of the upstream owner, so
this item should stay a direct recall rather than introduce any parallel local definition or
comparison isomorphism.
-/
/- Example 7.33.8: in the chaotic Grothendieck topology on `C`, every object `U₀`
defines the canonical point `GrothendieckTopology.pointBot U₀`. -/
recall GrothendieckTopology.pointBot

/- Example 7.33.8 also identifies the corresponding presheaf fiber functor with evaluation at
`U₀`; this is the canonical mathlib isomorphism `GrothendieckTopology.pointBotPresheafFiberIso`,
which specializes to presheaves of sets in the Stacks-style formulation. -/
recall GrothendieckTopology.pointBotPresheafFiberIso

end CategoryTheory

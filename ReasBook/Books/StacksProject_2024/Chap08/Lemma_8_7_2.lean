import Mathlib
import StacksProject_2024.Chap04.Lemma_4_39_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 8.7.2:
- primary domain: absolute inertia of stacks in groupoids over a site, together with the setoid
  condition on fibers;
- inspected owner declarations:
  `CategoryOver.relativeInertiaStructureMap`,
  `absoluteInertiaStructureMap_isEquivalenceOverBase_iff_isFibredInSetoids`,
  `StackInGroupoidsOver`,
  `IsStackInSetoids`;
- best owner abstraction: the core/canonical owner is the Chapter 4 absolute-inertia criterion for
  the projection functor `S.p`; this lemma is the stack-level bridge from that owner theorem to
  the bundled object `S : StackInGroupoidsOver J`;
- primitive data: the projection functor `S.p` together with the ambient stack-on-site structure
  already carried by `S`;
- derived API: the stack-in-setoids predicate `IsStackInSetoids J S.p`.

Source/core/bridge triage:
- source-facing: the equivalence criterion for the absolute inertia map of a bundled stack in
  groupoids over `(C, J)`;
- core/canonical: `absoluteInertiaStructureMap_isEquivalenceOverBase_iff_isFibredInSetoids`
  on `S.p`;
- bridge/view: the passage from the bundled owner `S : StackInGroupoidsOver J` to its projection
  functor `S.p`. -/

-- Proof sketch: specialize the Chapter 4 absolute-inertia criterion to the projection functor
-- `S.p`. For a bundled stack in groupoids, `IsStackInSetoids J S.p` is exactly the derived owner
-- obtained by adjoining the already bundled stack-in-groupoids structure to the primitive datum
-- `IsFibredInSetoids S.p`.
/-- Lemma 8.7.2: if `S` is a stack in groupoids over the site `(C, J)`, then the canonical
`1`-morphism from the absolute inertia `I_S` to `S` is an equivalence over `C` if and only if
`S.p` is a stack in setoids. -/
theorem absoluteInertiaStructureMap_isEquivalenceOverBase_iff_isStackInSetoids
    (S : StackInGroupoidsOver J) :
    (relativeInertiaStructureMap (S : BasedCategory C).toBase).IsEquivalenceOverBase ↔
      IsStackInSetoids J S.p := by
  let hInertia :=
    absoluteInertiaStructureMap_isEquivalenceOverBase_iff_isFibredInSetoids S.p
  constructor
  · intro h
    letI : IsFibredInSetoids S.p :=
      hInertia.1 <| by simpa using h
    exact inferInstance
  · intro h
    exact hInertia.2 h.toIsFibredInSetoids

end CategoryTheory

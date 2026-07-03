import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
variable [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) ↦ f.right) fun _ ↦ f.hom]

/- Domain-style sampling for Example 14.5.5:
- primary domain: Čech conerves as cosimplicial objects attached to an arrow via iterated wide
  pushouts;
- sampled owner API:
  `CategoryTheory.Arrow.cechConerve`,
  `CategoryTheory.Arrow.augmentedCechConerve`,
  `CategoryTheory.Arrow.mapCechConerve`,
  `CategoryTheory.CosimplicialObject.cechConerve`;
- best owner abstraction: `CategoryTheory.Arrow.cechConerve`; the source-facing example is already
  the canonical owner declaration, so the main entry should be direct recall rather than a local
  wrapper or restatement;
- source/core/bridge triage:
  `source-facing`: the arrow-level cosimplicial object `f.cechConerve`;
  `core/canonical`: the same mathlib owner `CategoryTheory.Arrow.cechConerve`;
  `bridge/view`: the functorial packaging `CategoryTheory.CosimplicialObject.cechConerve` and the
  augmented variant `f.augmentedCechConerve`;
- primitive data: the arrow `f` and the degreewise wide-pushout existence assumptions;
- derived API: functoriality in morphisms of arrows, the augmented conerve, and the degreewise
  description by `(n + 1)`-fold pushouts. -/

/- Example 14.5.5: a morphism `f : X ⟶ Y` whose iterated pushouts exist determines the canonical
cosimplicial object `f.cechConerve`. Its term in degree `n` is the `(n + 1)`-fold pushout of
copies of `Y` over `X`, and a simplex map acts by sending the `i`-th copy of `Y` to the
`φ(i)`-th copy. In degree `0` and `1`, this gives the map `U₁ ⟶ U₀` that is the identity on each
component and the two maps `U₀ ⟶ U₁` given by the coprojections. -/
#check (f.cechConerve : CosimplicialObject C)

/- Companion recall: the canonical owner declaration for this example is
`CategoryTheory.Arrow.cechConerve`. -/
recall cechConerve

end CategoryTheory.Arrow

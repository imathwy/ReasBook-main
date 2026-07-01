import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_2

noncomputable section

open scoped Rockafellar
open Function

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.24 uses the textbook closure surface `cl F` for a bifunction.
- `core/canonical`: Definition 6.29.2 already fixes the graph function as `Function.uncurry F`,
  and Chapter 2 already fixes Rockafellar's closure owner as `cl(·)`.
- `bridge/view`: no additional bifunction closure owner is needed; `cl F` is a thin notation
  bridge built directly from the canonical graph closure `cl(Function.uncurry F)`.

Primary mathematical domain:
- closure of extended-valued bifunctions via their graph functions on `U × X`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`, showing the chapter pattern of
  source-facing owners implemented as thin specializations of earlier function-level owners;
- `Function.uncurry` from `Definition_6_29_2`;
- `Function.curry`;
- `lowerSemicontinuousHull`, written `cl(·)`, from `Chap02.Text_7_0_4`;
- `Function.uncurry_curry`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop α`;
- source-facing notation introduced here: `cl F`;
- canonical defining expression: `curry (cl(uncurry F))`;
- derived API retained here: the pointwise evaluation formula and the graph-function identity
  obtained by uncurrying `cl F`.

Ambient-structure check:
- the closure owner acts on the graph function `Function.uncurry F : U × X → WithBotTop α`;
- accordingly the minimal ambient structure is exactly a
  `ConditionallyCompleteLinearOrder α`, a `TopologicalSpace α`, and a `TopologicalSpace` on
  `U × X`.

Layer target: `source-facing`, with a thin bridge to the canonical Chapter 2 closure owner on the
graph function.
-/

/-- Definition 6.29.24: the closure `cl F` of a bifunction `F` is the bifunction whose graph
function is the Chapter 2 closure of the graph function `Function.uncurry F`.

This is intentionally a thin notation bridge to the canonical graph-level owner
`cl (Function.uncurry F)`. -/
scoped[Rockafellar] prefix:max "cl " =>
  (Function.curry ∘ _root_.lowerSemicontinuousHull ∘ Function.uncurry)

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
variable [TopologicalSpace (U × X)]

-- Proof sketch: unfold the notation `cl F`; evaluation of `Function.curry` at `(u, x)` is
-- definitionally evaluation of `cl (Function.uncurry F)` at `(u, x)`.
/-- Evaluating the bifunction closure is the same as evaluating the closed graph function at the
corresponding pair. -/
@[simp] theorem closure_apply (F : U → X → WithBotTop α) (u : U) (x : X) :
    cl F u x = cl(uncurry F) (u, x) :=
  rfl

-- Proof sketch: this is exactly the defining graph-function specification of
-- the notation `cl F`.
/-- Uncurrying the source-facing bifunction closure recovers the canonical graph closure. -/
@[simp] theorem uncurry_closure (F : U → X → WithBotTop α) :
    uncurry (cl F) = cl(uncurry F) :=
  rfl

end

end Bifunction

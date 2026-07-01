import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1

noncomputable section

universe u v

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: the unnumbered definition before Theorem 38.4 introduces the image `Ff` of a
  function `f` under a bifunction `F`, namely `x ↦ inf_u (f u + F u x)`.
- `core/canonical`: the existing Chapter 6 owner for pointwise infima in the second variable is
  `Bifunction.perturbationFunction`.
- `bridge/view`: the new Chapter 38 source object is exactly the perturbation function of the
  bifunction `(x, u) ↦ f u + F u x`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` and its pointwise formulas
  `perturbationFunction_apply_eq_sInf_range` / `perturbationFunction_apply` from
  `Chap06.Definition_6_29_1`;
- `Bifunction.lagrangian` from `Chap07.Theorem_36_5`, another source-facing owner defined as a
  thin bridge to an existing one-variable conjugation owner;
- `Function.linearImage` from `Chap01.Theorem_5_7`, the more specific image-of-a-function owner
  for linear transformations that this Chapter 38 object generalizes.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop α` and a function
  `f : U → WithBotTop α`, at the codomain-generic additive/lattice layer;
- primitive source-facing owner introduced here: `Bifunction.image F f`;
- derived API: the bridge to `perturbationFunction`, the `sInf`-of-range formula, and the indexed
  `iInf` formula.

Layer target: `source-facing`. The Chapter 38 image operation is a genuine new source object, but
its implementation reuses the existing perturbation-function owner instead of duplicating another
pointwise-infimum definition.

Notation decision: no new notation is introduced. The raw owner name `image` is short and stable,
while the textbook juxtaposition `Ff` does not translate into an inference-stable Lean notation.
-/

section

variable {U : Type u} {X : Type v} {α : Type*}
variable [ConditionallyCompleteLattice α] [Add α]

/-- Definition 38.0.4: the image of a function `f` under a bifunction `F`, defined by
`x ↦ inf_u (f u + F u x)`. -/
abbrev image (F : U → X → WithBotTop α) (f : U → WithBotTop α) : X → WithBotTop α :=
  perturbationFunction (fun x u ↦ f u + F u x)

/-- Evaluating `image F f` at `x` gives the infimum of the range of the kernel
`u ↦ f u + F u x`. -/
@[simp] theorem image_apply_eq_sInf_range
    (F : U → X → WithBotTop α) (f : U → WithBotTop α) (x : X) :
    image F f x = sInf (Set.range fun u ↦ f u + F u x) := by
  rfl

/-- Evaluating `image F f` at `x` is the indexed infimum `inf_u (f u + F u x)`. -/
@[simp] theorem image_apply
    (F : U → X → WithBotTop α) (f : U → WithBotTop α) (x : X) :
    image F f x = ⨅ u, (f u + F u x) := by
  simpa [image] using perturbationFunction_apply (fun x u ↦ f u + F u x) x

end

end Bifunction

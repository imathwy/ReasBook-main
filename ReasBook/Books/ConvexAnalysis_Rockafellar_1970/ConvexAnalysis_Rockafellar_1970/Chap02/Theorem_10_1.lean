import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_17

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousConstSMul ℝ E] [FiniteDimensional ℝ E]

noncomputable instance instTopologicalSpaceWithTopBotRealFromEReal :
    TopologicalSpace (WithTopBot ℝ) := by
  change TopologicalSpace EReal
  infer_instance

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.1 states continuity of a convex extended-real-valued function on any
  relatively open convex subset of its effective domain. The textbook coordinate presentation is a
  specialization of the intrinsic finite-dimensional real topological-vector-space owner layer used
  here.
- `core/canonical`: the owner abstractions are `ConvexOn` on sets,
  `IsRelativelyOpen`, the effective-domain set `{x : E | f x < ⊤}`, and the relative continuity
  owner `ContinuousOn`.
- `bridge/view`: Rockafellar's `ri (dom f)` is represented by the chapter notation `riDom(f)`.

Domain-style sampling used here:
- `ConvexOn` and `ConvexOn.subset`;
- `ConvexOn.convex_dom` from `Prop_4_4_1`;
- `IsRelativelyOpen` and `isRelativelyOpen_ri` from `Text_6_11`/`Text_6_17`;
- `Convex.intrinsicInterior` from `Theorem_6_2`;
- mathlib's owner notion `ContinuousOn`.

Primitive data vs derived API:
- primitive inputs: the function `f`, its convexity-on-set owner hypothesis, and a relatively open
  convex set `C` contained in `dom(f)`;
- derived API: continuity of `f` on `C`, and the special case `C = riDom(f)` from whole-space
  convexity owner data `ConvexOn ℝ Set.univ f`.

Scalar-layer check for this item:
- the source item is an extended-real convex-analysis statement, and the codomain owner is
  intrinsically `WithTopBot ℝ`;
- replacing `ℝ` by a different scalar would define a different mathematical object rather than a
  weakening of assumptions for the same owner;
- therefore the canonical surface remains explicitly real, with domain notation `riDom(f)`.

Layer target: this item stays `source-facing`, expressed directly with the canonical owners
`ConvexOn`, `IsRelativelyOpen`, and `ContinuousOn`, with the real-domain notation `riDom(·)`.
-/

namespace ConvexOn

variable {f : E → WithTopBot ℝ} {C : Set E}

/-- Theorem 10.1 at the primitive restricted owner layer: if a `WithTopBot ℝ`-valued function is
convex on `C`, then it is continuous relative to every relatively open `C` contained in its
effective domain. -/
-- Proof sketch: same as the source statement, but at the primitive restricted owner layer
-- `ConvexOn ℝ C`. The convexity of `C` needed in the intrinsic-interior step is contained in `hf`.
theorem continuousOn_of_isRelativelyOpen_subset_dom
    (hf : ConvexOn ℝ C f) (hC_open : IsRelativelyOpen ℝ C)
    (hC_dom : C ⊆ dom(f)) :
    ContinuousOn f C := sorry

/-- The relative interior of the effective domain is a canonical relatively open convex subset on
which a globally convex `WithTopBot ℝ`-valued function is continuous. -/
theorem continuousOn_riDom
    (hf : ConvexOn ℝ (Set.univ : Set E) f) :
    ContinuousOn f (riDom(f)) := sorry

end ConvexOn

namespace Function

variable {f : E → WithTopBot ℝ}

/-- Theorem 10.1 source-facing whole-space-owner form: if `f` is convex on `Set.univ`, then `f`
is continuous relative to every relatively open convex set contained in its effective domain. -/
theorem continuousOn_of_convexOn_univ
    (hf : ConvexOn ℝ (Set.univ : Set E) f) {C : Set E}
    (hC_open : IsRelativelyOpen ℝ C)
    (hC_conv : Convex ℝ C) (hC_dom : C ⊆ dom(f)) :
    ContinuousOn f C := by
  exact ConvexOn.continuousOn_of_isRelativelyOpen_subset_dom
    (hf := hf.subset (Set.subset_univ C) hC_conv) hC_open hC_dom

/-- Theorem 10.1 `ri (dom f)` corollary at the whole-space-owner layer
`ConvexOn ℝ Set.univ f`. -/
theorem continuousOn_riDom_of_convexOn_univ
    (hf : ConvexOn ℝ (Set.univ : Set E) f) :
    ContinuousOn f (riDom(f)) :=
  hf.continuousOn_riDom

end Function

end

import Mathlib
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.Recall
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Separation.Hausdorff

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_3_1 (from Chap05) -/
/- Domain-style sampling for Hausdorff diagonal criteria:
- owner abstraction: the separation owner `T2Space`, with canonical diagonal criterion
  `t2_iff_isClosed_diagonal`
- same-domain declarations inspected:
  `t2_iff_isClosed_diagonal`,
  `isClosed_diagonal`,
  `isClosed_eq`,
  `t2Space_iff_of_isOpenQuotientMap`

Layer triage:
- `source-facing`: the textbook criterion that `X` is Hausdorff exactly when the diagonal
  `diagonal X ⊆ X × X` is closed
- `core/canonical`: the owner theorem `t2_iff_isClosed_diagonal` for the separation class
  `T2Space`
- `bridge/view`: derived diagonal and equalizer consequences such as `isClosed_diagonal` and
  `isClosed_eq`

Primitive data is only the ambient topological space together with its diagonal subset
`diagonal X`. The closed-diagonal criterion is already the canonical owner statement, while
closedness of the diagonal under `[T2Space X]` and equalizer-closedness are derived API. This file
should therefore recall the owner theorem directly instead of introducing a parallel local
Hausdorff predicate or a duplicate diagonal-closedness wrapper.
-/

/- Lemma 5.3.1: a topological space is Hausdorff if and only if its diagonal in `X × X` is
closed. This is the canonical mathlib theorem `t2_iff_isClosed_diagonal`. -/
recall t2_iff_isClosed_diagonal

/-! ### Lemma_5_3_2 (from Chap05) -/
universe u v

open Set

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/- Domain-style sampling for Hausdorff equalizer-closedness and graphs:
- owner abstraction: `isClosed_eq`
- same-domain declarations inspected:
  `isClosed_eq`,
  `IsClosed.isClosed_eq`,
  `Set.mem_graphOn`,
  `Set.graphOn_univ_eq_range`

Layer triage:
- `source-facing`: the graph `univ.graphOn f` of a continuous map
- `core/canonical`: the Hausdorff equalizer-closedness theorem `isClosed_eq`
- `bridge/view`: the graph-closedness specialization below

Primitive data is just the graph owner `Set.graphOn` and the continuity data needed by
`isClosed_eq`. The closed-graph statement is derived API, so this file should stay a thin bridge to
the canonical equalizer theorem rather than introducing a parallel owner for closed graphs.
-/

/- Companion recall: the canonical Hausdorff equalizer-closedness theorem is `isClosed_eq`. -/
recall isClosed_eq

/-- Helper for Lemma 5.3.2: the graph of `f` is the preimage of the diagonal under the map
`p ↦ (f p.1, p.2)`. -/
lemma graph_eq_preimage_diagonal {X : Type u} {Y : Type v} {f : X → Y} :
    (univ.graphOn f : Set (X × Y)) = (fun p : X × Y ↦ (f p.1, p.2)) ⁻¹' diagonal Y := by
  -- Unpack both sides pointwise so the graph condition becomes membership in the diagonal.
  ext p
  simp [mem_graphOn, Set.mem_diagonal_iff]

/-- Lemma 5.3.2: if `f : X → Y` is continuous and `Y` is Hausdorff, then the graph
`univ.graphOn f` is closed in `X × Y`. This is the inverse-image-of-the-diagonal argument
from Lemma 5.3.1. -/
theorem isClosed_graph {f : X → Y} (hf : Continuous f) [T2Space Y] :
    IsClosed (univ.graphOn f) := by
  -- Rewrite the graph as the pullback of the diagonal along the canonical pair map.
  rw [graph_eq_preimage_diagonal]
  -- The diagonal is closed in a Hausdorff space, and continuous preimages of closed sets are closed.
  exact isClosed_diagonal.preimage (hf.fst'.prodMk continuous_snd)

/-! ### Lemma_5_3_3 (from Chap05) -/
/- Domain-style sampling for closed retract subspaces in Hausdorff spaces:
- owner abstraction: `Function.LeftInverse.isClosed_range`
- same-domain declarations inspected:
  `Function.LeftInverse`,
  `Function.leftInverse_iff_comp`,
  `Function.LeftInverse.isClosed_range`,
  `Function.LeftInverse.isClosedEmbedding`

Layer triage:
- `source-facing`: a continuous section/retraction pair with `f ∘ s = id`
- `core/canonical`: the left-inverse owner theorem `Function.LeftInverse.isClosed_range`
- `bridge/view`: rewriting the source section/retraction equation as a `Function.LeftInverse`

Primitive data is the left-inverse relation together with continuity of the two maps. The
section/retraction equation `f ∘ s = id` is derived presentation data via
`Function.leftInverse_iff_comp`, so this file should stay a direct recall of the owner theorem
rather than keeping a parallel local closed-range wrapper.
-/

/- Lemma 5.3.3: a retract subspace of a Hausdorff space is closed. This is exactly the canonical
theorem `Function.LeftInverse.isClosed_range`. -/
recall Function.LeftInverse.isClosed_range

/-! ### Lemma_5_3_4 (from Chap05) -/
universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Z]
variable {f : X → Z} {g : Y → Z}

/- Domain-style sampling for Hausdorff equalizer-closedness and fiber products:
- owner abstraction: `isClosed_eq`
- same-domain declarations inspected:
  `isClosed_eq`,
  `IsClosed.isClosed_eq`,
  `Continuous.fst'`,
  `Continuous.snd'`

Layer triage:
- `source-facing`: the fiber-product subset `{p : X × Y | f p.1 = g p.2}`
- `core/canonical`: the Hausdorff equalizer-closedness theorem `isClosed_eq`
- `bridge/view`: the fiber-product specialization below

Primitive data is just the equalizer subset in `X × Y` together with the continuity data needed by
`isClosed_eq`. The closed fiber-product statement is derived API, so this file should stay a thin
bridge to the canonical equalizer theorem rather than introducing a parallel local owner.
-/

/-
Companion recall: the canonical Hausdorff equalizer-closedness theorem is `isClosed_eq`.
-/
recall isClosed_eq

/-- Lemma 5.3.4: if `f : X → Z` and `g : Y → Z` are continuous and `Z` is Hausdorff, then the
fiber-product subset `X ×_Z Y = {p : X × Y | f p.1 = g p.2}` is closed in `X × Y`. This is the
canonical mathlib closed equalizer statement `isClosed_eq` applied to the maps
`fun p : X × Y ↦ f p.1` and `fun p : X × Y ↦ g p.2`. -/
theorem isClosed_fiberProduct_subset (hf : Continuous f) (hg : Continuous g) :
    IsClosed { p : X × Y | f p.1 = g p.2 } :=
  isClosed_eq hf.fst' hg.snd'

import Mathlib.Tactic.Recall
import Mathlib.Topology.SeparatedMap

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_4_1 (from Chap05) -/
/- Domain-style sampling for separated maps:
- owner abstraction: `IsSeparatedMap`
- same-domain declarations inspected:
  `IsSeparatedMap`,
  `isSeparatedMap_iff_isClosed_diagonal`,
  `T2Space.isSeparatedMap`,
  `IsSeparatedMap.pullback`

Layer triage:
- `source-facing`: the textbook notion that a map is separated
- `core/canonical`: `IsSeparatedMap`
- `bridge/view`: the closed-diagonal criterion and pullback stability theorems

Primitive data is exactly the owner predicate: points in one fiber can be separated by disjoint
open neighborhoods. The closed-diagonal criterion, Hausdorff-source specialization, and pullback
stability are derived API around that owner. The source's continuity hypothesis is redundant for
the core predicate, so this file should recall the canonical owner directly rather than
introducing a parallel local predicate or a large `_iff` wrapper as the main entry.
-/

/-
Definition 5.4.1: the textbook separatedness condition for a continuous map of topological spaces
is the canonical mathlib predicate `IsSeparatedMap`.
-/
recall IsSeparatedMap

/-! ### Lemma_5_4_2 (from Chap05) -/
/- Domain-style sampling for separated maps:
- owner abstraction: `IsSeparatedMap`
- relevant declarations inspected:
  project: `Definition_5_4_1` recalling `IsSeparatedMap`
  mathlib: `IsSeparatedMap`, `isSeparatedMap_iff_isClosed_diagonal`,
    `isSeparatedMap_iff_isClosedEmbedding`

Layer triage:
- `source-facing`: the textbook diagonal criterion for a separated map
- `core/canonical`: the owner predicate `IsSeparatedMap`
- `bridge/view`: the diagonal-closedness and closed-embedding criteria attached to that owner

Primitive data is only the owner predicate `IsSeparatedMap`. The closedness of the pullback
diagonal is derived API expressing the same notion canonically. Since `Definition_5_4_1` already
exposes the core owner, this file should stay at the `bridge/view` layer and recall the exact
owner-attached bridge theorem directly, rather than introducing a second local theorem shell or a
duplicated diagonal-closedness wrapper.
-/

/- Lemma 5.4.2: for a continuous map of topological spaces, being separated is equivalent to the
closedness of the diagonal subset `Δ(X) ⊆ X ×_Y X`. This is the exact canonical bridge theorem
`isSeparatedMap_iff_isClosed_diagonal`, used here as the `bridge/view` companion to
`Definition_5_4_1`; its statement already drops the redundant continuity and target-topology
hypotheses. -/
recall isSeparatedMap_iff_isClosed_diagonal

/-! ### Lemma_5_4_3 (from Chap05) -/
/- Domain-style sampling for separated maps:
- owner abstraction: `IsSeparatedMap`
- relevant declarations inspected:
  project: `Definition_5_4_1` recalling `IsSeparatedMap`
  mathlib: `IsSeparatedMap`, `T2Space.isSeparatedMap`,
    `isSeparatedMap_iff_isClosed_diagonal`, `IsSeparatedMap.pullback`

Layer triage:
- `source-facing`: a map from a Hausdorff source is separated
- `core/canonical`: the owner predicate `IsSeparatedMap`
- `bridge/view`: `T2Space.isSeparatedMap`, which produces the owner predicate from the Hausdorff
  source hypothesis

Primitive data is only the owner predicate `IsSeparatedMap`; Hausdorffness of the source is a
canonical sufficient hypothesis, not extra primitive data. Since `Definition_5_4_1` already
recalls the owner, this lemma should stay at the `bridge/view` layer and reuse the exact
owner-attached theorem `T2Space.isSeparatedMap` rather than introduce a parallel local theorem
with the redundant continuity hypothesis from the source prose.
-/

/- Lemma 5.4.3: a continuous map from a Hausdorff topological space is a separated map. The
canonical bridge theorem is `T2Space.isSeparatedMap`, whose statement already drops the redundant
continuity hypothesis. -/
recall T2Space.isSeparatedMap

/-! ### Lemma_5_4_4 (from Chap05) -/
/- Domain-style sampling for separated maps:
- owner abstraction: `IsSeparatedMap`
- relevant declarations inspected:
  project: `Definition_5_4_1` recalling `IsSeparatedMap`
  mathlib: `IsSeparatedMap`, `isSeparatedMap_iff_isClosed_diagonal`,
    `T2Space.isSeparatedMap`, `IsSeparatedMap.pullback`

Layer triage:
- `source-facing`: separatedness is preserved by base change
- `core/canonical`: the owner predicate `IsSeparatedMap`
- `bridge/view`: the base-change stability theorem `IsSeparatedMap.pullback`

Primitive data is only the owner predicate `IsSeparatedMap`. Closed-diagonal characterizations,
Hausdorff-source specializations, and pullback stability are derived API around that owner. Since
`Definition_5_4_1` already recalls the core owner, this lemma should remain a pure `bridge/view`
entry and reuse the exact owner theorem `IsSeparatedMap.pullback`: it already states separatedness
of the canonical second projection from the pullback and so matches the source's base-change
statement without any parallel local wrapper or extra continuity packaging.
-/

/- Lemma 5.4.4: separated maps are stable under pullback. This is exactly the canonical mathlib
bridge theorem `IsSeparatedMap.pullback`. -/
recall IsSeparatedMap.pullback

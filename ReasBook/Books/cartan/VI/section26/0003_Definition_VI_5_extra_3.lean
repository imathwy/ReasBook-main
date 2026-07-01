import Mathlib.Topology.Covering.Basic
import Mathlib.Tactic.Recall

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the covering-space owner layer was checked directly against
-- `Mathlib/Topology/Covering/Basic.lean` and the adjacent chapter file
-- `0002_Definition_VI_5_extra_2.lean`, which already uses `IsCoveringMap`.

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: the primary domain here is topology of covering maps. The relevant canonical
-- owner declarations are `IsEvenlyCovered`, `IsCoveringMapOn`, and `IsCoveringMap`. Primitive data
-- lives in the local evenly covered neighborhoods of `IsEvenlyCovered`; the global textbook
-- condition "every point admits such a neighborhood" is the derived owner `IsCoveringMap`.
-- This item therefore operates at the `core/canonical` layer, not as a separate source-facing
-- wrapper.

/- Definition VI.5-extra-3: the textbook condition that a map `φ : X → Y` be a covering map,
meaning that every point of `Y` admits an open neighborhood whose preimage is a disjoint union of
open sheets mapped homeomorphically onto that neighborhood, is exactly the canonical mathlib
owner `IsCoveringMap φ`. The local evenly covered neighborhoods themselves are represented
upstream by `IsEvenlyCovered`. -/
recall IsCoveringMap

import StacksProject_2024.Chap05.Definition_5_12_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology TopologicalSpace

universe u v

/- Domain-style sampling for quasi-compact images in topological spaces:
- owner declarations: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`
- canonical range compactness: `isCompact_range`
- canonical subset bridge: `IsRetrocompact_iff_isSpectralMap_subtypeVal`

Layer triage:
- `source-facing`: Lemma 5.12.7 identifies compactness and retrocompactness consequences for the
  image of a quasi-compact map
- `core/canonical`: `CompactSpace`, `IsSpectralMap`, `IsRetrocompact`
- `bridge/view`: the range inclusion `Set.range f → Y`

Primitive data is the owner predicate `IsSpectralMap f`; retrocompactness of `range f` is derived
through the canonical subtype-inclusion bridge.
-/

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- Canonical recall: if `X` is quasi-compact, then the image `f(X)` is quasi-compact. This is
exactly the canonical theorem `isCompact_range`. -/
recall isCompact_range

-- Proof sketch: apply `IsRetrocompact_iff_isSpectralMap_subtypeVal` to the subtype inclusion of
-- `range f` and use `hf` to show compactness of preimages of compact open subsets.
/-- Lemma 5.12.7: if `f` is quasi-compact, then the image `f(X)` is retrocompact. -/
theorem IsSpectralMap.isRetrocompact_range (hf : IsSpectralMap f) :
    IsRetrocompact (range f) := sorry

end

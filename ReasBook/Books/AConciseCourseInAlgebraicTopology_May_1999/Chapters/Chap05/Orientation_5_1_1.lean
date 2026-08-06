import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.CompactlyGenerated

open CategoryTheory

universe u w

-- Semantic search tool `lean_leansearch` was unavailable in this environment; verified locally
-- against mathlib's `Mathlib.Topology.Category.CompactlyGenerated`.

/- Orientation 5.1.1: before the chapter introduces its source-facing space-level owners, mathlib
already provides the bundled category `CompactlyGenerated.{u, w}` of `u`-compactly generated
`w`-small spaces and its canonical inclusion into `TopCat`. -/
recall CompactlyGenerated : Type _

/- A `u`-compactly generated space can be bundled as an object of `CompactlyGenerated`. -/
recall CompactlyGenerated.of (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    CompactlyGenerated.{u, w}

/- The category of compactly generated spaces embeds canonically into the ordinary category of
topological spaces. -/
recall CompactlyGenerated.compactlyGeneratedToTop :
    CompactlyGenerated.{u, w} ⥤ TopCat.{w}

/- This canonical inclusion is fully faithful, so `CompactlyGenerated` is a full subcategory of
`TopCat`. -/
recall CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop :
    CompactlyGenerated.compactlyGeneratedToTop.{u, w}.FullyFaithful

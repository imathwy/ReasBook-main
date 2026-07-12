import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.Definition_17_13_1

/- Domain-style sampling for Remark 6.32.6:
- primary domain: closed immersions of ringed spaces and their relation to the underlying closed
  embedding of topological spaces;
- sampled owner API:
  `Topology.IsClosedEmbedding`,
  `CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion`,
  `AlgebraicGeometry.RingedSpace.closedImmersionIdealSheaf`,
  `AlgebraicGeometry.RingedSpace.IsClosedImmersion`;
- best owner abstraction: the source-facing owner for the ringed-space notion is
  `AlgebraicGeometry.RingedSpace.IsClosedImmersion`;
- primitive data: a morphism of ringed spaces, the closed-embedding condition on its underlying
  map, local surjectivity of `𝒪_X ⟶ i_* 𝒪_Z`, and local generators for the kernel ideal sheaf;
- derived API: the ideal sheaf `closedImmersionIdealSheaf` and later module-theoretic consequences.

Source/core/bridge triage:
- `source-facing`: `AlgebraicGeometry.RingedSpace.IsClosedImmersion`;
- `core/canonical`: the canonical structure-sheaf map
  `AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap` and its kernel ideal sheaf;
- `bridge/view`: `Topology.IsClosedEmbedding` for the underlying topological map, and
  `CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion` for the topos-level analogue.

This item should therefore not introduce a Chapter 6 wrapper. The canonical refinement is a direct
forward recall of the later source-facing owner. -/

/- Remark 6.32.6: the relationship between closed immersions and ringed spaces is deferred in this
chapter. The canonical source-facing owner later used in the project is
`AlgebraicGeometry.RingedSpace.IsClosedImmersion`, so this file recalls that owner directly rather
than introducing a Chapter 6 duplicate. -/
recall AlgebraicGeometry.RingedSpace.IsClosedImmersion

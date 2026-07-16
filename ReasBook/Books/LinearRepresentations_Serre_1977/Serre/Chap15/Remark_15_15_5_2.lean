import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open Representation

/- Source/core/bridge triage:
- source-facing: Remark `15-15.5-2` is a proof note saying that, under the stronger later
  hypothesis `p ∤ |G|`, one may still choose a stable lattice in any finite-dimensional ordinary
  representation.
- core/canonical: the owner for that existence statement is already
  `Representation.exists_stableLattice`.
- bridge/view: the stronger divisibility hypothesis does not change the mathematical owner, so this
  remark should remain a direct recall rather than a new wrapper theorem restating the same
  existence claim with extra assumptions. -/

/- Remark 15-15.5-2 uses the existing stable-lattice existence owner. The later hypothesis
`p ∤ |G|` is stronger than what that owner needs, so no new declaration is introduced here. -/
recall exists_stableLattice

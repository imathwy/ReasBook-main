import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap17.KoszulSectionMap

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- 31.20.0.2: a finite family `f_\bullet` of global sections of `\mathcal O_X` canonically
determines the free-to-unit morphism `\mathcal O_X^{\oplus n} \to \mathcal O_X`. The current
repository already owns this bridge as `AlgebraicGeometry.RingedSpace.koszulSectionMap`, so this
item is a direct source-facing recall of that canonical map. -/
recall AlgebraicGeometry.RingedSpace.koszulSectionMap

import Mathlib
import Mathlib.RepresentationTheory.Intertwining
import LinearRepresentations_Serre_1977.Serre.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_4_6.Index
import LinearRepresentations_Serre_1977.Serre.Chap14.Exercise_14_14_4_6

/-!
Helper owner for `Infra_14_4_ProjectiveLift`.

The statement `FiniteProjectiveGroupAlgebraModule.exists_residueFieldReduction_iso` — every
finite projective `k[G]`-module is the reduction of a finite projective `A[G]`-module over the
complete Noetherian local base, Serre's Proposition 42 part (c) — is now fully proven in
`Serre.Chap14.Exercise_14_14_4_6` via the Newton-iteration idempotent lift, and is re-exported
from here through the import above.
-/

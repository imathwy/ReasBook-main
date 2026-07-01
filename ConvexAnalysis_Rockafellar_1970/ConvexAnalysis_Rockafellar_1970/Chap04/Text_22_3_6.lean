import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_22_1

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 22.3.6 is the weak-inequality Farkas alternative.
- `core/canonical`: the project owner is
  `xor_exists_feasible_point_or_weak_pairing_inequality_farkas_certificate`, stated on finite
  families of pairing-side coefficients.
- `bridge/view`: functional and concrete matrix-coordinate formulations are downstream
  specializations and should not be the primary public owner surface in this source-item file.

Layer target: canonical owner recall.
-/

/- Text 22.3.6 is recorded at the canonical pairing owner layer. Functional and
matrix-coordinate spellings are downstream bridge views of this theorem. -/
recall xor_exists_feasible_point_or_weak_pairing_inequality_farkas_certificate

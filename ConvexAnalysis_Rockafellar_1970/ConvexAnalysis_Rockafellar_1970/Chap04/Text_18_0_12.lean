import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 18.0.12 records the transitivity of faces of a convex set and its
  singleton specialization to extreme points.
- `core/canonical`: the chapter owner abstraction is `Set.IsFace`, with `Set.extremePoints` as the
  canonical owner for extreme points.
- `bridge/view`: clause (1) is the owner theorem `Set.IsFace.trans`; clause (2) is
  `Set.IsFace.extremePoints_subset`. On this file surface we expose the same content through the
  chapter notation `𝓕[R](C)` for the family of faces.
- Primitive data vs derived API: the item introduces no new data; it only records derived
  transitivity consequences of the existing owner declarations.
- Domain-style sampling used here: `Set.IsFace`, `Set.IsFace.trans`, `Set.faces`,
  `𝓕[R](C)`, `Set.extremePoints`, and `Set.IsFace.extremePoints_subset`.
- Layer target: `source-facing`, with theorem surfaces stated on the chapter face-family notation.
-/

/- Text 18.0.12 (1): faces are transitive; if `C''` is a face of `C'` and `C'` is a face of `C`,
then `C''` is a face of `C`. This is exactly the owner theorem `Set.IsFace.trans`. -/
recall Set.IsFace.trans

/- Text 18.0.12 (2): the extreme points of a face `C'` of `C` are extreme points of `C`.
This is exactly the owner theorem `Set.IsFace.extremePoints_subset`. -/
recall Set.IsFace.extremePoints_subset

/- Text 18.0.12 (notation bridge): transitivity directly on the chapter face-family notation
`𝓕[R](·)`. -/
recall Set.IsFace.mem_faces_trans

/- Text 18.0.12 (notation bridge): extreme points are monotone along face-family membership in
`𝓕[R](·)`. -/
recall Set.IsFace.extremePoints_subset_of_mem_faces

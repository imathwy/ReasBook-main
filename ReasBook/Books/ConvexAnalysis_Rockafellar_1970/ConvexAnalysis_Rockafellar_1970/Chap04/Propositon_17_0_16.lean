import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Proposition 17.0.16 is the closedness statement for generalized simplices
  (with textbook coordinate phrasing treated as a specialization, not as the owner layer).
- `core/canonical`: the chapter already fixed the owner abstraction in `Definition_2_3_12` as
  mathlib's bundled simplex `Affine.Simplex 𝕜 P m` with carrier
  `Affine.Simplex.closedInterior`; the closedness statement is then the canonical owner theorem
  `Affine.Simplex.isClosed`.
- `bridge/view`: Rockafellar's generalized simplex is represented by the canonical carrier
  `s.closedInterior`; the set-level convex-hull presentation is already reused upstream via the
  earlier chapter recall of `Affine.Simplex.convexHull_eq_closedInterior`.
- Primitive data vs derived API: the simplex `s` is the primitive owner datum; closedness of
  `s.closedInterior` is derived owner API and should not be duplicated under a concrete coordinate
  wrapper.
- Domain-style sampling used here: the earlier project recall `Affine.Simplex` from
  `Definition_2_3_12`, the upstream bridge `Affine.Simplex.convexHull_eq_closedInterior`, the
  owner theorem `Affine.Simplex.isClosed` (definitionally from
  `Affine.Simplex.isClosed_closedInterior`), and its supporting compactness owner
  `Affine.Simplex.isCompact_closedInterior`.
- Layer target: `core/canonical`; this item is exact owner reuse, so the main entry should be a
  direct `recall`, with a short canonical owner bridge theorem for theorem-surface use.
-/

/- Abstraction checklist for this item:
- codomain/ambient over-concretion: none; this item is purely geometric (`Set`-valued closedness
  of simplex carriers), with no extended-valued codomain owner involved.
- scalar/ambient minimization: the owner theorem remains at mathlib's generic ordered-field
  topological affine-space layer; no concrete `ℝ`/coordinate model is introduced.
- owner choice: use intrinsic owner `Affine.Simplex` (not a coordinate wrapper for generalized
  simplices).
- topology phrasing: the intrinsic carrier `s.closedInterior` is used directly as the theorem
  surface; no ambient-coordinate reformulation is introduced.
- owner naming/notation: expose short canonical owner `Affine.Simplex.isClosed` and pointwise
  dot usage `s.isClosed` instead of forcing repeated long raw owner names on theorem surfaces.
-/

section

variable {𝕜 : Type*} {V : Type*} {P : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]
variable [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [Module 𝕜 V] [ContinuousSMul 𝕜 V]
variable [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P] [T2Space P]

namespace Affine.Simplex

/-- Short canonical owner theorem: a simplex has closed carrier `closedInterior`. This is
definitionally the owner theorem `Affine.Simplex.isClosed_closedInterior`, exposed under the
short owner surface `Affine.Simplex.isClosed` (hence pointwise as `s.isClosed`). -/
theorem isClosed {n : ℕ} (s : Affine.Simplex 𝕜 P n) :
    IsClosed s.closedInterior :=
  s.isClosed_closedInterior

end Affine.Simplex

end

/- Proposition 17.0.16: generalized simplices are closed. This is exactly the canonical owner
theorem `Affine.Simplex.isClosed`; concrete coordinate formulations are downstream
specializations. -/
recall Affine.Simplex.isClosed

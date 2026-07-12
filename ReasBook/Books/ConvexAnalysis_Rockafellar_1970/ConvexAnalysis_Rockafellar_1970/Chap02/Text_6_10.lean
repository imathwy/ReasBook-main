import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Rockafellar's scalar-annotated notation for relative boundary. The textbook real notation is
`rb(C)`. -/
scoped[Rockafellar] notation "rb[" 𝕜 "](" C ")" => intrinsicFrontier 𝕜 C

/- Rockafellar's textbook notation for relative boundary in the real case. -/
scoped[Rockafellar] notation "rb(" C ")" => intrinsicFrontier ℝ C

/-
Source/core/bridge triage:
- `source-facing`: Text 6.10 names `(closure C) \ (ri C)` as the relative boundary of `C`.
- `core/canonical`: mathlib's owner notion for relative boundary is `intrinsicFrontier`.
- `bridge/view`: the canonical owner identity is
  `intrinsicClosure_diff_intrinsicInterior`; the ambient-closure textbook formula is first exposed
  through the primitive bridge premise `intrinsicClosure 𝕜 C = closure C`, then recovered as a
  finite-dimensional normed specialization via `intrinsicClosure_eq_closure`.
- Domain-style sampling: `intrinsicFrontier`, `intrinsicInterior`,
  `closure_diff_intrinsicInterior`,
  `closure_diff_intrinsicInterior_of_intrinsicClosure_eq_closure`,
  `intrinsicClosure_diff_intrinsicInterior`.
- Layer target: the main labeled entry is `core/canonical` at the intrinsic-closure layer.
- Source-facing owner notation: this file introduces the reusable chapter notation `rb[𝕜](C)`,
  with the textbook real specialization `rb(C)`, while `ri[𝕜](C)` is reused from `Text_6_8`.
-/

open scoped Rockafellar

/- Text 6.10: the relative boundary of a set `C` is mathlib's canonical
`intrinsicFrontier`, written on the chapter theorem surface as `rb[𝕜](C)` and, in the textbook
real case, `rb(C)`. -/
recall intrinsicFrontier

/- Canonical owner bridge for Text 6.10 at the intrinsic layer: relative boundary is intrinsic
closure minus relative interior. -/
recall intrinsicClosure_diff_intrinsicInterior
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] (C : Set P) :
    intrinsicClosure 𝕜 C \ ri[𝕜](C) = rb[𝕜](C)

/- Primitive ambient-closure bridge for Text 6.10: once intrinsic closure agrees with ambient
closure for a set, the textbook formula `closure C \ ri C = rb C` follows immediately from the
canonical intrinsic owner identity. -/
theorem closure_diff_intrinsicInterior_of_intrinsicClosure_eq_closure
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] (C : Set P)
    (hcl : intrinsicClosure 𝕜 C = closure C) :
    closure C \ ri[𝕜](C) = rb[𝕜](C) := by
  simpa [hcl] using (intrinsicClosure_diff_intrinsicInterior (𝕜 := 𝕜) (s := C))

/- Ambient-closure textbook bridge for Text 6.10, obtained at the finite-dimensional normed
specialization where `intrinsicClosure 𝕜 C = closure C`. -/
recall closure_diff_intrinsicInterior
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [MetricSpace P] [NormedAddTorsor V P] (C : Set P) :
    closure C \ ri[𝕜](C) = rb[𝕜](C)

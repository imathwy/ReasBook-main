import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Text 1.8 names the affine hull of a subset.
- `core/canonical`: the ambient owner abstraction is `AffineSubspace`, whose primitive
  construction for this notion is `affineSpan`.
- `bridge/view`: the source-facing textbook notation can be exposed directly as `aff[𝕜] s`; the
  containment/minimality/monotonicity clauses stay as thin bridges of the canonical owner lemmas.
- Domain-style sampling used here:
  `affineSpan`,
  `subset_affineSpan`,
  `affineSpan_le`,
  `affineSpan_mono`.
- Primitive data vs derived API: `affineSpan` is primitive; `subset_affineSpan` and
  `affineSpan_le` are the canonical derived containment/minimality lemmas.
- Layer target: `core/canonical` with a lightweight source-facing notation surface.
- Abstraction checks:
  - codomain/ambient layer: already intrinsic (`AffineSubspace` / `affineSpan`), not tied to a
    concrete coordinate model.
  - scalar/ambient assumptions: keep the owner's native `Ring` layer; no extra scalar strength is
    imposed.
  - owner naming surface: add short notation-facing theorem names (`subset_aff`, `aff_le_iff`,
    `aff_min`, `aff_mono`).
  - topology language: not a topological item.
-/
universe u v w

/-- Textbook notation for affine hull. The raw owner remains `affineSpan`. -/
scoped[Rockafellar] notation:max "aff[" 𝕜 "] " s => affineSpan 𝕜 s

open scoped Rockafellar

section

variable {𝕜 : Type u} {V : Type v} {P : Type w}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

/- Text 1.8: the affine hull of a subset is the canonical owner construction `affineSpan`. -/
recall affineSpan

/- The textbook containment and minimality clauses are the canonical owner lemmas
`subset_affineSpan` and `affineSpan_le`; monotonicity of hull formation is the companion canonical
bridge `affineSpan_mono`. -/
recall subset_affineSpan
recall affineSpan_le
recall affineSpan_mono

namespace Set

/-- Every set is contained in its affine hull, in textbook notation. -/
theorem subset_aff (s : Set P) : s ⊆ aff[𝕜] s :=
  _root_.subset_affineSpan 𝕜 s

/-- The affine-hull minimality criterion in textbook notation. -/
theorem aff_le_iff {s : Set P} {Q : AffineSubspace 𝕜 P} :
    (aff[𝕜] s) ≤ Q ↔ s ⊆ Q :=
  affineSpan_le

/-- Minimality in textbook notation: any affine subspace containing `s` contains `aff[𝕜] s`. -/
theorem aff_min {s : Set P} {Q : AffineSubspace 𝕜 P} (hsQ : s ⊆ Q) :
    (aff[𝕜] s) ≤ Q :=
  (aff_le_iff).2 hsQ

/-- Monotonicity of affine hull in textbook notation. -/
theorem aff_mono {s t : Set P} (hst : s ⊆ t) :
    (aff[𝕜] s) ≤ (aff[𝕜] t) :=
  _root_.affineSpan_mono 𝕜 hst

end Set

end

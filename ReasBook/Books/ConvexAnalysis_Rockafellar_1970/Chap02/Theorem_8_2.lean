import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open scoped Rockafellar

section

universe u

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

namespace Convex

/- 
Source/core/bridge triage:
- `source-facing`: the chapter owner remains `0⁺[𝕜] C`.
- `core/canonical`: mathlib's closed-convex owner is `asymptoticCone 𝕜 C`.
- `bridge/view`: the owner-side bridge `Convex.recessionCone_eq_asymptoticCone` compares the
  source-facing owner `0⁺[𝕜] C` with mathlib's owner `asymptoticCone 𝕜 C`, while
  `Convex.isClosed_recessionCone` is the direct closedness companion.
- Domain-style sampling used here: `recessionCone`, `Set.mem_recessionCone_iff`,
  `asymptoticCone 𝕜`, `isClosed_asymptoticCone`, and
  `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`.
- Primitive data vs derived API: the primitive input is the convex-set owner hypothesis
  `hCconv : Convex 𝕜 C`; the owner identification and closedness result are derived API.
- Ambient minimization: this bridge section uses the exact ordered-topological scalar bundle needed
  by the asymptotic-cone bridge APIs; no normed/completeness assumptions are included.
- Layer target: `bridge/view`.
-/

/-- For a nonempty closed convex set in an ordered topological vector space over `𝕜`, the
source-facing recession cone agrees with mathlib's asymptotic cone. The textbook real statement is
recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: for `y ∈ 0⁺ C`, every ray `x + a • y` starting from `C` stays in `C`,
-- so the filter definition of `asymptoticCone` is satisfied by taking points arbitrarily far out on
-- that ray. Conversely, if `y` lies in `asymptoticCone 𝕜 C`, closed convexity lets one recover the
-- full ray-invariance condition from the asymptotic-ray theorem in mathlib.
theorem recessionCone_eq_asymptoticCone {C : Set E} (hCconv : Convex 𝕜 C)
    (hCclosed : IsClosed C) (hCne : C.Nonempty) :
    0⁺[𝕜] C = asymptoticCone 𝕜 C := sorry

/-- The recession cone `0⁺[𝕜] C` of a closed convex set is closed. -/
-- Proof sketch: rewrite `recessionCone C` as `asymptoticCone 𝕜 C` using the comparison theorem
-- above on the nonempty case, and use `recessionCone ∅ = univ` in the empty case; then apply
-- `isClosed_asymptoticCone`.
theorem isClosed_recessionCone {C : Set E} (hCconv : Convex 𝕜 C) (hCclosed : IsClosed C) :
    IsClosed (0⁺[𝕜] C) := by
  by_cases hCne : C.Nonempty
  · simpa [hCconv.recessionCone_eq_asymptoticCone hCclosed hCne] using
      (isClosed_asymptoticCone (k := 𝕜) (s := C))
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCne
    simp [hCempty]

end Convex

end

section

universe u

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

namespace PointedCone

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 8.2 studies the recession cone `0⁺ C` of a nonempty closed
  convex set `C` in a finite-dimensional topological vector space `E` over `𝕜` via the chapter owner
  `K[𝕜 | C] = {(λ, x) | 0 ≤ λ, x ∈ λ • C}` in `𝕜 × E`.
- `core/canonical`: the owner-side objects are the generated cone owner
  `cone[𝕜] (L[𝕜 | C])`, the source-facing recession cone `0⁺[𝕜] C`, and mathlib's
  `asymptoticCone 𝕜 C`.
- `bridge/view`: Proposition 2.6.12 identifies `K[𝕜 | C]` with the canonical generated
  pointed cone under the present convexity and nonemptiness hypotheses, while the preceding
  owner-side bridge `Convex.recessionCone_eq_asymptoticCone` identifies the zero-height slice with
  the canonical asymptotic-cone owner.
- Primitive data vs derived API: the primitive set-level inputs are `C` and its closed, convex,
  and nonempty hypotheses; the closure formula for `cone[𝕜] (L[𝕜 | C])` is the canonical owner
  theorem, and the homogenization-set formula is a bridge via Proposition 2.6.12.
- Domain-style sampling: this item follows the chapter owner-side APIs
  `homogenizationSet_eq_pointedConeHull`, `PointedCone.closure`,
  `Convex.recessionCone_eq_asymptoticCone`, `cone[𝕜]`, and `L[𝕜 | C]`.
- Ambient minimization: the theorem surface itself does not use norm or completeness assumptions,
  so the public API stays at the finite-dimensional topological-vector-space layer.
- Layer target: the canonical owner theorem is stated first for `cone[𝕜] (L[𝕜 | C])` with
  `asymptoticCone 𝕜 C`; source-facing `K[𝕜 | C]` and `0⁺[𝕜] C` formulas are thin bridge
  corollaries.
-/

/-- Canonical cone-owner form of Theorem 8.2: if `C` is a nonempty closed convex subset of a
finite-dimensional topological vector space over `𝕜`, then the closure of the generated cone
`cone[𝕜] (L[𝕜 | C])` is obtained by adjoining exactly the zero-height slice
`({0} : Set 𝕜) ×ˢ (asymptoticCone 𝕜 C)`. -/
theorem closure_homogenizationCone_eq_union_zeroSlice_asymptoticCone (C : Set E)
    (hCconv : Convex 𝕜 C) (hCclosed : IsClosed C) (hCne : C.Nonempty) :
    closure (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) =
      (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) ∪ ({0} ×ˢ asymptoticCone 𝕜 C) := sorry

/-- Source-facing homogenization-set bridge for Theorem 8.2: rewrite the canonical cone-owner
formula through Proposition 2.6.12. -/
theorem closure_homogenizationSet_eq_union_zeroSlice_asymptoticCone (C : Set E)
    (hCconv : Convex 𝕜 C) (hCclosed : IsClosed C) (hCne : C.Nonempty) :
    closure (K[𝕜 | C]) = K[𝕜 | C] ∪ ({0} ×ˢ asymptoticCone 𝕜 C) := by
  simpa [pointedConeHull_lift_eq_homogenizationSet C hCconv hCne] using
    closure_homogenizationCone_eq_union_zeroSlice_asymptoticCone
      C (hCconv := hCconv) (hCclosed := hCclosed) (hCne := hCne)

/-- Source-facing recession-owner bridge at the canonical cone layer: rewrite the zero-height
slice in `closure_homogenizationCone_eq_union_zeroSlice_asymptoticCone` through
`Convex.recessionCone_eq_asymptoticCone`. -/
theorem closure_homogenizationCone_eq_union_zeroSlice (C : Set E)
    (hCconv : Convex 𝕜 C) (hCclosed : IsClosed C) (hCne : C.Nonempty) :
    closure (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) =
      (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) ∪ ({0} ×ˢ 0⁺[𝕜] C) := by
  simpa [hCconv.recessionCone_eq_asymptoticCone hCclosed hCne] using
    closure_homogenizationCone_eq_union_zeroSlice_asymptoticCone
      C (hCconv := hCconv) (hCclosed := hCclosed) (hCne := hCne)

/-- Theorem 8.2 in source-facing recession-cone form: if `C` is a nonempty closed convex subset
of a finite-dimensional topological vector space over `𝕜`, then the closure of
`K[𝕜 | C]` is obtained by adjoining exactly the zero-height slice
`({0} : Set 𝕜) ×ˢ (0⁺[𝕜] C)`. The textbook real statement is recovered by specializing
`𝕜 = ℝ`. -/
theorem closure_homogenizationSet_eq_union_zeroSlice (C : Set E) (hCconv : Convex 𝕜 C)
    (hCclosed : IsClosed C) (hCne : C.Nonempty) :
    closure (K[𝕜 | C]) = K[𝕜 | C] ∪ ({0} ×ˢ 0⁺[𝕜] C) := by
  simpa [pointedConeHull_lift_eq_homogenizationSet C hCconv hCne] using
    closure_homogenizationCone_eq_union_zeroSlice
      C (hCconv := hCconv) (hCclosed := hCclosed) (hCne := hCne)

end PointedCone

end

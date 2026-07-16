import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent

-- Declarations for this item will be appended below by the statement pipeline.

/-- Local notation surface for Text 1.9.1: `aff[𝕜] s` denotes the affine hull `affineSpan 𝕜 s`. -/
scoped[Rockafellar] notation:max "aff[" 𝕜 "] " s => affineSpan 𝕜 s

variable {𝕜 : Type*} {V : Type*} {P : Type*}
variable [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

open AffineSubspace
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 1.9.1 rewrites the affine span and affine independence of
  `b 0, b 1, ..., b m` in terms of a chosen base point and the corresponding tail
  difference vectors.
- `core/canonical`: the owner declarations are `affineSpan`, `AffineSubspace.mk'`,
  `vectorSpan_range_eq_span_range_vsub_right_ne`, and
  `affineIndependent_iff_linearIndependent_vsub`.
- `bridge/view`: first expose the intrinsic bridge over arbitrary index types using the complement
  subtype `{x // x ≠ i0}`, then specialize to the finite `Fin` tail view via `Fin.succAbove`,
  and finally to the textbook `0`-based view via `Fin.zero_succAbove`.
- Abstraction checks:
  - Codomain/ambient concreteness: already at the intrinsic affine-space owner layer
    (`AffineSubspace`/`Submodule`), with no concrete coordinate model.
  - Scalar-strength minimization: the recalled core bridges here are already `Ring`-level; this file
    does not strengthen to a concrete scalar model.
  - Owner concreteness: upstream from `Fin` by exposing an equivalence-indexed bridge before the
    `Fin.succAbove` specialization.
  - Topology language: not a topology statement; no ambient/intrinsic topology replacement needed.
  - Notation/owner surface: keep canonical owners (`affineSpan`, `AffineIndependent`) and expose
    the affine-span owner on theorem surfaces through the existing chapter notation `aff[𝕜]`.
- Layer target: `bridge/view`.
- Primitive data vs derived API: the family `b : Fin (m + 1) → P` is the only primitive data; the
  tail-span and tail-independence statements are derived API.
- Domain-style sampling used here:
  `AffineSubspace.mk'_eq`,
  `vectorSpan_range_eq_span_range_vsub_right_ne`,
  `affineIndependent_iff_linearIndependent_vsub`,
  `finSuccAboveEquiv`.
-/

/-- Intrinsic owner-level bridge for Text 1.9.1 (1): for any index type and chosen base index
`i0`, the affine span of a family is the translate through `b i0` of the span of the difference
vectors indexed by the complement subtype `{x // x ≠ i0}`. -/
theorem affineSpan_range_eq_mk'_span_vsub_ne
    {ι : Type*} (b : ι → P) (i0 : ι) :
    (aff[𝕜] (Set.range b)) = mk' (b i0)
      (Submodule.span 𝕜 (Set.range fun i : { x : ι // x ≠ i0 } ↦ b i -ᵥ b i0)) := by
  rw [← mk'_eq (mem_affineSpan 𝕜 (Set.mem_range_self i0)), direction_affineSpan 𝕜 (Set.range b),
    vectorSpan_range_eq_span_range_vsub_right_ne 𝕜 b i0]

/-- Internal reindexing helper for Text 1.9.1 (1): transport the complement-subtype span formula
along an equivalence of index types. -/
private theorem affineSpan_range_eq_mk'_span_vsub_equiv
    {ι : Type*} {ι' : Type*} (b : ι → P) (i0 : ι) (e : ι' ≃ { x : ι // x ≠ i0 }) :
    (aff[𝕜] (Set.range b)) = mk' (b i0)
      (Submodule.span 𝕜 (Set.range fun i : ι' ↦ b (e i) -ᵥ b i0)) := by
  rw [affineSpan_range_eq_mk'_span_vsub_ne (b := b) (i0 := i0)]
  congr 2
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, by simp⟩

/-- Finite-index bridge for Text 1.9.1 (1): reindex by `Fin.succAbove i0`. -/
private theorem affineSpan_range_eq_mk'_span_vsub_succAbove
    {m : ℕ}
    (b : Fin (m + 1) → P) (i0 : Fin (m + 1)) :
    (aff[𝕜] (Set.range b)) = mk' (b i0)
      (Submodule.span 𝕜 (Set.range fun i : Fin m ↦ b (i0.succAbove i) -ᵥ b i0)) := by
  simpa [finSuccAboveEquiv_apply] using
    affineSpan_range_eq_mk'_span_vsub_equiv (b := b) (i0 := i0)
      (e := finSuccAboveEquiv i0)

/-- Source-facing Text 1.9.1 (1): the affine span of `b 0, b 1, ..., b m` is the translate through
`b 0` of the span of the tail vectors `b i.succ -ᵥ b 0`. -/
theorem affineSpan_range_eq_mk'_span_vsub_tail
    {m : ℕ}
    (b : Fin (m + 1) → P) :
    (aff[𝕜] (Set.range b)) = mk' (b 0)
      (Submodule.span 𝕜 (Set.range fun i : Fin m ↦ b i.succ -ᵥ b 0)) := by
  simpa [Fin.zero_succAbove] using
    affineSpan_range_eq_mk'_span_vsub_succAbove (b := b) (i0 := 0)

/-- Intrinsic owner-level bridge for Text 1.9.1 (2): affine independence is equivalent to linear
independence of the `i0`-anchored difference vectors indexed by the complement subtype
`{x // x ≠ i0}`. -/
theorem affineIndependent_iff_linearIndependent_vsub_ne
    {ι : Type*} (b : ι → P) (i0 : ι) :
    AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : { x : ι // x ≠ i0 } ↦ b i -ᵥ b i0) := by
  simpa using affineIndependent_iff_linearIndependent_vsub 𝕜 b i0

/-- Internal reindexing helper for Text 1.9.1 (2): transport the complement-subtype
linear-independence criterion along an equivalence of index types. -/
private theorem affineIndependent_iff_linearIndependent_vsub_equiv
    {ι : Type*} {ι' : Type*} (b : ι → P) (i0 : ι) (e : ι' ≃ { x : ι // x ≠ i0 }) :
    AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : ι' ↦ b (e i) -ᵥ b i0) := by
  simpa [Function.comp] using
    (affineIndependent_iff_linearIndependent_vsub_ne (b := b) (i0 := i0)).trans
      ((linearIndependent_equiv e).symm)

/-- Finite-index bridge for Text 1.9.1 (2): reindex by `Fin.succAbove i0`. -/
private theorem affineIndependent_iff_linearIndependent_vsub_succAbove
    {m : ℕ}
    (b : Fin (m + 1) → P) (i0 : Fin (m + 1)) :
    AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : Fin m ↦ b (i0.succAbove i) -ᵥ b i0) := by
  simpa [finSuccAboveEquiv_apply] using
    affineIndependent_iff_linearIndependent_vsub_equiv (b := b) (i0 := i0)
      (e := finSuccAboveEquiv i0)

/-- Source-facing Text 1.9.1 (2): the points `b 0, b 1, ..., b m` are affinely independent if and
only if the difference vectors `b i.succ -ᵥ b 0` are linearly independent. -/
theorem affineIndependent_iff_linearIndependent_vsub_tail
    {m : ℕ}
    (b : Fin (m + 1) → P) :
    AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : Fin m ↦ b i.succ -ᵥ b 0) := by
  simpa [Fin.zero_succAbove] using
    affineIndependent_iff_linearIndependent_vsub_succAbove (b := b) (i0 := 0)

/-- Text 1.9.1: the affine span of `b 0, b 1, ..., b m` is the translate through `b 0` of the
span of the tail difference vectors, and affine independence of the points is equivalent to linear
independence of those tail vectors. -/
theorem affineSpan_and_affineIndependent_vsub_tail
    {m : ℕ}
    (b : Fin (m + 1) → P) :
    (aff[𝕜] (Set.range b)) = mk' (b 0)
      (Submodule.span 𝕜 (Set.range fun i : Fin m ↦ b i.succ -ᵥ b 0)) ∧
    (AffineIndependent 𝕜 b ↔
      LinearIndependent 𝕜 (fun i : Fin m ↦ b i.succ -ᵥ b 0)) := by
  constructor
  · -- The affine-hull clause is exactly the established tail-span bridge.
    exact affineSpan_range_eq_mk'_span_vsub_tail (𝕜 := 𝕜) (b := b)
  · -- The independence clause is exactly the established tail-vector criterion.
    exact affineIndependent_iff_linearIndependent_vsub_tail (𝕜 := 𝕜) (b := b)

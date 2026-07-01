import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]
variable {I : Sort*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.5.2.1 identifies the polar of the convex hull of a family of
  sets with the intersection of the individual polar sets.
- `core/canonical`: the owner abstractions already present in the project are the source-facing
  set polar `Set.polar : Set X → Set Y` and the convex hull `convexHull 𝕜 (⋃ i, C i)`.
- `bridge/view`: Rockafellar's notation `Cᵒ[𝕜]` is used directly on the theorem surface, while
  `conv {C_i | i ∈ I}` is rendered by `convexHull 𝕜 (⋃ i, C i)`.

Domain-style sampling used here:
- `Set.polar`;
- the scalar-parameterized notation `Cᵒ[𝕜]`;
- `Set.mem_polar_iff`;
- `convexHull_min`.

Primitive data vs derived API:
- primitive input: a family of primal sets `C : I → Set X` with dual points in `Y`, on a
  module/pairing layer equipped with swap compatibility;
- derived output: the polar/intersection identity itself.

Layer target: `source-facing`, stated directly as an equality in the pairing owner layer
`Set X → Set Y`, with no specialization to `ℝ` or self-dual ambient choices. Specializing to
`X = Y` with the canonical self-dual pairing recovers the textbook `R^n` statement. The source
assumption that each `C i` is convex is redundant for this identity and is therefore omitted from
the public statement.
-/

-- Proof sketch: use `Set.mem_polar_iff` for the two inclusions.
-- `⊆`: membership in the polar of the convex hull immediately restricts to each `C i` via
-- `subset_convexHull`.
-- `⊇`: if `xStar` is in every `(C i)ᵒ[𝕜]`, then `⟪xStar, ·⟫ ≤ 1` on the union.
-- Using pairing swap, this says `⟪·, xStar⟫ ≤ 1` on the union. The latter inequality defines a
-- convex half-space, so by `convexHull_min` it holds on `convexHull 𝕜 (⋃ i, C i)`, and swapping
-- back yields membership in the left polar.
/-- Corollary 16.5.2.1: the polar of the convex hull of a family of sets is the intersection of
the individual polars at the pairing owner level `Set X → Set Y`. Specializing `X = Y` with the
canonical self-dual pairing recovers the source `R^n` statement. The source assumption that each
`C i` is convex is redundant for this identity. -/
theorem polar_convexHull_iUnion_eq_iInter_polar
    (C : I → Set X) :
    ((convexHull 𝕜 (⋃ i : I, C i))ᵒ[𝕜] : Set Y) = ⋂ i : I, (C i)ᵒ[𝕜] := by
  ext xStar
  constructor
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro i
    refine Set.mem_polar_iff.2 ?_
    intro x hxCi
    have hxconv : x ∈ convexHull 𝕜 (⋃ j : I, C j) :=
      subset_convexHull 𝕜 (⋃ j : I, C j) <| Set.mem_iUnion.2 ⟨i, hxCi⟩
    exact Set.mem_polar_iff.1 hx x hxconv
  · intro hx
    let H : Set X := {x : X | (⟪x, xStar⟫ₚ : 𝕜) ≤ (1 : 𝕜)}
    have hH_convex : Convex 𝕜 H := by
      intro x hxH y hyH a b ha hb hab
      change (⟪a • x + b • y, xStar⟫ₚ : 𝕜) ≤ (1 : 𝕜)
      have hx1 : (⟪x, xStar⟫ₚ : 𝕜) ≤ (1 : 𝕜) := hxH
      have hy1 : (⟪y, xStar⟫ₚ : 𝕜) ≤ (1 : 𝕜) := hyH
      calc
        (⟪a • x + b • y, xStar⟫ₚ : 𝕜)
            = a * (⟪x, xStar⟫ₚ : 𝕜) + b * (⟪y, xStar⟫ₚ : 𝕜) := by
                simp [HasLinearPairing.pairing_eq_pairingLinear]
        _ ≤ a * (1 : 𝕜) + b * (1 : 𝕜) := by
              exact add_le_add (mul_le_mul_of_nonneg_left hx1 ha)
                (mul_le_mul_of_nonneg_left hy1 hb)
        _ = (1 : 𝕜) := by simpa [mul_one] using hab
    have hUnion_subset : (⋃ i : I, C i) ⊆ H := by
      intro x hxU
      rcases Set.mem_iUnion.1 hxU with ⟨i, hxi⟩
      have hxiPolar : xStar ∈ (C i)ᵒ[𝕜] := (Set.mem_iInter.1 hx) i
      exact (Set.mem_polar_iff_swap (C := C i) (xStar := xStar)).1 hxiPolar x hxi
    have hConv_subset : convexHull 𝕜 (⋃ i : I, C i) ⊆ H :=
      convexHull_min hUnion_subset hH_convex
    refine (Set.mem_polar_iff_swap (C := convexHull 𝕜 (⋃ i : I, C i)) (xStar := xStar)).2 ?_
    intro z hz
    exact hConv_subset hz

end

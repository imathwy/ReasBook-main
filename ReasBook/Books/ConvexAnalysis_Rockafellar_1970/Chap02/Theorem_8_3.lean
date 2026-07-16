import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

universe u v

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-
Source/core/bridge triage:

- `source-facing`: Theorem 8.3 says that for a closed convex set, the existence of one forward ray
  in direction `y` forces `y` to be a recession direction for the whole set. Its second clause
  then upgrades recession directions of `C` to recession directions of `ri C`.
- `core/canonical`: the owner-side notions already present in the chapter are the source-facing
  `0⁺[𝕜] C` from Definition 8.0.2, together with mathlib's `Convex 𝕜`, `closure`, and
  `intrinsicInterior 𝕜`. The derived API therefore belongs on the `Convex` owner abstraction
  rather than as parallel flat wrappers.
- `bridge/view`: Rockafellar's `0⁺ C` and `0⁺ (ri C)` are rendered here by the scalar-parameterized
  owner `0⁺[𝕜] C` and `0⁺[𝕜] (ri[𝕜](C))`; the
  textbook real surface is recovered by specializing `𝕜 = ℝ`.
- Domain-style sampling used here: `recessionCone`, `Set.mem_recessionCone_iff`,
  `Set.mem_recessionCone_iff_vadd`,
  `Convex.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone`,
  `Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior`, and the
  chapter owner
  notation `ri[𝕜](C)`.
- Primitive data vs derived API: the primitive inputs are the set `C`, the direction `y`, the
  closed/convex hypotheses, and one chosen base-point ray witness for part (1). The explicit
  base-point theorem is therefore the primitive owner-side API, while the existential source
  formulation is kept as a thin companion. The owner-style content of part (2) is the cone
  inclusion `0⁺ C ⊆ 0⁺ (ri C)`; the pointwise membership implication is derived from that
  inclusion and should not remain the primitive public statement.
- Layer target: this item remains `source-facing`, expressed in the chapter's existing
  recession-cone language but with the derived API placed on the `Convex` owner. The ray criterion
  stays at the general ordered topological-semimodule level, while the `intrinsicInterior`
  clause is stated at the intrinsic-closure topological-vector-space level already canonicalized
  in Chapter 6.
-/

namespace Convex

variable {C : Set E} {x y : E}

/-- Primitive owner-side affine-action form of Theorem 8.3 (1): if a closed convex set `C`
contains the forward nonnegative ray `a • y +ᵥ x` from a chosen base point `x`, then `y` lies in
the recession cone `0⁺[𝕜] C`. The textbook real formulation is recovered by specializing `𝕜 = ℝ`,
while additive `x + a • y` source wording is the companion theorem below. -/
-- Proof sketch: for any `z ∈ C` and `a ≥ 0`, convexity puts
-- `t • y +ᵥ x ∈ C` for all `t ≥ 0`, so the ray produces `y ∈ asymptoticCone 𝕜 C`; then the
-- closed-convex asymptotic-cone ray theorem gives `z + a • y ∈ C` for every `z ∈ C`, `a ≥ 0`.
theorem mem_recessionCone_of_nonneg_vadd_ray (hC : Convex 𝕜 C) (hCclosed : IsClosed C)
    (hRay : ∀ a : 𝕜, 0 ≤ a → a • y +ᵥ x ∈ C) :
    y ∈ 0⁺[𝕜] C := by
  have hy_asymptotic : y ∈ asymptoticCone 𝕜 C := by
    rw [mem_asymptoticCone_iff]
    have hRay_eventually : ∀ᶠ a : 𝕜 in Filter.atTop, a • y + x ∈ C := by
      filter_upwards [Filter.eventually_ge_atTop (0 : 𝕜)] with a ha
      simpa [vadd_eq_add] using hRay a ha
    exact
      ((Filter.Tendsto.atTop_smul_const_tendsto_asymptoticNhds
          (k := 𝕜) (l := Filter.atTop) y Filter.tendsto_id).asymptoticNhds_vadd_const x).frequently
        (Filter.Eventually.frequently <| by simpa [vadd_eq_add] using hRay_eventually)
  rw [Set.mem_recessionCone_iff_vadd]
  intro z hz a ha
  exact hC.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone hCclosed ha hy_asymptotic hz

/-- Source-facing additive form of Theorem 8.3 (1): if a closed convex set `C` contains the
forward nonnegative ray `x + a • y` from a chosen base point `x`, then `y ∈ 0⁺[𝕜] C`. -/
theorem mem_recessionCone_of_nonneg_ray (hC : Convex 𝕜 C) (hCclosed : IsClosed C)
    (hRay : ∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C) :
    y ∈ 0⁺[𝕜] C := by
  refine hC.mem_recessionCone_of_nonneg_vadd_ray (x := x) hCclosed ?_
  intro a ha
  simpa [vadd_eq_add, add_comm] using hRay a ha

/-- Owner-level positive-ray form of Theorem 8.3 (1): if `x ∈ C` and all strictly positive
translates `x + a • y` stay in a closed convex set `C`, then `y ∈ 0⁺[𝕜] C`. -/
-- Proof sketch: reduce to the nonnegative-ray criterion by splitting `a ≥ 0` into `a = 0` and
-- `0 < a`.
theorem mem_recessionCone_of_pos_ray (hC : Convex 𝕜 C) (hCclosed : IsClosed C) (hx : x ∈ C)
    (hRay : ∀ a : 𝕜, 0 < a → x + a • y ∈ C) :
    y ∈ 0⁺[𝕜] C := by
  refine hC.mem_recessionCone_of_nonneg_vadd_ray (x := x) hCclosed ?_
  intro a ha
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simpa [vadd_eq_add] using hx
  · simpa [vadd_eq_add, add_comm] using hRay a ha_pos

/-- Theorem 8.3 (1), source-facing form: if a closed convex set `C` contains one forward
strictly-positive ray `{x + a • y | 0 < a}` from a base point `x ∈ C`, then `y` lies in the
recession cone `0⁺[𝕜] C`. The source's real topological-vector-space statement is recovered by
specializing `𝕜 = ℝ`. -/
-- Proof sketch: extract the base point and apply the owner-level positive-ray theorem above.
theorem mem_recessionCone_of_exists_pos_ray (hC : Convex 𝕜 C) (hCclosed : IsClosed C)
    (hRay : ∃ x : E, x ∈ C ∧ ∀ a : 𝕜, 0 < a → x + a • y ∈ C) :
    y ∈ 0⁺[𝕜] C := by
  rcases hRay with ⟨x, hx, hRay⟩
  exact hC.mem_recessionCone_of_pos_ray (x := x) hCclosed hx hRay

end Convex

end

section

open scoped Rockafellar

universe u v

variable {𝕜 : Type v} [Field 𝕜] [PartialOrder 𝕜] [PosMulReflectLT 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

namespace Convex

/-- Theorem 8.3 (2): for a convex set in a topological vector space over an ordered field `𝕜`,
recession direction of `C` is also a recession direction of its relative interior `ri[𝕜](C)`,
formalized here as the owner-level inclusion `0⁺[𝕜] C ⊆ 0⁺[𝕜] (ri[𝕜](C))`. The source's real
statement is recovered by specializing `𝕜 = ℝ`. -/
-- Proof sketch: let `x ∈ ri[𝕜](C)` and `a ≥ 0`. Since `y ∈ 0⁺[𝕜] C`,
-- `x + (a + a) • y ∈ C`. Theorem 6.1 applied to the segment from `x` to `x + (a + a) • y`
-- in intrinsic-closure form shows that its midpoint `x + a • y` lies in `ri[𝕜](C)`. Thus every
-- nonnegative translate of every point of `ri[𝕜](C)` stays in `ri[𝕜](C)`.
theorem recessionCone_subset_ri {C : Set E} (hCconv : Convex 𝕜 C) :
    0⁺[𝕜] C ⊆ 0⁺[𝕜] (ri[𝕜](C)) := by
  intro y hy
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  have hxy_mem_C : x + (a + a) • y ∈ C :=
    (Set.mem_recessionCone_iff.mp hy) x (intrinsicInterior_subset hx) (a + a) (add_nonneg ha ha)
  have hxy_mem_cl : x + (a + a) • y ∈ intrinsicClosure 𝕜 C :=
    subset_intrinsicClosure hxy_mem_C
  have hseg : openSegment 𝕜 x (x + (a + a) • y) ⊆ ri[𝕜](C) :=
    hCconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hx hxy_mem_cl
  apply hseg
  refine ⟨(1 / 2 : 𝕜), (1 / 2 : 𝕜), ?_, ?_, ?_, ?_⟩
  · exact half_pos zero_lt_one
  · exact half_pos zero_lt_one
  · ring
  · module

end Convex

end

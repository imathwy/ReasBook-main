import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_3
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Proposition_17_0_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_18_5

-- Declarations for this item will be appended below by the statement pipeline.

open Bornology Set
open scoped Pointwise Rockafellar

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 18.5.1 specializes the recession-cone owner form below to bounded
  sets by deriving `0⁺[𝕜]C = {0}` from nonemptiness and boundedness through the primitive
  recession-cone membership owner.
- `core/canonical`: the owner abstractions are `convexHull 𝕜`, `Set.extremePoints`,
  `Set.extremeDirections`, `Set.HasAffineLine`, `recessionCone`, the Chapter 2 owners
  `Convex.mem_recessionCone_of_nonneg_ray`, together with the chapter theorem
  `eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_not_hasAffineLine` and the bridge
  `mixedConvexHull_eq_convexHull_add_ray`.
- `bridge/view`: the primitive owner theorem uses `0⁺[𝕜]C = {0}` directly. Affine-line witnesses
  and extreme-direction witnesses both produce impossible nonzero recession directions by
  `Convex.mem_recessionCone_of_nonneg_ray`. The `Set.HasAffineLine` bridge from Theorem 18.5
  then gives the mixed-hull representation, and the empty direction set collapses it to the
  ordinary convex hull of `C.extremePoints 𝕜`.

Domain-style sampling used here:
- `Set.extremePoints`;
- `Set.extremeDirections`;
- `Set.HasAffineLine`;
- `Convex.mem_recessionCone_of_nonneg_ray`;
- `eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_not_hasAffineLine`;
- `mixedConvexHull_eq_convexHull_add_ray`.

Primitive data vs derived API:
- primitive inputs: a closed convex set with the canonical owner condition `0⁺[𝕜]C = {0}`;
- derived API: the source-facing bounded corollary, obtained in the nonempty branch by
  eliminating nonzero recession directions directly from boundedness;
- owner-side reduction: `0⁺[𝕜]C = {0}` implies no affine lines and no extreme directions, so
  Theorem 18.5 gives the mixed-hull decomposition, then Proposition 17.0.6 removes the direction
  part.

Ambient refinement:
- the upstream owner theorem
  `eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_not_hasAffineLine` already lives on
  ordered topological-field modules with finite-dimensional affine-hull data, so concrete
  real-coordinate ambient models were over-concrete here.

Layer target: `source-facing`, stated directly in the canonical
`conv[𝕜]` hull language and proved by reusing the chapter owner theorems.
-/

/-- Corollary 18.5.1, owner form: a closed convex set with trivial recession cone and
finite-dimensional affine-hull data is the canonical hull `conv[𝕜] (C.extremePoints 𝕜)`. -/
-- Proof sketch: `0⁺[𝕜]C = {0}` rules out nontrivial affine-line witnesses (`Set.HasAffineLine`) and
-- nontrivial extreme directions, since each yields a nonzero recession direction by Theorem 8.3.
-- Theorem 18.5 then writes `C` as a mixed convex hull with empty direction part, and
-- Proposition 17.0.6 collapses that mixed hull to `conv[𝕜] (C.extremePoints 𝕜)`.
theorem eq_convexHull_extremePoints_of_isClosed_of_recessionCone_eq_singleton_zero_of_convex
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_recession : 0⁺[𝕜]C = ({0} : Set E)) :
    C = conv[𝕜] (C.extremePoints 𝕜) := by
  have hC_not_hasAffineLine : ¬ Set.HasAffineLine 𝕜 C := by
    rintro ⟨x, y, hy, hxy⟩
    have hy_mem : y ∈ 0⁺[𝕜]C :=
      hC_convex.mem_recessionCone_of_nonneg_ray (x := x) hC_closed (fun a _ ↦ hxy a)
    have hy_zero : y = 0 := by
      rw [hC_recession] at hy_mem
      simpa using hy_mem
    exact hy hy_zero
  have hC_extremeDirections : Set.extremeDirections 𝕜 C = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun r hr ↦ ?_
    rcases mem_extremeDirections_iff.mp hr with ⟨x, hx⟩
    have hr_mem : r.someVector ∈ 0⁺[𝕜]C :=
      hC_convex.mem_recessionCone_of_nonneg_ray (x := x) hC_closed
        (fun a ha ↦ hx.subset <| add_smul_someVector_mem_affineHalfLine x r ha)
    have hr_zero : r.someVector = 0 := by
      simp [hC_recession] at hr_mem
    exact r.someVector_ne_zero hr_zero
  calc
    C = mixedConvexHull 𝕜 (C.extremePoints 𝕜) (ray (Set.extremeDirections 𝕜 C)) := by
      simpa using
        eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_not_hasAffineLine
          hC_closed hC_convex hC_not_hasAffineLine
    _ = mixedConvexHull 𝕜 (C.extremePoints 𝕜) (ray (∅ : Set (Module.Ray 𝕜 E))) := by
      rw [hC_extremeDirections]
    _ = conv[𝕜] (C.extremePoints 𝕜) := by
      simpa using
        mixedConvexHull_eq_convexHull_add_ray
          (C.extremePoints 𝕜) (∅ : Set (Module.Ray 𝕜 E))

end

section

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

omit [LinearOrder 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem not_isBounded_range_add_natCast_smul (x y : E) (hy : y ≠ 0) :
    ¬ IsBounded (Set.range fun n : ℕ ↦ x + (n : 𝕜) • y) := by
  intro hbounded
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : E)
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x‖) / ‖y‖)
  have hnorm : ‖x + (n : 𝕜) • y‖ ≤ R := by
    have hxR : x + (n : 𝕜) • y ∈ Metric.closedBall (0 : E) R := hR ⟨n, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
  have hny : ‖(n : 𝕜)‖ * ‖y‖ ≤ R + ‖x‖ := by
    calc
      ‖(n : 𝕜)‖ * ‖y‖ = ‖(n : 𝕜) • y‖ := by
        simpa using (norm_smul (n : 𝕜) y).symm
      _ = ‖(x + (n : 𝕜) • y) - x‖ := by simp
      _ ≤ ‖x + (n : 𝕜) • y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := add_le_add hnorm le_rfl
  have hgt' : R + ‖x‖ < (n : ℝ) * ‖y‖ := (div_lt_iff₀ hy_norm).mp hn
  have hgt : R + ‖x‖ < ‖(n : 𝕜)‖ * ‖y‖ := by
    calc
      R + ‖x‖ < (n : ℝ) * ‖y‖ := hgt'
      _ = ‖(n : 𝕜)‖ * ‖y‖ := by simp [norm_natCast]
  exact not_lt_of_ge hny hgt

omit [OrderTopology 𝕜] in
private theorem recessionCone_eq_singleton_zero_of_nonempty_isBounded {C : Set E}
    (hC_nonempty : C.Nonempty) (hC_bounded : IsBounded C) :
    0⁺[𝕜]C = ({0} : Set E) := by
  obtain ⟨x, hx⟩ := hC_nonempty
  ext y
  constructor
  · intro hy
    by_contra hy_ne
    have hrange_subset : Set.range (fun n : ℕ ↦ x + (n : 𝕜) • y) ⊆ C := by
      rintro _ ⟨n, rfl⟩
      exact (Set.mem_recessionCone_iff.mp hy) x hx (n : 𝕜) (Nat.cast_nonneg n)
    exact not_isBounded_range_add_natCast_smul x y hy_ne (hC_bounded.subset hrange_subset)
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    simpa using (show (0 : E) ∈ 0⁺[𝕜]C from zero_mem_recessionCone (R := 𝕜) C)

/-- Corollary 18.5.1, source-facing form: a closed bounded convex set is the convex hull of its
extreme points. -/
-- Proof sketch: split on `C.Nonempty`. In the nonempty branch, boundedness rules out every nonzero
-- recession direction directly from the recession-cone definition, yielding `0⁺[𝕜]C = {0}`, then
-- apply the owner theorem above. In the empty branch, the claim is immediate.
theorem eq_convexHull_extremePoints_of_isClosed_of_isBounded_of_convex {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_closed : IsClosed C) (hC_bounded : IsBounded C) (hC_convex : Convex 𝕜 C) :
    C = conv[𝕜] (C.extremePoints 𝕜) := by
  by_cases hC_nonempty : C.Nonempty
  · have hC_recession : 0⁺[𝕜]C = ({0} : Set E) :=
      recessionCone_eq_singleton_zero_of_nonempty_isBounded hC_nonempty hC_bounded
    exact
      eq_convexHull_extremePoints_of_isClosed_of_recessionCone_eq_singleton_zero_of_convex
        hC_closed hC_convex hC_recession
  · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    simp [hC_empty]

end

import Mathlib
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_18_5_1 (from Chap04) -/
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

/-! ### Text_18_5_1 (from Chap04) -/
open Bornology Set
open scoped Rockafellar

section

variable {K : Type*} [CommSemiring K] [PartialOrder K] [IsStrictOrderedRing K]
variable {E : Type*} [AddCommMonoid E] [Module K E]

/-- Text 18.5.1 (point-owner form): if `C` is generated by point generators `points` and direction
 generators `directions`, then every extreme point of `C` lies in `points`. -/
theorem extremePoints_subset_of_generators
    {C points : Set E} {directions : Set (Module.Ray K E)}
    (hC : C = mconv[K](points | ray directions)) :
    C.extremePoints K ⊆ points := by
  subst C
  intro x hx
  exact mem_points_of_mem_extremePoints_mixedConvexHull_of_rayDirections hx

end

section

variable {K : Type*} [CommSemiring K] [PartialOrder K] [IsStrictOrderedRing K]
variable {E : Type*} [Bornology E] [AddCancelCommMonoid E] [Module K E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 18.5.1 asserts the minimality of the extreme-point and extreme-direction
  generators of a mixed generating set for `C`, under the regularity condition that affine
  half-lines contained in `C` meet the point generators in bounded sets.
- `core/canonical`: the owner abstractions already present in the chapter are
  `mconv[K](points | ray directions)` for a generating set with points and
  directions, `C.extremePoints K` for extreme points, `C.extremeDirections K` for extreme
  directions, and `affineHalfLine x r` for the half-lines used in the regularity condition.
- `bridge/view`: the textbook mixed set `S'` of points and directions is rendered canonically as a
  pair of sets `points : Set E` and `directions : Set (Module.Ray K E)`, with generation expressed
  by `mconv[K](points | ray directions)`.

Domain-style sampling used here:
- `mixedConvexHull`;
- `rayOfDirections`;
- `affineHalfLine`;
- `extremePoints_subset_of_generators`;
- `mem_directions_of_mem_extremeDirections_mixedConvexHull`.

Primitive data vs derived API:
- primitive inputs: the point generators `points`, the direction generators
  `directions`, the regularity condition on affine half-lines
  contained in the mixed hull, and the ambient bounded-convex-hull bridge;
- derived API: the set-level owner consequences that extreme points lie in `points` and extreme
  directions lie in `directions`, then the bundled conjunction from those owner-level pieces.
- ambient refinement: the reused owner theorems are already stated on the ordered-semiring +
  bornological layer for rays and bounded convex hulls, so neither normed-space nor
  finite-dimensional structure belongs in this file's public surface.

Layer target: `core/canonical`, expressed on the intrinsic owner surface
`C.extremePoints K` / `C.extremeDirections K` with generation witness
`C = mconv[K](points | ray directions)`.
-/

/-- Text 18.5.1 (direction-owner form): if `C` is generated by point generators `points` and
 direction generators `directions`, and every affine half-line contained in `C` meets `points` in
 a bounded set, then every extreme direction of `C` lies in `directions`. -/
theorem extremeDirections_subset_of_generators
    {C points : Set E} {directions : Set (Module.Ray K E)}
    (hC : C = mconv[K](points | ray directions))
    (hbounded_convexHull :
      ∀ {s : Set E}, IsBounded s → IsBounded (convexHull K s))
    (hnot_isBounded_affineHalfLine :
      ∀ (x : E) (r : Module.Ray K E), ¬ IsBounded (affineHalfLine x r))
    (hpoints_on_affineHalfLine :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray K E⦄,
        affineHalfLine x r ⊆ C →
          IsBounded (points ∩ affineHalfLine x r)) :
    C.extremeDirections K ⊆ directions := by
  subst C
  intro r hr
  exact mem_directions_of_mem_extremeDirections_mixedConvexHull
    (hbounded_convexHull := hbounded_convexHull)
    (hnot_isBounded_affineHalfLine := hnot_isBounded_affineHalfLine)
    hpoints_on_affineHalfLine hr

/-- Text 18.5.1: if a set `C` is generated by point generators `points` and direction generators
`directions`, and every affine half-line contained in `C` meets `points` in a bounded set, then
every extreme point of `C` lies in `points` and every extreme direction of `C` lies in
`directions`. -/
-- Proof sketch: combine the owner-level subset theorems
-- `extremePoints_subset_of_generators` and `extremeDirections_subset_of_generators`.
theorem extremePoints_and_extremeDirections_subset_of_generators
    {C points : Set E} {directions : Set (Module.Ray K E)}
    (hC : C = mconv[K](points | ray directions))
    (hbounded_convexHull :
      ∀ {s : Set E}, IsBounded s → IsBounded (convexHull K s))
    (hnot_isBounded_affineHalfLine :
      ∀ (x : E) (r : Module.Ray K E), ¬ IsBounded (affineHalfLine x r))
    (hpoints_on_affineHalfLine :
      ∀ ⦃x : E⦄ ⦃r : Module.Ray K E⦄,
        affineHalfLine x r ⊆ C →
          IsBounded (points ∩ affineHalfLine x r)) :
    C.extremePoints K ⊆ points ∧ C.extremeDirections K ⊆ directions := by
  refine ⟨extremePoints_subset_of_generators hC, ?_⟩
  exact extremeDirections_subset_of_generators
    hC hbounded_convexHull hnot_isBounded_affineHalfLine hpoints_on_affineHalfLine

end

/-! ### Corollary_18_5_2 (from Chap04) -/
open Set
open scoped Pointwise Rockafellar

section

variable {R E : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R]
  [AddCommGroup E] [Module R E]

namespace PointedCone

/- A pointed cone has trivial lineality exactly when it contains no nontrivial line through the
origin. This theorem is only a source-facing bridge; the owner-level hypothesis remains
`K.lineal = ⊥`. -/
theorem lineal_eq_bot_iff_no_nontrivial_line (K : PointedCone R E) :
    K.lineal = ⊥ ↔ ¬ ∃ y : E, y ≠ 0 ∧ ∀ a : R, a • y ∈ K := by
  constructor
  · intro hK
    rintro ⟨y, hy0, hyLine⟩
    have hy_lineal : y ∈ K.lineal := by
      rw [mem_lineal]
      constructor
      · simpa using hyLine 1
      · simpa using hyLine (-1)
    rw [Submodule.eq_bot_iff] at hK
    exact hy0 <| hK y hy_lineal
  · intro hK
    rw [Submodule.eq_bot_iff]
    intro y hy_lineal
    by_contra hy0
    have hy_mem : y ∈ K := (mem_lineal.mp hy_lineal).1
    have hneg_mem : -y ∈ K := (mem_lineal.mp hy_lineal).2
    exact hK ⟨y, hy0, fun a ↦ by
      by_cases ha : 0 ≤ a
      · exact K.smul_mem ha hy_mem
      · have hneg_a : 0 ≤ -a := le_of_lt <| neg_pos.mpr <| lt_of_not_ge ha
        rw [show a • y = (-a) • (-y) by simp]
        exact K.smul_mem hneg_a hneg_mem⟩

end PointedCone

end

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 18.5.2 says that a closed convex cone with no lines is generated by
  any set `T` of vectors in the cone that supplies one generator for each extreme ray.
- `core/canonical`: the owner abstractions are the bundled cone `PointedCone 𝕜 E`, its lineality
  submodule `PointedCone.lineal`, the chapter generated-cone owner `cone[𝕜] T`, and the
  extreme-direction owner `(K : Set E).extremeDirections 𝕜` together with canonical direction rays
  `originRay r`.
- `bridge/view`: the textbook no-line phrase is only a companion bridge theorem to the owner
  condition `K.lineal = ⊥`; the extreme-ray generator hypothesis is kept directly in source-facing
  direction-ray quantifier form rather than packaged as a one-off wrapper.

Domain-style sampling used here:
- `PointedCone.lineal`;
- `PointedCone.mem_lineal`;
- `cone[𝕜]`;
- `Set.extremeDirections`;
- `PointedCone.lineal_eq_sSup`.

Primitive data vs derived API:
- primitive inputs: the closed cone `K`, the subset `T ⊆ K`, the exclusion of nontrivial lines in
  `K` expressed canonically as `K.lineal = ⊥` for the core owner theorem, together with the
  source-facing bridge phrase `¬ ∃ y ≠ 0, ∀ a, a • y ∈ K` linked by
  `PointedCone.lineal_eq_bot_iff_no_nontrivial_line`, and the generator condition on extreme
  direction rays stated directly over `K.extremeDirections 𝕜`;
- derived API: the equality identifying `K` with the canonical cone generated by `T`.

Layer target: split owner/bridge surfaces, with the core theorem at the owner condition
`K.lineal = ⊥`, the companion source theorem at the textbook no-line phrase, the extreme-ray
generator hypothesis kept directly in direction-ray quantifier form, and the generated cone
expressed by the chapter owner `cone[𝕜]`.

Ambient refinement:
- this corollary stays at the same scalar/topological owner layer as
  `eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_not_hasAffineLine`, which is the
  canonical chapter bridge from closed convex sets to mixed-hull generation by extreme points and
  extreme directions;
- no Euclidean-coordinate owner is introduced.
-/

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem finiteDimensional_direction_affineSpan_lineal_of_eq_bot
    {K : PointedCone 𝕜 E} (hK_lineal : K.lineal = ⊥) :
    FiniteDimensional 𝕜 (affineSpan 𝕜 (K.lineal : Set E)).direction := by
  have hdir_bot : (affineSpan 𝕜 (K.lineal : Set E)).direction = (⊥ : Submodule 𝕜 E) := by
    rw [hK_lineal]
    rw [direction_affineSpan 𝕜 (s := (((⊥ : Submodule 𝕜 E) : Set E)))]
    simp
  rw [hdir_bot]
  infer_instance

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem originRay_subset_cone_of_mem {T : Set E} {x : E}
    (hxT : x ∈ T) (hx0 : x ≠ 0) :
    originRay (rayOfNeZero 𝕜 x hx0) ⊆ (cone[𝕜] T : Set E) := by
  intro y hy
  rw [originRay_eq_nonnegative_smul_singleton hx0] at hy
  rcases Set.mem_smul.mp hy with ⟨a, ha, z, hz, rfl⟩
  have hz' : z = x := by
    simpa using hz
  subst hz'
  exact (cone[𝕜] T).smul_mem ha <| PointedCone.subset_hull hxT

/-- Corollary 18.5.2, core owner form: if a closed convex cone `K` has trivial lineality and the
vectors on extreme directions of `K` already lie in the generated cone `cone[𝕜] T`, then
`K = cone[𝕜] T`. -/
theorem eq_cone_of_ray_extremeDirections_subset_generatedCone
    {K : PointedCone 𝕜 E} {T : Set E} (hK_closed : IsClosed (K : Set E))
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (K : Set E)).direction]
    (hK_lineal : K.lineal = ⊥) (hT_subset : T ⊆ K)
    (hdir_subset : ray ((K : Set E).extremeDirections 𝕜) ⊆ (cone[𝕜] T : Set E)) :
    K = cone[𝕜] T := by
  letI : FiniteDimensional 𝕜 (affineSpan 𝕜 (K.lineal : Set E)).direction :=
    finiteDimensional_direction_affineSpan_lineal_of_eq_bot (K := K) hK_lineal
  have hK_convex : Convex 𝕜 (K : Set E) := K.convex
  have hK_not_hasAffineLine : ¬ Set.HasAffineLine 𝕜 (K : Set E) := by
    intro hline
    have hK_nonempty : ((K : Set E).Nonempty) := ⟨0, K.zero_mem⟩
    rcases
        (Set.hasAffineLine_iff_exists_ne_zero_mem_lineal hK_nonempty hK_closed hK_convex).mp
          hline with
      ⟨y, hy0, hy_lineal⟩
    rw [Submodule.eq_bot_iff] at hK_lineal
    apply hy0
    apply hK_lineal y
    rw [PointedCone.mem_lineal]
    rw [Set.mem_lineal_iff] at hy_lineal
    constructor
    · have hy_mem := (Set.mem_recessionCone_iff.mp hy_lineal.1) 0 K.zero_mem 1 zero_le_one
      simpa using hy_mem
    · have hneg_mem := (Set.mem_recessionCone_iff.mp hy_lineal.2) 0 K.zero_mem 1 zero_le_one
      simpa using hneg_mem
  have hpoints :
      (K : Set E).extremePoints 𝕜 ⊆ (cone[𝕜] T : Set E) := by
    intro z hz
    by_cases hz0 : z = 0
    · exact hz0 ▸ (cone[𝕜] T).zero_mem
    · rcases mem_extremePoints.mp hz with ⟨hzK, hz_extreme⟩
      have h2z : (2 : 𝕜) • z ∈ (K : Set E) := K.smul_mem (by norm_num) hzK
      have hz_seg : z ∈ openSegment 𝕜 (0 : E) ((2 : 𝕜) • z) := by
        rw [openSegment_eq_image_lineMap]
        refine ⟨(1 / 2 : 𝕜), by constructor <;> norm_num, ?_⟩
        simp [AffineMap.lineMap_apply_module]
      have hz_eq : (0 : E) = z := (hz_extreme 0 K.zero_mem ((2 : 𝕜) • z) h2z hz_seg).1
      exact (hz0 hz_eq.symm).elim
  have hdirections :
      ray ((K : Set E).extremeDirections 𝕜) ⊆ 0⁺[𝕜] (cone[𝕜] T : Set E) := by
    intro y hy
    have hy_cone : y ∈ (cone[𝕜] T : Set E) := hdir_subset hy
    rw [Set.mem_recessionCone_iff]
    intro z hz a ha
    exact (cone[𝕜] T).add_mem hz <| (cone[𝕜] T).smul_mem ha hy_cone
  have hmixed_subset :
      mixedConvexHull 𝕜 ((K : Set E).extremePoints 𝕜) (ray ((K : Set E).extremeDirections 𝕜)) ⊆
        (cone[𝕜] T : Set E) :=
    mixedConvexHull_min 𝕜 (cone[𝕜] T).convex hpoints hdirections
  have hK_subset_cone : (K : Set E) ⊆ (cone[𝕜] T : Set E) := by
    rw [eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_not_hasAffineLine
      hK_closed hK_convex hK_not_hasAffineLine]
    exact hmixed_subset
  have hcone_subset : (cone[𝕜] T : Set E) ⊆ (K : Set E) := by
    exact Submodule.span_le.mpr hT_subset
  exact le_antisymm hK_subset_cone hcone_subset

/-- Corollary 18.5.2, source-facing bridge form: if a closed convex cone `K` contains no
nontrivial line through the origin and every extreme ray of `K` is generated by some vector of a
subset `T ⊆ K`, then `K = cone[𝕜] T`. -/
-- Proof sketch: derive the core owner inclusion
-- `ray (K.extremeDirections 𝕜) ⊆ cone[𝕜] T` from the ray-generator witnesses in `T`, then apply
-- `eq_cone_of_ray_extremeDirections_subset_generatedCone`.
theorem eq_cone_of_extremeRay_generating_subset
    {K : PointedCone 𝕜 E} {T : Set E} (hK_closed : IsClosed (K : Set E))
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (K : Set E)).direction]
    (hK_no_nontrivial_line : ¬ ∃ y : E, y ≠ 0 ∧ ∀ a : 𝕜, a • y ∈ K) (hT_subset : T ⊆ K)
    (hT_extreme : ∀ ⦃r : Module.Ray 𝕜 E⦄,
      r ∈ (K : Set E).extremeDirections 𝕜 → ∃ x ∈ T, x ≠ 0 ∧ x ∈ originRay r) :
    K = cone[𝕜] T := by
  have hK_lineal : K.lineal = ⊥ :=
    (PointedCone.lineal_eq_bot_iff_no_nontrivial_line (K := K)).2 hK_no_nontrivial_line
  have hdir_subset : ray ((K : Set E).extremeDirections 𝕜) ⊆ (cone[𝕜] T : Set E) := by
    intro y hy
    rcases (mem_ray_iff ((K : Set E).extremeDirections 𝕜) y).mp hy with
        rfl | ⟨hy0, hr⟩
    · exact (cone[𝕜] T).zero_mem
    · rcases hT_extreme hr with ⟨x, hxT, hx0, hxray⟩
      have hy_ray : y ∈ originRay (rayOfNeZero 𝕜 y hy0) :=
        (mem_originRay_iff).2 <| Or.inr ⟨hy0, rfl⟩
      rcases (mem_originRay_iff.mp hxray) with rfl | ⟨hx0', hxy⟩
      · exact (hx0 rfl).elim
      · have hx_cone :
            originRay (rayOfNeZero 𝕜 x hx0') ⊆ (cone[𝕜] T : Set E) :=
          originRay_subset_cone_of_mem hxT hx0'
        exact hx_cone <| by simpa [hxy] using hy_ray
  exact eq_cone_of_ray_extremeDirections_subset_generatedCone
    hK_closed hK_lineal hT_subset hdir_subset

end

/-! ### Text_18_5_2 (from Chap04) -/
open Bornology

/-!
Source/core/bridge triage:

- Primary mathematical domain: extreme points of convex sets in finite-dimensional ordered
  normed spaces.
- `source-facing`: Text 18.5.2 records a 3-dimensional counterexample.
- `core/canonical`: this file keeps the source-level owner theorem at exact ambient
  dimension `Module.finrank ℝ E = 3`; compactness is exposed as a bridge consequence.
- owner abstractions: `IsClosed C`, `IsBounded C`,
  `Convex ℝ C`, and `Set.extremePoints ℝ C`.
- `bridge/view`: compactness upgrade from closed-bounded to compact in proper ambient spaces.

Domain-style sampling used here:
- `Set.extremePoints`, recalled as the owner for Definition 18.2 in `Chap04/Defn_18_2`;
- `mem_extremePoints`, the standard bridge theorem for pointwise use of that owner;
- `extremePoints_subset_closure_exposedPoints` from `Chap04/Theorem_18_6`,
  showing that the chapter's later extreme-point API continues to work directly with
  `C.extremePoints ℝ` and ordinary closure;
- `Metric.isCompact_of_isClosed_isBounded`, the canonical proper-space bridge used only for the
  compact companion below.

Primitive data vs derived API:
- primitive data: a set `C : Set E` in a finite-dimensional ambient normed space over `ℝ`
  with `Module.finrank ℝ E = 3`;
- source-facing properties: `IsClosed C`, `IsBounded C`, `Convex ℝ C`, and the failure
  of closedness for `C.extremePoints ℝ`;
- derived bridge properties: `IsCompact C` in proper spaces.

Layer target:
- the source-level exact-3 owner theorem is primary;
- the compact formulation is retained as a bridge view.
-/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Scalar-layer validation:
- the source item is intrinsically real (`ℝ³`) and this file keeps that scalar layer;
- normed-space/topological bridges (`IsBounded`/`IsCompact`) are used in the ambient space. -/

/-- Text 18.5.2, owner form: in every ambient real normed space with
`Module.finrank ℝ E = 3`, there exists a closed bounded convex set whose set of extreme points is
not closed. -/
-- Proof sketch: take the convex hull of the closed unit disk in the plane `z = 0` together with a
-- vertical segment through one of its boundary points. The resulting set is closed and bounded.
-- The two endpoints of the segment and every other boundary point of the disk are extreme, while
-- the distinguished boundary point is their limit but is not extreme because it lies in the
-- interior of the added segment.
theorem exists_isClosed_isBounded_convex_nonclosed_extremePoints
    (hE_dim : Module.finrank ℝ E = 3) :
    ∃ C : Set E, IsClosed C ∧ IsBounded C ∧ Convex ℝ C ∧ ¬ IsClosed (C.extremePoints ℝ) := sorry

/-- Proper-space bridge reformulation of Text 18.5.2: if the ambient metric space is proper, the
same counterexample is compact. -/
theorem exists_isCompact_convex_nonclosed_extremePoints_of_properSpace [ProperSpace E]
    (hE_dim : Module.finrank ℝ E = 3) :
    ∃ C : Set E, IsCompact C ∧ Convex ℝ C ∧ ¬ IsClosed (C.extremePoints ℝ) := by
  rcases exists_isClosed_isBounded_convex_nonclosed_extremePoints hE_dim with
    ⟨C, hC_closed, hC_bounded, hC_convex, hC_extremePoints⟩
  refine ⟨C, Metric.isCompact_of_isClosed_isBounded hC_closed hC_bounded,
    hC_convex, hC_extremePoints⟩

/-- Compact bridge form: every ambient real normed space with
`Module.finrank ℝ E = 3` admits a compact convex set whose extreme-point set is not closed. -/
theorem exists_isCompact_convex_nonclosed_extremePoints
    (hE_dim : Module.finrank ℝ E = 3) :
    ∃ C : Set E, IsCompact C ∧ Convex ℝ C ∧ ¬ IsClosed (C.extremePoints ℝ) := by
  have hE_pos : 0 < Module.finrank ℝ E := by
    simp [hE_dim]
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos hE_pos
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  exact exists_isCompact_convex_nonclosed_extremePoints_of_properSpace hE_dim

end

/-! ### Corollary_18_5_3 (from Chap04) -/
open Set
open scoped Rockafellar

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 18.5.3 says that a nonempty closed convex set containing no lines has
  at least one extreme point.
- `core/canonical`: the owner abstractions are `HasAffineLine` and the intrinsic lineality-space
  owner `¬ ∃ y, y ≠ 0 ∧ y ∈ lin[𝕜](C)` for line-freeness, together with
  `Set.extremePoints 𝕜 C` for the conclusion.
- `bridge/view`: the finite-dimensional lineality-number condition `lineality[𝕜](C) = 0` is kept
  as a companion bridge by passing through the primitive no-nonzero-lineality-vector owner.

Domain-style sampling used here:
- `Set.lineality_eq_zero_iff_not_exists_ne_zero_mem_lineal`;
- `Set.hasAffineLine_iff_exists_ne_zero_mem_lineal`;
- `HasAffineLine`;
- `lin[𝕜](·)`;
- `Set.extremePoints`;
- `eq_mixedConvexHull_extremePoints_rayOfExtremeDirections`;
- `ray`;
- `mixedConvexHull_eq_empty_of_points_eq_empty`.

Primitive data vs derived API:
- primitive inputs: the set `C`, its nonemptiness, closedness, convexity, and `¬ HasAffineLine 𝕜 C`;
- derived API: the existence of an extreme point, most naturally recorded as
  `(C.extremePoints 𝕜).Nonempty`;
- bridge/view: the intrinsic no-nonzero-lineality-vector condition, the finite-dimensional
  lineality-number wording, and the old quantifier no-line wording are companion theorems.

Ambient refinement:
- the owner theorem `eq_mixedConvexHull_extremePoints_rayOfExtremeDirections` already lives on
  arbitrary topological modules over linearly ordered fields with finite-dimensional affine-hull
  data on the specific set `C`, and this corollary uses no coordinate data, so the source-facing
  statement should live on that same ambient layer rather than on `EuclideanSpace ℝ (Fin n)`.

Layer target: `source-facing`, stated directly in terms of the canonical owner `Set.extremePoints`
without introducing any wrapper around the mixed-hull representation from Theorem 18.5.
-/

/-- Corollary 18.5.3, owner form: a nonempty closed convex set with finite-dimensional affine-hull
data and no affine-line owner witness has at least one extreme point.
Specializing `𝕜 = ℝ`, `E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` formulation
after unfolding `HasAffineLine`. -/
-- Proof sketch: apply Theorem 18.5 to write `C` as the mixed convex hull generated by
-- `C.extremePoints 𝕜` and its extreme directions. If `C.extremePoints 𝕜 = ∅`, then
-- `mixedConvexHull_eq_empty_of_points_eq_empty` forces that mixed convex hull to be empty, hence
-- `C = ∅`, contradicting `hC_nonempty`.
theorem extremePoints_nonempty_of_isClosed_convex_not_hasAffineLine
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_no_affineLine : ¬ HasAffineLine 𝕜 C) :
    (C.extremePoints 𝕜).Nonempty := by
  by_contra hC_extreme
  have hC_eq_empty : C = ∅ := by
    calc
      C = mixedConvexHull 𝕜 (C.extremePoints 𝕜)
            (ray (C.extremeDirections 𝕜)) := by
        simpa using
          eq_mixedConvexHull_extremePoints_rayOfExtremeDirections
            hC_closed hC_convex hC_no_affineLine
      _ = ∅ :=
        mixedConvexHull_eq_empty_of_points_eq_empty 𝕜
          (Set.not_nonempty_iff_eq_empty.mp hC_extreme)
  exact hC_nonempty.ne_empty hC_eq_empty

/-- Corollary 18.5.3, lineality-space bridge: a nonempty closed convex set with no nonzero
lineality vector has at least one extreme point. -/
theorem extremePoints_nonempty_of_isClosed_convex_not_exists_ne_zero_mem_lineal
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_no_nonzero_lineal : ¬ ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C)) :
    (C.extremePoints 𝕜).Nonempty := by
  have hC_no_affineLine : ¬ HasAffineLine 𝕜 C := by
    intro hC_hasAffineLine
    rcases (Set.hasAffineLine_iff_exists_ne_zero_mem_lineal hC_nonempty hC_closed hC_convex).1
        hC_hasAffineLine with ⟨y, hy_ne_zero, hy_lineal⟩
    exact hC_no_nonzero_lineal ⟨y, hy_ne_zero, hy_lineal⟩
  exact extremePoints_nonempty_of_isClosed_convex_not_hasAffineLine
    hC_nonempty hC_closed hC_convex hC_no_affineLine

/-- Corollary 18.5.3, finite-dimensional lineality-number bridge: a nonempty closed convex set
with vanishing lineality has at least one extreme point. -/
theorem extremePoints_nonempty_of_isClosed_convex_lineality_eq_zero
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_lineality : lineality[𝕜](C) = 0) :
    (C.extremePoints 𝕜).Nonempty := by
  have hC_no_nonzero_lineal :
      ¬ ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) :=
    (Set.lineality_eq_zero_iff_not_exists_ne_zero_mem_lineal (C := C)).1 hC_lineality
  exact extremePoints_nonempty_of_isClosed_convex_not_exists_ne_zero_mem_lineal
    hC_nonempty hC_closed hC_convex hC_no_nonzero_lineal

/-- Corollary 18.5.3, textbook bridge: a nonempty closed convex set containing no affine lines has
at least one extreme point. -/
theorem extremePoints_nonempty_of_isClosed_convex_no_affineLine
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_no_affineLine : ¬ ∃ x y : E, y ≠ 0 ∧ ∀ a : 𝕜, x + a • y ∈ C) :
    (C.extremePoints 𝕜).Nonempty := by
  simpa [HasAffineLine] using
    extremePoints_nonempty_of_isClosed_convex_not_hasAffineLine
      hC_nonempty hC_closed hC_convex hC_no_affineLine

end

/-! ### Theorem_18_5 (from Chap04) -/
section

open Set
open scoped Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 18.5 says that a closed convex set containing no affine lines is
  generated by its extreme points together with its extreme directions.
- `core/canonical`: the owner abstractions already present in the project are `HasAffineLine` for
  the line-free hypothesis, `Set.extremePoints` for extreme points,
  `Set.extremeDirections` for extreme directions, `rayOfDirections`, written source-facingly as
  `ray`, for turning direction rays into vectors, and `mixedConvexHull` for the convex hull
  generated by points and recession directions.
- `bridge/view`: the lineality-owner formulation is a companion bridge obtained from
  `Set.lineality_eq_zero_iff_not_hasAffineLine` on the nonempty branch, while the quantifier
  wording is recovered from `HasAffineLine`; the
  mixed generating set `conv S` is rendered canonically as `mixedConvexHull 𝕜
  (C.extremePoints 𝕜) (ray (C.extremeDirections 𝕜))`.

Domain-style sampling used here:
- `lineality[𝕜](·)`;
- `Set.lineality_eq_zero_iff_not_hasAffineLine`;
- `HasAffineLine`;
- `Set.extremePoints`;
- `Set.extremeDirections`;
- `rayOfDirections` / `ray`;
- `mixedConvexHull`.

Primitive data vs derived API:
- primitive inputs: the closed convex set `C` together with the canonical owner-side condition
  `¬ HasAffineLine 𝕜 C`;
- derived API: the equality identifying `C` with the mixed convex hull generated by its extreme
  points and extreme directions;
- bridge/view: on the nonempty branch, the lineality-owner condition
  `lineality[𝕜](C) = 0` is equivalent to `¬ HasAffineLine 𝕜 C`.
- ambient refinement: finite-dimensionality is carried at the affine-hull layer of `C` rather than
  as a global ambient-space default.

Layer target: `source-facing`, expressed directly through the chapter's `HasAffineLine`,
extreme-point, extreme-direction, and mixed-convex-hull owners.
-/

/-- Theorem 18.5, owner form: a closed convex set containing no affine-line owner witness is the
mixed convex hull generated by its extreme points and its extreme directions. -/
theorem eq_mixedConvexHull_extremePoints_rayOfExtremeDirections
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_no_affineLine : ¬ HasAffineLine 𝕜 C) :
    C = mconv[𝕜](C.extremePoints 𝕜 | ray (C.extremeDirections 𝕜)) := sorry

/-- Backward-compatible owner-name surface for Theorem 18.5. -/
theorem eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_not_hasAffineLine
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_no_affineLine : ¬ HasAffineLine 𝕜 C) :
    C = mconv[𝕜](C.extremePoints 𝕜 | ray (C.extremeDirections 𝕜)) := by
  simpa using
    eq_mixedConvexHull_extremePoints_rayOfExtremeDirections
      hC_closed hC_convex hC_no_affineLine

/-- Theorem 18.5, lineality-owner bridge: if `C` is empty or has vanishing lineality, then `C`
is the mixed convex hull generated by its extreme points and extreme directions. -/
theorem eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_empty_or_lineality_eq_zero
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_empty_or_lineality : C = ∅ ∨ lineality[𝕜](C) = 0) :
    C = mconv[𝕜](C.extremePoints 𝕜 | ray (C.extremeDirections 𝕜)) := by
  by_cases hC_empty : C = ∅
  · have hC_no_affineLine : ¬ HasAffineLine 𝕜 C := by
      simp [HasAffineLine, hC_empty]
    exact eq_mixedConvexHull_extremePoints_rayOfExtremeDirections
      hC_closed hC_convex hC_no_affineLine
  · have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
    have hC_no_affineLine : ¬ HasAffineLine 𝕜 C := by
      rcases hC_empty_or_lineality with hC_empty' | hC_lineality
      · exact (hC_empty hC_empty').elim
      · exact (Set.lineality_eq_zero_iff_not_hasAffineLine hC_nonempty hC_closed hC_convex).1
          hC_lineality
    exact eq_mixedConvexHull_extremePoints_rayOfExtremeDirections
      hC_closed hC_convex hC_no_affineLine

/-- Theorem 18.5, textbook bridge: a closed convex set containing no affine lines is the mixed
convex hull generated by its extreme points and its extreme directions. -/
theorem eq_mixedConvexHull_extremePoints_rayOfExtremeDirections_of_no_affineLine
    {C : Set E} [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (hC_no_affineLine : ¬ ∃ x y : E, y ≠ 0 ∧ ∀ a : 𝕜, x + a • y ∈ C) :
    C = mconv[𝕜](C.extremePoints 𝕜 | ray (C.extremeDirections 𝕜)) := by
  simpa [HasAffineLine] using
    eq_mixedConvexHull_extremePoints_rayOfExtremeDirections
      hC_closed hC_convex hC_no_affineLine

end

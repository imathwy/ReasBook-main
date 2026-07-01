import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Set
open scoped Rockafellar

variable {𝕜 : Type v} [Semiring 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: the text says that if the lineality space of `C` is nontrivial, then `C` has
  no extreme points.
- `core/canonical`: the owner objects are the project-level `Set.lineal` and mathlib's
  `Set.extremePoints 𝕜 C`.
- `bridge/view`: the source-facing nontriviality condition
  `Set.lineal 𝕜 C ≠ ({0} : Set E)` is kept as a bridge corollary. The primitive public theorem
  uses the owner-side data `∃ y, y ≠ 0 ∧ y ∈ lin[𝕜](C)`.

Domain-style sampling used here:
- `Set.lineal`;
- `Set.mem_lineal_iff`;
- `Set.mem_lineal_iff_forall`;
- `Set.extremePoints`;
- `openSegment`.

Primitive data vs derived API:
- the primitive input is the set `C` together with the existence of a nonzero direction in
  `lin[𝕜](C)`;
- midpoint data are primitive in this abstraction layer: we assume the existence of
  `a : 𝕜` with `0 < a` and `a + a = 1`;
- the source-facing nontriviality condition `lin[𝕜](C) ≠ ({0} : Set E)` is kept as a bridge form;
- the conclusion that `C` has no extreme points is theorem-level content, best expressed as
  `C.extremePoints 𝕜 = ∅`.

Ambient refinement:
- the proof only uses the canonical owners `lin[𝕜](C)` and `C.extremePoints 𝕜`, plus the direct
  open-segment witness at coefficients `(a, a)` where `a + a = 1`;
- the `⅟2` specialization is kept only as a convenience bridge.

The textbook mentions convexity, but for the canonical lineal owner the conclusion only uses the
existence of a nonzero direction in `lin[𝕜](C)`, so no separate convexity hypothesis is needed in
the statement.
-/

/- Text 18.3.1: if the lineality space of `C` is nontrivial, then `C` has no extreme points.
For nonempty `C`, this hypothesis implies that `C` contains a line; the file keeps the stronger
canonical lineality-space hypothesis rather than asserting that geometric reformulation as an
equivalence. -/
-- Proof sketch: choose a nonzero `v ∈ lin[𝕜](C)`. For any `x ∈ C`, membership in the
-- lineality space gives `x + v ∈ C` and `x - v ∈ C`, while `x` is the midpoint of those two
-- distinct points. Hence `x` lies in a nontrivial open segment with endpoints in `C`, so
-- `x ∉ C.extremePoints 𝕜`. Therefore `C.extremePoints 𝕜 = ∅`.
/-- Primitive public form of Text 18.3.1: a nonzero direction in `lin[𝕜](C)` forces the
extreme-point set of `C` to be empty, assuming explicit midpoint data. -/
theorem extremePoints_eq_empty_of_exists_ne_zero_mem_lineal_of_exists_midpoint
    [PartialOrder 𝕜] [ZeroLEOneClass 𝕜]
    {C : Set E}
    (hmid : ∃ a : 𝕜, 0 < a ∧ a + a = 1)
    (hlineal : ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C)) :
    C.extremePoints 𝕜 = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro x hxext
  rcases hmid with ⟨a, ha_pos, ha_sum⟩
  rcases hlineal with ⟨y, hy0, hy⟩
  rcases mem_extremePoints.mp hxext with ⟨hxC, hxextreme⟩
  have hy_forall := mem_lineal_iff_forall.mp hy
  have hx_sub : x - y ∈ C := by
    simpa [sub_eq_add_neg] using hy_forall.1 x hxC 1 zero_le_one
  have hx_add : x + y ∈ C := by
    simpa using hy_forall.2 x hxC 1 zero_le_one
  have hx_seg : x ∈ openSegment 𝕜 (x - y) (x + y) := by
    refine ⟨a, a, ha_pos, ha_pos, ha_sum, ?_⟩
    calc
      a • (x - y) + a • (x + y) = a • ((x - y) + (x + y)) := by rw [← smul_add]
      _ = a • (x + x) := by abel_nf
      _ = a • x + a • x := by rw [smul_add]
      _ = (a + a) • x := by rw [add_smul]
      _ = (1 : 𝕜) • x := by rw [ha_sum]
      _ = x := by simp
  have hx_eq := hxextreme (x - y) hx_sub (x + y) hx_add hx_seg
  have hy_zero : y = 0 := by
    have hx_eq' : x + y = x + 0 := by
      simpa using hx_eq.2
    exact add_left_cancel hx_eq'
  exact hy0 hy_zero

/-- Source-facing bridge form of Text 18.3.1: nontrivial lineality
`lin[𝕜](C) ≠ ({0} : Set E)` forces the extreme-point set to be empty. -/
theorem extremePoints_eq_empty_of_lineal_nontrivial_of_exists_midpoint
    [PartialOrder 𝕜] [ZeroLEOneClass 𝕜]
    {C : Set E}
    (hmid : ∃ a : 𝕜, 0 < a ∧ a + a = 1)
    (hlineal : lin[𝕜](C) ≠ ({0} : Set E)) :
    C.extremePoints 𝕜 = ∅ := by
  have hzero : (0 : E) ∈ lin[𝕜](C) := by
    rw [mem_lineal_iff_forall]
    constructor <;> intro x hx a ha <;> simpa using hx
  have hnonzero : ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C) := by
    by_contra hnonzero
    apply hlineal
    rw [Set.eq_singleton_iff_unique_mem]
    exact ⟨hzero, fun y hy ↦ by
      by_contra hy0
      exact hnonzero ⟨y, hy0, hy⟩⟩
  exact extremePoints_eq_empty_of_exists_ne_zero_mem_lineal_of_exists_midpoint hmid hnonzero

/-- Ordered-ring convenience corollary of
`extremePoints_eq_empty_of_exists_ne_zero_mem_lineal_of_exists_midpoint`. -/
theorem extremePoints_eq_empty_of_exists_ne_zero_mem_lineal_of_invOf_two_pos {C : Set E}
    [PartialOrder 𝕜] [ZeroLEOneClass 𝕜] [Invertible (2 : 𝕜)]
    (hhalf_pos : 0 < ⅟(2 : 𝕜))
    (hlineal : ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C)) :
    C.extremePoints 𝕜 = ∅ := by
  refine extremePoints_eq_empty_of_exists_ne_zero_mem_lineal_of_exists_midpoint
    (hmid := ⟨⅟(2 : 𝕜), hhalf_pos, invOf_two_add_invOf_two⟩)
    hlineal

/-- Lineality-nontrivial bridge corollary using `⅟2`: if `⅟2` is positive, then
`lin[𝕜](C) ≠ ({0} : Set E)` forces `C.extremePoints 𝕜 = ∅`. -/
theorem extremePoints_eq_empty_of_lineal_nontrivial_of_invOf_two_pos {C : Set E}
    [PartialOrder 𝕜] [ZeroLEOneClass 𝕜] [Invertible (2 : 𝕜)]
    (hhalf_pos : 0 < ⅟(2 : 𝕜))
    (hlineal : lin[𝕜](C) ≠ ({0} : Set E)) :
    C.extremePoints 𝕜 = ∅ := by
  refine extremePoints_eq_empty_of_lineal_nontrivial_of_exists_midpoint
    (hmid := ⟨⅟(2 : 𝕜), hhalf_pos, invOf_two_add_invOf_two⟩)
    hlineal

/-- Ordered-ring convenience corollary of
`extremePoints_eq_empty_of_exists_ne_zero_mem_lineal_of_invOf_two_pos`. -/
theorem extremePoints_eq_empty_of_exists_ne_zero_mem_lineal {C : Set E}
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Invertible (2 : 𝕜)]
    (hlineal : ∃ y : E, y ≠ 0 ∧ y ∈ lin[𝕜](C)) :
    C.extremePoints 𝕜 = ∅ := by
  exact extremePoints_eq_empty_of_exists_ne_zero_mem_lineal_of_invOf_two_pos
    ((invOf_pos (a := (2 : 𝕜))).2 two_pos) hlineal

/-- Ordered-ring convenience corollary of
`extremePoints_eq_empty_of_lineal_nontrivial_of_invOf_two_pos`. -/
theorem extremePoints_eq_empty_of_lineal_nontrivial {C : Set E}
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Invertible (2 : 𝕜)]
    (hlineal : lin[𝕜](C) ≠ ({0} : Set E)) :
    C.extremePoints 𝕜 = ∅ := by
  exact extremePoints_eq_empty_of_lineal_nontrivial_of_invOf_two_pos
    ((invOf_pos (a := (2 : 𝕜))).2 two_pos) hlineal

end

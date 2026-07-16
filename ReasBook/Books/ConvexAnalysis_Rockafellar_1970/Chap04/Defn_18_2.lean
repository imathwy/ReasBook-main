import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Defn 18.2 introduces extreme points of a convex set by forbidding nontrivial
  strict convex-combination representations `(1 - λ) y + λ z` with `0 < λ < 1`.
- `core/canonical`: mathlib's owner abstraction is `C.extremePoints 𝕜`.
- `bridge/view`: the canonical membership theorem `mem_extremePoints` expresses the definition via
  open segments. The primitive weighted-form bridge below unpacks that segment membership as
  coefficients `a, b` with `0 < a`, `0 < b`, `a + b = 1`. For the one-parameter view, the
  intrinsic affine surface is `openSegment_eq_image_lineMap`, and
  `AffineMap.lineMap_apply_module` recovers the textbook convex combination formula
  `(1 - λ) y + λ z`.
  `openSegment_eq_image_lineMap`, and `lineMap`.
- Primitive data vs derived API: the owner notion is the set of extreme points itself; the
  primitive bridge lives directly on the defining open-segment data; the textbook
  `(1 - λ) y + λ z` criterion is a derived coordinate bridge view, not a new local definition.
- Layer target: `core/canonical`, with the source phrasing recovered by direct bridge recalls.
- Ambient refinement: the owner `Set.extremePoints` itself lives on the weak ordered-semiring smul
  layer; the first bridge theorem below stays exactly on that primitive layer, and the explicit
  one-parameter affine bridge theorem uses only the additional structure required by
  `openSegment_eq_image_lineMap` (ring, ordered additive monotonicity, additive group, and module),
  while the textbook convex-combination form is recovered without specializing to `ℝ`.
-/

/- Defn 18.2: the extreme points of a set `C` are given by the canonical mathlib construction
`C.extremePoints 𝕜`; a point `x` is extreme when it cannot lie in a nontrivial open segment
with endpoints in `C`. -/
recall Set.extremePoints

/- Membership in `C.extremePoints 𝕜` is exactly the statement that any open-segment
representation of `x` with endpoints in `C` is trivial. -/
recall mem_extremePoints

/- One-parameter affine parametrization of `openSegment 𝕜 y z`. -/
recall openSegment_eq_image_lineMap

/- Coordinate formula for line-map parametrization, yielding `(1 - λ) y + λ z`. -/
recall AffineMap.lineMap_apply_module

section

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

namespace Set

/-- Defn 18.2 bridge at the primitive open-segment layer: `x` is an extreme point of `C` iff every
strict weighted representation `a • y + b • z = x` with `0 < a`, `0 < b`, and `a + b = 1` forces
both endpoints to equal `x`. -/
theorem mem_extremePoints_iff_forall_weightedCombination_eq
    {C : Set E} {x : E} :
    x ∈ C.extremePoints 𝕜 ↔
      x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ a b : 𝕜,
        0 < a → 0 < b → a + b = 1 →
          a • y + b • z = x → y = x ∧ z = x := by
  constructor
  · intro hx
    rcases (mem_extremePoints.mp hx) with ⟨hxC, hxExtreme⟩
    refine ⟨hxC, ?_⟩
    intro y hy z hz a b ha hb hab hcombo
    exact hxExtreme y hy z hz ⟨a, b, ha, hb, hab, hcombo⟩
  · rintro ⟨hxC, hxCombo⟩
    refine mem_extremePoints.mpr ⟨hxC, ?_⟩
    intro y hy z hz hxSeg
    rcases hxSeg with ⟨a, b, ha, hb, hab, hcombo⟩
    exact hxCombo y hy z hz a b ha hb hab hcombo

/-- One-sided weighted-combination corollary for Defn 18.2: in the same strict weighted
representation, the left endpoint is forced to equal `x`. -/
theorem mem_extremePoints_iff_forall_weightedCombination_eq_left
    {C : Set E} {x : E} :
    x ∈ C.extremePoints 𝕜 ↔
      x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ a b : 𝕜,
        0 < a → 0 < b → a + b = 1 →
          a • y + b • z = x → y = x := by
  constructor
  · intro hx
    rcases (mem_extremePoints_iff_forall_weightedCombination_eq.mp hx) with ⟨hxC, hxCombo⟩
    refine ⟨hxC, ?_⟩
    intro y hy z hz a b ha hb hab hcombo
    exact (hxCombo y hy z hz a b ha hb hab hcombo).1
  · rintro ⟨hxC, hxCombo⟩
    refine mem_extremePoints_iff_forall_weightedCombination_eq.mpr ⟨hxC, ?_⟩
    intro y hy z hz a b ha hb hab hcombo
    refine ⟨hxCombo y hy z hz a b ha hb hab hcombo, ?_⟩
    exact hxCombo z hz y hy b a hb ha (by simpa [add_comm] using hab)
      (by simpa [add_comm] using hcombo)

end Set

end

section

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

open AffineMap

namespace Set

/-- Defn 18.2 bridge in textbook parameter form: `x` is an extreme point of `C` iff every strict
affine line-map representation of `x` with endpoints in `C` forces both endpoints to equal `x`.
-/
theorem mem_extremePoints_iff_forall_lineMap_eq
    {C : Set E} {x : E} :
    x ∈ C.extremePoints 𝕜 ↔
      x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ t : 𝕜,
        t ∈ Set.Ioo (0 : 𝕜) 1 →
          lineMap y z t = x → y = x ∧ z = x := by
  constructor
  · intro hx
    rcases (mem_extremePoints.mp hx) with ⟨hxC, hxExtreme⟩
    refine ⟨hxC, ?_⟩
    intro y hy z hz t ht hline
    exact hxExtreme y hy z hz <| by
      rw [openSegment_eq_image_lineMap]
      exact ⟨t, ht, hline⟩
  · rintro ⟨hxC, hxLine⟩
    refine mem_extremePoints.mpr ⟨hxC, ?_⟩
    intro y hy z hz hxSeg
    rcases (show x ∈ (lineMap y z) '' Set.Ioo (0 : 𝕜) 1 by
      simpa [openSegment_eq_image_lineMap] using hxSeg) with ⟨t, ht, hline⟩
    exact hxLine y hy z hz t ht hline

/-- One-sided affine line-map corollary for Defn 18.2: in the same strict representation, the
left endpoint is forced to equal `x`. -/
theorem mem_extremePoints_iff_forall_lineMap_eq_left
    {C : Set E} {x : E} :
    x ∈ C.extremePoints 𝕜 ↔
      x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ t : 𝕜,
        t ∈ Set.Ioo (0 : 𝕜) 1 →
          lineMap y z t = x → y = x := by
  constructor
  · intro hx
    rcases (mem_extremePoints_iff_forall_lineMap_eq.mp hx) with ⟨hxC, hxLine⟩
    refine ⟨hxC, ?_⟩
    intro y hy z hz t ht hline
    exact (hxLine y hy z hz t ht hline).1
  · rintro ⟨hxC, hxLine⟩
    refine mem_extremePoints_iff_forall_lineMap_eq.mpr ⟨hxC, ?_⟩
    intro y hy z hz t ht hline
    have hx : x ∈ C.extremePoints 𝕜 := by
      refine mem_extremePoints_iff_left.mpr ⟨hxC, ?_⟩
      intro y' hy' z' hz' hxSeg
      rcases (show x ∈ (lineMap y' z') '' Set.Ioo (0 : 𝕜) 1 by
        simpa [openSegment_eq_image_lineMap] using hxSeg) with ⟨t', ht', hline'⟩
      exact hxLine y' hy' z' hz' t' ht' hline'
    exact (mem_extremePoints_iff_forall_lineMap_eq.mp hx).2 y hy z hz t ht hline

end Set

end

section

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
  [AddCommMonoid E] [SMul 𝕜 E]

namespace Set

/-- Defn 18.2 bridge in textbook parameter form: `x` is an extreme point of `C` iff every strict
convex-combination representation `(1 - t) • y + t • z` of `x` with endpoints in `C` forces both
endpoints to equal `x`. -/
theorem mem_extremePoints_iff_forall_strictConvexCombination_eq
    {C : Set E} {x : E} :
    x ∈ C.extremePoints 𝕜 ↔
      x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ t : 𝕜,
        t ∈ Set.Ioo (0 : 𝕜) 1 →
          (1 - t) • y + t • z = x → y = x ∧ z = x := by
  constructor
  · intro hx
    rcases (mem_extremePoints_iff_forall_weightedCombination_eq.mp hx) with
      ⟨hxC, hxWeighted⟩
    refine ⟨hxC, ?_⟩
    intro y hy z hz t ht hcombo
    exact hxWeighted y hy z hz (1 - t) t (sub_pos.mpr ht.2) ht.1 (sub_add_cancel 1 t) hcombo
  · rintro ⟨hxC, hxStrict⟩
    refine mem_extremePoints_iff_forall_weightedCombination_eq.mpr ⟨hxC, ?_⟩
    intro y hy z hz a b ha hb hab hcombo
    have hb_lt_one : b < 1 := by
      have hlt : b < a + b := by
        simpa [add_comm] using lt_add_of_pos_left b ha
      simpa [hab] using hlt
    have htb : b ∈ Set.Ioo (0 : 𝕜) 1 := ⟨hb, hb_lt_one⟩
    have ha_eq : a = 1 - b := by
      exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hab)
    exact hxStrict y hy z hz b htb (by simpa [ha_eq] using hcombo)

/-- One-sided textbook corollary for Defn 18.2: in the same strict convex-combination
representation, the left endpoint is forced to equal `x`. -/
theorem mem_extremePoints_iff_forall_strictConvexCombination_eq_left
    {C : Set E} {x : E} :
    x ∈ C.extremePoints 𝕜 ↔
      x ∈ C ∧ ∀ y ∈ C, ∀ z ∈ C, ∀ t : 𝕜,
        t ∈ Set.Ioo (0 : 𝕜) 1 →
          (1 - t) • y + t • z = x → y = x := by
  constructor
  · intro hx
    rcases (mem_extremePoints_iff_forall_strictConvexCombination_eq.mp hx) with
      ⟨hxC, hxStrict⟩
    refine ⟨hxC, ?_⟩
    intro y hy z hz t ht hcombo
    exact (hxStrict y hy z hz t ht hcombo).1
  · rintro ⟨hxC, hxStrict⟩
    refine mem_extremePoints_iff_forall_strictConvexCombination_eq.mpr ⟨hxC, ?_⟩
    intro y hy z hz t ht hcombo
    have hx : x ∈ C.extremePoints 𝕜 := by
      refine mem_extremePoints_iff_forall_weightedCombination_eq_left.mpr ⟨hxC, ?_⟩
      intro y' hy' z' hz' a b ha hb hab hcombo'
      have hb_lt_one : b < 1 := by
        have hlt : b < a + b := by
          simpa [add_comm] using lt_add_of_pos_left b ha
        simpa [hab] using hlt
      have htb : b ∈ Set.Ioo (0 : 𝕜) 1 := ⟨hb, hb_lt_one⟩
      have ha_eq : a = 1 - b := by
        exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hab)
      exact hxStrict y' hy' z' hz' b htb (by simpa [ha_eq] using hcombo')
    exact (mem_extremePoints_iff_forall_strictConvexCombination_eq.mp hx).2 y hy z hz t ht hcombo

end Set

end

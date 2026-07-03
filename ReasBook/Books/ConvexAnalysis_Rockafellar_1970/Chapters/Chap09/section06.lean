import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_9_6_1 (from Chap02) -/
section

open scoped Pointwise Rockafellar


/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.6.1 is expressed at the generated-cone owner level:
  a closed convex set avoiding `0` and with trivial recession cone has closed generated cone.
- `core/canonical`: the generated cone owner is `cone[𝕜] C` (raw owner `PointedCone.hull 𝕜 C`),
  and the primitive closure trigger is the asymptotic-cone subset condition
  `asymptoticCone 𝕜 C ⊆ ({0} : Set E)`.
- `bridge/view`: Theorem 9.6 gives `closure cone = cone ∪ asymptoticCone`, and
  `Convex.recessionCone_eq_asymptoticCone` bridges the source-facing recession hypothesis to that
  canonical owner hypothesis.

Domain-style sampling used here:
- `cone[𝕜]`;
- `PointedCone.closure_cone_eq_union_asymptoticCone`;
- `Convex.recessionCone_eq_asymptoticCone`;
- `PointedCone.coe_closure`.

Primitive data vs derived API:
- primitive owner-level inputs: `IsClosed C`, `Convex 𝕜 C`, `0 ∉ C`, and
  `asymptoticCone 𝕜 C ⊆ ({0} : Set E)`;
- source-facing bridge input: `0⁺[𝕜] C ⊆ ({0} : Set E)`;
- derived owner output: `IsClosed (cone[𝕜] C : Set E)`;
- nonempty is an internal branch condition used only to invoke Theorem 9.6; the empty-set branch
  is discharged directly from the canonical empty owners.

Layer target:
- canonical owner theorem plus a thin source-facing bridge theorem.
-/

namespace PointedCone

section OrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T1Space E]

/-- Corollary 9.6.1 (canonical owner form, primitive subset layer): if a closed convex set avoids
`0` and has asymptotic cone contained in `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_asymptoticCone_subset_singleton_zero
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) (hAsym : asymptoticCone 𝕜 C ⊆ ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  by_cases hC_nonempty : C.Nonempty
  · have hCone_closure : ((cone[𝕜] C).closure : Set E) = (cone[𝕜] C : Set E) := by
      calc
        ((cone[𝕜] C).closure : Set E)
            = (cone[𝕜] C : Set E) ∪ asymptoticCone 𝕜 C := by
              simpa using
                (closure_cone_eq_union_asymptoticCone C hC_nonempty hC_closed hC_convex h0C)
        _ = (cone[𝕜] C : Set E) := by
              refine Set.union_eq_left.2 ?_
              exact Set.Subset.trans hAsym
                (Set.singleton_subset_iff.2 (cone[𝕜] C).zero_mem)
    rw [← closure_eq_iff_isClosed, ← PointedCone.coe_closure]
    exact hCone_closure
  · have hC_empty : C = (∅ : Set E) := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
    subst hC_empty
    have hcone_empty : (cone[𝕜] (∅ : Set E) : Set E) = ({0} : Set E) := by
      simp
    rw [hcone_empty]
    exact isClosed_singleton

/-- Corollary 9.6.1 (canonical owner form, equality bridge): if a closed convex set avoids `0` and
has asymptotic cone exactly `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_asymptoticCone_eq_singleton_zero
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) (hAsym : asymptoticCone 𝕜 C = ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  exact isClosed_cone_of_asymptoticCone_subset_singleton_zero
    C hC_closed hC_convex h0C hAsym.subset

/-- Corollary 9.6.1 (source-facing recession form, primitive subset layer): if a closed convex set
avoids `0` and has recession cone contained in `{0}`, then its generated cone `cone[𝕜] C` is
closed. -/
theorem isClosed_cone_of_recessionCone_subset_singleton_zero
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) (hRec : 0⁺[𝕜]C ⊆ ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  have hAsym : asymptoticCone 𝕜 C ⊆ ({0} : Set E) := by
    by_cases hC_nonempty : C.Nonempty
    · rw [← hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty]
      exact hRec
    · have hC_empty : C = (∅ : Set E) := Set.not_nonempty_iff_eq_empty.mp hC_nonempty
      subst hC_empty
      simp [asymptoticCone_empty]
  exact isClosed_cone_of_asymptoticCone_subset_singleton_zero
    C hC_closed hC_convex h0C hAsym

/-- Corollary 9.6.1 (source-facing recession form, equality bridge): if a closed convex set avoids
`0` and has recession cone exactly `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_recessionCone_eq_singleton_zero
    (C : Set E) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) (hRec : 0⁺[𝕜]C = ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  exact isClosed_cone_of_recessionCone_subset_singleton_zero
    C hC_closed hC_convex h0C hRec.subset

end OrderedField

end PointedCone

namespace Convex

section OrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T1Space E]

/-- Corollary 9.6.1 in object-prefix source-facing form: if a closed convex set avoids `0` and has
recession cone contained in `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_recessionCone_subset_singleton_zero
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    (h0C : (0 : E) ∉ C) (hRec : 0⁺[𝕜]C ⊆ ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  exact
    PointedCone.isClosed_cone_of_recessionCone_subset_singleton_zero
      C hC_closed hC_convex h0C hRec

/-- Corollary 9.6.1 in object-prefix source-facing equality form: if a closed convex set avoids
`0` and has recession cone exactly `{0}`, then its generated cone `cone[𝕜] C` is closed. -/
theorem isClosed_cone_of_recessionCone_eq_singleton_zero
    {C : Set E} (hC_convex : Convex 𝕜 C) (hC_closed : IsClosed C)
    (h0C : (0 : E) ∉ C) (hRec : 0⁺[𝕜]C = ({0} : Set E)) :
    IsClosed (cone[𝕜] C : Set E) := by
  exact
    PointedCone.isClosed_cone_of_recessionCone_eq_singleton_zero
      C hC_closed hC_convex h0C hRec

end OrderedField

end Convex

end

/-! ### Remark_9_6_1_2 (from Chap02) -/
section

/-- The shifted unit disk `{(x, y) | (x - 1)^2 + y^2 ≤ 1}` in `ℝ × ℝ`. -/
def closedBallAtE1 : Set (ℝ × ℝ) := {p : ℝ × ℝ | (p.1 - 1)^2 + p.2^2 ≤ (1 : ℝ)}

/-- The affine vertical line `{(1, t) | t ∈ ℝ}` in `ℝ × ℝ`. -/
def offsetLine : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 = (1 : ℝ)}

local notation "coneClosedBallAtE1" => (cone[ℝ] closedBallAtE1 : Set (ℝ × ℝ))
local notation "coneOffsetLine" => (cone[ℝ] offsetLine : Set (ℝ × ℝ))

open Bornology Metric Set
open scoped Pointwise

/-!
Source/core/bridge triage:

- `source-facing`: this remark gives two concrete counterexamples showing that the hypotheses
  `0 ∉ C` in Theorem 9.6 and Corollary 9.6.1, and boundedness in Corollary 9.6.1, are genuinely
  needed.
- `core/canonical`: the generated cone owner is `cone[ℝ] C`. The two witness sets are written
  directly as canonical subsets of `ℝ × ℝ`: the algebraic Euclidean closed unit disk centered at
  `(1, 0)`, and the affine line `{(1, t)}`.
- `bridge/view`: no inner-product/`EuclideanSpace` owner is required.

Domain-style sampling used here:
- `cone[ℝ]`;
- `isClosed_le` for polynomial sublevel sets;
- direct `Convex` proof for the shifted Euclidean unit-disk equation;
- `Metric.isBounded_iff_subset_closedBall`;
- `isClosed_eq continuous_fst continuous_const`;
- direct `Convex` proof for `{p | p.1 = 1}`.

Primitive data vs derived API:
- primitive data: the canonical owner expressions
  `{p | (p.1 - 1)^2 + p.2^2 ≤ 1}` and `offsetLine`;
- derived API: the origin-membership witness for the first set, the origin-avoidance and
  unboundedness witnesses for the affine line, and the nonclosedness of their generated pointed
  cones. The owner facts `IsClosed`, `Convex`, and `IsBounded` are reused directly inside the two
  source-facing counterexamples rather than republished as local wrapper theorems.

Layer target: `source-facing`, stated as explicit counterexamples rather than as an existential
repackaging.
-/

private theorem zero_mem_closedBallAtE1 :
    (0 : ℝ × ℝ) ∈ closedBallAtE1 := by
  change (((0 : ℝ) - 1)^2 + (0 : ℝ)^2 ≤ (1 : ℝ))
  norm_num

private theorem fst_nonneg_of_mem_closedBallAtE1 {p : ℝ × ℝ}
    (hp : p ∈ closedBallAtE1) : 0 ≤ p.1 := by
  change (p.1 - 1)^2 + p.2^2 ≤ (1 : ℝ) at hp
  have hp1_sq_le : (p.1 - 1)^2 ≤ (1 : ℝ) := by
    nlinarith [hp, sq_nonneg p.2]
  have hp1_abs_le : |p.1 - 1| ≤ (1 : ℝ) :=
    (sq_le_one_iff_abs_le_one (p.1 - 1)).1 hp1_sq_le
  have hp1_bounds : -1 ≤ p.1 - 1 ∧ p.1 - 1 ≤ 1 := abs_le.mp hp1_abs_le
  linarith [hp1_bounds.1]

private theorem eq_zero_of_mem_closedBallAtE1_of_fst_eq_zero {p : ℝ × ℝ}
    (hp : p ∈ closedBallAtE1) (hp0 : p.1 = 0) : p = 0 := by
  change (p.1 - 1)^2 + p.2^2 ≤ (1 : ℝ) at hp
  have hp2_sq_le_zero : p.2^2 ≤ 0 := by
    nlinarith [hp, hp0]
  have hp2_zero : p.2 = 0 := by
    nlinarith [hp2_sq_le_zero, sq_nonneg p.2]
  ext <;> simp [hp0, hp2_zero]

private theorem sq_weighted_le (a b u v : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * u + b * v)^2 ≤ a * u^2 + b * v^2 := by
  have hxy : 2 * u * v ≤ u^2 + v^2 := by
    nlinarith [sq_nonneg (u - v)]
  calc
    (a * u + b * v)^2 = a^2 * u^2 + b^2 * v^2 + 2 * a * b * (u * v) := by ring
    _ ≤ a^2 * u^2 + b^2 * v^2 + (a * b) * (u^2 + v^2) := by
      have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
      nlinarith
    _ = (a + b) * (a * u^2 + b * v^2) := by ring
    _ = (1 : ℝ) * (a * u^2 + b * v^2) := by rw [hab]
    _ = a * u^2 + b * v^2 := by ring

private theorem convex_closedBallAtE1 :
    Convex ℝ closedBallAtE1 := by
  intro x hx y hy a b ha hb hab
  change ((a * x.1 + b * y.1) - 1)^2 + (a * x.2 + b * y.2)^2 ≤ (1 : ℝ)
  have hlin : (a * x.1 + b * y.1) - 1 = a * (x.1 - 1) + b * (y.1 - 1) := by
    nlinarith [hab]
  have h1 : (a * (x.1 - 1) + b * (y.1 - 1))^2 ≤ a * (x.1 - 1)^2 + b * (y.1 - 1)^2 :=
    sq_weighted_le a b (x.1 - 1) (y.1 - 1) ha hb hab
  have h2 : (a * x.2 + b * y.2)^2 ≤ a * x.2^2 + b * y.2^2 :=
    sq_weighted_le a b x.2 y.2 ha hb hab
  have hx' : (x.1 - 1)^2 + x.2^2 ≤ (1 : ℝ) := by simpa using hx
  have hy' : (y.1 - 1)^2 + y.2^2 ≤ (1 : ℝ) := by simpa using hy
  have hsum :
      (a * (x.1 - 1) + b * (y.1 - 1))^2 + (a * x.2 + b * y.2)^2 ≤
        a * ((x.1 - 1)^2 + x.2^2) + b * ((y.1 - 1)^2 + y.2^2) := by
    nlinarith [h1, h2]
  calc
    ((a * x.1 + b * y.1) - 1)^2 + (a * x.2 + b * y.2)^2
        = (a * (x.1 - 1) + b * (y.1 - 1))^2 + (a * x.2 + b * y.2)^2 := by
          rw [hlin]
    _ ≤ a * ((x.1 - 1)^2 + x.2^2) + b * ((y.1 - 1)^2 + y.2^2) := hsum
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = (1 : ℝ) := by nlinarith [hab]

private theorem isClosed_closedBallAtE1 :
    IsClosed closedBallAtE1 := by
  let f : ℝ × ℝ → ℝ := fun p => (p.1 - 1)^2 + p.2^2
  have hf : Continuous f := by continuity
  change IsClosed {p : ℝ × ℝ | f p ≤ (1 : ℝ)}
  simpa using isClosed_le hf continuous_const

private theorem isBounded_closedBallAtE1 :
    IsBounded closedBallAtE1 := by
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).2 ?_
  refine ⟨2, ?_⟩
  intro p hp
  change (p.1 - 1)^2 + p.2^2 ≤ (1 : ℝ) at hp
  have hp1_sq_le : (p.1 - 1)^2 ≤ (1 : ℝ) := by
    nlinarith [hp, sq_nonneg p.2]
  have hp2_sq_le : p.2^2 ≤ (1 : ℝ) := by
    nlinarith [hp, sq_nonneg (p.1 - 1)]
  have hp1_abs_le_one : |p.1 - 1| ≤ (1 : ℝ) :=
    (sq_le_one_iff_abs_le_one (p.1 - 1)).1 hp1_sq_le
  have hp2_abs_le_one : |p.2| ≤ (1 : ℝ) :=
    (sq_le_one_iff_abs_le_one p.2).1 hp2_sq_le
  have hp1_bounds : -1 ≤ p.1 - 1 ∧ p.1 - 1 ≤ 1 := abs_le.mp hp1_abs_le_one
  have hp1_nonneg : 0 ≤ p.1 := by
    linarith [hp1_bounds.1]
  have hp1_le_two : p.1 ≤ 2 := by
    linarith [hp1_bounds.2]
  have hp1_abs_le_two : |p.1| ≤ (2 : ℝ) := by
    calc
      |p.1| = p.1 := abs_of_nonneg hp1_nonneg
      _ ≤ 2 := hp1_le_two
  have hp2_abs_le_two : |p.2| ≤ (2 : ℝ) := by
    linarith [hp2_abs_le_one]
  have hnorm_le_two : ‖p‖ ≤ (2 : ℝ) := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le hp1_abs_le_two hp2_abs_le_two
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le_two

private theorem mem_coneClosedBallAtE1_of_fst_pos {x : ℝ × ℝ}
    (hx1 : 0 < x.1) : x ∈ coneClosedBallAtE1 := by
  let l : ℝ := (x.1^2 + x.2^2) / (2 * x.1)
  have hl_pos : 0 < l := by
    have hnum_pos : 0 < x.1^2 + x.2^2 := by
      nlinarith [sq_pos_of_ne_zero hx1.ne', sq_nonneg x.2]
    have hden_pos : 0 < 2 * x.1 := by nlinarith
    exact div_pos hnum_pos hden_pos
  have hl_ne : l ≠ 0 := hl_pos.ne'
  let y : ℝ × ℝ := (x.1 / l, x.2 / l)
  have hy_mem : y ∈ closedBallAtE1 := by
    change (x.1 / l - 1)^2 + (x.2 / l)^2 ≤ (1 : ℝ)
    have hEq' :
        (x.1 / ((x.1^2 + x.2^2) / (2 * x.1)) - 1)^2 +
          (x.2 / ((x.1^2 + x.2^2) / (2 * x.1)))^2 = (1 : ℝ) := by
      field_simp [hx1.ne']
      ring
    have hEq : (x.1 / l - 1)^2 + (x.2 / l)^2 = (1 : ℝ) := by
      simpa [l] using hEq'
    linarith [hEq]
  have hyCone : y ∈ coneClosedBallAtE1 := PointedCone.subset_hull hy_mem
  have hxy : x = l • y := by
    ext
    · simp [y, smul_eq_mul]
      field_simp [hl_ne]
    · simp [y, smul_eq_mul]
      field_simp [hl_ne]
  exact hxy.symm ▸ (cone[ℝ] closedBallAtE1).smul_mem (le_of_lt hl_pos) hyCone

private theorem coneClosedBallAtE1_eq_zero_of_fst_eq_zero {x : ℝ × ℝ}
    (hx : x ∈ coneClosedBallAtE1) (hx0 : x.1 = 0) : x = 0 := by
  rcases PointedCone.mem_hull_set.mp hx with ⟨c, hcS, hc0, hsum⟩
  have hx1_eq : x.1 = c.support.sum (fun m => (c m • m).1) := by
    have hfst := congrArg (AddMonoidHom.fst ℝ ℝ) hsum.symm
    simpa [Finsupp.sum, map_sum] using hfst
  have hsum_first_zero : c.support.sum (fun m => (c m • m).1) = 0 := by
    linarith [hx1_eq, hx0]
  have hterm_nonneg : ∀ m ∈ c.support, 0 ≤ (c m • m).1 := by
    intro m hm
    have hmS : m ∈ closedBallAtE1 := hcS (by simpa using hm)
    exact mul_nonneg (hc0 m) (fst_nonneg_of_mem_closedBallAtE1 hmS)
  have hterm_first_zero : ∀ m ∈ c.support, (c m • m).1 = 0 := by
    intro m hm
    exact (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1 hsum_first_zero m hm
  have hterm_vec_zero : ∀ m ∈ c.support, c m • m = 0 := by
    intro m hm
    have hmS : m ∈ closedBallAtE1 := hcS (by simpa using hm)
    have hcm_ne : c m ≠ 0 := by simpa [Finsupp.mem_support_iff] using hm
    have hm1_zero : m.1 = 0 := by
      have hm_prod : c m * m.1 = 0 := by
        simpa [smul_eq_mul] using hterm_first_zero m hm
      exact (mul_eq_zero.mp hm_prod).resolve_left hcm_ne
    have hm_zero : m = 0 := eq_zero_of_mem_closedBallAtE1_of_fst_eq_zero hmS hm1_zero
    simp [hm_zero]
  have hsum_vec_zero : c.support.sum (fun m => c m • m) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    exact hterm_vec_zero m hm
  calc
    x = c.support.sum (fun m => c m • m) := hsum.symm
    _ = 0 := hsum_vec_zero

private theorem mem_coneClosedBallAtE1_iff (x : ℝ × ℝ) :
    x ∈ coneClosedBallAtE1 ↔ x = 0 ∨ 0 < x.1 := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hx1_nonneg : 0 ≤ x.1 := by
        rcases PointedCone.mem_hull_set.mp hx with ⟨c, hcS, hc0, hsum⟩
        have hx1_eq : x.1 = c.support.sum (fun m => (c m • m).1) := by
          have hfst := congrArg (AddMonoidHom.fst ℝ ℝ) hsum.symm
          simpa [Finsupp.sum, map_sum] using hfst
        rw [hx1_eq]
        refine Finset.sum_nonneg ?_
        intro m hm
        have hmS : m ∈ closedBallAtE1 := hcS (by simpa using hm)
        exact mul_nonneg (hc0 m) (fst_nonneg_of_mem_closedBallAtE1 hmS)
      have hx1_ne : x.1 ≠ 0 := by
        intro hx10
        exact hx0 (coneClosedBallAtE1_eq_zero_of_fst_eq_zero hx hx10)
      exact lt_of_le_of_ne hx1_nonneg hx1_ne.symm
  · rintro (rfl | hx1)
    · exact (cone[ℝ] closedBallAtE1).zero_mem
    · exact mem_coneClosedBallAtE1_of_fst_pos hx1

/-- The pointed cone generated by the boundary-origin closed ball is not closed. -/
private theorem pointedConeHull_closedBall_centeredAt_e1_not_isClosed :
    ¬ IsClosed coneClosedBallAtE1 := by
  intro hClosed
  have hmem : ((0 : ℝ), (1 : ℝ)) ∈ coneClosedBallAtE1 := by
    apply (Metric.mem_of_closed' hClosed).2
    intro ε hε
    refine ⟨((ε / 2), (1 : ℝ)), ?_, ?_⟩
    · exact mem_coneClosedBallAtE1_of_fst_pos (x := ((ε / 2), (1 : ℝ))) (half_pos hε)
    · simp [Prod.dist_eq, Real.dist_eq, abs_of_pos (half_pos hε), hε]
  have hp_ne : ((0 : ℝ), (1 : ℝ)) ≠ (0 : ℝ × ℝ) := by simp
  have hnot : ((0 : ℝ), (1 : ℝ)) ∉ coneClosedBallAtE1 := by
    intro hp
    rcases (mem_coneClosedBallAtE1_iff ((0 : ℝ), (1 : ℝ))).1 hp with hzero | hfst
    · exact hp_ne hzero
    · linarith
  exact hnot hmem

/-- The origin does not lie on the affine line `{(1, t) | t ∈ ℝ}`. -/
private theorem zero_not_mem_offsetLine :
    (0 : ℝ × ℝ) ∉ offsetLine := by
  simp [offsetLine, zero_ne_one]

/-- The affine line `{(1, t) | t ∈ ℝ}` is unbounded. -/
private theorem offsetLine_not_isBounded :
    ¬ IsBounded offsetLine := by
  intro hB
  rcases isBounded_iff_forall_norm_le.mp hB with ⟨C, hC⟩
  have hmem : ((1 : ℝ), (C + 1 : ℝ)) ∈ offsetLine := by
    simp [offsetLine]
  have hnorm_le : ‖((1 : ℝ), (C + 1 : ℝ))‖ ≤ C := hC _ hmem
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg ((1 : ℝ), (C + 1 : ℝ))) hnorm_le
  have hnorm_eq : ‖((1 : ℝ), (C + 1 : ℝ))‖ = C + 1 := by
    have hC1_ge_one : (1 : ℝ) ≤ C + 1 := by linarith
    have hC1_nonneg : 0 ≤ C + 1 := by linarith
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hC1_nonneg, max_eq_right hC1_ge_one]
  linarith [hnorm_le, hnorm_eq]

private theorem coneOffsetLine_eq_zero_of_fst_eq_zero {x : ℝ × ℝ}
    (hx : x ∈ coneOffsetLine) (hx0 : x.1 = 0) : x = 0 := by
  rcases PointedCone.mem_hull_set.mp hx with ⟨c, hcS, hc0, hsum⟩
  have hx1_eq : x.1 = c.support.sum (fun m => (c m • m).1) := by
    have hfst := congrArg (AddMonoidHom.fst ℝ ℝ) hsum.symm
    simpa [Finsupp.sum, map_sum] using hfst
  have hsupport_empty : c.support = ∅ := by
    by_contra hne
    obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hmS : m ∈ offsetLine := hcS (by simpa using hm)
    have hm1 : m.1 = (1 : ℝ) := by simpa [offsetLine] using hmS
    have hcm_ne : c m ≠ 0 := by simpa [Finsupp.mem_support_iff] using hm
    have hcm_pos : 0 < c m := lt_of_le_of_ne (hc0 m) hcm_ne.symm
    have hm_term_pos : 0 < (c m • m).1 := by
      simpa [smul_eq_mul, hm1] using hcm_pos
    have hsum_pos : 0 < c.support.sum (fun y : ℝ × ℝ => (c y • y).1) := by
      refine Finset.sum_pos' ?_ ?_
      · intro y hy
        have hyS : y ∈ offsetLine := hcS (by simpa using hy)
        have hy1 : y.1 = (1 : ℝ) := by simpa [offsetLine] using hyS
        simp [smul_eq_mul, hy1, hc0 y]
      · exact ⟨m, hm, hm_term_pos⟩
    have hx1_zero : c.support.sum (fun y : ℝ × ℝ => (c y • y).1) = 0 := by
      linarith [hx1_eq, hx0]
    exact (lt_irrefl (0 : ℝ)) (hx1_zero ▸ hsum_pos)
  have hc_zero : c = 0 := by
    ext m
    by_cases hm : m ∈ c.support
    · simp [hsupport_empty] at hm
    · simpa [Finsupp.mem_support_iff] using hm
  calc
    x = c.support.sum (fun m => c m • m) := hsum.symm
    _ = 0 := by simp [hc_zero]

private theorem mem_coneOffsetLine_of_fst_pos {x : ℝ × ℝ}
    (hx1 : 0 < x.1) : x ∈ coneOffsetLine := by
  let y : ℝ × ℝ := (1, x.2 / x.1)
  have hy : y ∈ offsetLine := by simp [y, offsetLine]
  have hyCone : y ∈ coneOffsetLine := PointedCone.subset_hull hy
  have hxy : x = x.1 • y := by
    ext
    · simp [y]
    · have hx1ne : x.1 ≠ 0 := hx1.ne'
      calc
        x.2 = (x.1 * x.2) / x.1 := by field_simp [hx1ne]
        _ = x.1 * (x.2 / x.1) := by ring
        _ = (x.1 • y).2 := by simp [y, smul_eq_mul]
  refine hxy.symm ▸ (cone[ℝ] offsetLine).smul_mem (le_of_lt hx1) hyCone

private theorem mem_coneOffsetLine_iff (x : ℝ × ℝ) :
    x ∈ coneOffsetLine ↔ x = 0 ∨ 0 < x.1 := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hx1_nonneg : 0 ≤ x.1 := by
        rcases PointedCone.mem_hull_set.mp hx with ⟨c, hcS, hc0, hsum⟩
        have hx1_eq : x.1 = c.support.sum (fun m => (c m • m).1) := by
          have hfst := congrArg (AddMonoidHom.fst ℝ ℝ) hsum.symm
          simpa [Finsupp.sum, map_sum] using hfst
        rw [hx1_eq]
        refine Finset.sum_nonneg ?_
        intro m hm
        have hmS : m ∈ offsetLine := hcS (by simpa using hm)
        have hm1 : m.1 = (1 : ℝ) := by simpa [offsetLine] using hmS
        simpa [smul_eq_mul, hm1] using hc0 m
      have hx1_ne : x.1 ≠ 0 := by
        intro hx10
        exact hx0 (coneOffsetLine_eq_zero_of_fst_eq_zero hx hx10)
      exact lt_of_le_of_ne hx1_nonneg hx1_ne.symm
  · rintro (rfl | hx1)
    · exact (cone[ℝ] offsetLine).zero_mem
    · exact mem_coneOffsetLine_of_fst_pos hx1

/-- The pointed cone generated by the affine line `{(1, t) | t ∈ ℝ}` is not closed. -/
private theorem pointedConeHull_offsetLine_not_isClosed :
    ¬ IsClosed coneOffsetLine := by
  intro hClosed
  have hmem : ((0 : ℝ), (1 : ℝ)) ∈ coneOffsetLine := by
    apply (Metric.mem_of_closed' hClosed).2
    intro ε hε
    refine ⟨((ε / 2), (1 : ℝ)), ?_, ?_⟩
    · exact mem_coneOffsetLine_of_fst_pos (x := ((ε / 2), (1 : ℝ))) (half_pos hε)
    · simp [Prod.dist_eq, Real.dist_eq, abs_of_pos (half_pos hε), hε]
  have hp_ne : ((0 : ℝ), (1 : ℝ)) ≠ (0 : ℝ × ℝ) := by simp
  have hnot : ((0 : ℝ), (1 : ℝ)) ∉ coneOffsetLine := by
    intro hp
    rcases (mem_coneOffsetLine_iff ((0 : ℝ), (1 : ℝ))).1 hp with hzero | hfst
    · exact hp_ne hzero
    · linarith
  exact hnot hmem

/-- The closed unit ball centered at `(1, 0)` satisfies all of the other hypotheses from
Theorem 9.6 and Corollary 9.6.1 except `0 ∉ C`, but its generated pointed cone is not closed. -/
theorem closedBallAtE1_counterexample :
    (0 : ℝ × ℝ) ∈ closedBallAtE1 ∧
      IsClosed closedBallAtE1 ∧
      Convex ℝ closedBallAtE1 ∧
      IsBounded closedBallAtE1 ∧
      ¬ IsClosed coneClosedBallAtE1 := by
  exact
    ⟨zero_mem_closedBallAtE1, isClosed_closedBallAtE1, convex_closedBallAtE1,
      isBounded_closedBallAtE1, pointedConeHull_closedBall_centeredAt_e1_not_isClosed⟩

/-- The affine line `{(1, t) | t ∈ ℝ}` satisfies the other explicit hypotheses from
Corollary 9.6.1 except boundedness, but its generated pointed cone is not closed. -/
theorem offsetLine_counterexample :
    IsClosed offsetLine ∧
      Convex ℝ offsetLine ∧
      (0 : ℝ × ℝ) ∉ offsetLine ∧
      ¬ IsBounded offsetLine ∧
      ¬ IsClosed coneOffsetLine := by
  have hOffsetClosed : IsClosed offsetLine := by
    change IsClosed {p : ℝ × ℝ | p.1 = (1 : ℝ)}
    simpa using isClosed_eq continuous_fst continuous_const
  have hOffsetConvex : Convex ℝ offsetLine := by
    intro x hx y hy a b _ha _hb hab
    have hx1 : x.1 = (1 : ℝ) := by simpa [offsetLine] using hx
    have hy1 : y.1 = (1 : ℝ) := by simpa [offsetLine] using hy
    change a * x.1 + b * y.1 = (1 : ℝ)
    calc
      a * x.1 + b * y.1 = a * 1 + b * 1 := by simp [hx1, hy1]
      _ = 1 := by nlinarith [hab]
  exact
    ⟨hOffsetClosed, hOffsetConvex, zero_not_mem_offsetLine, offsetLine_not_isBounded,
      pointedConeHull_offsetLine_not_isClosed⟩

end

/-! ### Theorem_9_6 (from Chap02) -/
section

open scoped Pointwise
open scoped Rockafellar

namespace PointedCone

section RayBridge

variable {𝕜 : Type*} [Semifield 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [PosMulReflectLT 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- Algebraic owner bridge used by Theorem 9.6: for a nonempty convex set, replacing the generated
cone by its nonnegative-ray description does not change a union surface. -/
theorem cone_union_eq_nonnegativeRay_union
    (C S : Set E) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    (cone[𝕜] C : Set E) ∪ S = 𝕜≥0 • C ∪ S := by
  rw [cone_eq_nonnegativeRay_of_convex C hC_convex hC_nonempty]

/-- Source-facing recession-cone specialization of
`cone_union_eq_nonnegativeRay_union`. -/
theorem cone_union_recessionCone_eq_nonnegativeRay_union_recessionCone
    (C : Set E) (hC_convex : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    (cone[𝕜] C : Set E) ∪ 0⁺[𝕜] C = 𝕜≥0 • C ∪ 0⁺[𝕜] C := by
  simpa using cone_union_eq_nonnegativeRay_union
    (C := C) (S := 0⁺[𝕜] C) hC_convex hC_nonempty

end RayBridge

section PositiveRayBridge

variable {𝕜 : Type*} [Zero 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [Zero E] [SMulWithZero 𝕜 E]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)
local notation "𝕜>0" => Set.Ioi (0 : 𝕜)

/-- Algebraic owner bridge used by Theorem 9.6: in the nonempty case, adjoining any set that
contains the origin absorbs the inserted origin, so nonnegative-ray and positive-ray union
surfaces agree. -/
theorem nonnegativeRay_union_eq_positiveRay_union_of_zero_mem
    (C S : Set E) (hC_nonempty : C.Nonempty) (h0S : (0 : E) ∈ S) :
    𝕜≥0 • C ∪ S = 𝕜>0 • C ∪ S := by
  rw [← Set.insert_zero_smul_Ioi_eq_smul_Ici (S := C) hC_nonempty]
  rw [Set.insert_union]
  exact Set.insert_eq_of_mem (Or.inr h0S)

end PositiveRayBridge

section PositiveRayRecessionBridge

variable {𝕜 : Type*} [Zero 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddZeroClass E] [SMulWithZero 𝕜 E]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)
local notation "𝕜>0" => Set.Ioi (0 : 𝕜)

/-- Source-facing recession-cone specialization of
`nonnegativeRay_union_eq_positiveRay_union_of_zero_mem`. -/
theorem nonnegativeRay_union_recessionCone_eq_positiveRay_union_recessionCone
    (C : Set E) (hC_nonempty : C.Nonempty) :
    𝕜≥0 • C ∪ 0⁺[𝕜] C = 𝕜>0 • C ∪ 0⁺[𝕜] C := by
  have hzero : (0 : E) ∈ 0⁺[𝕜] C := by
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    simpa using hx
  simpa using nonnegativeRay_union_eq_positiveRay_union_of_zero_mem
    (C := C) (S := 0⁺[𝕜] C) hC_nonempty hzero

end PositiveRayRecessionBridge

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T1Space E]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)
local notation "𝕜>0" => Set.Ioi (0 : 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 9.6 identifies the closure of the convex cone generated by a nonempty
  closed convex set in a finite-dimensional topological vector space over `𝕜`, avoiding the origin.
- `core/canonical`: the generated cone is the bundled owner `cone[𝕜] C` (raw owner
  `PointedCone.hull 𝕜 C`), its ambient closure is the owner `PointedCone.closure`, and the
  recession object is the chapter owner `0⁺[𝕜] C`.
- `bridge/view`: Theorem 8.2 supplies the homogenization-closure description in one dimension
  higher; the nonnegative-ray formulation is the direct nonempty cone bridge, while the
  positive-ray formulation is a derived textbook restatement.

Domain-style sampling used here:
- `PointedCone.hull`;
- `cone[𝕜]`;
- `PointedCone.coe_closure`;
- `recessionCone_eq_asymptoticCone`;
- `PointedCone.cone_eq_nonnegativeRay_of_convex`;
- `PointedCone.cone_eq_insert_zero_positiveRay_of_convex`.

Primitive data vs derived API:
- primitive inputs: the set `C` and the hypotheses that it is nonempty, closed, convex, and
  avoids the origin;
- derived outputs: the closure formula for the generated pointed cone and two companion bridge
  restatements replacing that owner cone by nonnegative and positive dilate surfaces.

Layer target:
- owner theorem at `core/canonical`: ambient closure of `cone[𝕜] C` with
  `asymptoticCone 𝕜 C`;
- source-facing bridge theorem: the equivalent recession-cone statement with `0⁺[𝕜] C`;
- bridge theorems at the weaker algebraic layer (`RayBridge` above), so the nonnegative/positive
  ray rewrites do not carry finite-dimensional topological assumptions.
-/

/-- Canonical owner form of Theorem 9.6: if `C` is a nonempty closed convex subset of a
finite-dimensional topological vector space over `𝕜`, with `0 ∉ C`, then the closure of the
generated cone `cone[𝕜] C` is the union of that generated cone with the asymptotic cone
`asymptoticCone 𝕜 C`. -/
-- Proof sketch: homogenize `C` to the cone generated by `{(1, x) | x ∈ C}` in `𝕜 × E` and apply
-- Theorem 8.2 to describe the closure of that cone. Project to `E` by the linear map
-- `(λ, x) ↦ x`; Theorem 9.1 identifies the image of the closure with the closure of the image
-- because the homogenized closure has no nonzero kernel direction. The positive-height slice
-- projects to `cone[𝕜] C`, while the zero-height slice projects to `asymptoticCone 𝕜 C`.

private theorem snd_image_zeroSlice_asymptoticCone_eq (C : Set E) :
    LinearMap.snd 𝕜 𝕜 E '' ({0} ×ˢ asymptoticCone 𝕜 C) = asymptoticCone 𝕜 C := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨p, hp, hpy⟩
    rcases hp with ⟨hp0, hpasym⟩
    rcases p with ⟨a, x⟩
    simp at hp0
    have : x = y := by simpa using hpy
    simpa [this] using hpasym
  · intro hy
    refine ⟨(0, y), ?_, by simp⟩
    exact ⟨by simp, hy⟩

private theorem snd_recessionKernelTrivial_closure_cone_unitLift
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) :
    (LinearMap.snd 𝕜 𝕜 E).recessionKernelTrivial
      (((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) := by
  intro z hz
  have hz_rec : z ∈ 0⁺[𝕜] (((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) := hz.1
  have hz_ker : z ∈ (LinearMap.snd 𝕜 𝕜 E).ker := hz.2
  have hz2 : z.2 = 0 := by simpa using hz_ker
  have hz_mem_closure : z ∈ ((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E)) := by
    rw [Set.mem_recessionCone_iff] at hz_rec
    have hzero : (0 : 𝕜 × E) ∈ ((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E)) :=
      (cone[𝕜] (L[𝕜 | C])).closure.zero_mem
    simpa [one_smul, zero_add] using hz_rec 0 hzero 1 zero_le_one
  have hz_cases : z ∈ (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) ∪ ({0} ×ˢ asymptoticCone 𝕜 C) := by
    have hz_mem_closure' : z ∈ closure (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) := by
      simpa [PointedCone.coe_closure] using hz_mem_closure
    rw [closure_homogenizationCone_eq_union_zeroSlice_asymptoticCone
      (C := C) (hCconv := hC_convex) (hCclosed := hC_closed) (hCne := hC_nonempty)] at hz_mem_closure'
    exact hz_mem_closure'
  rcases hz_cases with hz_cone | hz_zero
  · have hz_homog : z = (0 : 𝕜 × E) ∨ z ∈ K[𝕜 | C] := by
      simpa [pointedConeHull_lift_eq_insert_homogenizationSet
        (C := C) (hC := hC_convex)] using hz_cone
    rcases hz_homog with rfl | hz_homog
    · simp
    · rcases (mem_homogenizationSet_iff 𝕜 C z).1 hz_homog with ⟨_, hz2_smul⟩
      by_cases hz1 : z.1 = 0
      · have hz_eq_zero : z = 0 := by
          ext <;> simp [hz1, hz2]
        simpa [hz_eq_zero]
      · exfalso
        rcases Set.mem_smul_set.mp hz2_smul with ⟨x, hxC, hxz⟩
        have hz1_ne_zero : (z.1 : 𝕜) ≠ 0 := hz1
        have hx_zero : x = 0 := by
          apply (smul_eq_zero.mp ?_).resolve_left hz1_ne_zero
          simpa [hz2] using hxz
        exact h0C (hx_zero ▸ hxC)
  · have hz1 : z.1 = 0 := by simpa using hz_zero.1
    have hz_eq_zero : z = 0 := by
      ext <;> simp [hz1, hz2]
    simpa [hz_eq_zero]

theorem closure_cone_eq_union_asymptoticCone
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) :
    ((cone[𝕜] C).closure : Set E) = (cone[𝕜] C : Set E) ∪ asymptoticCone 𝕜 C := by
  let sndMap : (𝕜 × E) →ₗ[𝕜] E := LinearMap.snd 𝕜 𝕜 E
  have hkernel_trivial :
      sndMap.recessionKernelTrivial
        (((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) :=
    snd_recessionKernelTrivial_closure_cone_unitLift
      (C := C) hC_nonempty hC_closed hC_convex h0C
  have hkernel_lineality :
      sndMap.recessionKernelLeLineality
        (((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) :=
    LinearMap.recessionKernelLeLineality_of_recessionKernelTrivial (A := sndMap)
      (C := ((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) hkernel_trivial
  have hclosure_image :
      closure (sndMap '' (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E))) =
        sndMap '' (((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) := by
    exact LinearMap.closure_image_eq_image_closure_of_recessionKernelLeLineality
      (A := sndMap)
      (C := (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)))
      (hC := (cone[𝕜] (L[𝕜 | C])).convex)
      (hkernel_lineality := hkernel_lineality)
  have hclosure_expanded :
      sndMap '' (((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) =
        (cone[𝕜] C : Set E) ∪ asymptoticCone 𝕜 C := by
    calc
      sndMap '' (((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) =
          sndMap '' closure (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) := by
        simp [PointedCone.coe_closure]
      _ = sndMap ''
            ((cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) ∪ ({0} ×ˢ asymptoticCone 𝕜 C)) := by
        rw [closure_homogenizationCone_eq_union_zeroSlice_asymptoticCone
          (C := C) (hCconv := hC_convex) (hCclosed := hC_closed) (hCne := hC_nonempty)]
      _ = sndMap '' (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E)) ∪
            sndMap '' ({0} ×ˢ asymptoticCone 𝕜 C) := by
        rw [Set.image_union]
      _ = (cone[𝕜] C : Set E) ∪ asymptoticCone 𝕜 C := by
        rw [PointedCone.snd_image_cone_unitLift_eq_cone (R := 𝕜) (E := E) (C := C),
          snd_image_zeroSlice_asymptoticCone_eq (C := C)]
  calc
    ((cone[𝕜] C).closure : Set E) = closure (cone[𝕜] C : Set E) := by
      simpa [PointedCone.coe_closure]
    _ = closure (sndMap '' (cone[𝕜] (L[𝕜 | C]) : Set (𝕜 × E))) := by
      rw [PointedCone.snd_image_cone_unitLift_eq_cone (R := 𝕜) (E := E) (C := C)]
    _ = sndMap '' (((cone[𝕜] (L[𝕜 | C])).closure : Set (𝕜 × E))) := hclosure_image
    _ = (cone[𝕜] C : Set E) ∪ asymptoticCone 𝕜 C := hclosure_expanded

/-- Theorem 9.6 in source-facing recession-cone form: if `C` is a nonempty closed convex subset
of a finite-dimensional topological vector space over `𝕜`, with `0 ∉ C`, then the closure of the
generated cone `cone[𝕜] C` is the union of that generated cone with the recession cone `0⁺[𝕜] C`.
-/
theorem closure_cone_eq_union_recessionCone
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) :
    ((cone[𝕜] C).closure : Set E) = (cone[𝕜] C : Set E) ∪ 0⁺[𝕜] C := by
  simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using
    (closure_cone_eq_union_asymptoticCone C hC_nonempty hC_closed hC_convex h0C)

/-- Nonempty canonical decomposition of Theorem 9.6: the closure of the generated pointed cone
is the union of the nonnegative ray through `C` with the asymptotic cone of `C`. -/
-- Proof sketch: combine `closure_cone_eq_union_asymptoticCone` with the owner-level nonempty
-- cone description `PointedCone.cone_eq_nonnegativeRay_of_convex`.
theorem closure_cone_eq_nonnegativeRay_union_asymptoticCone
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) :
    ((cone[𝕜] C).closure : Set E) = 𝕜≥0 • C ∪ asymptoticCone 𝕜 C := by
  calc
    ((cone[𝕜] C).closure : Set E) = (cone[𝕜] C : Set E) ∪ asymptoticCone 𝕜 C := by
      rw [closure_cone_eq_union_asymptoticCone C hC_nonempty hC_closed hC_convex h0C]
    _ = 𝕜≥0 • C ∪ asymptoticCone 𝕜 C := by
      simpa using
        cone_union_eq_nonnegativeRay_union
          (C := C) (S := asymptoticCone 𝕜 C) hC_convex hC_nonempty

/-- Source-facing nonempty decomposition of Theorem 9.6: the closure of the generated pointed cone
is the union of the nonnegative ray through `C` with the recession cone of `C`. -/
theorem closure_cone_eq_nonnegativeRay_union_recessionCone
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) :
    ((cone[𝕜] C).closure : Set E) = 𝕜≥0 • C ∪ 0⁺[𝕜] C := by
  simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using
    closure_cone_eq_nonnegativeRay_union_asymptoticCone
      C hC_nonempty hC_closed hC_convex h0C

/-- Companion bridge view of Theorem 9.6: the closure of the generated pointed cone is the union
of the positive ray through `C` with the asymptotic cone of `C`. -/
-- Proof sketch: rewrite the nonnegative-ray formula with
-- `Set.insert_zero_smul_Ioi_eq_smul_Ici`; then absorb the inserted origin using
-- `0 ∈ asymptoticCone 𝕜 C`.
theorem closure_cone_eq_positiveRay_union_asymptoticCone
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) :
    ((cone[𝕜] C).closure : Set E) = 𝕜>0 • C ∪ asymptoticCone 𝕜 C := by
  have hzero : (0 : E) ∈ asymptoticCone 𝕜 C := by
    exact (zero_mem_asymptoticCone (k := 𝕜) (s := C)).2 hC_nonempty
  calc
    ((cone[𝕜] C).closure : Set E) = 𝕜≥0 • C ∪ asymptoticCone 𝕜 C := by
      exact
        closure_cone_eq_nonnegativeRay_union_asymptoticCone
          C hC_nonempty hC_closed hC_convex h0C
    _ = 𝕜>0 • C ∪ asymptoticCone 𝕜 C := by
      simpa using nonnegativeRay_union_eq_positiveRay_union_of_zero_mem
        (C := C) (S := asymptoticCone 𝕜 C) hC_nonempty hzero

/-- Source-facing companion view of Theorem 9.6: the closure of the generated pointed cone is the
union of the positive ray through `C` with the recession cone of `C`. -/
theorem closure_cone_eq_positiveRay_union_recessionCone
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    (h0C : (0 : E) ∉ C) :
    ((cone[𝕜] C).closure : Set E) = 𝕜>0 • C ∪ 0⁺[𝕜] C := by
  simpa [hC_convex.recessionCone_eq_asymptoticCone hC_closed hC_nonempty] using
    closure_cone_eq_positiveRay_union_asymptoticCone
      C hC_nonempty hC_closed hC_convex h0C

end PointedCone

end

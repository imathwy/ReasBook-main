import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_11_4_1 (from Chap03) -/
section

open scoped Pointwise Rockafellar
open Set

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E Y 𝕜]
/-!
Source/core/bridge triage:

- `core/canonical`: the primitive Chapter 11 owner bridge is
  `exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub`.
  At this layer, the essential extra input is closedness of `C1 - C2`.
- `source-facing`: Corollary 11.4.1 adds the textbook common-recession hypothesis as a sufficient
  condition implying that closedness.
- `bridge/view`: this file keeps both layers explicitly:
  1) a primitive owner theorem from `Disjoint + IsClosed (C1 - C2)`, then
  2) a source-facing corollary deriving `IsClosed (C1 - C2)` by rewriting as `C1 + (-C2)` and
     using the Chapter 2 closed-sum owner.
-/

/-- Primitive separation bridge on the Chapter 11 owner layer: for nonempty convex sets, disjoint
sets with closed difference admit a strongly separating hyperplane. -/
theorem exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC1_convex : Convex 𝕜 C1)
    (hC2_nonempty : C2.Nonempty) (hC2_convex : Convex 𝕜 C2) (hdisj : Disjoint C1 C2)
    (hsub_closed : IsClosed (C1 - C2)) :
    ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2 := by
  have hzero_notMem_sub : (0 : E) ∉ C1 - C2 := by
    intro h0
    rcases Set.mem_sub.mp h0 with ⟨x1, hx1, x2, hx2, hsub⟩
    exact hdisj.le_bot ⟨hx1, by simpa [sub_eq_zero.mp hsub] using hx2⟩
  have hsep_iff :
      (∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2) ↔
        (0 : E) ∉ closure (C1 - C2) :=
    exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub
      hC1_convex hC1_nonempty hC2_convex hC2_nonempty
  exact hsep_iff.mpr (by simpa [hsub_closed.closure_eq] using hzero_notMem_sub)

end

section

open scoped Pointwise Rockafellar
open Set

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [HasLinearPairing E Y 𝕜]

/-- Corollary 11.4.1: if `C1` and `C2` are nonempty disjoint closed convex sets and
`C1 ⟂₀⁺[𝕜] (-C2)`, then some hyperplane strongly separates `C1` and `C2`.
This owner condition is equivalent to saying that every common recession direction of
`C1` and `C2` is zero. -/
-- Proof sketch: derive `IsClosed (C1 - C2)` from `C1 ⟂₀⁺[𝕜] (-C2)` by rewriting
-- `C1 - C2` as `C1 + (-C2)` and applying the Chapter 2 closed-sum owner. Then invoke the
-- primitive separation bridge
-- `exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub`.
theorem
    exists_hyperplane_strongly_separating_of_disjoint_convex_of_no_common_recession_directions
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC1_closed : IsClosed C1)
    (hC1_convex : Convex 𝕜 C1) (hC2_nonempty : C2.Nonempty) (hC2_closed : IsClosed C2)
    (hC2_convex : Convex 𝕜 C2) (hdisj : Disjoint C1 C2)
    (hno_common : C1 ⟂₀⁺[𝕜] (-C2)) :
    ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2 := by
  have hclosed_sub : IsClosed (C1 - C2) := by
    have hneg_closed : IsClosed (-C2) := by
      simpa [Set.mem_neg] using hC2_closed.preimage continuous_neg
    have hneg_convex : Convex 𝕜 (-C2) := by
      simpa using hC2_convex.neg
    have hclosed_add : IsClosed (C1 + (-C2)) :=
      hno_common.isClosed_add hC1_closed hneg_closed hC1_convex hneg_convex
    simpa [sub_eq_add_neg] using hclosed_add
  exact
    exists_hyperplane_strongly_separating_of_disjoint_convex_of_isClosed_sub
      hC1_nonempty hC1_convex hC2_nonempty hC2_convex hdisj hclosed_sub

end

/-! ### Corollary_11_4_2 (from Chap03) -/
section

open scoped Pointwise Rockafellar
open Bornology Set

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormSMulClass ℤ 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
/-!
Source/core/bridge triage:

- `source-facing`: Corollary 11.4.2 says that two nonempty convex sets with disjoint closures
  admit a strongly separating hyperplane as soon as either set is bounded.
- `core/canonical`: the owner abstractions already present in the chapter are
  `AffineSubspace.StronglySeparates`, the closure operator `closure`, the bornological boundedness
  predicate `Bornology.IsBounded`, and the upstream Chapter 11 owner-side bridge
  `exists_hyperplane_strongly_separating_of_disjoint_convex_of_no_common_recession_
  directions`.
- `bridge/view`: the closure-disjoint hypothesis is stated directly as
  `Disjoint (closure C1) (closure C2)`, and the textbook boundedness hypothesis is stated by
  `IsBounded C1 ∨ IsBounded C2`.

Domain-style sampling used here:
- `AffineSubspace.StronglySeparates`;
- `AffineSubspace.StronglySeparates.mono`;
- `Set.mem_recessionCone_iff`;
- `exists_hyperplane_strongly_separating_of_disjoint_convex_of_no_common_recession_
  directions`;

Primitive data vs derived API:
- primitive inputs: the two sets, their nonemptiness and convexity, disjointness of their
  closures, and boundedness of at least one of them;
- derived output: existence of a hyperplane strongly separating the original sets. The intermediate
  no-common-recession condition on the closures is itself derived from the boundedness owner
  theorem and should not be stored as extra primitive data here.

Layer target: `source-facing`, using the existing chapter owner
`AffineSubspace.StronglySeparates` rather than a new wrapper around separation data.
-/

omit [OrderTopology 𝕜] [FiniteDimensional 𝕜 E] in
private theorem eq_zero_of_mem_recessionCone_of_isBounded
    {C : Set E} (hC_nonempty : C.Nonempty) (hC_bounded : IsBounded C) {y : E}
    (hy : y ∈ 0⁺[𝕜]C) : y = 0 := by
  rcases hC_nonempty with ⟨x0, hx0⟩
  obtain ⟨R, hR⟩ := hC_bounded.subset_closedBall (0 : E)
  have hmem : ∀ n : ℕ, x0 + (n : 𝕜) • y ∈ C := by
    intro n
    exact (Set.mem_recessionCone_iff.mp hy) x0 hx0 (n : 𝕜) (Nat.cast_nonneg n)
  have hnorm : ∀ n : ℕ, ‖x0 + (n : 𝕜) • y‖ ≤ R := by
    intro n
    have hxR : x0 + (n : 𝕜) • y ∈ Metric.closedBall (0 : E) R := hR (hmem n)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
  by_contra hy0
  have hy_norm : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖x0‖) / ‖y‖)
  have hny : ‖(n : 𝕜)‖ * ‖y‖ ≤ R + ‖x0‖ := by
    calc
      ‖(n : 𝕜)‖ * ‖y‖ = ‖(n : 𝕜) • y‖ := by
        simpa using (norm_smul (n : 𝕜) y).symm
      _ = ‖(x0 + (n : 𝕜) • y) - x0‖ := by simp
      _ ≤ ‖x0 + (n : 𝕜) • y‖ + ‖x0‖ := norm_sub_le _ _
      _ ≤ R + ‖x0‖ := add_le_add (hnorm n) le_rfl
  have hgt' : R + ‖x0‖ < (n : ℝ) * ‖y‖ := (div_lt_iff₀ hy_norm).mp hn
  have hgt : R + ‖x0‖ < ‖(n : 𝕜)‖ * ‖y‖ := by
    calc
      R + ‖x0‖ < (n : ℝ) * ‖y‖ := hgt'
      _ = ‖(n : 𝕜)‖ * ‖y‖ := by simp [norm_natCast]
  exact not_lt_of_ge hny hgt

omit [OrderTopology 𝕜] [FiniteDimensional 𝕜 E] in
private theorem no_opposite_recession_direction_of_neg_of_either_closure_isBounded
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC2_nonempty : C2.Nonempty)
    (hclosure_bounded : IsBounded (closure C1) ∨ IsBounded (closure C2)) :
    (closure C1) ⟂₀⁺[𝕜] (-closure C2 : Set E) := by
  change (∀ {y : E}, y ∈ 0⁺[𝕜] (closure C1) → -y ∈ 0⁺[𝕜] (-closure C2 : Set E) → y = 0)
  intro y hy1 hy2
  have hy2' : y ∈ 0⁺[𝕜] (closure C2) := by
    simpa using (Set.neg_mem_recessionCone_neg_iff).1 hy2
  rcases hclosure_bounded with hclosure_C1_bounded | hclosure_C2_bounded
  · exact
      eq_zero_of_mem_recessionCone_of_isBounded
        hC1_nonempty.closure hclosure_C1_bounded hy1
  · exact
      eq_zero_of_mem_recessionCone_of_isBounded
        hC2_nonempty.closure hclosure_C2_bounded hy2'

section

variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜]

/-- Canonical closure-bounded owner form for Corollary 11.4.2: if nonempty convex sets have
disjoint closures and one closure is bounded, then some hyperplane strongly separates the
original sets. -/
theorem
    exists_hyperplane_strongly_separating_of_disjoint_closures_of_convex_of_either_closure_isBounded
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC1_convex : Convex 𝕜 C1)
    (hC2_nonempty : C2.Nonempty) (hC2_convex : Convex 𝕜 C2)
    (hclosure_disjoint : Disjoint (closure C1) (closure C2))
    (hclosure_bounded : IsBounded (closure C1) ∨ IsBounded (closure C2)) :
    ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2 := by
  have hsep_closure :
      ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] (closure C1) and (closure C2) :=
      exists_hyperplane_strongly_separating_of_disjoint_convex_of_no_common_recession_directions
        hC1_nonempty.closure isClosed_closure hC1_convex.closure
        hC2_nonempty.closure isClosed_closure hC2_convex.closure
        hclosure_disjoint
        (no_opposite_recession_direction_of_neg_of_either_closure_isBounded
          hC1_nonempty hC2_nonempty hclosure_bounded)
  rcases hsep_closure with ⟨H, hH⟩
  exact ⟨H, hH.mono subset_closure subset_closure⟩

/-- Corollary 11.4.2, source-facing boundedness form: if `C1` and `C2` are nonempty convex sets
with disjoint closures, and either `C1` or `C2` is bounded, then some hyperplane strongly
separates `C1` and `C2`. -/
theorem exists_hyperplane_strongly_separating_of_disjoint_closures_of_convex_of_either_isBounded
    {C1 C2 : Set E} (hC1_nonempty : C1.Nonempty) (hC1_convex : Convex 𝕜 C1)
    (hC2_nonempty : C2.Nonempty) (hC2_convex : Convex 𝕜 C2)
    (hclosure_disjoint : Disjoint (closure C1) (closure C2))
    (hbounded : IsBounded C1 ∨ IsBounded C2) :
    ∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2 := by
  have hclosure_bounded : IsBounded (closure C1) ∨ IsBounded (closure C2) := by
    rcases hbounded with hC1_bounded | hC2_bounded
    · exact Or.inl hC1_bounded.closure
    · exact Or.inr hC2_bounded.closure
  exact
    exists_hyperplane_strongly_separating_of_disjoint_closures_of_convex_of_either_closure_isBounded
    hC1_nonempty hC1_convex hC2_nonempty hC2_convex hclosure_disjoint hclosure_bounded

end

end

/-! ### Theorem_11_4 (from Chap03) -/
section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} {E : Type*} {Y : Type*}
variable [NormedField 𝕜] [LinearOrder 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
variable {C1 C2 : Set E}

/-- Theorem 11.4 on the chapter's finite-dimensional normed pairing layer: for nonempty convex
sets `C1` and `C2`, there exists a hyperplane strongly separating them (in pairing codomain `Y`)
if and only if the origin does not belong to `closure (C1 - C2)`.

This file keeps the ambient closure formulation as the primary theorem surface, because the
criterion is about the ambient difference set `C1 - C2`; the positive-distance form is then a thin
restatement via `Metric.infDist_pos_iff_notMem_closure`. -/
-- Proof sketch: strong separation means that for some `ε > 0`, suitable closed-ball thickenings
-- of `C1` and `C2` lie in opposite open half-spaces. By the preceding separation criterion for
-- convex thickenings, this is equivalent to asking that `0` lie outside the pointwise
-- difference of those thickenings for some `ε > 0`. That difference is a `2 ε`-ball thickening
-- of `C1 - C2`, so the condition is exactly `0 ∉ closure (C1 - C2)`.
theorem exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub
    (hC1_conv : Convex 𝕜 C1) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2) ↔
      0 ∉ closure (C1 - C2) := sorry

/-- Theorem 11.4 in distance-to-set form: strong separation is equivalent to
`0 < Metric.infDist 0 (C1 - C2)`. -/
theorem exists_hyperplane_strongly_separating_iff_infDist_pos_sub
    (hC1_conv : Convex 𝕜 C1) (hC1_nonempty : C1.Nonempty)
    (hC2_conv : Convex 𝕜 C2) (hC2_nonempty : C2.Nonempty) :
    (∃ H : AffineSubspace 𝕜 E, H stronglySeparates[Y] C1 and C2) ↔
      0 < Metric.infDist 0 (C1 - C2) := by
  have hsub_nonempty : (C1 - C2).Nonempty := hC1_nonempty.sub hC2_nonempty
  rw [exists_hyperplane_strongly_separating_iff_zero_notMem_closure_sub
    hC1_conv hC1_nonempty hC2_conv hC2_nonempty]
  simpa using Metric.infDist_pos_iff_notMem_closure hsub_nonempty

end

import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_6_27_5 (from Chap06) -/
noncomputable section

open scoped Pointwise Rockafellar

universe u v

section

variable {𝕜 : Type v} [CommRing 𝕜] [Preorder 𝕜]
variable [AddLeftMono 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 27.5 adds the polyhedral qualification branch to the constrained
  first-order optimality criterion for minimizing a convex extended-valued function on a convex
  set: besides the earlier qualification `ri(dom h) ∩ ri[𝕜](C) ≠ ∅`, one may also assume that `C`
  is polyhedral and `ri(dom h) ∩ C ≠ ∅`.
- `core/canonical`: the owner abstractions already present in the chapter are `IsMinOn`,
  `subdifferentialAt`, `N[𝕜](· | ·)`, `riDom(·)`, and `Set.IsPolyhedral`.
- `bridge/view`: the unconditional sufficiency clause and the `riDom[𝕜](h) ∩ ri[𝕜](C)` necessity
  clause
  already live upstream in `Theorem_6_27_4`, so this file keeps the genuinely new polyhedral
  branch as the primary declaration and exposes the source's disjunctive statement only as a thin
  wrapper over the two owner-level qualification theorems.

Domain-style sampling used here:
- `isMinOn_of_exists_subgradient_neg_mem_normalCone`;
- `isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_intrinsicInterior`;
- `Set.IsPolyhedral.convex`;
- `N[𝕜](· | ·)`;

Primitive data vs derived API:
- primitive inputs: the convex function `h` with the primitive anti-`⊥` hypothesis
  `∀ y, h y ≠ ⊥`, the polyhedral constraint set `C`, the point `x`, and the source qualification
  on `riDom[𝕜](h)` relative to `C`;
- derived API: the minimizer owner `IsMinOn h C x` and the normal-cone/subgradient certificate
  `∃ xStar, xStar ∈ (∂ h at x) ∧ -xStar ∈ N[𝕜](x | C)`.

Layer target: `source-facing`, stated directly on the chapter owner abstractions rather than via a
parallel local KKT-point package.
-/

/- The unconditional sufficiency clause of Theorem 27.4 is already the chapter owner theorem
`isMinOn_of_exists_subgradient_neg_mem_normalCone`. -/
recall isMinOn_of_exists_subgradient_neg_mem_normalCone

/-- Core owner-level bridge: if the subdifferential of `δ_C + h` at `x` decomposes as the
Minkowski sum of the indicator and objective subdifferentials, then the normal-cone subgradient
condition is equivalent to constrained minimality. This theorem is pairing-parametric and keeps
the polyhedral qualification as a downstream source-facing wrapper. -/
theorem isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_subdifferentialAt_indicator_add_eq
    {Y : Type (max u v)} [AddCommGroup Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E}
    (hneBot : ∀ y, h y ≠ ⊥)
    (hsum_sub :
      subdifferentialAt (fun y ↦ δ[𝕜](y | C) + h y) x Y =
        subdifferentialAt (δ[𝕜](· | C)) x Y + subdifferentialAt h x Y) :
    (x ∈ C ∧ IsMinOn h C x) ↔
      ∃ xStar : Y,
        xStar ∈ (∂[Y]h(x)) ∧ -xStar ∈ N[𝕜](x | C) := by
  constructor
  · intro hxmin
    have hsum_min : x ∈ minimumSet (fun y ↦ δ[𝕜](y | C) + h y) := by
      rw [mem_minimumSet_iff]
      intro y
      by_cases hyC : y ∈ C
      · have hxy : h x ≤ h y := (isMinOn_iff.mp hxmin.2) y hyC
        simpa [hxmin.1, hyC, add_comm, add_left_comm, add_assoc] using hxy
      · have hy_top : (δ[𝕜](y | C) : WithTopBot 𝕜) + h y = ⊤ := by
          calc
            (δ[𝕜](y | C) : WithTopBot 𝕜) + h y = ⊤ + h y := by simp [hyC]
            _ = ⊤ := WithTopBot.top_add_of_ne_bot (hneBot y)
        calc
          (δ[𝕜](x | C) : WithTopBot 𝕜) + h x = h x := by simp [hxmin.1]
          _ ≤ ⊤ := le_top
          _ = (δ[𝕜](y | C) : WithTopBot 𝕜) + h y := hy_top.symm
    have hzero_sub : (0 : Y) ∈ subdifferentialAt (fun y ↦ δ[𝕜](y | C) + h y) x Y := by
      exact
        (mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing
          (Y := Y) (f := fun y ↦ δ[𝕜](y | C) + h y) (x := x)).1 hsum_min
    rw [hsum_sub] at hzero_sub
    rcases (Set.mem_add.mp hzero_sub) with ⟨u, hu, v, hv, huv0⟩
    refine ⟨v, hv, ?_⟩
    have hu_normal : u ∈ N[𝕜, Y](x | C) := by
      exact
        (subdifferentialAt_indicatorFunction_eq_normalCone
          (𝕜 := 𝕜) (N := Y) C x) ▸ hu
    have hu_eq : u = -v := eq_neg_of_add_eq_zero_left huv0
    exact hu_eq ▸ hu_normal
  · intro hopt
    simpa using
      (isMinOn_of_exists_subgradient_neg_mem_normalCone
        (N := Y) (h := h) (C := C) (x := x) hopt)

end

section

variable {𝕜 : Type v} [ConditionallyCompleteLinearOrder 𝕜] [NormedField 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddLeftMono 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

recall _root_.subdifferentialAt_sum_eq_sum_subdifferentialAt_of_polyhedralSubset_mixedDomain

/-- Theorem 27.5, polyhedral qualification branch: for a convex function with no `⊥` values on a
polyhedral set `C`, the normal-cone subgradient condition is necessary as well as sufficient at a
minimizer whenever `ri(dom h)` meets `C`. The qualifier is exposed on the canonical owner surface
`C.IsPolyhedral 𝕜`, and convexity of `C` is derived from polyhedrality via
`Set.IsPolyhedral.convex`. This is the genuinely new source-facing content beyond
`Theorem_6_27_4`. -/
theorem isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_polyhedral
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E}
    (hneBot : ∀ y, h y ≠ ⊥) (hh_convex : h.IsConvex 𝕜) (hC_poly : C.IsPolyhedral 𝕜)
    (hqual : (riDom[𝕜](h) ∩ C).Nonempty) :
    (x ∈ C ∧ IsMinOn h C x) ↔
      ∃ xStar,
        xStar ∈ (∂ h at x) ∧ -xStar ∈ N[𝕜](x | C) := by
  classical
  let f : Fin 2 → E → WithTopBot 𝕜 := Fin.cases (δ[𝕜](· | C)) (fun _ : Fin 1 => h)
  have hh_proper : h.IsProper := by
    rcases hqual with ⟨xq, hxq_ri, _⟩
    refine (Function.isProper_iff (f := h)).2 ?_
    refine ⟨⟨xq, intrinsicInterior_subset hxq_ri⟩, hneBot⟩
  have h_ind_proper : (δ[𝕜](· | C) : E → WithTopBot 𝕜).IsProper := by
    rcases hqual with ⟨xq, _, hxqC⟩
    refine (Function.isProper_iff (f := (δ[𝕜](· | C) : E → WithTopBot 𝕜))).2 ?_
    refine ⟨?_, ?_⟩
    · refine ⟨xq, ?_⟩
      rw [mem_effectiveDomain]
      exact (indicator_lt_top_iff_mem (α := 𝕜) (C := C) (x := xq)).2 hxqC
    · intro y
      by_cases hy : y ∈ C
      · simp [hy]
      · simp [hy]
  have hf_suffixConvex : ∀ i : Fin 2, i ∉ ({0} : Set (Fin 2)) → (f i).IsConvex 𝕜 := by
    intro i hi
    fin_cases i
    · exact False.elim (hi (by simp))
    · simpa [f] using hh_convex
  have hf_proper : ∀ i : Fin 2, (f i).IsProper := by
    intro i
    fin_cases i
    · simpa [f] using h_ind_proper
    · simpa [f] using hh_proper
  have hpoly : ∀ i : Fin 2, i ∈ ({0} : Set (Fin 2)) → (f i).HasPolyhedralEpigraph := by
    intro i hi
    fin_cases i
    · exact (Function.HasPolyhedralEpigraph.indicator_iff_isPolyhedral
        (𝕜 := 𝕜) (E := E) C).2 hC_poly
    · simp at hi
  have hdom :
      ∃ y : E, (∀ i : Fin 2, i ∈ ({0} : Set (Fin 2)) → y ∈ dom(f i)) ∧
        ∀ i : Fin 2, i ∉ ({0} : Set (Fin 2)) → y ∈ riDom[𝕜](f i) := by
    rcases hqual with ⟨xq, hxq_ri, hxqC⟩
    refine ⟨xq, ?_, ?_⟩
    · intro i hi
      fin_cases i
      · rw [mem_effectiveDomain]
        simpa [f] using (indicator_lt_top_iff_mem (α := 𝕜) (C := C) (x := xq)).2 hxqC
      · simp at hi
    · intro i hi
      fin_cases i
      · exact False.elim (hi (by simp))
      · simpa [f] using hxq_ri
  have hsum_sub :
      subdifferentialAt (∑ i, f i) x = ∑ i, subdifferentialAt (f i) x :=
    subdifferentialAt_sum_eq_sum_subdifferentialAt_of_polyhedralSubset_mixedDomain
      f ({0} : Set (Fin 2)) hf_suffixConvex hf_proper hpoly hdom x
  have hsum_sub' :
      subdifferentialAt (fun y ↦ δ[𝕜](y | C) + h y) x (StrongDual 𝕜 E) =
        subdifferentialAt (δ[𝕜](· | C)) x (StrongDual 𝕜 E) +
          subdifferentialAt h x (StrongDual 𝕜 E) := by
    simpa [Fin.sum_univ_two, f] using hsum_sub
  change (x ∈ C ∧ IsMinOn h C x) ↔
      ∃ xStar : StrongDual 𝕜 E,
        xStar ∈ (∂[StrongDual 𝕜 E]h(x)) ∧ -xStar ∈ N[𝕜](x | C)
  exact
    (isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_subdifferentialAt_indicator_add_eq
      (𝕜 := 𝕜) (E := E) (Y := StrongDual 𝕜 E)
      (h := h) (C := C) (x := x) hneBot hsum_sub')

/-- Theorem 27.5, combined source-facing form: the constrained optimality certificate of
`Theorem_6_27_4` remains equivalent to constrained minimality under either of the two textbook
qualification branches, namely the convex-set hypothesis
`Convex 𝕜 C ∧ (ri(dom h) ∩ ri[𝕜](C)).Nonempty` or the polyhedral alternative
`C.IsPolyhedral 𝕜 ∧ (riDom[𝕜](h) ∩ C).Nonempty`, stated directly on the canonical polyhedral owner
surface. -/
theorem isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_intrinsicInterior_or_polyhedral
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E}
    (hneBot : ∀ y, h y ≠ ⊥) (hh_convex : h.IsConvex 𝕜)
    (hqual : Convex 𝕜 C ∧ (riDom[𝕜](h) ∩ ri[𝕜](C)).Nonempty ∨
      (C.IsPolyhedral 𝕜) ∧ (riDom[𝕜](h) ∩ C).Nonempty) :
    (x ∈ C ∧ IsMinOn h C x) ↔
      ∃ xStar,
        xStar ∈ (∂ h at x) ∧ -xStar ∈ N[𝕜](x | C) := by
  rcases hqual with ⟨hC_convex, hri⟩ | hpoly
  · exact
      isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_intrinsicInterior
        hneBot hh_convex hC_convex hri
  · rcases hpoly with ⟨hC_poly, hri⟩
    exact
      isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_polyhedral
        hneBot hh_convex hC_poly hri

end

/-! ### Corollary_6_27_6 (from Chap06) -/
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [AddCommGroup 𝕜] [PartialOrder 𝕜]
variable {E : Type u} {Y : Type*} [HasPairing E Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.27.6 says that once a weakly separating nonvertical hyperplane for
  `epi h` and `C₂ C α` is chosen through the feasible contact point `(xBar, α)`, its dual normal
  vector is both a subgradient of `h` at `xBar` and a normal vector to `C` at `xBar`.
- `core/canonical`: the owner abstractions already present upstream are the epigraph owner
  `epi h`, the Chapter 6 auxiliary-set owner `C₂ C α`, the Chapter 23 subdifferential owner
  `_root_.subdifferentialAt`, the Chapter 1 normal-cone owner `N[𝕜](· | ·)`, and the Chapter 6
  separator theorem
  `weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone`,
  which already fixes the separator height canonically as `α - ⟪xBar, xStar⟫ₚ`.
- `bridge/view`: the canonical-height formulation is the specialization obtained by rewriting an
  arbitrary source separator height `β` at the contact point `(xBar, α)`.

Domain-style sampling used here:
- `mem_epi_iff` / `epi h`;
- `mem_C₂_iff` for `C₂ C α`;
- `_root_.mem_subdifferentialAt_pairing` and `mem_normalCone_iff_sub_nonpos`;
- `weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone`.

Primitive data vs derived API:
- primitive inputs: a feasible contact point `xBar ∈ C` with `h xBar = α`, together with the two
  weak-separation inequalities for a separator dual normal `xStar`;
- derived API: the canonical separator height `α - ⟪xBar, xStar⟫ₚ`, its agreement with an
  arbitrary source height `β`, subgradient membership of `xStar`, and normal-cone membership of
  `-xStar`.

Layer target:
- `source-facing`: the main corollary keeps the textbook arbitrary separator height `β`;
- `bridge/view`: a thin companion specializes that source-facing theorem to the canonical height
  `α - ⟪xBar, xStar⟫ₚ`.

The closedness, convexity, attainment, and qualification hypotheses from the preceding theorem are
intentionally not repeated here, since the corollary's conclusions depend only on the contact-point
equalities and the separator inequalities themselves.
-/

-- Proof sketch: the point `(xBar, α)` belongs both to `epi h` and to `C₂ C α`, so the two weak
-- separation inequalities sandwich `α` between `⟪xBar, xStar⟫ₚ + β` and itself. Rearranging gives
-- the canonical separator height `α - ⟪xBar, xStar⟫ₚ`.
/-- A weakly separating source height agrees with the canonical height
`α - ⟪xBar, xStar⟫ₚ` at the feasible contact point `(xBar, α)`. -/
theorem separatorHeight_eq_canonical_of_weaklySeparating_epi_and_C₂
    {h : E → WithBotTop 𝕜} {C : Set E} {α β : 𝕜} {xBar : E} {xStar : Y}
    (hxBar_mem : xBar ∈ C) (hxBar_value : h xBar = α)
    (hsep_epi : ∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + β ≤ μ)
    (hsep_aux : ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + β) :
    β = α - ⟪xBar, xStar⟫ₚ := by
  have hle_epi : ⟪xBar, xStar⟫ₚ + β ≤ α :=
    hsep_epi xBar α <| by simp [hxBar_value]
  have hle_aux : α ≤ ⟪xBar, xStar⟫ₚ + β :=
    hsep_aux xBar α <| by simp [hxBar_mem]
  have hEq : (⟪xBar, xStar⟫ₚ : 𝕜) + β = α := le_antisymm hle_epi hle_aux
  exact (eq_sub_iff_add_eq').2 hEq

end

section

variable {𝕜 : Type v}
variable [CommRing 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜] [AddLeftMono 𝕜] [NoBotOrder 𝕜]
variable {E : Type u}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {Y : Type (max u v)} [AddCommGroup Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

/-!
Ambient-layer note for the subgradient/normal-cone conclusions:

- the separator-height theorem above is purely pairing-level and needs no normed-space structure;
- the theorems below conclude membership in `_root_.subdifferentialAt` and `N[𝕜](· | ·)`;
- in this chapter, `_root_.subdifferentialAt` is the ordered-scalar owner
  `(E → WithBotTop 𝕜) → E → Set Y` parameterized by
  `[AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]`.

Hence these ambient assumptions are owner-surface requirements of the stated conclusions, not
proof-local artifacts.
-/

-- Proof sketch: use the epigraph half of the canonical weak-separation inequality to rewrite the
-- support bound into the defining inequality of `_root_.subdifferentialAt h xBar`. For `x ∈ C`,
-- use the auxiliary-set half with height `α` and conclude `-xStar ∈ N[𝕜](xBar | C)` via
-- `mem_normalCone_iff_sub_nonpos`.
private theorem mem_subdifferentialAt_and_neg_mem_normalCone_of_canonicalSeparatorHeight
    {h : E → WithBotTop 𝕜} {C : Set E} {α : 𝕜} {xBar : E} {xStar : Y}
    (hxBar_mem : xBar ∈ C) (hxBar_value : h xBar = α)
    (hsep_epi :
      ∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ μ)
    (hsep_aux :
      ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ)) :
    xStar ∈ (∂[Y]h(xBar)) ∧ -xStar ∈ N[𝕜](xBar | C) := by
  refine ⟨?_, ?_⟩
  · rw [mem_subdifferentialAt_pairing]
    intro z
    change h xBar + ((⟪z - xBar, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ h z
    have hz_sep :
        ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithBotTop 𝕜) ≤ h z := by
      by_cases hz_bot : h z = (⊥ : WithBotTop 𝕜)
      · exfalso
        have hz_sep_all :
            ∀ μ : 𝕜, (⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) ≤ μ := by
          intro μ
          exact hsep_epi z μ <| by simp [hz_bot]
        rcases NoBotOrder.exists_not_ge
            (a := (⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜)) with ⟨μ, hμ⟩
        exact hμ (hz_sep_all μ)
      · by_cases hz_top : h z = (⊤ : WithBotTop 𝕜)
        · simp [hz_top]
        · rcases (WithBotTop.canLift_iff_ne_top_ne_bot).2 ⟨hz_top, hz_bot⟩ with ⟨r, hr⟩
          have hreal : ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ r :=
            hsep_epi z r <| by simp [hr]
          exact hr ▸ WithBotTop.coe_le_coe.mpr hreal
    have hz_real :
        α + (⟪z - xBar, xStar⟫ₚ : 𝕜) =
          ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
      calc
        α + (⟪z - xBar, xStar⟫ₚ : 𝕜)
            = α + ((⟪z, xStar⟫ₚ : 𝕜) - (⟪xBar, xStar⟫ₚ : 𝕜)) := by
                simp [sub_eq_add_neg, map_add, map_neg]
        _ = ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by ring
    have hz_eq :
        h xBar + ((⟪z - xBar, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) =
          ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithBotTop 𝕜) := by
      rw [hxBar_value, ← WithBotTop.coe_add]
      exact congrArg (fun t : 𝕜 ↦ ((t : 𝕜) : WithBotTop 𝕜)) hz_real
    rw [hz_eq]
    exact hz_sep
  · rw [mem_normalCone_iff_sub_nonpos]
    refine ⟨hxBar_mem, ?_⟩
    intro z hzC
    have hz_sep : α ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) :=
      hsep_aux z α <| by simp [hzC]
    have hbase : (⟪xBar, xStar⟫ₚ : 𝕜) - (⟪z, xStar⟫ₚ : 𝕜) ≤ 0 := by
      have hshift :=
        add_le_add_right hz_sep ((⟪xBar, xStar⟫ₚ : 𝕜) - α)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift
    simpa [sub_eq_add_neg, map_add, map_neg, add_assoc, add_left_comm, add_comm] using hbase

/-- Corollary 6.27.6: an arbitrary weakly separating hyperplane for `epi h` and `C₂ C α`
through the feasible contact point `(xBar, α)` yields a dual vector `xStar` that is simultaneously a
subgradient of `h` at `xBar` and a normal vector to `C` at `xBar`. -/
theorem mem_subdifferentialAt_and_neg_mem_normalCone_of_weaklySeparating_epi_and_C₂
    {h : E → WithBotTop 𝕜} {C : Set E} {α β : 𝕜} {xBar : E} {xStar : Y}
    (hxBar_mem : xBar ∈ C) (hxBar_value : h xBar = α)
    (hsep_epi : ∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + β ≤ μ)
    (hsep_aux : ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + β) :
    xStar ∈ (∂[Y]h(xBar)) ∧ -xStar ∈ N[𝕜](xBar | C) := by
  have hβ :
      β = α - ⟪xBar, xStar⟫ₚ :=
    separatorHeight_eq_canonical_of_weaklySeparating_epi_and_C₂
      hxBar_mem hxBar_value hsep_epi hsep_aux
  refine mem_subdifferentialAt_and_neg_mem_normalCone_of_canonicalSeparatorHeight
    hxBar_mem hxBar_value ?_ ?_
  · intro z μ hz
    simpa [hβ] using hsep_epi z μ hz
  · intro z μ hz
    simpa [hβ] using hsep_aux z μ hz

/-- Corollary 6.27.6, canonical-height companion: specializing the source separator height to
`α - ⟪xBar, xStar⟫ₚ` recovers the same converse surface as
`weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone`. -/
theorem mem_subdifferentialAt_and_neg_mem_normalCone_of_weaklySeparates_epi_and_C₂
    {h : E → WithBotTop 𝕜} {C : Set E} {α : 𝕜} {xBar : E} {xStar : Y}
    (hxBar_mem : xBar ∈ C) (hxBar_value : h xBar = α)
    (hsep_epi :
      ∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ μ)
    (hsep_aux :
      ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ)) :
    xStar ∈ (∂[Y]h(xBar)) ∧ -xStar ∈ N[𝕜](xBar | C) :=
  mem_subdifferentialAt_and_neg_mem_normalCone_of_weaklySeparating_epi_and_C₂
    hxBar_mem hxBar_value hsep_epi hsep_aux

end

/-! ### Definition_6_27_6 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.6 recalls Rockafellar's `0/+∞` indicator function of a set.
- `core/canonical`: this project already owns that notion at the Chapter 1 notation/API layer
  `δ[α](· | C)`, with intrinsic owner `indicator` and bridge APIs
  `indicator_eq_piecewise` / `indicator_def`.
- `bridge/view`: no new mathematics is introduced here, so the faithful refinement is direct
  canonical recall rather than a second alias.

Primary mathematical domain: set indicators on the canonical ordered-extended codomain layer
`WithTopBot α`.

Domain-style sampling used here:
- `indicator`;
- `indicator_eq_piecewise`;
- `indicator_def`;
- `indicator_of_mem` / `indicator_of_notMem`;
- `Set.piecewise`;
- the notation `δ(· | C)`.

Primitive data:
- a set `C : Set E`.

Derived API:
- owner-level indicator notation plus the pointwise `if` formula.

Layer target: `core/canonical recall/use`.
-/

/- Definition 6.27.6: Rockafellar's indicator is recalled at the Chapter 1 canonical notation/API
surface `δ[α](· | C)`, with primitive owner `indicator`. -/
recall indicator

/- Owner bridge: the chapter indicator is exactly the `Set.piecewise` two-branch surface. -/
recall indicator_eq_piecewise

/- The source pointwise formula is exactly the canonical unfolding theorem `indicator_def`; this
item reuses it directly instead of introducing a local wrapper theorem. -/
recall indicator_def

/- Branch-level source consequences: on-set value `0` and off-set value `+∞`. -/
recall indicator_of_mem
recall indicator_of_notMem

/-! ### Proposition_6_27_6 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [AddZeroClass 𝕜] [Preorder 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.6 says that a point belongs to the minimum set of a function
  exactly when the zero functional belongs to the subdifferential there.
- `core/canonical`: the chapter owners are `minimumSet` and `_root_.subdifferentialAt`, so the
  dual-side condition is written directly as zero membership in `subdifferentialAt f x`.
- `bridge/view`: in inner-product spaces, the same criterion is transported through the
  Fréchet-Riesz bridge owner to zero membership in `Function.subdifferentialAt`.

Domain-style sampling used here:
- the Chapter 6 minimum-set owner `minimumSet` from `Definition_6_27_3`;
- the Chapter 23 dual-valued owner `_root_.subdifferentialAt` from `Definition_23_0_6`;
- the Euclidean bridge `Function.subdifferentialAt` from the same file;
- mathlib's canonical dual owner `StrongDual 𝕜 E`;
- mathlib's inner-product-space bridge owner `Function.subdifferentialAt`.

Primitive data vs derived API:
- primitive inputs: only `f : E → WithTopBot 𝕜` and the point `x : E`;
- primitive owner statement: membership in `minimumSet f` versus zero membership in
  `subdifferentialAt f x`;
- derived API: the textbook zero-vector bridge
  `(0 : E) ∈ Function.subdifferentialAt f x`.

Semantic note:
- the equivalence uses only the defining inequality of the minimum set and the zero-subgradient
  membership criterion, so the source assumptions "proper convex" are redundant for this
  statement and are not kept in the main Lean header.
-/

-- Proof sketch: unfold the two owner membership conditions. In any pairing model where pairing
-- against the distinguished zero element vanishes (through the canonical
-- `HasPairingZeroRight` owner),
-- `0 ∈ subdifferentialAt f x Y` is exactly the pointwise inequality `∀ z, f x ≤ f z`, and this
-- is exactly the primitive minimum-set membership criterion.
/-- Pairing-level minimizer criterion: in any pairing model where the zero dual element pairs to
zero, a point belongs to the minimum set exactly when that zero element is a subgradient there. -/
theorem mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing
    {Y : Type (max u v)} [Zero Y] [HasPairing E Y 𝕜] [HasPairingZeroRight E Y 𝕜]
    {f : E → WithTopBot 𝕜} {x : E} :
    x ∈ minimumSet f ↔ (0 : Y) ∈ (∂[Y]f(x)) := by
  rw [mem_minimumSet_iff, mem_subdifferentialAt_pairing]
  constructor
  · intro hx z
    simpa [pairing_zero_right (x := z - x)] using hx z
  · intro hx z
    simpa [pairing_zero_right (x := z - x)] using hx z

end

section

variable {𝕜 : Type v} [NormedField 𝕜] [Preorder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

-- Proof sketch: specialize the pairing-level criterion to the canonical continuous-dual model
-- `StrongDual 𝕜 E`.
/-- Proposition 6.27.6: a point belongs to the minimum set of an extended-valued function if
and only if the zero continuous linear functional is a subgradient there. This is the canonical
dual-valued form of the textbook minimizer criterion. -/
theorem mem_minimumSet_iff_zero_mem_subdifferentialAt
    {f : E → WithTopBot 𝕜} {x : E} :
    x ∈ minimumSet f ↔ (0 : StrongDual 𝕜 E) ∈ (∂ f at x) := by
  exact
    mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing
      (𝕜 := 𝕜) (E := E) (Y := StrongDual 𝕜 E) (f := f) (x := x)

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [Preorder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- Proof sketch: unfold both owners. In the Euclidean bridge theorem
-- `Function.mem_subdifferentialAt`, the zero vector pairing term vanishes, so the primitive
-- minimum-set membership criterion applies directly.
/-- The textbook `x⋆ = 0` formulation of the minimizer criterion in an inner-product-space model.
-/
theorem mem_minimumSet_iff_zero_mem_subdifferentialAt_vector
    {f : E → WithTopBot 𝕜} {x : E} :
    x ∈ minimumSet f ↔ 0 ∈ (∂ᵥf(x)) := by
  rw [mem_minimumSet_iff, Function.mem_subdifferentialAt]
  simp

end

/-! ### Theorem_6_27_6 (from Chap06) -/
open scoped Rockafellar

noncomputable section

universe u v

section

variable {𝕜 : Type v} [AddCommGroup 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]
variable {E : Type u}
variable [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.27.6 is the weak-separation statement for the constrained minimum
  problem, expressed by a non-vertical hyperplane `μ = ⟪z, x⋆⟫ₚ + β` separating the epigraph
  `epi h` from the auxiliary set `C₂ C α`.
- `core/canonical`: the owner abstractions already present in the project are `epi h`, `C₂ C α`,
  `Function.IsConvex`, `_root_.subdifferentialAt`, `N[𝕜](· | ·)`, `IsMinOn`, and the chapter
  relative-interior notations `riDom(h)` and `ri(C)`.
- `bridge/view`: the source hyperplane is recorded directly through inequalities on those owner
  sets rather than through a second local separator wrapper.

Primitive data vs derived API:
- primitive bridge data for the separator construction: a dual subgradient
  `xStar ∈ subdifferentialAt h xBar`, a normal-cone certificate
  `-xStar ∈ N[𝕜](xBar | C)`, and the attained-value identity `h xBar = α`;
- derived API: weak-separation inequalities on `epi h` and `C₂ C α`, with canonical height
  `α - ⟪xBar, xStar⟫ₚ`.

Layer target: `source-facing`, with the owner kept at the intrinsic dual/pairing layer rather than
at a Euclidean Fréchet-Riesz bridge layer.
-/

-- Proof sketch: use the subgradient inequality to control points in `epi h` and the normal-cone
-- inequality to control points in `C₂ C α`, with canonical separator height
-- `β = α - ⟪xBar, xStar⟫ₚ`.
/-- A dual subgradient at `xBar` whose negative is normal to `C` yields weak-separation
inequalities for `epi h` and `C₂ C α`, with canonical source height
`α - ⟪xBar, xStar⟫ₚ`. -/
theorem weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone
    {Y : Type (max u v)} [Neg Y] [HasPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜]
    [HasPairingNegRight E Y 𝕜]
    {h : E → WithTopBot 𝕜} {C : Set E} {α : 𝕜} {xBar : E} {xStar : Y}
    (hxStar_sub : xStar ∈ ∂[Y]h(xBar))
    (hxStar_normal : -xStar ∈ N[𝕜](xBar | C))
    (hxBar_value : h xBar = α) :
    (∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ μ) ∧
      ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
  refine ⟨?_, ?_⟩
  · intro z μ hz_epi
    have hz_sub :
        h xBar + ((⟪z - xBar, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ h z :=
      (mem_subdifferentialAt_pairing.mp hxStar_sub) z
    have hz_eq :
        h xBar + ((⟪z - xBar, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) =
          ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithTopBot 𝕜) := by
      rw [hxBar_value]
      have hz_real :
          α + (⟪z - xBar, xStar⟫ₚ : 𝕜) =
            ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
        calc
          α + (⟪z - xBar, xStar⟫ₚ : 𝕜)
              = α + ((⟪z, xStar⟫ₚ : 𝕜) - (⟪xBar, xStar⟫ₚ : 𝕜)) := by
                  simpa using (congrArg (fun t : 𝕜 ↦ α + t)
                    (HasPairingSubLeft.pairing_sub_left z xBar xStar))
          _ = ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      change (((α + (⟪z - xBar, xStar⟫ₚ : 𝕜) : 𝕜) : WithTopBot 𝕜)) =
        ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithTopBot 𝕜)
      simpa using congrArg (fun t : 𝕜 ↦ ((t : 𝕜) : WithTopBot 𝕜)) hz_real
    have hz_le :
        ((⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) : 𝕜) : WithTopBot 𝕜) ≤ μ := by
      rw [← hz_eq]
      exact le_trans hz_sub (mem_epi_iff.mp hz_epi)
    exact WithTopBot.coe_le_coe.mp hz_le
  · intro z μ hz_aux
    rcases (mem_C₂_iff.mp hz_aux) with ⟨hzC, hμ⟩
    rcases (mem_normalCone_iff_sub_nonpos.mp hxStar_normal) with ⟨_, hxStar_normal'⟩
    have hsub_nonneg : (0 : 𝕜) ≤ (⟪z - xBar, xStar⟫ₚ : 𝕜) := by
      have hsub_nonneg_neg : (0 : 𝕜) ≤ -(⟪z - xBar, -xStar⟫ₚ : 𝕜) :=
        neg_nonneg.mpr (hxStar_normal' z hzC)
      simpa [HasPairingNegRight.pairing_neg_right] using hsub_nonneg_neg
    have hbase : (⟪xBar, xStar⟫ₚ : 𝕜) ≤ (⟪z, xStar⟫ₚ : 𝕜) := by
      have hbase' : (0 : 𝕜) ≤ (⟪z, xStar⟫ₚ : 𝕜) - (⟪xBar, xStar⟫ₚ : 𝕜) := by
        simpa [HasPairingSubLeft.pairing_sub_left] using hsub_nonneg
      exact sub_nonneg.mp hbase'
    have hα : α ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
      have hα' := add_le_add_right hbase (α - ⟪xBar, xStar⟫ₚ)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hα'
    exact le_trans hμ hα

end

section

variable {𝕜 : Type v} [ConditionallyCompleteLinearOrder 𝕜] [NormedField 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddLeftMono 𝕜]
variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Theorem 6.27.6: if `xBar ∈ C` attains the finite minimum value `α` of a convex
function `h` on the convex set `C`, if `h` never takes the value `⊥`, and if `ri(dom h)` meets
`ri[𝕜](C)`, then some continuous-dual vector `xStar` determines a non-vertical hyperplane with
canonical height `β = α - ⟪xBar, xStar⟫ₚ` that weakly separates `epi h` from `C₂ C α`. -/
theorem exists_weaklySeparating_nonverticalHyperplane_of_isMinOn_of_intrinsicInterior
    {h : E → WithTopBot 𝕜} {C : Set E} {α : 𝕜} {xBar : E}
    (hneBot : ∀ y, h y ≠ ⊥) (hh_convex : h.IsConvex 𝕜) (hC_convex : Convex 𝕜 C)
    (hxBar_mem : xBar ∈ C)
    (hxBar_min : IsMinOn h C xBar) (hxBar_value : h xBar = α)
    (hqual : (riDom[𝕜](h) ∩ ri[𝕜](C)).Nonempty) :
    ∃ xStar : StrongDual 𝕜 E,
      (∀ z μ, (z, μ) ∈ epi h → ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) ≤ μ) ∧
        ∀ z μ, (z, μ) ∈ C₂ C α → μ ≤ ⟪z, xStar⟫ₚ + (α - ⟪xBar, xStar⟫ₚ) := by
  rcases
      (isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_intrinsicInterior
        hneBot hh_convex hC_convex hqual).mp ⟨hxBar_mem, hxBar_min⟩ with
    ⟨xStar, hxStar_sub, hxStar_normal⟩
  exact ⟨xStar,
    weaklySeparates_epi_and_C₂_of_mem_subdifferentialAt_and_neg_mem_normalCone
      hxStar_sub
      hxStar_normal
      hxBar_value⟩

end

/-! ### Definition_6_27_7 (from Chap06) -/
noncomputable section

section LEPseudoMetric

universe u

variable {𝕜 : Type u} [LE 𝕜] [Pow 𝕜 ℕ] [PseudoMetricSpace (𝕜 × 𝕜)]

open scoped Rockafellar

local notation "R2" => (𝕜 × 𝕜)
local notation "P" => (paraboloidEpigraph : Set R2)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.7 introduces the function `f₀`, the squared metric
distance to the Section 27 parabola set `P`.
- `core/canonical`: the ambient owners are the shared paraboloid-set owner
  `paraboloidEpigraph : Set (𝕜 × 𝕜)` and the Chapter 1 point-to-set distance owner
  `d(x, C) = Metric.infEDist x C`; the real-valued `Metric.infDist` formula is a bridge view.
- Primitive data vs derived API: the primitive source data are the point `x` and the fixed
source-facing set `paraboloidEpigraph`.

Domain-style sampling used here:
- `d(x, C)` / `Metric.infEDist`;
- `distanceToSet_toReal_eq_infDist`;
- the source-facing set `paraboloidEpigraph` from `Chap02/ParaboloidEpigraph`.

Layer target: `source-facing`, defined from the canonical point-to-set distance owner and then
read on the finite real branch.
-/

/-- Definition 6.27.7: the squared metric distance from `x` to the parabola set `P`
in `𝕜 × 𝕜`. -/
def parabolicF0 (x : R2) : ℝ :=
  (d(x, P)).toReal ^ 2

local notation "f₀" => parabolicF0

/-- The source-facing branch `f₀` is exactly squared `Metric.infDist` on the source set `P`. -/
@[simp] theorem parabolicF0_eq_infDist_sq (x : R2) :
    f₀ x = Metric.infDist x P ^ 2 :=
  by
    simp [parabolicF0, distanceToSet_toReal_eq_infDist]

end LEPseudoMetric

/-! ### Proposition_6_27_7 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.7 has two clauses. A local minimum point of a convex
  extended-valued function in the effective domain is globally minimizing, hence has zero
  subgradient.
- `core/canonical`: theorem surfaces here use the canonical convexity owner
  `ConvexOn 𝕜 (Set.univ : Set E)`, minimum-set owner `minimumSet`, and intrinsic subdifferential
  owner `_root_.subdifferentialAt`.
- `bridge/view`: the Euclidean vector form is kept as a corollary via
  `mem_minimumSet_iff_zero_mem_subdifferentialAt_vector`.

Canonicalization pass note:
- The codomain layer is normalized to `WithTopBot 𝕜`, and Proposition 6.27.7 now keeps the public
  convexity surface at `ConvexOn` rather than the chapter epigraph alias `Function.IsConvex`.
- Assumption stacks are split by theorem surface so each statement only carries the ambient
  structure needed by its owner/notation layer.
-/

universe u v

open scoped Rockafellar Topology

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
variable [SMul 𝕜 (WithTopBot 𝕜)]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- Proposition 6.27.7 (1): if `f` is convex and `x` is a local minimum point in `dom(f)`, then
`x` belongs to the minimum set of `f`. -/
theorem mem_minimumSet_of_isLocalMin_of_convexOn_univ
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hx : x ∈ dom(f)) (hlocal : IsLocalMin f x) :
    x ∈ minimumSet f := by
  sorry

/-- Pairing-level clause of Proposition 6.27.7 (2): in any pairing model where pairing with `0`
vanishes, a local minimizer in `dom(f)` has `0` in its subdifferential. -/
theorem zero_mem_subdifferentialAt_pairing_of_isLocalMin_of_convexOn_univ
    {Y : Type (max u v)} [Zero Y] [HasPairing E Y 𝕜] [HasPairingZeroRight E Y 𝕜]
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hx : x ∈ dom(f)) (hlocal : IsLocalMin f x) :
    (0 : Y) ∈ (∂[Y]f(x)) := by
  exact
    (mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing
      (𝕜 := 𝕜) (E := E) (Y := Y) (f := f) (x := x)).1
      (mem_minimumSet_of_isLocalMin_of_convexOn_univ
        (𝕜 := 𝕜) (E := E) hf_convex hx hlocal)

/-- Proposition 6.27.7 (2): a local minimizer in `dom(f)` has zero continuous-dual subgradient.
-/
theorem zero_mem_subdifferentialAt_of_isLocalMin_of_convexOn_univ
    [TopologicalSpace 𝕜]
    [HasPairing E (StrongDual 𝕜 E) 𝕜] [HasPairingZeroRight E (StrongDual 𝕜 E) 𝕜]
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hx : x ∈ dom(f)) (hlocal : IsLocalMin f x) :
    (0 : StrongDual 𝕜 E) ∈ (∂ f at x) := by
  simpa using
    (zero_mem_subdifferentialAt_pairing_of_isLocalMin_of_convexOn_univ
      (𝕜 := 𝕜) (E := E) (Y := StrongDual 𝕜 E) hf_convex hx hlocal)

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LinearOrder 𝕜]
variable [SMul 𝕜 (WithTopBot 𝕜)]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Euclidean bridge form of Proposition 6.27.7 (2): a local minimizer in `dom(f)` has zero vector
subgradient. -/
theorem zero_mem_subdifferentialAt_vector_of_isLocalMin_of_convexOn_univ
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f)
    (hx : x ∈ dom(f)) (hlocal : IsLocalMin f x) :
    (0 : E) ∈ (∂ᵥf(x)) := by
  exact
    (mem_minimumSet_iff_zero_mem_subdifferentialAt_vector
      (𝕜 := 𝕜) (E := E) (f := f) (x := x)).1
      (mem_minimumSet_of_isLocalMin_of_convexOn_univ
        (𝕜 := 𝕜) (E := E) hf_convex hx hlocal)

end

/-! ### Definition_6_27_8 (from Chap06) -/
noncomputable section

section OrderedNormed

universe u

open scoped Rockafellar

variable {𝕜 : Type u} [Preorder 𝕜] [Pow 𝕜 ℕ] [SeminormedAddCommGroup 𝕜]

local notation "R2" => (𝕜 × 𝕜)
local notation "P" => (paraboloidEpigraph : Set R2)
local notation "f₀" => parabolicF0
local notation "q₂" => ((Function.toWithTopBot (fun ξ : R2 ↦ ‖ξ‖ ^ 2)) : R2 → WithTopBot ℝ)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.8 presents the squared-distance branch `f₀` as the infimal
  convolution of the quadratic branch with the indicator of `P`, and then defines the real-valued
  example `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁`.
- `core/canonical`: the owner abstractions already present are the source-facing squared-distance
  owner `parabolicF0`, the Chapter 1 infimal convolution owner `infimal_convolution` (notation
  `□`), the lifted quadratic branch
  `((fun x : R2 ↦ ‖x‖ ^ 2).toWithTopBot : R2 → WithTopBot ℝ)`, and the indicator owner
  `δ(· | P)`.
- `bridge/view`: this file keeps `parabolicF0` as the source-facing owner from
  Definition 6.27.7 and adds the canonical bridge theorem identifying its `WithTopBot` lift with
  the infimal convolution presentation. The affine perturbation `parabolicObjective` remains the
  genuinely new source-facing definition in this item.
- Primitive data vs derived API: the only new public data are the real-valued objective
  `parabolicObjective`; the infimal-convolution formula for `f₀` is exposed as derived bridge API
  on the existing owner `parabolicF0`.

Domain-style sampling used here:
- `parabolicF0`;
- `Function.toWithTopBot`;
- `indicator` / `δ(· | C)`;
- the binary infimal-convolution owner `infimal_convolution`.

Layer target: `bridge/view` for the infimal-convolution presentation of `f₀`, and
`source-facing` for the new objective.
-/

-- Proof sketch: by definition, `f₀ x` is the infimum over
-- `p ∈ P` of the squared Euclidean distance `‖x - p‖ ^ 2`. Unfolding the Chapter 1 owner
-- `infimal_convolution` with the indicator of `P` gives the same infimum over decompositions
-- `x = y + p`, i.e. over `p ∈ P` with quadratic cost `‖y‖ ^ 2 = ‖x - p‖ ^ 2`.
/-- Definition 6.27.8 (1): owner-level bridge form. The source-facing squared-distance branch
`f₀` is exactly the infimal convolution of the squared Euclidean norm with the indicator of the
parabolic set `P`. -/
theorem parabolicF0_eq_infimalConvolution :
    parabolicF0.toWithTopBot = infimal_convolution q₂ (δ[ℝ](· | P)) := sorry

/-- Pointwise form of `parabolicF0_eq_infimalConvolution`. -/
@[simp] theorem parabolicF0_eq_infimalConvolution_apply (ξ : R2) :
    parabolicF0.toWithTopBot ξ = (infimal_convolution q₂ (δ[ℝ](· | P))) ξ := sorry

end OrderedNormed

section RealObjective

local notation "R2" => (ℝ × ℝ)
local notation "f₀" => parabolicF0

/-- Definition 6.27.8 (2): the example objective `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁`. -/
def parabolicObjective : R2 → ℝ :=
  fun ξ ↦ f₀ ξ - ξ.1

@[simp] theorem parabolicObjective_apply (ξ : R2) :
    parabolicObjective ξ = f₀ ξ - ξ.1 :=
  rfl

end RealObjective

/-! ### Proposition_6_27_8 (from Chap06) -/
noncomputable section

open scoped Rockafellar

local notation "R2" => (ℝ × ℝ)

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.27.8 states that the Section 27 example
  `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁` is a finite convex function on `R²`.
- `core/canonical`: the source owner is the real-valued `ConvexOn ℝ Set.univ` surface for
  `parabolicObjective`.
- `bridge/view`: the source-facing function itself is already the chapter owner
  `parabolicObjective` from Definition 6.27.8, so this item keeps `ConvexOn` on the theorem
  surface and exposes `toWithTopBot.IsConvex` only as a finite-height bridge.

Domain-style sampling used here:
- `Function.IsConvex` from `Chap01.Theorem_4_2`;
- `Function.isConvex_coe_of_convexOn_univ` from the same file;
- `distanceToSet_isConvex` from `Chap01.Text_5_4_1_5`;
- `Function.isConvexOn_iff_convex_epigraph` and `convexOn_iff_convex_epigraph` as the
  codomain-bridge conversion between `WithTopBot` and finite real branches;
- `LinearMap.convexOn` / `ConvexOn.add` from mathlib's convex-function owner layer;
- the source-facing functions `parabolicF0` and `parabolicObjective` from
  `Definition_6_27_8`.

Primitive data vs derived API:
- primitive source data: the real-valued functions `parabolicF0` and `parabolicObjective`;
- derived API: the finite-height bridge theorem via
  `Function.isConvex_coe_of_convexOn_univ`.

Layer target: `source-facing` `ConvexOn ℝ Set.univ` statement, with
`toWithTopBot.IsConvex` as a bridge/view companion.

Real-scalar justification: this item's source owner `parabolicObjective` is intrinsically the
real-valued perturbation `f₀(ξ) - ξ.1` on `R2 = ℝ × ℝ`; both the codomain and the ambient space
are fixed by that source datum, not by proof convenience.
-/

-- Proof sketch for `parabolicF0_convexOn_univ`: `distanceToSet_isConvex` gives convexity of
-- `d(·, P)` in the chapter codomain `WithTopBot ℝ`. Because `P` is nonempty,
-- `d(·, P) = infDist · P` in `WithTopBot ℝ`; the finite-height epigraph bridge converts this to
-- convexity of the real branch `infDist · P`. Squaring by `ConvexOn.pow` gives convexity of `f₀`.
/-- Convexity of the source branch `f₀` from Definition 6.27.8 on `R²`. -/
theorem parabolicF0_convexOn_univ :
    ConvexOn ℝ Set.univ parabolicF0 := by
  let P : Set R2 := (paraboloidEpigraph : Set R2)
  have hP_nonempty : P.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [P, paraboloidEpigraph]
  have hdist_isConvex :
      Function.IsConvex ℝ (fun ξ : R2 ↦ (d(ξ, P) : WithTopBot ℝ)) := by
    simpa [P] using
      (distanceToSet_isConvex P (by simpa [P] using (paraboloidEpigraph_convex (𝕜 := ℝ))))
  have hdist_on :
      Function.IsConvexOn ℝ Set.univ (fun ξ : R2 ↦ (d(ξ, P) : WithTopBot ℝ)) := by
    simpa [Function.IsConvex] using hdist_isConvex
  have hdist_eq_infDist :
      (fun ξ : R2 ↦ (d(ξ, P) : WithTopBot ℝ)) =
        fun ξ : R2 ↦ ((Metric.infDist ξ P : ℝ) : WithTopBot ℝ) := by
    funext ξ
    simpa [P] using (distanceToSet_eq_infDist (E := R2) (C := P) hP_nonempty ξ)
  have hInfDist_coe_on :
      Function.IsConvexOn ℝ Set.univ (fun ξ : R2 ↦ ((Metric.infDist ξ P : ℝ) : WithTopBot ℝ)) := by
    simpa [hdist_eq_infDist] using hdist_on
  have hInfDist : ConvexOn ℝ Set.univ (fun ξ : R2 ↦ Metric.infDist ξ P) := by
    rw [convexOn_iff_convex_epigraph]
    simpa [Function.IsConvexOn, epi_eq_setOf_mem_and_le] using hInfDist_coe_on
  simpa [parabolicF0, P] using
    (hInfDist.pow (by intro ξ _; exact Metric.infDist_nonneg) 2)

/-- Owner-level convexity bridge for `f₀`: finite-valued convexity on `R²` lifted to
`WithTopBot ℝ`. -/
theorem parabolicF0_isConvex :
    parabolicF0.toWithTopBot.IsConvex ℝ := by
  simpa [Function.toWithTopBot] using
    Function.isConvex_coe_of_convexOn_univ parabolicF0_convexOn_univ

-- Proof sketch for `parabolicObjective_convexOn_univ`: combine convexity of `f₀` with convexity
-- of the affine branch `ξ ↦ -ξ.1`.
/-- Proposition 6.27.8, source-facing canonical form:
the Section 27 objective `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁` is convex on `R²`. -/
theorem parabolicObjective_convexOn_univ :
    ConvexOn ℝ Set.univ parabolicObjective := by
  have hF0 : ConvexOn ℝ Set.univ parabolicF0 := parabolicF0_convexOn_univ
  have hlin : ConvexOn ℝ Set.univ (fun ξ : R2 ↦ -ξ.1) := by
    have hlin' : ConvexOn ℝ Set.univ (-(fun ξ : R2 ↦ ξ.1)) :=
      ConcaveOn.neg <|
        LinearMap.concaveOn (LinearMap.fst ℝ ℝ ℝ) (s := (Set.univ : Set R2)) convex_univ
    change ConvexOn ℝ Set.univ (-(fun ξ : R2 ↦ ξ.1))
    exact hlin'
  simpa [parabolicObjective, sub_eq_add_neg] using hF0.add hlin

/-- Proposition 6.27.8, finite-height bridge form:
the Section 27 objective `f(ξ₁, ξ₂) = f₀(ξ₁, ξ₂) - ξ₁` is a finite convex function on `R²`. -/
theorem parabolicObjective_isConvex :
    parabolicObjective.toWithTopBot.IsConvex ℝ := by
  simpa [Function.toWithTopBot] using
    Function.isConvex_coe_of_convexOn_univ parabolicObjective_convexOn_univ

/-! ### Definition_6_27_9 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.9 names the epigraph of an ordered-extended-codomain function
  `h : E → WithTopBot α` as the set of pairs `(x, μ)` with `h x ≤ μ`.
- `core/canonical`: the project already owns this notion in Chapter 1 as `epi`, together with
  the textbook notations `epi[S] f` and `epi f`.
- `bridge/view`: owner-level membership (`mem_epi_iff`) is the intrinsic API surface, and the
  global source set-builder formula is the companion bridge `epi_univ_eq_setOf_le`.
- Primitive data vs derived API: the only primitive datum is the function `h`; the global set
  description and membership rewrites are derived from the Chapter 1 owner.
- Layer target: `core/canonical recall/use`.

Domain-style sampling used here:
- `epi`;
- `mem_epi_iff`;
- `epi_univ_eq_setOf_le`;
- `epi_restrict_eq_preimage_fst_inter`.
-/

/- Definition 6.27.9: Rockafellar's epigraph is the existing chapter owner `epi`,
specialized to the full domain and written downstream as `epi h`. -/
recall epi

/- Intrinsic owner-level membership for the global epigraph surface. -/
recall mem_epi_iff

/- The source's global set formula is already the chapter owner theorem
`epi_univ_eq_setOf_le`, so this file reuses it directly instead of keeping a renamed shell. -/
recall epi_univ_eq_setOf_le

/-! ### Definition_6_27_10 (from Chap06) -/
universe u

section

variable {E : Type u}
variable {R : Type*} [Preorder R]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.10 introduces the auxiliary set `C₂` attached to the
  constrained minimum problem, namely the pairs `(x, μ)` with `x ∈ C` and `μ ≤ α`.
- `core/canonical`: the owner surface is the canonical product/interval object
  `C ×ˢ Set.Iic α`.
- `bridge/view`: the source-facing pair-membership reading `(x, μ) ∈ C₂ C α ↔ x ∈ C ∧ μ ≤ α`
  is a direct derived view of this canonical owner.
- Primitive data vs derived API: primitive data are the set `C` and the level `α`; the
  pointwise membership view is derived API.
- Domain-style sampling used here:
- `Set.prod`;
- `Set.mem_prod`;
- `Set.Iic` / `Set.mem_Iic`;
- the nearby product-form bridge `epi_indicator_eq_prod`.
- Layer target: `source-facing`, with `C₂` as a thin alias of the canonical set-product owner.
-/

/-- Definition 6.27.10: textbook symbol for the lower cylinder, implemented as a thin alias of
the canonical owner `C ×ˢ Set.Iic α`. -/
def C₂ (C : Set E) (α : R) : Set (E × R) :=
  C ×ˢ Set.Iic α

@[simp] theorem mem_C₂_iff
    {C : Set E} {α : R} {x : E} {μ : R} :
    (x, μ) ∈ C₂ C α ↔ x ∈ C ∧ μ ≤ α := by
  simp [C₂, Set.mem_Iic]

end

/-! ### Definition_6_27_11 (from Chap06) -/
universe u

section

variable {E : Type u}
variable {β : Type*} [Preorder β]

/-!
Source/core/bridge triage:

- `source-facing`: in the constrained-minimum reformulation used in Section 27, one compares the
  epigraph `epi h` with the auxiliary set `C₂ C α`. The source
  content at this stage is the level-feasibility reading of that comparison.
- `core/canonical`: the owner abstractions are the Chapter 1 epigraph owner `epi h` and the
  Chapter 6 auxiliary-set owner `C₂ C α`; no separate public `C₁` wrapper is mathematically
  needed.
- `bridge/view`: intersecting these two owners is equivalent to asking for a feasible point
  `x ∈ C` with value in the finite-level closed-sublevel owner
  `h ⁻¹' Set.Iic (α : WithTopBot β)`.
- Primitive data vs derived API: the primitive data are the function `h`, the constraint set `C`,
  and the level `α`; the intersection-membership and nonemptiness reformulations are derived API.
Domain-style sampling used here:
- `epi` / `mem_epi_iff`;
- `C₂` / `mem_C₂_iff`;
- preimage-sublevel owner `h ⁻¹' Set.Iic (α : WithTopBot β)`;
- `Set.mem_inter_iff` and `Set.Nonempty`.
- Layer target: `bridge/view`, stated directly on the existing owner objects instead of
  introducing a parallel local name for the first set.
-/

/-- Definition 6.27.11, canonical owner form: `epi h` meets `C₂ C α` exactly when the finite-level
sublevel owner `C ∩ h ⁻¹' Set.Iic (α : WithTopBot β)` is nonempty. -/
theorem inter_epi_C₂_nonempty_iff_nonempty_inter_preimage_Iic
    {h : E → WithTopBot β} {C : Set E} {α : β} :
    (epi h ∩ C₂ C α).Nonempty ↔
      (C ∩ h ⁻¹' Set.Iic (α : WithTopBot β)).Nonempty := by
  constructor
  · rintro ⟨⟨x, μ⟩, hxμ⟩
    simp only [Set.mem_inter_iff, mem_epi_iff, mem_C₂_iff] at hxμ
    rcases hxμ with ⟨hx_epi, hxC, hμα⟩
    have hμα' : (μ : WithTopBot β) ≤ (α : WithTopBot β) := by
      simpa using hμα
    refine ⟨x, hxC, ?_⟩
    change h x ∈ Set.Iic (α : WithTopBot β)
    exact Set.mem_Iic.mpr (hx_epi.trans hμα')
  · rintro ⟨x, hxC, hxIic⟩
    refine ⟨(x, α), ?_⟩
    refine ⟨?_, ?_⟩
    · exact (mem_epi_iff).2 (Set.mem_Iic.mp hxIic)
    · exact (mem_C₂_iff).2 ⟨hxC, le_rfl⟩

/-- Definition 6.27.11, set-builder companion: `epi h ∩ C₂ C α` is nonempty exactly when the
finite-level sublevel set `C ∩ {x | h x ≤ α}` is nonempty. -/
theorem inter_epi_C₂_nonempty_iff_nonempty_inter_sublevel
    {h : E → WithTopBot β} {C : Set E} {α : β} :
    (epi h ∩ C₂ C α).Nonempty ↔
      (C ∩ {x | h x ≤ α}).Nonempty := by
  simpa [Set.mem_preimage, Set.mem_Iic] using
    (inter_epi_C₂_nonempty_iff_nonempty_inter_preimage_Iic (h := h) (C := C) (α := α))

/-- Definition 6.27.11, source-reading companion: `epi h ∩ C₂ C α` is nonempty exactly when
there exists `x ∈ C` with `h x ≤ α`. -/
theorem inter_epi_C₂_nonempty_iff
    {h : E → WithTopBot β} {C : Set E} {α : β} :
    (epi h ∩ C₂ C α).Nonempty ↔
      ∃ x ∈ C, h x ≤ α := by
  simpa [Set.Nonempty, Set.mem_inter_iff] using
    (inter_epi_C₂_nonempty_iff_nonempty_inter_sublevel (h := h) (C := C) (α := α))

end

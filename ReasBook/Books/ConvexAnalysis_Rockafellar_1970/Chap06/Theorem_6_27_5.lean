import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap05.Example_23_0_7
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_27_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_27_4

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

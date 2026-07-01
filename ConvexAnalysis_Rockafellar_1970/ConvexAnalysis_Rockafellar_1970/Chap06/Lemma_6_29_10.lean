import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10

noncomputable section

universe u

section

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [LinearOrder β] [TopologicalSpace β]
variable [OrderTopology β] [NoMinOrder β] [NoMaxOrder β] [DenselyOrdered β] [SMul 𝕜 β]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.10 is the pure-inequality characterization of strict consistency for
  an ordinary convex program: when there are no equality constraints, strict consistency is
  equivalent to the existence of a point of the constraint set where every inequality is strict.
- `core/canonical`: the strict-consistency owner already exists as
  `Bifunction.IsStrictlyConsistent`, applied to the associated perturbation bifunction.
- `bridge/view`: in the pure-inequality case `s = 0`, the associated bifunction is the
  perturbed-problem owner `P.perturbedProblem` on `P.ConstraintIndex = ι ⊕ κ` with empty equality
  block `κ`, i.e. the
  canonical index-sum perturbation layer with an empty equality block.

Domain-style sampling used here:
- `Bifunction.IsStrictlyConsistent` from `Definition_6_29_10`;
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `OrdinaryConvexProgram.exists_kuhnTuckerVector_of_strict_inequality_point` from
  `Corollary_6_28_3`, which already uses the same strict-inequality witness surface
  `∃ x : P.constraintSet, ∀ i, P.inequality i x < 0`.

Primitive data vs derived API:
- primitive source data: a pure-inequality ordinary convex program
  `P : OrdinaryConvexProgram 𝕜 E β r 0 ι κ` with `Fintype.card κ = 0`;
- canonical owner-side predicate: strict consistency of the associated perturbation bifunction
  `P.perturbedProblem`;
- derived source-facing bridge: existence of a point of `P.constraintSet` satisfying all
  inequalities strictly.

Layer target: `source-facing`, stated directly on the existing ordinary-program owner and the
canonical strict-consistency predicate for the associated bifunction.
-/

variable {r : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = 0)]
variable (P : OrdinaryConvexProgram 𝕜 E β r 0 ι κ)

-- Proof sketch: unfold `Bifunction.IsStrictlyConsistent` for the associated bifunction
-- `P.perturbedProblem`, then rewrite the parameter domain using the pure-inequality description
-- of `P.perturbedFeasibleSet`. For the
-- forward implication, choose a
-- small negative perturbation vector in the interior neighborhood of `0`. For the reverse
-- implication, use the strict inequalities `P.inequality i x < 0` to build an open neighborhood
-- of `0` contained in that parameter domain.
/-- Lemma 6.29.10: when an ordinary convex program has only inequality constraints, it is
strictly consistent exactly when there exists a point of the constraint set where every
inequality constraint is satisfied strictly. -/
theorem strictlyConsistent_iff_exists_strict_inequality_point :
    Bifunction.IsStrictlyConsistent P.perturbedProblem ↔
      ∃ x : P.constraintSet, ∀ i, P.inequality i x < 0 := by
  letI : IsEmpty κ := Fintype.card_eq_zero_iff.mp (Fact.out : Fintype.card κ = 0)
  have hdom_iff {u : P.ConstraintIndex → β} :
      u ∈ Bifunction.dom P.perturbedProblem ↔
        ∃ x : P.constraintSet, ∀ i, P.inequality i x ≤ u (Sum.inl i) := by
    rw [Bifunction.mem_dom_iff_exists]
    constructor
    · rintro ⟨x, hx⟩
      have hxmem : x ∈ P.perturbedFeasibleSet u := by
        by_cases hmem : x ∈ P.perturbedFeasibleSet u
        · exact hmem
        · simp [hmem] at hx
      rcases (P.mem_perturbedFeasibleSet_split).1 hxmem with ⟨hxC, hxI, _⟩
      refine ⟨⟨x, hxC⟩, fun i ↦ hxI i⟩
    · rintro ⟨x, hxI⟩
      have hxmem : x.1 ∈ P.perturbedFeasibleSet u := by
        rw [P.mem_perturbedFeasibleSet_split]
        refine ⟨x.2, ?_, ?_⟩
        · intro i
          simpa using hxI i
        · intro j
          exact isEmptyElim j
      refine ⟨x.1, ?_⟩
      simpa [P.perturbedProblem_apply, hxmem] using
        (WithBotTop.coe_lt_top (P.objective x))
  rw [Bifunction.isStrictlyConsistent_iff]
  constructor
  · intro hstrict
    rcases (isOpen_pi_iff'.1 isOpen_interior) 0 hstrict with ⟨v, hv, hsubset⟩
    choose a b hab hsub using
      fun i ↦ (mem_nhds_iff_exists_Ioo_subset.1 ((hv i).1.mem_nhds (hv i).2))
    choose c hca hc0 using
      fun i ↦ exists_between ((Set.mem_Ioo.mp (hab i)).1)
    let u : P.ConstraintIndex → β := c
    have hu_box : u ∈ Set.univ.pi v := by
      rw [Set.mem_pi]
      intro i hi
      apply hsub i
      rcases (Set.mem_Ioo.mp (hab i)) with ⟨hai, hbi⟩
      refine Set.mem_Ioo.mpr ?_
      constructor
      · simpa [u] using hca i
      · exact lt_trans (by simpa [u] using hc0 i) hbi
    rcases hdom_iff.1 (interior_subset (hsubset hu_box)) with ⟨x, hx⟩
    refine ⟨x, fun i ↦ ?_⟩
    have hu_neg : u (Sum.inl i) < 0 := by
      simpa [u] using hc0 (Sum.inl i)
    exact lt_of_le_of_lt (hx i) hu_neg
  · rintro ⟨x, hxstrict⟩
    let lower : P.ConstraintIndex → β := Sum.elim (fun i ↦ P.inequality i x) isEmptyElim
    have hbox :
        Set.univ.pi (fun i ↦ Set.Ioi (lower i)) ∈ nhds (0 : P.ConstraintIndex → β) := by
      refine set_pi_mem_nhds Set.finite_univ ?_
      intro i hi
      cases i with
      | inl i =>
          simpa [lower] using Ioi_mem_nhds (hxstrict i)
      | inr j =>
          exact isEmptyElim j
    have hsubset :
        Set.univ.pi (fun i ↦ Set.Ioi (lower i)) ⊆ Bifunction.dom P.perturbedProblem := by
      intro u hu
      refine hdom_iff.2 ⟨x, fun i ↦ ?_⟩
      have hui : u (Sum.inl i) ∈ Set.Ioi (lower (Sum.inl i)) :=
        (Set.mem_pi.mp hu) (Sum.inl i) (by simp)
      simpa [lower] using le_of_lt hui
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset hbox hsubset

end OrdinaryConvexProgram

end

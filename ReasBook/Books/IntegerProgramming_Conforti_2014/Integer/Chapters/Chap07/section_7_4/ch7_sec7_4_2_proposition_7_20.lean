import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19
import Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_18

open SimpleGraph
open scoped BigOperators Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

-- This file keeps only the comb-specific source-facing layer, reusing the Chapter 3 owner
-- `is_valid_inequality`, the Chapter 4 complete-graph induced-edge owner `E[G]`, and the
-- Section 7.4 traveling-salesman owners.

section Proposition720

variable {n k : ℕ}

/-- `IsComb handle teeth` records the standard comb hypotheses for the handle `handle` and the
teeth `teeth 0, ..., teeth (k - 1)`. -/
@[mk_iff isComb_iff]
class IsComb (handle : Finset (Fin n)) (teeth : Fin k → Finset (Fin n)) : Prop where
  /-- A comb has an odd number of teeth. -/
  odd_card : Odd k
  /-- A comb has at least three teeth. -/
  three_le_card : 3 ≤ k
  /-- Distinct teeth are disjoint. -/
  pairwise_disjoint : Pairwise fun i j ↦ Disjoint (teeth i) (teeth j)
  /-- Each tooth meets the handle. -/
  inter_nonempty : ∀ i : Fin k, (teeth i ∩ handle).Nonempty
  /-- Each tooth also has a vertex outside the handle. -/
  diff_nonempty : ∀ i : Fin k, (teeth i \ handle).Nonempty

/-- The coefficient of the comb inequality on the edge `e`: one copy for the handle and one copy
for each tooth whose induced subgraph in the complete graph contains `e`. -/
def comb_coefficient (handle : Finset (Fin n)) (teeth : Fin k → Finset (Fin n)) :
    complete_graph_edges n → ℝ :=
  fun e ↦
    (if completeGraphEdge e ∈ E[completeGraph (Fin n)] (handle : Set (Fin n)) then (1 : ℝ)
      else 0) +
      ∑ i : Fin k,
        if completeGraphEdge e ∈ E[completeGraph (Fin n)] (teeth i : Set (Fin n)) then (1 : ℝ)
        else 0

/-- Evaluating the comb coefficient at `e` gives one copy from the handle and one copy from each
tooth that induces `e`. -/
theorem comb_coefficient_apply
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (e : complete_graph_edges n) :
    comb_coefficient handle teeth e =
      (if completeGraphEdge e ∈ E[completeGraph (Fin n)] (handle : Set (Fin n)) then (1 : ℝ)
        else 0) +
        ∑ i : Fin k,
          if completeGraphEdge e ∈ E[completeGraph (Fin n)] (teeth i : Set (Fin n))
          then (1 : ℝ) else 0 := by
  rfl

/-- The right-hand side of the comb inequality (7.23). -/
def comb_rhs (handle : Finset (Fin n)) (teeth : Fin k → Finset (Fin n)) : ℝ :=
  (handle.card : ℝ) + ∑ i : Fin k, ((teeth i).card : ℝ) -
    ((((3 : ℕ) * k + 1) / 2 : ℕ) : ℝ)

/-- Proposition 7.20. If `handle` and `teeth` form a comb, then the comb inequality (7.23),
written as `comb_coefficient handle teeth ⬝ᵥ x ≤ comb_rhs handle teeth`, is valid for the
traveling salesman polytope. -/
theorem comb_inequality_valid_for_traveling_salesman_polytope
    (handle : Finset (Fin n))
    (teeth : Fin k → Finset (Fin n))
    (hcomb : IsComb handle teeth) :
    is_valid_inequality
      (travelingSalesmanPolytope n)
      (comb_coefficient handle teeth)
      (comb_rhs handle teeth) := sorry

end Proposition720

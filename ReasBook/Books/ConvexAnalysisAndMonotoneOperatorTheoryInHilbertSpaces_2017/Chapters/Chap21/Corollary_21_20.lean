import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap21.Definition_21_10
import BauschkeLean.Chap21.Theorem_21_18

open scoped InnerProductSpace

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Corollary 21.20: a maximally monotone operator on a real Hilbert space has
nonempty domain. -/
lemma dom_nonempty_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    A.dom.Nonempty := by
  -- If the domain were empty, the Minty membership criterion would force `(0, 0)` into the graph.
  by_contra hdom
  have hdom_empty : A.dom = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact hdom ⟨x, hx⟩
  have hzero_mem : (0 : H) ∈ A (0 : H) := by
    -- The monotonicity test is vacuous because no graph point can exist when the domain is empty.
    refine (Maximal.mem_iff hA 0 0).2 ?_
    intro y v hv
    have hy_dom : y ∈ A.dom := (mem_dom_iff A y).2 ⟨v, hv⟩
    simp [hdom_empty] at hy_dom
  have hzero_dom : (0 : H) ∈ A.dom := (mem_dom_iff A 0).2 ⟨0, hzero_mem⟩
  exact hdom ⟨0, hzero_dom⟩

section

variable [CompleteSpace H]

/-- Helper for Corollary 21.20: if a maximally monotone operator is locally bounded everywhere,
then the frontier of its domain is empty. -/
lemma frontier_dom_eq_empty_of_isLocallyBounded
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hLoc : A.IsLocallyBounded) :
    frontier A.dom = ∅ := by
  -- Theorem 21.18 identifies local boundedness at each point with avoidance of the frontier.
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  exact
    (isLocallyBoundedAt_iff_not_mem_frontier_dom_of_maximal A hA x).1 (hLoc x) hx

/-- Helper for Corollary 21.20: for a maximally monotone operator, local boundedness everywhere
forces the domain to be all of `H`. -/
lemma dom_eq_univ_of_isLocallyBounded_of_maximal
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hLoc : A.IsLocallyBounded) :
    A.dom = Set.univ := by
  have hfrontier : frontier A.dom = ∅ :=
    frontier_dom_eq_empty_of_isLocallyBounded A hA hLoc
  -- In a preconnected Hilbert space, empty frontier means the set is either empty or universal.
  rcases (frontier_eq_empty_iff (s := A.dom)).1 hfrontier with hdom_empty | hdom_univ
  · exfalso
    rcases dom_nonempty_of_maximal A hA with ⟨x, hx⟩
    simp [hdom_empty] at hx
  · exact hdom_univ

/-- Corollary 21.20: a set-valued operator on a real Hilbert space that is maximal among monotone
operators is locally bounded everywhere if and only if its domain is all of `H`. -/
theorem isLocallyBounded_iff_dom_eq_univ
    (A : SetValuedOperator H H)
    (hA : Maximal IsMonotone A) :
    A.IsLocallyBounded ↔ A.dom = Set.univ := by
  constructor
  · intro hLoc
    -- The forward direction is the globalized Theorem 21.18 route through the domain frontier.
    exact dom_eq_univ_of_isLocallyBounded_of_maximal A hA hLoc
  · intro hdom x
    -- If the domain is all of `H`, then its frontier is empty, so Theorem 21.18 gives local
    -- boundedness at every point.
    refine (isLocallyBoundedAt_iff_not_mem_frontier_dom_of_maximal A hA x).2 ?_
    simp [hdom]

end

end SetValuedOperator

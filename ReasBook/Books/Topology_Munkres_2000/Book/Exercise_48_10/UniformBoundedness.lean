module

public import Topology_Munkres_2000.Book.Definition_45_3.PointwiseBounded
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Defs.Basic

public section

universe u v

namespace PointwiseBounded

/-- A pointwise bounded indexed family of continuous real-valued functions on a
nonempty Baire space is uniformly bounded on some nonempty open set. -/
theorem existsOpenUniformBound {ι : Type v} {X : Type u} [TopologicalSpace X]
    [BaireSpace X] [Nonempty X] (F : ι → ContinuousMap X ℝ)
    (hF : PointwiseBounded (fun i ↦ (F i : X → ℝ))) :
    ∃ U : Set X, U.Nonempty ∧ IsOpen U ∧
      ∃ M : ℝ, ∀ x ∈ U, ∀ i, |F i x| ≤ M := by
  let A : ℕ → Set X := fun n ↦ {x | ∀ i, |F i x| ≤ n}
  rw [_root_.pointwiseBounded_iff] at hF
  have hAclosed : ∀ n, IsClosed (A n) := by
    intro n
    simp only [A, Set.setOf_forall]
    exact isClosed_iInter fun i ↦ isClosed_le (F i).continuous.abs continuous_const
  have hAcover : ⋃ n, A n = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨lower, hlower⟩ := (hF x).bddBelow
    obtain ⟨upper, hupper⟩ := (hF x).bddAbove
    obtain ⟨n, hn⟩ := exists_nat_ge (max (-lower) upper)
    refine ⟨n, ?_⟩
    intro i
    rw [abs_le]
    constructor
    · have hnlower : -(n : ℝ) ≤ lower := by
        linarith [((le_max_left (-lower) upper).trans hn)]
      exact hnlower.trans (hlower ⟨i, rfl⟩)
    · exact (hupper ⟨i, rfl⟩).trans ((le_max_right _ _).trans hn)
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hAclosed hAcover
  refine ⟨interior (A n), hn, isOpen_interior, n, ?_⟩
  intro x hx i
  exact interior_subset hx i

end PointwiseBounded

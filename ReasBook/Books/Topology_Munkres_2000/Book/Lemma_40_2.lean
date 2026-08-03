module

public import Topology_Munkres_2000.Book.Exercise_33_4

public section

open Set

universe u

/-- Lemma 40.2: In a normal space, every closed `Gδ` set is the zero set of a
continuous map to `Set.Icc 0 1` that is strictly positive off the set. -/
theorem exists_continuousMap_Icc_zero_of_closed_isGδ {X : Type u} [TopologicalSpace X]
    [T4Space X] {A : Set X} (hA : IsClosed A) (hG : IsGδ A) :
    ∃ f : C(X, Set.Icc (0 : ℝ) 1),
      (∀ x ∈ A, (f x : ℝ) = 0) ∧ ∀ x, x ∉ A → 0 < (f x : ℝ) :=
  let ⟨f, hf⟩ :=
    (ContinuousMap.exists_vanishesPreciselyOn_iff_closed_isGδ A).2 ⟨hA, hG⟩
  ⟨f, fun x hx ↦ (ContinuousMap.vanishesPreciselyOn_iff f A).1 hf x |>.2 hx,
    fun x hx ↦ (hf.positive_iff_notMem x).2 hx⟩

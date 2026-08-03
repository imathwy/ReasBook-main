module

public import Mathlib.Topology.Baire.Lemmas

public section

universe u

/- Definition 48.2. The canonical notion of a Baire topological space. -/
#check BaireSpace

/-- A topological space is Baire if and only if every countable union of closed
subsets with empty interior has empty interior. -/
theorem baireSpace_iff_iUnion_closed {X : Type u} [TopologicalSpace X] :
    BaireSpace X ↔
      ∀ A : ℕ → Set X, (∀ n, IsClosed (A n)) → (∀ n, interior (A n) = ∅) →
        interior (⋃ n, A n) = ∅ := by
  constructor
  · intro hBaire A hclosed hinterior
    letI : BaireSpace X := hBaire
    -- Pass to the open dense complements and apply the Baire property.
    rw [interior_eq_empty_iff_dense_compl, Set.compl_iUnion]
    refine BaireSpace.baire_property (fun n ↦ (A n)ᶜ) ?_ ?_
    · intro n
      exact (hclosed n).isOpen_compl
    · intro n
      exact interior_eq_empty_iff_dense_compl.mp (hinterior n)
  · intro hclosedUnion
    -- Recover the defining dense-intersection property by complement duality.
    refine ⟨?_⟩
    intro f hopen hdense
    have hinteriorCompl : interior ((⋂ n, f n)ᶜ) = ∅ := by
      rw [Set.compl_iInter]
      refine hclosedUnion (fun n ↦ (f n)ᶜ) ?_ ?_
      · intro n
        exact (hopen n).isClosed_compl
      · intro n
        have hdenseDoubleCompl : Dense ((f n)ᶜ)ᶜ := by
          simpa using hdense n
        exact interior_eq_empty_iff_dense_compl.mpr hdenseDoubleCompl
    -- The complement criterion returns density after cancelling two complements.
    simpa using interior_eq_empty_iff_dense_compl.mp hinteriorCompl

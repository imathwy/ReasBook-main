module

public import Topology_Munkres_2000.Book.Example_31_2.Instances
public import Mathlib.Topology.Separation.Regular

public section

universe u

/-- A regular `T₁` space with a countable basis is completely normal in the book's
`T₁` convention. -/
instance T3Space.toT5SpaceOfSecondCountableTopology {X : Type u} [TopologicalSpace X]
    [T3Space X] [SecondCountableTopology X] : T5Space X where
  toT1Space := inferInstance
  toCompletelyNormalSpace := inferInstance

namespace SorgenfreyLine

/-- The Sorgenfrey line is completely normal in the book's `T₁` convention. -/
instance instT5Space : T5Space SorgenfreyLine where
  toT1Space := inferInstance
  toCompletelyNormalSpace := by
    refine ⟨fun A B hClosureA hClosureB ↦ ?_⟩
    classical
    -- Around each point, choose a based half-open interval avoiding the opposite closure.
    have hAIntervals : ∀ a : A,
        ∃ endpoint : ℝ, toReal a < endpoint ∧
          toReal ⁻¹' Set.Ico (toReal a) endpoint ⊆ (closure B)ᶜ := by
      intro a
      have ha : (a : SorgenfreyLine) ∈ (closure B)ᶜ := by
        exact fun haClosureB ↦ Set.disjoint_left.mp hClosureB a.property haClosureB
      obtain ⟨V, ⟨left, right, hleftRight, rfl⟩, haV, hV⟩ :=
        isTopologicalBasis_lowerLimitBasis.exists_subset_of_mem_open ha
          isClosed_closure.isOpen_compl
      refine ⟨right, haV.2, ?_⟩
      intro (x : SorgenfreyLine) hx
      exact hV ⟨haV.1.trans hx.1, hx.2⟩
    have hBIntervals : ∀ b : B,
        ∃ endpoint : ℝ, toReal b < endpoint ∧
          toReal ⁻¹' Set.Ico (toReal b) endpoint ⊆ (closure A)ᶜ := by
      intro b
      have hb : (b : SorgenfreyLine) ∈ (closure A)ᶜ := by
        exact fun hbClosureA ↦ Set.disjoint_left.mp hClosureA hbClosureA b.property
      obtain ⟨V, ⟨left, right, hleftRight, rfl⟩, hbV, hV⟩ :=
        isTopologicalBasis_lowerLimitBasis.exists_subset_of_mem_open hb
          isClosed_closure.isOpen_compl
      refine ⟨right, hbV.2, ?_⟩
      intro (x : SorgenfreyLine) hx
      exact hV ⟨hbV.1.trans hx.1, hx.2⟩
    choose r hrlt hrAvoid using hAIntervals
    choose s hslt hsAvoid using hBIntervals
    rw [← separatedNhds_iff_disjoint]
    refine ⟨⋃ a : A, toReal ⁻¹' Set.Ico (toReal a) (r a),
      ⋃ b : B, toReal ⁻¹' Set.Ico (toReal b) (s b), ?_, ?_, ?_, ?_, ?_⟩
    · refine isOpen_iUnion fun a ↦ isTopologicalBasis_lowerLimitBasis.isOpen ?_
      exact ⟨toReal a, r a, hrlt a, rfl⟩
    · refine isOpen_iUnion fun b ↦ isTopologicalBasis_lowerLimitBasis.isOpen ?_
      exact ⟨toReal b, s b, hslt b, rfl⟩
    · intro a ha
      exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, Set.left_mem_Ico.mpr (hrlt ⟨a, ha⟩)⟩
    · intro b hb
      exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, Set.left_mem_Ico.mpr (hslt ⟨b, hb⟩)⟩
    · refine Set.disjoint_left.mpr ?_
      intro x hxA hxB
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxA
      obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hxB
      rcases le_total (toReal a) (toReal b) with hab | hba
      · have hbInterval : (b : SorgenfreyLine) ∈ toReal ⁻¹' Set.Ico (toReal a) (r a) :=
          ⟨hab, hxb.1.trans_lt hxa.2⟩
        exact (hrAvoid a hbInterval) (subset_closure b.property)
      · have haInterval : (a : SorgenfreyLine) ∈ toReal ⁻¹' Set.Ico (toReal b) (s b) :=
          ⟨hba, hxa.1.trans_lt hxb.2⟩
        exact (hsAvoid b haInterval) (subset_closure a.property)

end SorgenfreyLine

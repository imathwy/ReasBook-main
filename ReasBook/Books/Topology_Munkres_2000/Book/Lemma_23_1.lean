module

public import Topology_Munkres_2000.Book.Definition_23_1.Separation
public import Topology_Munkres_2000.Book.Lemma_23_1.SeparatedSets

public section

open Set
open scoped Set.Notation

universe u

namespace Set

/-- Helper for Lemma 23.1: the left member of a separation is closed. -/
theorem IsSeparation.isClosed_left {X : Type u} [TopologicalSpace X] {U V : Set X}
    (h : U.IsSeparation V) : IsClosed U := by
  -- The other open member is the complement of the left member.
  have hU : U = Vᶜ := eq_compl_iff_isCompl.mpr
    ⟨h.disjoint, codisjoint_iff.mpr h.union_eq_univ⟩
  rw [hU]
  exact h.isOpen_right.isClosed_compl

/-- Helper for Lemma 23.1: ambiently separated sets covering `Y` induce a closed
left member in the subspace `Y`. -/
theorem AreSeparated.isClosed_preimage_val_left {X : Type u} [TopologicalSpace X]
    {Y A B : Set X} (h : AreSeparated A B) (h_union : A ∪ B = Y) :
    IsClosed (Y ↓∩ A) := by
  -- Normalize the relative-closure criterion using the fact that `A ⊆ Y`.
  have hA_sub : A ⊆ Y := by
    rw [← h_union]
    exact subset_union_left
  rw [isClosed_preimage_val, inter_eq_right.mpr hA_sub]
  intro x hx
  -- A point of `Y` lies in `A` or `B`; the latter contradicts separation.
  rw [← h_union] at hx
  rcases hx.1 with hxA | hxB
  · exact hxA
  · exact (disjoint_left.mp h.disjoint_closure_left hx.2 hxB).elim

/-- Lemma 23.1 (1): Disjoint nonempty subsets `A` and `B` covering `Y` form a
separation of the subspace `Y` exactly when neither contains an ambient limit
point of the other. -/
theorem isSeparation_preimage_val_iff_disjoint_derivedSet {X : Type u}
    [TopologicalSpace X] {Y A B : Set X} (hAB : Disjoint A B) (hA : A.Nonempty)
    (hB : B.Nonempty) (h_union : A ∪ B = Y) :
    (Y ↓∩ A).IsSeparation (Y ↓∩ B) ↔
      Disjoint A (derivedSet B) ∧ Disjoint B (derivedSet A) := by
  -- Record the ambient subsets determined by the covering equation.
  have hA_sub : A ⊆ Y := by
    rw [← h_union]
    exact subset_union_left
  have hB_sub : B ⊆ Y := by
    rw [← h_union]
    exact subset_union_right
  constructor
  · intro h
    -- Relative closedness excludes the other member from each ambient closure.
    have hclosedA := h.isClosed_left
    rw [isClosed_preimage_val, inter_eq_right.mpr hA_sub] at hclosedA
    have hclosedB := h.symm.isClosed_left
    rw [isClosed_preimage_val, inter_eq_right.mpr hB_sub] at hclosedB
    have hclosureAB : Disjoint (closure A) B := by
      rw [disjoint_left]
      intro x hxClosure hxB
      exact disjoint_left.mp hAB (hclosedA ⟨hB_sub hxB, hxClosure⟩) hxB
    have hclosureBA : Disjoint A (closure B) := by
      rw [disjoint_left]
      intro x hxA hxClosure
      exact disjoint_left.mp hAB hxA (hclosedB ⟨hA_sub hxA, hxClosure⟩)
    exact (areSeparated_iff_disjoint_derivedSet.mp
      (areSeparated_of_disjoint_closure hclosureAB hclosureBA)).2
  · intro hlimits
    -- The derived-set conditions are the canonical ambient separation criterion.
    have hseparated : AreSeparated A B :=
      areSeparated_iff_disjoint_derivedSet.mpr ⟨hAB, hlimits⟩
    have hclosedA := hseparated.isClosed_preimage_val_left h_union
    have hclosedB := hseparated.symm.isClosed_preimage_val_left
      ((union_comm B A).trans h_union)
    have hinducedDisjoint : Disjoint (Y ↓∩ A) (Y ↓∩ B) := hAB.preimage Subtype.val
    have hinducedUnion : (Y ↓∩ A) ∪ (Y ↓∩ B) = univ := by
      apply eq_univ_of_univ_subset
      intro y hy
      have hyAB : y.1 ∈ A ∪ B := by
        rw [h_union]
        exact y.2
      exact hyAB
    have hinducedCompl : IsCompl (Y ↓∩ A) (Y ↓∩ B) :=
      ⟨hinducedDisjoint, codisjoint_iff.mpr hinducedUnion⟩
    have hopenA : IsOpen (Y ↓∩ A) := by
      rw [eq_compl_iff_isCompl.mpr hinducedCompl]
      exact hclosedB.isOpen_compl
    have hopenB : IsOpen (Y ↓∩ B) := by
      rw [eq_compl_iff_isCompl.mpr hinducedCompl.symm]
      exact hclosedA.isOpen_compl
    -- Lift ambient witnesses and assemble the induced separation.
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨hopenA, hopenB, hinducedDisjoint, ⟨⟨a, hA_sub ha⟩, ha⟩,
      ⟨⟨b, hB_sub hb⟩, hb⟩, hinducedUnion⟩

/-- Nonempty subsets covering `Y` form a separation of the subspace `Y` exactly when they are
separated in the ambient space. -/
theorem isSeparation_preimage_val_iff_areSeparated {X : Type u} [TopologicalSpace X]
    {Y A B : Set X} (hA : A.Nonempty) (hB : B.Nonempty) (h_union : A ∪ B = Y) :
    (Y ↓∩ A).IsSeparation (Y ↓∩ B) ↔ AreSeparated A B := by
  constructor
  · intro h
    have hA_sub : A ⊆ Y := by
      rw [← h_union]
      exact subset_union_left
    have hB_sub : B ⊆ Y := by
      rw [← h_union]
      exact subset_union_right
    have hAB : Disjoint A B := by
      rw [disjoint_left]
      intro x hxA hxB
      exact disjoint_left.mp h.disjoint (show (⟨x, hA_sub hxA⟩ : Y) ∈ Y ↓∩ A by exact hxA)
        (show (⟨x, hB_sub hxB⟩ : Y) ∈ Y ↓∩ B by exact hxB)
    exact areSeparated_iff_disjoint_derivedSet.2
      ⟨hAB, (isSeparation_preimage_val_iff_disjoint_derivedSet hAB hA hB h_union).1 h⟩
  · intro h
    exact (isSeparation_preimage_val_iff_disjoint_derivedSet h.disjoint hA hB h_union).2
      (areSeparated_iff_disjoint_derivedSet.1 h).2

end Set

/-- Lemma 23.1 (2): A subspace `Y` is preconnected exactly when it cannot be
partitioned into disjoint nonempty sets, neither containing an ambient limit
point of the other. -/
theorem isPreconnected_iff_no_limitPointSeparation {X : Type u} [TopologicalSpace X]
    {Y : Set X} :
    IsPreconnected Y ↔
      ¬ ∃ A B : Set X,
        Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧ A ∪ B = Y ∧
          Disjoint A (derivedSet B) ∧ Disjoint B (derivedSet A) := by
  -- Replace preconnectedness by the absence of a separation of the subtype.
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_no_separation]
  constructor
  · intro hnoSeparation ⟨A, B, hAB, hA, hB, h_union, hlimits⟩
    apply hnoSeparation
    -- An ambient limit-point partition pulls back to a subtype separation.
    exact ⟨Y ↓∩ A, Y ↓∩ B,
      (Set.isSeparation_preimage_val_iff_disjoint_derivedSet
        hAB hA hB h_union).mpr hlimits⟩
  · intro hnoPartition ⟨U, V, hUV⟩
    apply hnoPartition
    -- Push a subtype separation into the ambient space along the injective value map.
    have hdisjoint : Disjoint (↑U : Set X) (↑V : Set X) :=
      Set.disjoint_image_of_injective Subtype.val_injective hUV.disjoint
    have hU : (↑U : Set X).Nonempty := hUV.left_nonempty.image Subtype.val
    have hV : (↑V : Set X).Nonempty := hUV.right_nonempty.image Subtype.val
    have h_union : (↑U : Set X) ∪ (↑V : Set X) = Y := by
      rw [← Set.image_val_union, hUV.union_eq_univ, Set.image_univ, Subtype.range_val]
    have hinduced :
        (Y ↓∩ (↑U : Set X)).IsSeparation (Y ↓∩ (↑V : Set X)) := by
      simpa only [Set.preimage_val_image_val_eq_self] using hUV
    refine ⟨(↑U : Set X), (↑V : Set X), hdisjoint, hU, hV, h_union, ?_⟩
    exact (Set.isSeparation_preimage_val_iff_disjoint_derivedSet
      hdisjoint hU hV h_union).mp hinduced

/-- A subspace `Y` is preconnected exactly when it cannot be partitioned into two
nonempty ambiently separated subsets. -/
theorem isPreconnected_iff_no_separated_partition {X : Type u} [TopologicalSpace X]
    {Y : Set X} :
    IsPreconnected Y ↔
      ¬ ∃ A B : Set X,
        A.Nonempty ∧ B.Nonempty ∧ A ∪ B = Y ∧ AreSeparated A B := by
  rw [isPreconnected_iff_no_limitPointSeparation]
  simp only [areSeparated_iff_disjoint_derivedSet]
  aesop

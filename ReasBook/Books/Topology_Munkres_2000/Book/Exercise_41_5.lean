module

public import Topology_Munkres_2000.Book.Theorem_41_1

public section

universe u v

namespace LocallyFinite

/-- Helper for Exercise 41.5: regrouping a locally finite family along a relation with
finite reverse fibers preserves local finiteness. -/
private lemma iUnion_of_finite_fibers {ι : Type u} {κ : Type*} {X : Type v}
    [TopologicalSpace X] {W : κ → Set X} {R : ι → κ → Prop} (hW : LocallyFinite W)
    (hR : ∀ k, {i | R i k}.Finite) :
    LocallyFinite (fun i ↦ ⋃ k, ⋃ (_ : R i k), W k) := by
  -- Use a neighborhood that meets only finitely many members of the original family.
  intro x
  rcases hW x with ⟨t, htx, ht⟩
  refine ⟨t, htx, ?_⟩
  -- Every new index meeting `t` lies in a finite union of reverse relation fibers.
  refine (ht.biUnion fun k _ ↦ hR k).subset ?_
  intro i hi
  rcases hi with ⟨y, hyU, hyt⟩
  simp only [Set.mem_iUnion] at hyU
  rcases hyU with ⟨k, hik, hyW⟩
  refine Set.mem_iUnion_of_mem k ?_
  refine Set.mem_iUnion_of_mem ?_ hik
  exact ⟨y, hyW, hyt⟩

/-- Helper for Exercise 41.5: a covered family contains every set in the union of the
cover members incident to that set. -/
private lemma subset_iUnion_incident_of_iUnion_eq_univ {ι : Type u} {κ : Type*}
    {X : Type v} {B : ι → Set X} {W : κ → Set X} (hcover : ⋃ k, W k = Set.univ) :
    ∀ i, B i ⊆ ⋃ k, ⋃ (_ : (B i ∩ W k).Nonempty), W k := by
  -- Choose a cover member containing the given point and use the point as incidence witness.
  intro i x hxi
  have hxcover : x ∈ ⋃ k, W k := by
    rw [hcover]
    exact Set.mem_univ x
  simp only [Set.mem_iUnion] at hxcover
  rcases hxcover with ⟨k, hxW⟩
  refine Set.mem_iUnion_of_mem k ?_
  refine Set.mem_iUnion_of_mem ?_ hxW
  exact ⟨x, hxi, hxW⟩

/-- Exercise 41.5. Every locally finite indexed family of subsets of a paracompact
Hausdorff space has a locally finite, pointwise containing indexed family of open sets. -/
theorem exists_open_superset {ι : Type u} {X : Type v} [TopologicalSpace X]
    [ParacompactSpace X] [T2Space X] {B : ι → Set X} (hB : LocallyFinite B) :
    ∃ U : ι → Set X, LocallyFinite U ∧ (∀ i, IsOpen (U i)) ∧ ∀ i, B i ⊆ U i := by
  classical
  -- Choose at each point an open neighborhood meeting only finitely many `B i`.
  choose V hV using fun x ↦ hB.exists_mem_basis (nhds_basis_opens x)
  have hVcover : ⋃ x, V x = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    exact Set.mem_iUnion_of_mem x (hV x).1.1
  -- Replace this cover by a locally finite precise refinement.
  rcases precise_refinement V (fun x ↦ (hV x).1.2) hVcover with
    ⟨W, hWopen, hWcover, hWfinite, hWV⟩
  have hWincidence : ∀ x, {i | (B i ∩ W x).Nonempty}.Finite := by
    intro x
    refine (hV x).2.subset ?_
    intro i hi
    exact hi.mono (Set.inter_subset_inter_right _ (hWV x))
  -- Expand `B i` by the union of all refinement members incident to it.
  let U : ι → Set X := fun i ↦ ⋃ x, ⋃ (_ : (B i ∩ W x).Nonempty), W x
  refine ⟨U, ?_, ?_, ?_⟩
  · exact iUnion_of_finite_fibers hWfinite hWincidence
  · intro i
    exact isOpen_iUnion fun x ↦ isOpen_iUnion fun _ ↦ hWopen x
  · exact subset_iUnion_incident_of_iUnion_eq_univ hWcover

end LocallyFinite

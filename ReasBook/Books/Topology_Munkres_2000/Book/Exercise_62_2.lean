module

public import Topology_Munkres_2000.Book.Lemma_62_2
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Topology.Homotopy.Contractible

public section

open Set

/-- Helper for Exercise 62.2: pairwise membership in relative connected components
implies that the ambient set is preconnected. -/
lemma isPreconnected_of_mem_connectedComponentIn {X : Type*} [TopologicalSpace X]
    {F : Set X} (h : ∀ x ∈ F, ∀ y ∈ F, y ∈ connectedComponentIn F x) :
    IsPreconnected F := by
  -- Use each relative connected component as the preconnected set joining a pair.
  refine isPreconnected_of_forall_pair fun x hx y hy ↦ ?_
  exact ⟨connectedComponentIn F x, connectedComponentIn_subset F x,
    mem_connectedComponentIn hx, h x hx y hy, isPreconnected_connectedComponentIn⟩

/-- Helper for Exercise 62.2: two points outside a compact contractible subset
of the standard two-sphere lie in the same relative connected component. -/
lemma contractibleSubtype_mem_connectedComponentIn_compl
    (A : Set (StandardSphere 2)) [CompactSpace A] [ContractibleSpace A]
    {a b : StandardSphere 2} (ha : a ∈ Aᶜ) (hb : b ∈ Aᶜ) :
    b ∈ connectedComponentIn Aᶜ a := by
  -- The subtype inclusion avoids both selected complement points.
  have inclusion_mem : ∀ x : A, (x : StandardSphere 2) ∈ ({a, b}ᶜ : Set (StandardSphere 2)) := by
    intro x
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun hxa ↦ ha (hxa ▸ x.property), fun hxb ↦ hb (hxb ▸ x.property)⟩
  let inclusion : C(A, ({a, b}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun x ↦ ⟨x, inclusion_mem x⟩, continuous_subtype_val.subtype_mk _⟩
  have inclusion_injective : Function.Injective inclusion := by
    intro x y hxy
    have hxy_val : (x : StandardSphere 2) = y :=
      congrArg (fun z : ({a, b}ᶜ : Set (StandardSphere 2)) ↦ (z : StandardSphere 2)) hxy
    exact Subtype.ext hxy_val
  have inclusion_nullhomotopic : inclusion.Nullhomotopic := by
    -- Contractibility nullhomotopes the identity, hence also the inclusion.
    simpa only [ContinuousMap.comp_id] using (id_nullhomotopic A).comp_right inclusion
  have inclusion_range : Set.range (fun x : A ↦ (inclusion x : StandardSphere 2)) = A := by
    -- Forgetting the punctured-sphere codomain leaves the ordinary subtype inclusion.
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  -- Borsuk's lemma now identifies the required component in the complement of A.
  rw [← inclusion_range]
  exact borsukLemma a b inclusion inclusion_injective inclusion_nullhomotopic

/-- Exercise 62.2. Every compact contractible subspace of the standard two-sphere
does not separate the sphere. -/
theorem compactContractible_not_separates_twoSphere
    (A : Set (StandardSphere 2)) [CompactSpace A] [ContractibleSpace A] :
    ¬ A.Separates := by
  -- Pairwise Borsuk applications make the entire complement preconnected.
  have complement_preconnected : IsPreconnected Aᶜ :=
    isPreconnected_of_mem_connectedComponentIn fun _ ha _ hb ↦
      contractibleSubtype_mem_connectedComponentIn_compl A ha hb
  have complement_preconnectedSpace : PreconnectedSpace (Aᶜ : Set (StandardSphere 2)) :=
    Subtype.preconnectedSpace complement_preconnected
  -- This directly contradicts the definition of separation.
  intro hA
  exact (Set.separates_iff.mp hA) complement_preconnectedSpace

end

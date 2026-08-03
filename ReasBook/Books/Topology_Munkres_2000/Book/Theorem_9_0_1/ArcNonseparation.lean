module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_61_2.Arc
import Topology_Munkres_2000.Book.Exercise_51_3.Contractible
public import Mathlib.Topology.Homotopy.Contractible

public section

open Set

/-- Helper for Theorem 9.0.1: pairwise membership in relative connected
components makes the ambient set preconnected. -/
lemma isPreconnected_of_pairwise_mem_connectedComponentIn
    {X : Type*} [TopologicalSpace X] {F : Set X}
    (h : ∀ x ∈ F, ∀ y ∈ F, y ∈ connectedComponentIn F x) :
    IsPreconnected F := by
  -- Use the relative component of the first point as a connected witness for each pair.
  refine isPreconnected_of_forall_pair fun x hx y hy ↦ ?_
  exact ⟨connectedComponentIn F x, connectedComponentIn_subset F x,
    mem_connectedComponentIn hx, h x hx y hy, isPreconnected_connectedComponentIn⟩

/-- Helper for Theorem 9.0.1: pairwise component membership in a complement
rules out separation by the omitted set. -/
lemma not_separates_of_pairwise_mem_connectedComponentIn
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (h : ∀ x ∈ Aᶜ, ∀ y ∈ Aᶜ, y ∈ connectedComponentIn Aᶜ x) :
    ¬ A.Separates := by
  -- Pairwise component membership gives a preconnected complement subtype.
  have hComplement : IsPreconnected Aᶜ :=
    isPreconnected_of_pairwise_mem_connectedComponentIn h
  have hComplementSpace : PreconnectedSpace (Aᶜ : Set X) :=
    Subtype.preconnectedSpace hComplement
  -- Separation is exactly the failure of that preconnectedness property.
  intro hA
  exact (Set.separates_iff.mp hA) hComplementSpace

/-- Helper for Theorem 9.0.1: an arc inclusion avoids any two exterior points,
is injective and nullhomotopic, and has the arc as its ambient range. -/
lemma arcInclusion_nullhomotopic
    (A : Set (StandardSphere 2)) [Topology.IsArc A]
    {a b : StandardSphere 2} (ha : a ∈ Aᶜ) (hb : b ∈ Aᶜ) :
    ∃ inclusion : C(A, ({a, b}ᶜ : Set (StandardSphere 2))),
      Function.Injective inclusion ∧ inclusion.Nullhomotopic ∧
        Set.range (fun x : A ↦ (inclusion x : StandardSphere 2)) = A := by
  classical
  -- Transport compactness and contractibility from the unit interval to the arc.
  obtain ⟨arcHomeomorph⟩ := Topology.IsArc.homeomorphic_unitInterval (X := A)
  letI : CompactSpace A := arcHomeomorph.symm.compactSpace
  letI : ContractibleSpace A := arcHomeomorph.contractibleSpace
  -- Restrict the subtype inclusion to the sphere with the two exterior points removed.
  have inclusion_mem :
      ∀ x : A, (x : StandardSphere 2) ∈ ({a, b}ᶜ : Set (StandardSphere 2)) := by
    intro x
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun hxa ↦ ha (hxa ▸ x.property), fun hxb ↦ hb (hxb ▸ x.property)⟩
  let inclusion : C(A, ({a, b}ᶜ : Set (StandardSphere 2))) :=
    ⟨fun x ↦ ⟨x, inclusion_mem x⟩, continuous_subtype_val.subtype_mk _⟩
  refine ⟨inclusion, ?_, ?_, ?_⟩
  · -- Forgetting the codomain restriction reduces injectivity to subtype injectivity.
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : ({a, b}ᶜ : Set (StandardSphere 2)) ↦ (z : StandardSphere 2)) hxy
  · -- Contractibility nullhomotopes the identity and hence the inclusion.
    simpa only [ContinuousMap.comp_id] using (id_nullhomotopic A).comp_right inclusion
  · -- The ambient range of the restricted inclusion is exactly the original arc.
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩

end

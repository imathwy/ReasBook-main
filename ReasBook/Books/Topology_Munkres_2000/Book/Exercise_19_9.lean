module

public import Topology_Munkres_2000.Book.Assumption_9_1
public import Mathlib.Logic.Nonempty

public section

universe u

/-- Exercise 19.9. The axiom of choice for pairwise disjoint nonempty sets is
equivalent to nonemptiness of every dependent Cartesian product of nonempty
types. The source assumption that the index type is nonempty is redundant,
since the empty product is nonempty. -/
theorem axiomOfChoiceForDisjointSets_iff_nonempty_pi :
    (∀ {α : Type u} (𝒜 : Set (Set α)),
      𝒜.PairwiseDisjoint id → (∀ A ∈ 𝒜, A.Nonempty) → ∃ C, 𝒜.IsChoiceSet C) ↔
    (∀ {ι : Type u} (A : ι → Type u),
      (∀ i, Nonempty (A i)) → Nonempty (∀ i, A i)) := by
  constructor
  · -- Classical choice selects one element from every nonempty factor.
    intro _ _ A hA
    exact Classical.nonempty_pi.mpr hA
  · -- The imported disjoint-set choice theorem supplies the reverse formulation.
    intro _ _ 𝒜 hdisjoint hnonempty
    exact axiomOfChoiceForDisjointSets 𝒜 hdisjoint hnonempty

/-- The repository's source-facing disjoint-set choice axiom implies the
dependent Cartesian-product formulation of choice. -/
theorem nonempty_pi_of_axiomOfChoiceForDisjointSets {ι : Type u} (A : ι → Type u)
    (hA : ∀ i, Nonempty (A i)) : Nonempty (∀ i, A i) :=
  axiomOfChoiceForDisjointSets_iff_nonempty_pi.mp axiomOfChoiceForDisjointSets A hA

/-- The dependent Cartesian-product formulation implies the repository's
source-facing axiom of choice for pairwise disjoint families. -/
theorem axiomOfChoiceForDisjointSets_of_nonempty_pi
    (hpi : ∀ {ι : Type u} (A : ι → Type u),
      (∀ i, Nonempty (A i)) → Nonempty (∀ i, A i))
    {α : Type u} (𝒜 : Set (Set α)) (hdisjoint : 𝒜.PairwiseDisjoint id)
    (hnonempty : ∀ A ∈ 𝒜, A.Nonempty) : ∃ C, 𝒜.IsChoiceSet C := by
  obtain ⟨choice⟩ := hpi (fun A : 𝒜 ↦ A) fun A ↦ (hnonempty A A.property).to_subtype
  refine ⟨Set.range (fun A : 𝒜 ↦ choice A), ?_⟩
  apply Set.IsChoiceSet.mk
  · rintro x ⟨A, rfl⟩
    exact Set.mem_sUnion_of_mem (choice A).property A.property
  · intro A hA
    let A' : 𝒜 := ⟨A, hA⟩
    refine ⟨choice A', ⟨⟨A', rfl⟩, (choice A').property⟩, ?_⟩
    rintro x ⟨⟨B, rfl⟩, hxA⟩
    have hBA : (B : Set α) = A := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisjoint B.property hA hne) (choice B).property hxA
    have : B = A' := Subtype.ext hBA
    subst B
    rfl

/- A member of a dependent Cartesian product gives a member of each factor;
this direction is constructive and does not use a choice principle. -/
#check Classical.nonempty_pi.mp

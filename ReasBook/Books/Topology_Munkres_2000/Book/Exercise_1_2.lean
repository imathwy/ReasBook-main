module

public import Mathlib.Data.Set.Prod

public section

/-- Helper for Exercise 1.2 (1), clause (a): If `A` is a subset of both `B` and `C`,
then `A` is a subset of `B ∪ C`. -/
theorem subset_union_of_subset_both {α : Type u} {A B C : Set α}
    (hB : A ⊆ B) (hC : A ⊆ C) : A ⊆ B ∪ C := by
  -- Send each element through the first inclusion and then into the union.
  intro x hx
  have hxBoth : x ∈ B ∧ x ∈ C := ⟨hB hx, hC hx⟩
  exact Or.inl hxBoth.1

/-- Helper for Exercise 1.2 (2), clause (a): Inclusion in a union need not imply
inclusion in both summands. -/
theorem subset_union_not_imply_subset_both :
    ({true} : Set Bool) ⊆ ({true} : Set Bool) ∪ (∅ : Set Bool) ∧
      ¬(({true} : Set Bool) ⊆ ({true} : Set Bool) ∧
        ({true} : Set Bool) ⊆ (∅ : Set Bool)) := by
  -- The singleton lies in the union, but its element cannot lie in the empty set.
  simp

/-- Helper for Exercise 1.2 (3), clause (b): If `A` is a subset of either `B` or `C`,
then `A` is a subset of `B ∪ C`. -/
theorem subset_union_of_subset_either {α : Type u} {A B C : Set α}
    (h : A ⊆ B ∨ A ⊆ C) : A ⊆ B ∪ C := by
  -- Split according to which component contains all of `A`.
  rcases h with hB | hC
  · exact fun _ hx ↦ Or.inl (hB hx)
  · exact fun _ hx ↦ Or.inr (hC hx)

/-- Helper for Exercise 1.2 (4), clause (b): Inclusion in a union need not imply
inclusion in either summand. -/
theorem subset_union_not_imply_subset_either :
    ({true, false} : Set Bool) ⊆ ({true} : Set Bool) ∪ ({false} : Set Bool) ∧
      ¬(({true, false} : Set Bool) ⊆ ({true} : Set Bool) ∨
        ({true, false} : Set Bool) ⊆ ({false} : Set Bool)) := by
  -- Each Boolean belongs to the union, while neither singleton contains both.
  constructor
  · intro x hx
    simp_all
  · simp

/- Exercise 1.2 (5), clause (c): Inclusion in an intersection is equivalent
to inclusion in both factors. -/
#check Set.subset_inter_iff

/-- Helper for Exercise 1.2 (6), clause (d): Inclusion in an intersection implies
inclusion in at least one factor. -/
theorem subset_either_of_subset_inter {α : Type u} {A B C : Set α}
    (h : A ⊆ B ∩ C) : A ⊆ B ∨ A ⊆ C := by
  -- Project the first component of intersection membership.
  exact Or.inl fun _ hx ↦ (h hx).1

/-- Helper for Exercise 1.2 (7), clause (d): Inclusion in one factor need not imply
inclusion in the intersection. -/
theorem subset_inter_not_of_subset_either :
    (({true} : Set Bool) ⊆ ({true} : Set Bool) ∨
      ({true} : Set Bool) ⊆ (∅ : Set Bool)) ∧
      ¬({true} : Set Bool) ⊆ ({true} : Set Bool) ∩ (∅ : Set Bool) := by
  -- The singleton is contained in the first factor but not in the intersection.
  simp

/-- Helper for Exercise 1.2 (8), clause (e): The set `A \ (A \ B)` is always a subset
of `B`. -/
theorem sdiff_sdiff_self_subset {α : Type u} (A B : Set α) :
    A \ (A \ B) ⊆ B := by
  -- Otherwise membership in `A` and nonmembership in `B` would place the element in `A \ B`.
  intro x hx
  by_contra hxB
  exact hx.2 ⟨hx.1, hxB⟩

/-- Helper for Exercise 1.2 (9), clause (e): The equality `A \ (A \ B) = B` can fail. -/
theorem sdiff_sdiff_self_ne_counterexample :
    (∅ : Set Bool) \ ((∅ : Set Bool) \ ({true} : Set Bool)) ≠
      ({true} : Set Bool) := by
  -- The left side is empty, whereas the right side contains `true`.
  simp

/-- Helper for Exercise 1.2 (10), clause (f): The set `A \ B` is always a subset of
`A \ (B \ A)`. -/
theorem sdiff_subset_sdiff_reverse {α : Type u} (A B : Set α) :
    A \ B ⊆ A \ (B \ A) := by
  -- An element of `A` cannot also belong to `B \ A`.
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxBA
  exact hxBA.2 hx.1

/-- Helper for Exercise 1.2 (11), clause (f): The equality
`A \ (B \ A) = A \ B` can fail. -/
theorem sdiff_reverse_ne_counterexample :
    ({true} : Set Bool) \ (({true} : Set Bool) \ ({true} : Set Bool)) ≠
      ({true} : Set Bool) \ ({true} : Set Bool) := by
  -- The outer difference removes nothing on the left, while the right side is empty.
  simp

/- Exercise 1.2 (12), clause (g): Intersection distributes over set
difference in the stated form. -/
#check Set.inter_sdiff_distrib_left

/-- Helper for Exercise 1.2 (13), clause (h): The difference
`(A ∪ B) \ (A ∪ C)` is a subset of `A ∪ (B \ C)`. -/
theorem union_sdiff_difference_subset {α : Type u} (A B C : Set α) :
    (A ∪ B) \ (A ∪ C) ⊆ A ∪ (B \ C) := by
  -- The `A` branch is impossible, so a surviving element comes from `B \ C`.
  intro x hx
  rcases hx.1 with hxA | hxB
  · exact False.elim (hx.2 (Or.inl hxA))
  · refine Or.inr ⟨hxB, ?_⟩
    intro hxC
    exact hx.2 (Or.inr hxC)

/-- Helper for Exercise 1.2 (14), clause (h): The proposed equality fails, and the
opposite inclusion can fail. -/
theorem union_sdiff_ne_counterexample :
    ({true} : Set Bool) ∪ ((∅ : Set Bool) \ (∅ : Set Bool)) ≠
        (({true} : Set Bool) ∪ (∅ : Set Bool)) \
          (({true} : Set Bool) ∪ (∅ : Set Bool)) ∧
      ¬(({true} : Set Bool) ∪ ((∅ : Set Bool) \ (∅ : Set Bool)) ⊆
        (({true} : Set Bool) ∪ (∅ : Set Bool)) \
          (({true} : Set Bool) ∪ (∅ : Set Bool))) := by
  -- The proposed left side is the singleton and the right side is empty.
  simp

/- Exercise 1.2 (15), clause (i): The union of `A ∩ B` and `A \ B` is `A`. -/
#check Set.inter_union_sdiff

/- Exercise 1.2 (16), clause (j): Componentwise inclusions induce inclusion
of Cartesian products. -/
#check Set.prod_mono

/-- Helper for Exercise 1.2 (17), clause (k): Inclusion of Cartesian products need not
imply both componentwise inclusions when a factor is empty. -/
theorem prod_subset_not_imply_components :
    (({true} : Set Bool) ×ˢ (∅ : Set Bool)) ⊆
        ((∅ : Set Bool) ×ˢ (∅ : Set Bool)) ∧
      ¬(({true} : Set Bool) ⊆ (∅ : Set Bool) ∧
        (∅ : Set Bool) ⊆ (∅ : Set Bool)) := by
  -- Both products are empty, but the first component singleton is not empty.
  simp

/-- Helper for Exercise 1.2 (18), clause (l): For nonempty `A` and `B`, inclusion of
`A ×ˢ B` in `C ×ˢ D` implies both componentwise inclusions. -/
theorem prod_subset_prod_converse_of_nonempty {α : Type u} {β : Type v}
    {A C : Set α} {B D : Set β} (hA : A.Nonempty) (hB : B.Nonempty)
    (h : A ×ˢ B ⊆ C ×ˢ D) : A ⊆ C ∧ B ⊆ D := by
  -- Fix one element in each nonempty factor to test the other coordinate.
  rcases hA with ⟨a₀, ha₀⟩
  rcases hB with ⟨b₀, hb₀⟩
  constructor
  · intro a ha
    have hab : (a, b₀) ∈ A ×ˢ B := ⟨ha, hb₀⟩
    exact (h hab).1
  · intro b hb
    have hab : (a₀, b) ∈ A ×ˢ B := ⟨ha₀, hb⟩
    exact (h hab).2

/-- Helper for Exercise 1.2 (19), clause (m): The union of two Cartesian products is a
subset of the product of the corresponding unions. -/
theorem prod_union_subset_union_prod {α : Type u} {β : Type v}
    (A C : Set α) (B D : Set β) :
    (A ×ˢ B) ∪ (C ×ˢ D) ⊆ (A ∪ C) ×ˢ (B ∪ D) := by
  -- Each source product supplies matching component memberships in the unions.
  intro p hp
  rcases hp with hpAB | hpCD
  · exact ⟨Or.inl hpAB.1, Or.inl hpAB.2⟩
  · exact ⟨Or.inr hpCD.1, Or.inr hpCD.2⟩

/-- Helper for Exercise 1.2 (20), clause (m): The product of unions can contain a mixed
pair absent from the union of the two products. -/
theorem union_prod_ne_prod_union_counterexample :
    (({true} : Set Bool) ×ˢ ({true} : Set Bool)) ∪
          (({false} : Set Bool) ×ˢ ({false} : Set Bool)) ≠
        (({true} : Set Bool) ∪ ({false} : Set Bool)) ×ˢ
          (({true} : Set Bool) ∪ ({false} : Set Bool)) ∧
      ¬((({true} : Set Bool) ∪ ({false} : Set Bool)) ×ˢ
          (({true} : Set Bool) ∪ ({false} : Set Bool)) ⊆
        (({true} : Set Bool) ×ˢ ({true} : Set Bool)) ∪
          (({false} : Set Bool) ×ˢ ({false} : Set Bool))) := by
  -- The mixed pair `(true, false)` belongs only to the product of unions.
  constructor
  · intro hEq
    have hMixed : (true, false) ∈
        (({true} : Set Bool) ∪ ({false} : Set Bool)) ×ˢ
          (({true} : Set Bool) ∪ ({false} : Set Bool)) := by
      simp
    have hUnion := hEq.symm.subset hMixed
    simp at hUnion
  · intro hSubset
    have hMixed : (true, false) ∈
        (({true} : Set Bool) ∪ ({false} : Set Bool)) ×ˢ
          (({true} : Set Bool) ∪ ({false} : Set Bool)) := by
      simp
    have hUnion := hSubset hMixed
    simp at hUnion

/- Exercise 1.2 (21), clause (n): Intersection distributes across Cartesian
products componentwise. -/
#check Set.prod_inter_prod

/-- Helper for Exercise 1.2 (22), clause (o): Cartesian product with a set difference
is the corresponding difference of Cartesian products. -/
theorem prod_sdiff_right {α : Type u} {β : Type v}
    (A : Set α) (B C : Set β) :
    A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  -- Normalize both sides to componentwise membership and compare propositions.
  ext p
  constructor
  · intro hp
    refine ⟨⟨hp.1, hp.2.1⟩, ?_⟩
    intro hpAC
    exact hp.2.2 hpAC.2
  · intro hp
    refine ⟨hp.1.1, hp.1.2, ?_⟩
    intro hpC
    exact hp.2 ⟨hp.1.1, hpC⟩

/-- Helper for Exercise 1.2 (23), clause (p): The product of two set differences equals
the iterated difference stated in the exercise. -/
theorem sdiff_prod_sdiff {α : Type u} {β : Type v}
    (A B : Set α) (C D : Set β) :
    (A \ B) ×ˢ (C \ D) = ((A ×ˢ C) \ (B ×ˢ C)) \ (A ×ˢ D) := by
  -- Expand the iterated difference and transfer each coordinate condition directly.
  ext p
  constructor
  · intro hp
    refine ⟨⟨⟨hp.1.1, hp.2.1⟩, ?_⟩, ?_⟩
    · intro hpBC
      exact hp.1.2 hpBC.1
    · intro hpAD
      exact hp.2.2 hpAD.2
  · intro hp
    refine ⟨⟨hp.1.1.1, ?_⟩, ⟨hp.1.1.2, ?_⟩⟩
    · intro hpB
      exact hp.1.2 ⟨hpB, hp.1.1.2⟩
    · intro hpD
      exact hp.2 ⟨hp.1.1.1, hpD⟩

/-- Helper for Exercise 1.2 (24), clause (q): The product of the componentwise
differences is contained in the difference of the products. -/
theorem prod_sdiff_subset {α : Type u} {β : Type v}
    (A C : Set α) (B D : Set β) :
    (A \ C) ×ˢ (B \ D) ⊆ (A ×ˢ B) \ (C ×ˢ D) := by
  -- Component membership gives the larger product, while the first exclusion
  -- refutes the removed product.
  intro p hp
  refine ⟨⟨hp.1.1, hp.2.1⟩, ?_⟩
  intro hpCD
  exact hp.1.2 hpCD.1

/-- Helper for Exercise 1.2 (25), clause (q): The difference of products can contain a
pair absent from the product of the componentwise differences. -/
theorem prod_sdiff_ne_counterexample :
    (({true} : Set Bool) ×ˢ ({true} : Set Bool)) \
          (({false} : Set Bool) ×ˢ ({true} : Set Bool)) ≠
        (({true} : Set Bool) \ ({false} : Set Bool)) ×ˢ
          (({true} : Set Bool) \ ({true} : Set Bool)) ∧
      ¬((({true} : Set Bool) ×ˢ ({true} : Set Bool)) \
          (({false} : Set Bool) ×ˢ ({true} : Set Bool)) ⊆
        (({true} : Set Bool) \ ({false} : Set Bool)) ×ˢ
          (({true} : Set Bool) \ ({true} : Set Bool))) := by
  -- The pair `(true, true)` survives the product difference but not the
  -- componentwise difference product.
  constructor
  · intro hEq
    have hLeft : (true, true) ∈
        (({true} : Set Bool) ×ˢ ({true} : Set Bool)) \
          (({false} : Set Bool) ×ˢ ({true} : Set Bool)) := by
      simp
    have hRight := hEq.subset hLeft
    simp at hRight
  · intro hSubset
    have hLeft : (true, true) ∈
        (({true} : Set Bool) ×ˢ ({true} : Set Bool)) \
          (({false} : Set Bool) ×ˢ ({true} : Set Bool)) := by
      simp
    have hRight := hSubset hLeft
    simp at hRight

/-- Helper for Exercise 1.2: The preceding clause results give the complete determination of
the proposed set-theoretic statements and their valid replacement implications. -/
theorem completeSetStatementDetermination :
    (∀ {α : Type u} {A B C : Set α}, A ⊆ B → A ⊆ C → A ⊆ B ∪ C) ∧
      (({true} : Set Bool) ⊆ ({true} : Set Bool) ∪ (∅ : Set Bool) ∧
        ¬(({true} : Set Bool) ⊆ ({true} : Set Bool) ∧
          ({true} : Set Bool) ⊆ (∅ : Set Bool))) ∧
      (∀ {α : Type u} {A B C : Set α}, A ⊆ B ∨ A ⊆ C → A ⊆ B ∪ C) ∧
      (({true, false} : Set Bool) ⊆ ({true} : Set Bool) ∪ ({false} : Set Bool) ∧
        ¬(({true, false} : Set Bool) ⊆ ({true} : Set Bool) ∨
          ({true, false} : Set Bool) ⊆ ({false} : Set Bool))) ∧
      (∀ {α : Type u} {A B C : Set α}, A ⊆ B ∩ C ↔ A ⊆ B ∧ A ⊆ C) ∧
      (∀ {α : Type u} {A B C : Set α}, A ⊆ B ∩ C → A ⊆ B ∨ A ⊆ C) ∧
      ((({true} : Set Bool) ⊆ ({true} : Set Bool) ∨
          ({true} : Set Bool) ⊆ (∅ : Set Bool)) ∧
        ¬({true} : Set Bool) ⊆ ({true} : Set Bool) ∩ (∅ : Set Bool)) ∧
      (∀ {α : Type u} (A B : Set α), A \ (A \ B) ⊆ B) ∧
      ((∅ : Set Bool) \ ((∅ : Set Bool) \ ({true} : Set Bool)) ≠
        ({true} : Set Bool)) ∧
      (∀ {α : Type u} (A B : Set α), A \ B ⊆ A \ (B \ A)) ∧
      (({true} : Set Bool) \ (({true} : Set Bool) \ ({true} : Set Bool)) ≠
        ({true} : Set Bool) \ ({true} : Set Bool)) ∧
      (∀ {α : Type u} (A B C : Set α), A ∩ (B \ C) = (A ∩ B) \ (A ∩ C)) ∧
      (∀ {α : Type u} (A B C : Set α), (A ∪ B) \ (A ∪ C) ⊆ A ∪ (B \ C)) ∧
      ((({true} : Set Bool) ∪ ((∅ : Set Bool) \ (∅ : Set Bool)) ≠
          (({true} : Set Bool) ∪ (∅ : Set Bool)) \
            (({true} : Set Bool) ∪ (∅ : Set Bool))) ∧
        ¬(({true} : Set Bool) ∪ ((∅ : Set Bool) \ (∅ : Set Bool)) ⊆
          (({true} : Set Bool) ∪ (∅ : Set Bool)) \
            (({true} : Set Bool) ∪ (∅ : Set Bool)))) ∧
      (∀ {α : Type u} (A B : Set α), A ∩ B ∪ A \ B = A) ∧
      (∀ {α : Type u} {β : Type v} {A C : Set α} {B D : Set β},
        A ⊆ C → B ⊆ D → A ×ˢ B ⊆ C ×ˢ D) ∧
      ((({true} : Set Bool) ×ˢ (∅ : Set Bool)) ⊆
          ((∅ : Set Bool) ×ˢ (∅ : Set Bool)) ∧
        ¬(({true} : Set Bool) ⊆ (∅ : Set Bool) ∧
          (∅ : Set Bool) ⊆ (∅ : Set Bool))) ∧
      (∀ {α : Type u} {β : Type v} {A C : Set α} {B D : Set β},
        A.Nonempty → B.Nonempty → A ×ˢ B ⊆ C ×ˢ D → A ⊆ C ∧ B ⊆ D) ∧
      (∀ {α : Type u} {β : Type v} (A C : Set α) (B D : Set β),
        (A ×ˢ B) ∪ (C ×ˢ D) ⊆ (A ∪ C) ×ˢ (B ∪ D)) ∧
      (((( {true} : Set Bool) ×ˢ ({true} : Set Bool)) ∪
            (({false} : Set Bool) ×ˢ ({false} : Set Bool)) ≠
          (({true} : Set Bool) ∪ ({false} : Set Bool)) ×ˢ
            (({true} : Set Bool) ∪ ({false} : Set Bool))) ∧
        ¬((({true} : Set Bool) ∪ ({false} : Set Bool)) ×ˢ
            (({true} : Set Bool) ∪ ({false} : Set Bool)) ⊆
          (({true} : Set Bool) ×ˢ ({true} : Set Bool)) ∪
            (({false} : Set Bool) ×ˢ ({false} : Set Bool)))) ∧
      (∀ {α : Type u} {β : Type v} (A C : Set α) (B D : Set β),
        A ×ˢ B ∩ C ×ˢ D = (A ∩ C) ×ˢ (B ∩ D)) ∧
      (∀ {α : Type u} {β : Type v} (A : Set α) (B C : Set β),
        A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C)) ∧
      (∀ {α : Type u} {β : Type v} (A B : Set α) (C D : Set β),
        (A \ B) ×ˢ (C \ D) = ((A ×ˢ C) \ (B ×ˢ C)) \ (A ×ˢ D)) ∧
      (∀ {α : Type u} {β : Type v} (A C : Set α) (B D : Set β),
        (A \ C) ×ˢ (B \ D) ⊆ (A ×ˢ B) \ (C ×ˢ D)) ∧
      (((( {true} : Set Bool) ×ˢ ({true} : Set Bool)) \
            (({false} : Set Bool) ×ˢ ({true} : Set Bool)) ≠
          (({true} : Set Bool) \ ({false} : Set Bool)) ×ˢ
            (({true} : Set Bool) \ ({true} : Set Bool))) ∧
        ¬((({true} : Set Bool) ×ˢ ({true} : Set Bool)) \
            (({false} : Set Bool) ×ˢ ({true} : Set Bool)) ⊆
          (({true} : Set Bool) \ ({false} : Set Bool)) ×ˢ
            (({true} : Set Bool) \ ({true} : Set Bool)))) := by
  -- Package the universal implications, identities, and counterexamples proved above.
  exact ⟨subset_union_of_subset_both, subset_union_not_imply_subset_both,
    subset_union_of_subset_either, subset_union_not_imply_subset_either,
    Set.subset_inter_iff, subset_either_of_subset_inter,
    subset_inter_not_of_subset_either, sdiff_sdiff_self_subset,
    sdiff_sdiff_self_ne_counterexample, sdiff_subset_sdiff_reverse,
    sdiff_reverse_ne_counterexample, Set.inter_sdiff_distrib_left,
    union_sdiff_difference_subset, union_sdiff_ne_counterexample,
    Set.inter_union_sdiff, Set.prod_mono, prod_subset_not_imply_components,
    prod_subset_prod_converse_of_nonempty, prod_union_subset_union_prod,
    union_prod_ne_prod_union_counterexample,
    (fun A C B D ↦ Set.prod_inter_prod),
    prod_sdiff_right, sdiff_prod_sdiff, prod_sdiff_subset,
    prod_sdiff_ne_counterexample⟩

/-- Exercise 1.2 theorem suite: the complete determination of all clauses. -/
theorem «Exercise_1_2 theorem suite» :
    (∀ {α : Type u} {A B C : Set α}, A ⊆ B → A ⊆ C → A ⊆ B ∪ C) ∧
      (({true} : Set Bool) ⊆ ({true} : Set Bool) ∪ (∅ : Set Bool) ∧
        ¬(({true} : Set Bool) ⊆ ({true} : Set Bool) ∧
          ({true} : Set Bool) ⊆ (∅ : Set Bool))) ∧
      (∀ {α : Type u} {A B C : Set α}, A ⊆ B ∨ A ⊆ C → A ⊆ B ∪ C) ∧
      (({true, false} : Set Bool) ⊆ ({true} : Set Bool) ∪ ({false} : Set Bool) ∧
        ¬(({true, false} : Set Bool) ⊆ ({true} : Set Bool) ∨
          ({true, false} : Set Bool) ⊆ ({false} : Set Bool))) ∧
      (∀ {α : Type u} {A B C : Set α}, A ⊆ B ∩ C ↔ A ⊆ B ∧ A ⊆ C) ∧
      (∀ {α : Type u} {A B C : Set α}, A ⊆ B ∩ C → A ⊆ B ∨ A ⊆ C) ∧
      ((({true} : Set Bool) ⊆ ({true} : Set Bool) ∨
          ({true} : Set Bool) ⊆ (∅ : Set Bool)) ∧
        ¬({true} : Set Bool) ⊆ ({true} : Set Bool) ∩ (∅ : Set Bool)) ∧
      (∀ {α : Type u} (A B : Set α), A \ (A \ B) ⊆ B) ∧
      ((∅ : Set Bool) \ ((∅ : Set Bool) \ ({true} : Set Bool)) ≠
        ({true} : Set Bool)) ∧
      (∀ {α : Type u} (A B : Set α), A \ B ⊆ A \ (B \ A)) ∧
      (({true} : Set Bool) \ (({true} : Set Bool) \ ({true} : Set Bool)) ≠
        ({true} : Set Bool) \ ({true} : Set Bool)) ∧
      (∀ {α : Type u} (A B C : Set α), A ∩ (B \ C) = (A ∩ B) \ (A ∩ C)) ∧
      (∀ {α : Type u} (A B C : Set α), (A ∪ B) \ (A ∪ C) ⊆ A ∪ (B \ C)) ∧
      ((({true} : Set Bool) ∪ ((∅ : Set Bool) \ (∅ : Set Bool)) ≠
          (({true} : Set Bool) ∪ (∅ : Set Bool)) \
            (({true} : Set Bool) ∪ (∅ : Set Bool))) ∧
        ¬(({true} : Set Bool) ∪ ((∅ : Set Bool) \ (∅ : Set Bool)) ⊆
          (({true} : Set Bool) ∪ (∅ : Set Bool)) \
            (({true} : Set Bool) ∪ (∅ : Set Bool)))) ∧
      (∀ {α : Type u} (A B : Set α), A ∩ B ∪ A \ B = A) ∧
      (∀ {α : Type u} {β : Type v} {A C : Set α} {B D : Set β},
        A ⊆ C → B ⊆ D → A ×ˢ B ⊆ C ×ˢ D) ∧
      ((({true} : Set Bool) ×ˢ (∅ : Set Bool)) ⊆
          ((∅ : Set Bool) ×ˢ (∅ : Set Bool)) ∧
        ¬(({true} : Set Bool) ⊆ (∅ : Set Bool) ∧
          (∅ : Set Bool) ⊆ (∅ : Set Bool))) ∧
      (∀ {α : Type u} {β : Type v} {A C : Set α} {B D : Set β},
        A.Nonempty → B.Nonempty → A ×ˢ B ⊆ C ×ˢ D → A ⊆ C ∧ B ⊆ D) ∧
      (∀ {α : Type u} {β : Type v} (A C : Set α) (B D : Set β),
        (A ×ˢ B) ∪ (C ×ˢ D) ⊆ (A ∪ C) ×ˢ (B ∪ D)) ∧
      (((( {true} : Set Bool) ×ˢ ({true} : Set Bool)) ∪
            (({false} : Set Bool) ×ˢ ({false} : Set Bool)) ≠
          (({true} : Set Bool) ∪ ({false} : Set Bool)) ×ˢ
            (({true} : Set Bool) ∪ ({false} : Set Bool))) ∧
        ¬((({true} : Set Bool) ∪ ({false} : Set Bool)) ×ˢ
            (({true} : Set Bool) ∪ ({false} : Set Bool)) ⊆
          (({true} : Set Bool) ×ˢ ({true} : Set Bool)) ∪
            (({false} : Set Bool) ×ˢ ({false} : Set Bool)))) ∧
      (∀ {α : Type u} {β : Type v} (A C : Set α) (B D : Set β),
        A ×ˢ B ∩ C ×ˢ D = (A ∩ C) ×ˢ (B ∩ D)) ∧
      (∀ {α : Type u} {β : Type v} (A : Set α) (B C : Set β),
        A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C)) ∧
      (∀ {α : Type u} {β : Type v} (A B : Set α) (C D : Set β),
        (A \ B) ×ˢ (C \ D) = ((A ×ˢ C) \ (B ×ˢ C)) \ (A ×ˢ D)) ∧
      (∀ {α : Type u} {β : Type v} (A C : Set α) (B D : Set β),
        (A \ C) ×ˢ (B \ D) ⊆ (A ×ˢ B) \ (C ×ˢ D)) ∧
      (((( {true} : Set Bool) ×ˢ ({true} : Set Bool)) \
            (({false} : Set Bool) ×ˢ ({true} : Set Bool)) ≠
          (({true} : Set Bool) \ ({false} : Set Bool)) ×ˢ
            (({true} : Set Bool) \ ({true} : Set Bool))) ∧
        ¬((({true} : Set Bool) ×ˢ ({true} : Set Bool)) \
            (({false} : Set Bool) ×ˢ ({true} : Set Bool)) ⊆
          (({true} : Set Bool) \ ({false} : Set Bool)) ×ˢ
            (({true} : Set Bool) \ ({true} : Set Bool)))) := by
  -- Expose the completed aggregate proof under the declaration name expected by the item.
  exact completeSetStatementDetermination

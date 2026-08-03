module

public import Topology_Munkres_2000.Book.Example_12_1.ThreePointTopology

public section

open Set

universe u v

/- Exercise 13.4 (1). The intersection of the collections of open sets of a family of
topologies is the collection of open sets of their supremum. -/
#check (setOf_isOpen_iSup :
  ∀ {X : Type u} {ι : Type v} {t : ι → TopologicalSpace X},
    {s | (⨆ i, t i).IsOpen s} = ⋂ i, {s | (t i).IsOpen s})

namespace ThreePointTopology

/-- Helper for Exercise 13.4: the two displayed two-point open sets intersect in `{b}`. -/
lemma pairInterPair_eq_singleton_b :
    ({.a, .b} : Set ThreePoint) ∩ {.b, .c} = {.b} := by
  -- Check membership pointwise on the three elements of `ThreePoint`.
  ext x
  cases x <;> simp

/-- Helper for Exercise 13.4: `{b}` does not belong to the first displayed family. -/
lemma singleton_b_not_mem_openSets_aAndAB :
    ({.b} : Set ThreePoint) ∉ openSets .aAndAB := by
  -- Reduce membership to the displayed list and distinguish the candidate sets pointwise.
  rw [mem_openSets_aAndAB_iff]
  simp only [not_or]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hb := congrArg (fun s : Set ThreePoint ↦ ThreePoint.b ∈ s) h
    simp at hb
  · intro h
    have hb := congrArg (fun s : Set ThreePoint ↦ ThreePoint.b ∈ s) h
    simp at hb
  · intro h
    have ha := congrArg (fun s : Set ThreePoint ↦ ThreePoint.a ∈ s) h
    simp at ha
  · intro h
    have hc := congrArg (fun s : Set ThreePoint ↦ ThreePoint.c ∈ s) h
    simp at hc

/-- Helper for Exercise 13.4: `{b}` does not belong to the second displayed family. -/
lemma singleton_b_not_mem_openSets_aAndBC :
    ({.b} : Set ThreePoint) ∉ openSets .aAndBC := by
  -- Reduce membership to the displayed list and distinguish the candidate sets pointwise.
  rw [mem_openSets_aAndBC_iff]
  simp only [not_or]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hb := congrArg (fun s : Set ThreePoint ↦ ThreePoint.b ∈ s) h
    simp at hb
  · intro h
    have hb := congrArg (fun s : Set ThreePoint ↦ ThreePoint.b ∈ s) h
    simp at hb
  · intro h
    have hc := congrArg (fun s : Set ThreePoint ↦ ThreePoint.c ∈ s) h
    simp at hc
  · intro h
    have ha := congrArg (fun s : Set ThreePoint ↦ ThreePoint.a ∈ s) h
    simp at ha

end ThreePointTopology

open ThreePointTopology

/-- Exercise 13.4 (2). The union of two collections of open sets need not be the
collection of open sets of a topology. -/
theorem ThreePointTopology.openSets_union_not_topology :
    ¬ ∃ t : TopologicalSpace ThreePoint,
      t.IsOpen = openSets .aAndAB ∪ openSets .aAndBC := by
  rintro ⟨t, ht⟩
  -- The assumed union contains both two-point generators.
  have hab : t.IsOpen ({.a, .b} : Set ThreePoint) := by
    rw [ht]
    left
    rw [mem_openSets_aAndAB_iff]
    exact Or.inr (Or.inr (Or.inl rfl))
  have hbc : t.IsOpen ({.b, .c} : Set ThreePoint) := by
    rw [ht]
    right
    rw [mem_openSets_aAndBC_iff]
    exact Or.inr (Or.inr (Or.inl rfl))
  -- Closure under intersections would then make `{b}` open, which the union omits.
  have hb : t.IsOpen ({.b} : Set ThreePoint) := by
    rw [← pairInterPair_eq_singleton_b]
    exact t.isOpen_inter _ _ hab hbc
  rw [ht] at hb
  rcases hb with hb | hb
  · exact singleton_b_not_mem_openSets_aAndAB hb
  · exact singleton_b_not_mem_openSets_aAndBC hb

/- Exercise 13.4 (3). In Lean's reverse order on topologies, the infimum is the greatest
lower bound, hence the smallest topology whose open sets contain those of every member. -/
#check (isGLB_iInf :
  ∀ {X : Type u} {ι : Type v} {t : ι → TopologicalSpace X},
    IsGLB (Set.range t) (⨅ i, t i))

/- Exercise 13.4 (4). In Lean's reverse order on topologies, the supremum is the least
upper bound, hence the largest topology whose open sets are contained in every member. -/
#check (isLUB_iSup :
  ∀ {X : Type u} {ι : Type v} {t : ι → TopologicalSpace X},
    IsLUB (Set.range t) (⨆ i, t i))

namespace ThreePointTopology

/-- Helper for Exercise 13.4: subsets in which membership of `c` forces membership of `b`
are exactly the six sets occurring in the generated topology. -/
lemma c_mem_imp_b_mem_iff (s : Set ThreePoint) :
    (ThreePoint.c ∈ s → ThreePoint.b ∈ s) ↔
      s = ∅ ∨ s = {.a} ∨ s = {.b} ∨ s = {.a, .b} ∨ s = {.b, .c} ∨
        s = Set.univ := by
  constructor
  · intro h
    -- Split on membership of the three points and identify the possible subset extensionally.
    by_cases ha : ThreePoint.a ∈ s
    · by_cases hb : ThreePoint.b ∈ s
      · by_cases hc : ThreePoint.c ∈ s
        · right
          right
          right
          right
          right
          ext x
          cases x <;> simp [ha, hb, hc]
        · right
          right
          right
          left
          ext x
          cases x <;> simp [ha, hb, hc]
      · by_cases hc : ThreePoint.c ∈ s
        · exact False.elim (hb (h hc))
        · right
          left
          ext x
          cases x <;> simp [ha, hb, hc]
    · by_cases hb : ThreePoint.b ∈ s
      · by_cases hc : ThreePoint.c ∈ s
        · right
          right
          right
          right
          left
          ext x
          cases x <;> simp [ha, hb, hc]
        · right
          right
          left
          ext x
          cases x <;> simp [ha, hb, hc]
      · by_cases hc : ThreePoint.c ∈ s
        · exact False.elim (hb (h hc))
        · left
          ext x
          cases x <;> simp [ha, hb, hc]
  · intro hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Helper for Exercise 13.4: `{a}` is disjoint from `{b, c}`. -/
lemma singleton_a_inter_pair_bc_eq_empty :
    ({.a} : Set ThreePoint) ∩ {.b, .c} = ∅ := by
  -- Check membership pointwise on the three elements of `ThreePoint`.
  ext x
  cases x <;> simp

/-- Helper for Exercise 13.4: the topology generated by the two displayed families consists
exactly of the sets for which membership of `c` forces membership of `b`. -/
lemma generateOpen_union_iff (s : Set ThreePoint) :
    TopologicalSpace.GenerateOpen (openSets .aAndAB ∪ openSets .aAndBC) s ↔
      (ThreePoint.c ∈ s → ThreePoint.b ∈ s) := by
  constructor
  · intro hs
    -- The implication is preserved by every constructor of `GenerateOpen`.
    induction hs with
    | basic s hs =>
        rcases hs with hs | hs
        · rw [mem_openSets_aAndAB_iff] at hs
          rcases hs with rfl | rfl | rfl | rfl <;> simp
        · rw [mem_openSets_aAndBC_iff] at hs
          rcases hs with rfl | rfl | rfl | rfl <;> simp
    | univ =>
        simp
    | inter s t hs ht ihs iht =>
        intro hc
        exact ⟨ihs hc.1, iht hc.2⟩
    | sUnion S hS ih =>
        intro hc
        rcases hc with ⟨u, huS, hcu⟩
        exact ⟨u, huS, ih u huS hcu⟩
  · intro h
    -- Classify the subset, then construct each of the six possibilities from generators.
    rw [c_mem_imp_b_mem_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← singleton_a_inter_pair_bc_eq_empty]
      exact TopologicalSpace.GenerateOpen.inter _ _
        (TopologicalSpace.GenerateOpen.basic ({ThreePoint.a} : Set ThreePoint)
          (Or.inl ((mem_openSets_aAndAB_iff _).mpr (Or.inr (Or.inl rfl)))))
        (TopologicalSpace.GenerateOpen.basic ({ThreePoint.b, ThreePoint.c} : Set ThreePoint)
          (Or.inr ((mem_openSets_aAndBC_iff _).mpr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact TopologicalSpace.GenerateOpen.basic ({ThreePoint.a} : Set ThreePoint)
        (Or.inl ((mem_openSets_aAndAB_iff _).mpr (Or.inr (Or.inl rfl))))
    · rw [← pairInterPair_eq_singleton_b]
      exact TopologicalSpace.GenerateOpen.inter _ _
        (TopologicalSpace.GenerateOpen.basic ({ThreePoint.a, ThreePoint.b} : Set ThreePoint)
          (Or.inl ((mem_openSets_aAndAB_iff _).mpr (Or.inr (Or.inr (Or.inl rfl))))))
        (TopologicalSpace.GenerateOpen.basic ({ThreePoint.b, ThreePoint.c} : Set ThreePoint)
          (Or.inr ((mem_openSets_aAndBC_iff _).mpr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact TopologicalSpace.GenerateOpen.basic ({ThreePoint.a, ThreePoint.b} : Set ThreePoint)
        (Or.inl ((mem_openSets_aAndAB_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact TopologicalSpace.GenerateOpen.basic ({ThreePoint.b, ThreePoint.c} : Set ThreePoint)
        (Or.inr ((mem_openSets_aAndBC_iff _).mpr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact TopologicalSpace.GenerateOpen.univ

/-- Exercise 13.4 (5). The smallest topology containing the two displayed topologies
on `{a, b, c}` has exactly the six listed open sets. -/
theorem isOpen_inf :
    (topology .aAndAB ⊓ topology .aAndBC).IsOpen =
      fun s ↦
        s = ∅ ∨ s = {.a} ∨ s = {.b} ∨ s = {.a, .b} ∨ s = {.b, .c} ∨
          s = Set.univ := by
  -- Route correction: `.bAndABAndBC` omits `{a}`, so it cannot normalize this infimum.
  -- Instead, combine the generators and use the intrinsic implication invariant.
  rw [topology_eq_generateFrom, topology_eq_generateFrom, ← generateFrom_union]
  funext s
  apply propext
  exact generateOpen_union_iff s |>.trans (c_mem_imp_b_mem_iff s)

/-- Exercise 13.4 (6). The largest topology contained in the two displayed topologies
on `{a, b, c}` has exactly the three listed open sets. -/
theorem isOpen_sup :
    (topology .aAndAB ⊔ topology .aAndBC).IsOpen =
      fun s ↦ s = ∅ ∨ s = {.a} ∨ s = Set.univ := by
  funext s
  apply propext
  -- Openness in the supremum is openness in both displayed topologies.
  refine _root_.isOpen_sup.trans ?_
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' := (isOpen_iff .aAndAB s).mp h₁
    have h₂' := (isOpen_iff .aAndBC s).mp h₂
    rw [mem_openSets_aAndAB_iff] at h₁'
    rw [mem_openSets_aAndBC_iff] at h₂'
    rcases h₁' with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · rcases h₂' with h | h | h | h
      · have ha := congrArg (fun u : Set ThreePoint ↦ ThreePoint.a ∈ u) h
        simp at ha
      · have hb := congrArg (fun u : Set ThreePoint ↦ ThreePoint.b ∈ u) h
        simp at hb
      · have ha := congrArg (fun u : Set ThreePoint ↦ ThreePoint.a ∈ u) h
        simp at ha
      · have hc := congrArg (fun u : Set ThreePoint ↦ ThreePoint.c ∈ u) h
        simp at hc
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact ⟨(isOpen_iff .aAndAB _).mpr ((mem_openSets_aAndAB_iff _).mpr (Or.inl rfl)),
        (isOpen_iff .aAndBC _).mpr ((mem_openSets_aAndBC_iff _).mpr (Or.inl rfl))⟩
    · exact ⟨(isOpen_iff .aAndAB _).mpr
          ((mem_openSets_aAndAB_iff _).mpr (Or.inr (Or.inl rfl))),
        (isOpen_iff .aAndBC _).mpr
          ((mem_openSets_aAndBC_iff _).mpr (Or.inr (Or.inl rfl)))⟩
    · exact ⟨(isOpen_iff .aAndAB _).mpr
          ((mem_openSets_aAndAB_iff _).mpr (Or.inr (Or.inr (Or.inr rfl)))),
        (isOpen_iff .aAndBC _).mpr
          ((mem_openSets_aAndBC_iff _).mpr (Or.inr (Or.inr (Or.inr rfl))))⟩

/-- Pointwise form of `isOpen_inf`. -/
@[simp]
theorem isOpen_inf_iff (s : Set ThreePoint) :
    (topology .aAndAB ⊓ topology .aAndBC).IsOpen s ↔
      s = ∅ ∨ s = {.a} ∨ s = {.b} ∨ s = {.a, .b} ∨ s = {.b, .c} ∨
        s = Set.univ := by
  rw [isOpen_inf]

/-- Pointwise form of `isOpen_sup`. -/
@[simp]
theorem isOpen_sup_iff (s : Set ThreePoint) :
    (topology .aAndAB ⊔ topology .aAndBC).IsOpen s ↔
      s = ∅ ∨ s = {.a} ∨ s = Set.univ := by
  rw [isOpen_sup]

end ThreePointTopology

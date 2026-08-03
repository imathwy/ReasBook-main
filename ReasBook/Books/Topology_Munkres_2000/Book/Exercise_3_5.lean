module

public import Topology_Munkres_2000.Book.Example_3_4
public import Mathlib.Tactic

public section

/-- The relation `S` consisting of pairs `(x, x + 1)` with `0 < x < 2`. -/
def unitStepRel (x y : ℝ) : Prop :=
  y = x + 1 ∧ 0 < x ∧ x < 2

/-- The relation `S'` in which two reals differ by an integer. -/
def integerDifferenceRel (x y : ℝ) : Prop :=
  ∃ n : ℤ, y - x = n

/-- Part (a) of Exercise 3.5: `S'` is an equivalence relation on the real line. -/
theorem integerDifferenceRel_equivalence : Equivalence integerDifferenceRel := by
  -- Integer differences are closed under zero, negation, and addition.
  refine ⟨?_, ?_, ?_⟩
  · intro x
    refine ⟨0, ?_⟩
    ring
  · intro x y hxy
    obtain ⟨n, hn⟩ := hxy
    refine ⟨-n, ?_⟩
    rw [Int.cast_neg]
    linarith
  · intro x y z hxy hyz
    obtain ⟨n, hn⟩ := hxy
    obtain ⟨m, hm⟩ := hyz
    refine ⟨n + m, ?_⟩
    rw [Int.cast_add]
    linarith

/-- Part (a) of Exercise 3.5: The relation `S'` contains `S`. -/
theorem unitStepRel_le_integerDifferenceRel :
    unitStepRel ≤ integerDifferenceRel := by
  -- Every generating step has integer difference one.
  intro x y hxy
  obtain ⟨rfl, _, _⟩ := hxy
  refine ⟨1, ?_⟩
  norm_num

/-- Part (a) of Exercise 3.5: The `S'`-class of `x` is the integer translate `x + ℤ`. -/
theorem integerDifferenceRel_class (x : ℝ) :
    {y | integerDifferenceRel x y} = Set.range (fun n : ℤ ↦ x + n) := by
  -- Extracting the integer difference gives exactly an integer translate.
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := hy
    refine ⟨n, ?_⟩
    linarith
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    ring

/-- Part (b) of Exercise 3.5: An arbitrary intersection of equivalence relations is an
equivalence relation. -/
theorem equivalence_iInter {A : Type u} {ι : Type v} (r : ι → A → A → Prop)
    (hr : ∀ i, Equivalence (r i)) :
    Equivalence (fun x y ↦ ∀ i, r i x y) := by
  -- Each equivalence-law is verified pointwise in the family.
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    exact (hr i).refl x
  · intro x y hxy i
    exact (hr i).symm (hxy i)
  · intro x y z hxy hyz i
    exact (hr i).trans (hxy i) (hyz i)

/-- The smallest equivalence relation containing `unitStepRel`. -/
def unitStepClosure : Setoid ℝ :=
  Relation.EqvGen.setoid unitStepRel

/-- Part (c) of Exercise 3.5: `T` is the intersection of all equivalence relations on `ℝ`
that contain `S`. -/
theorem unitStepClosure_eq_sInf :
    unitStepClosure = sInf {r : Setoid ℝ | unitStepRel ≤ r} :=
  Setoid.eqvGen_eq unitStepRel

/-- Helper for Exercise 3.5: unequal related points lie in `(0, 3)` and differ by an integer. -/
def unitStepBoundedIntegerRel (x y : ℝ) : Prop :=
  x = y ∨
    (x ∈ Set.Ioo (0 : ℝ) 3 ∧ y ∈ Set.Ioo (0 : ℝ) 3 ∧ integerDifferenceRel x y)

/-- Helper for Exercise 3.5: `unitStepBoundedIntegerRel` is an equivalence relation. -/
lemma unitStepBoundedIntegerRel_equivalence : Equivalence unitStepBoundedIntegerRel := by
  -- Equality handles the exterior singleton classes; the bounded integer part is stable inside.
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact Or.inl rfl
  · intro x y hxy
    rcases hxy with rfl | ⟨hx, hy, hxy⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hy, hx, integerDifferenceRel_equivalence.symm hxy⟩
  · intro x y z hxy hyz
    rcases hxy with rfl | ⟨hx, hy, hxy⟩
    · exact hyz
    · rcases hyz with rfl | ⟨_, hz, hyz⟩
      · exact Or.inr ⟨hx, hy, hxy⟩
      · exact Or.inr ⟨hx, hz, integerDifferenceRel_equivalence.trans hxy hyz⟩

/-- Helper for Exercise 3.5: the bounded integer-difference relation as a setoid. -/
def unitStepBoundedIntegerSetoid : Setoid ℝ where
  r := unitStepBoundedIntegerRel
  iseqv := unitStepBoundedIntegerRel_equivalence

/-- Helper for Exercise 3.5: every unit step belongs to the bounded integer-difference setoid. -/
lemma unitStepRel_le_boundedIntegerSetoid :
    unitStepRel ≤ unitStepBoundedIntegerSetoid := by
  -- A step beginning in `(0, 2)` has both endpoints in `(0, 3)`.
  intro x y hxy
  obtain ⟨hy, hx0, hx2⟩ := hxy
  right
  refine ⟨⟨hx0, ?_⟩, ⟨?_, ?_⟩, ⟨1, ?_⟩⟩
  · linarith
  · linarith
  · linarith
  · rw [hy]
    norm_num

/-- Helper for Exercise 3.5: the bounded integer-difference relation has the
displayed components. -/
lemma unitStepBoundedIntegerRel_iff_components (x y : ℝ) :
    unitStepBoundedIntegerRel x y ↔
      x = y ∨
        (x = 1 ∧ y = 2) ∨
        (x = 2 ∧ y = 1) ∨
        ∃ z ∈ Set.Ioo (0 : ℝ) 1, x ∈ ({z, z + 1, z + 2} : Set ℝ) ∧
          y ∈ ({z, z + 1, z + 2} : Set ℝ) := by
  constructor
  · intro hxy
    rcases hxy with hxy | ⟨⟨hx0, hx3⟩, ⟨hy0, hy3⟩, n, hn⟩
    · exact Or.inl hxy
    · have hnLowerReal : (-3 : ℝ) < n := by linarith
      have hnUpperReal : (n : ℝ) < 3 := by linarith
      have hnLower : (-3 : ℤ) < n := by exact_mod_cast hnLowerReal
      have hnUpper : n < (3 : ℤ) := by exact_mod_cast hnUpperReal
      have hnCases : n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases hnCases with rfl | rfl | rfl | rfl | rfl
      · right
        right
        right
        refine ⟨y, ⟨hy0, ?_⟩, ?_, ?_⟩
        · norm_num at hn
          linarith
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          right
          right
          norm_num at hn ⊢
          linarith
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          simp
      · norm_num at hn
        rcases lt_trichotomy x 2 with hx2 | rfl | hx2
        · right
          right
          right
          refine ⟨y, ⟨hy0, ?_⟩, ?_, ?_⟩
          · linarith
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            right
            left
            linarith
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            simp
        · right
          right
          left
          constructor
          · rfl
          · linarith
        · right
          right
          right
          refine ⟨y - 1, ⟨?_, ?_⟩, ?_, ?_⟩
          · linarith
          · linarith
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            right
            right
            linarith
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            right
            left
            ring
      · left
        norm_num at hn
        linarith
      · norm_num at hn
        rcases lt_trichotomy x 1 with hx1 | rfl | hx1
        · right
          right
          right
          refine ⟨x, ⟨hx0, hx1⟩, ?_, ?_⟩
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            simp
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            right
            left
            linarith
        · right
          left
          constructor
          · rfl
          · linarith
        · right
          right
          right
          refine ⟨x - 1, ⟨?_, ?_⟩, ?_, ?_⟩
          · linarith
          · linarith
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            right
            left
            ring
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            right
            right
            linarith
      · right
        right
        right
        refine ⟨x, ⟨hx0, ?_⟩, ?_, ?_⟩
        · norm_num at hn
          linarith
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          simp
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          right
          right
          norm_num at hn ⊢
          linarith
  · intro hxy
    rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨z, ⟨hz0, hz1⟩, hx, hy⟩
    · exact Or.inl rfl
    · right
      refine ⟨?_, ?_, 1, ?_⟩
      · norm_num
      · norm_num
      · norm_num
    · right
      refine ⟨?_, ?_, -1, ?_⟩
      · norm_num
      · norm_num
      · norm_num
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl
      · rcases hy with rfl | rfl | rfl
        · exact Or.inl rfl
        · right
          refine ⟨⟨hz0, ?_⟩, ⟨?_, ?_⟩, 1, ?_⟩
          · linarith
          · linarith
          · linarith
          · norm_num
        · right
          refine ⟨⟨hz0, ?_⟩, ⟨?_, ?_⟩, 2, ?_⟩
          · linarith
          · linarith
          · linarith
          · norm_num
      · rcases hy with rfl | rfl | rfl
        · right
          refine ⟨⟨?_, ?_⟩, ⟨hz0, ?_⟩, -1, ?_⟩
          · linarith
          · linarith
          · linarith
          · norm_num
        · exact Or.inl rfl
        · right
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, 1, ?_⟩
          · linarith
          · linarith
          · linarith
          · linarith
          · norm_num
      · rcases hy with rfl | rfl | rfl
        · right
          refine ⟨⟨?_, ?_⟩, ⟨hz0, ?_⟩, -2, ?_⟩
          · linarith
          · linarith
          · linarith
          · norm_num
        · right
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, -1, ?_⟩
          · linarith
          · linarith
          · linarith
          · linarith
          · norm_num
        · exact Or.inl rfl

/-- Helper for Exercise 3.5: a valid unit step belongs to `unitStepClosure`. -/
lemma unitStepClosure_succ {x : ℝ} (hx0 : 0 < x) (hx2 : x < 2) :
    unitStepClosure x (x + 1) := by
  -- Insert the generating relation into its equivalence closure.
  apply Relation.EqvGen.rel
  exact ⟨rfl, hx0, hx2⟩

/-- Helper for Exercise 3.5: two consecutive valid unit steps connect `x` to `x + 2`. -/
lemma unitStepClosure_add_two {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    unitStepClosure x (x + 2) := by
  -- Compose the steps from `x` to `x + 1` and from `x + 1` to `x + 2`.
  have hx2 : x < 2 := by linarith
  have hxOne0 : 0 < x + 1 := by linarith
  have hxOne2 : x + 1 < 2 := by linarith
  have firstStep := unitStepClosure_succ hx0 hx2
  have secondStep : unitStepClosure (x + 1) (x + 2) := by
    apply Relation.EqvGen.rel
    refine ⟨?_, hxOne0, hxOne2⟩
    ring
  exact Relation.EqvGen.trans _ _ _ firstStep secondStep

/-- Helper for Exercise 3.5: the points `1` and `2` are related by one unit step. -/
lemma unitStepClosure_one_two : unitStepClosure 1 2 := by
  -- The generating step starts at `1`, which lies in `(0, 2)`.
  apply Relation.EqvGen.rel
  norm_num [unitStepRel]

/-- Helper for Exercise 3.5: all points in one canonical triple are equivalent
in the generated relation. -/
lemma unitStepClosure_of_mem_triple {z x y : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hx : x ∈ ({z, z + 1, z + 2} : Set ℝ))
    (hy : y ∈ ({z, z + 1, z + 2} : Set ℝ)) :
    unitStepClosure x y := by
  -- Relate the base point to each member using the two generating steps, then compose.
  have hz2 : z < 2 := by linarith
  have step01 := unitStepClosure_succ hz0 hz2
  have step02 := unitStepClosure_add_two hz0 hz1
  have baseToX : unitStepClosure z x := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact step01
    · exact step02
  have baseToY : unitStepClosure z y := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact step01
    · exact step02
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ baseToX) baseToY

/-- Exercise 3.5: Explicit description of the equivalence relation `T`. -/
theorem unitStepClosure_rel_iff (x y : ℝ) :
    unitStepClosure x y ↔
      x = y ∨
        (x = 1 ∧ y = 2) ∨
        (x = 2 ∧ y = 1) ∨
        ∃ z ∈ Set.Ioo (0 : ℝ) 1, x ∈ ({z, z + 1, z + 2} : Set ℝ) ∧
          y ∈ ({z, z + 1, z + 2} : Set ℝ) := by
  -- Minimality gives the bounded invariant; the component lemma normalizes it.
  constructor
  · intro hxy
    apply (unitStepBoundedIntegerRel_iff_components x y).mp
    exact Setoid.eqvGen_le unitStepRel_le_boundedIntegerSetoid hxy
  · intro hxy
    rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨z, ⟨hz0, hz1⟩, hx, hy⟩
    · exact Relation.EqvGen.refl _
    · exact unitStepClosure_one_two
    · exact Relation.EqvGen.symm _ _ unitStepClosure_one_two
    · exact unitStepClosure_of_mem_triple hz0 hz1 hx hy

/-- Part (c) of Exercise 3.5: For `0 < z < 1`, the `T`-class of `z` is
`{z, z + 1, z + 2}`. -/
theorem unitStepClosure_class_triple {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    {y | unitStepClosure z y} = {z, z + 1, z + 2} := by
  -- The explicit relation formula forces any triple containing `z` to have base `z`.
  ext y
  constructor
  · intro hy
    rcases (unitStepClosure_rel_iff z y).mp hy with
      rfl | ⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨w, ⟨hw0, hw1⟩, hzw, hyw⟩
    · simp
    · linarith
    · linarith
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzw
      rcases hzw with rfl | hzw | hzw
      · exact hyw
      · linarith
      · linarith
  · intro hy
    apply unitStepClosure_of_mem_triple hz0 hz1
    · simp
    · exact hy

/-- Part (c) of Exercise 3.5: The remaining nonsingleton `T`-class is `{1, 2}`. -/
theorem unitStepClosure_class_one :
    {y | unitStepClosure 1 y} = {1, 2} := by
  -- The point `1` is not in any open-base triple, leaving only `1` and `2`.
  ext y
  constructor
  · intro hy
    rcases (unitStepClosure_rel_iff 1 y).mp hy with
      rfl | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨z, ⟨hz0, hz1⟩, hz, _⟩
    · simp
    · simp
    · norm_num at h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz
      · linarith
      · linarith
      · linarith
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact unitStepClosure_one_two

/-- Part (c) of Exercise 3.5: Every point outside the interval `(0, 3)` has a singleton
`T`-class. -/
theorem unitStepClosure_class_singleton {x : ℝ} (hx : x ≤ 0 ∨ 3 ≤ x) :
    {y | unitStepClosure x y} = {x} := by
  -- Every nonidentity component lies strictly inside `(0, 3)`, contradicting `hx`.
  ext y
  constructor
  · intro hy
    rcases (unitStepClosure_rel_iff x y).mp hy with
      hxy | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨z, ⟨hz0, hz1⟩, hxz, _⟩
    · simpa using hxy.symm
    · rcases hx with hx | hx
      · norm_num at hx
      · norm_num at hx
    · rcases hx with hx | hx
      · norm_num at hx
      · norm_num at hx
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxz
      rcases hxz with rfl | rfl | rfl
      · rcases hx with hx | hx <;> linarith
      · rcases hx with hx | hx <;> linarith
      · rcases hx with hx | hx <;> linarith
  · intro hy
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact Relation.EqvGen.refl _

module

public import Topology_Munkres_2000.Book.Exercise_3_12.Orders
public import Mathlib.Order.Cover

@[expose] public section

open PositivePairOrder

/-- Helper for Exercise 3.12: a positive natural has an immediate predecessor exactly when it
is greater than `1`. -/
private lemma pnatHasImmediatePredecessor_iff (p : ℕ+) :
    (∃ q : ℕ+, q ⋖ p) ↔ 1 < p := by
  -- A successor step is a cover, and every non-one positive natural is a successor.
  constructor
  · rintro ⟨q, hq⟩
    exact lt_of_le_of_lt q.property hq.lt
  · intro hp
    obtain ⟨q, hq⟩ := PNat.exists_eq_succ_of_ne_one (ne_of_gt hp)
    refine ⟨q, hq ▸ ?_⟩
    refine ⟨PNat.lt_add_right q 1, ?_⟩
    intro c hleft hright
    exact (not_lt_of_ge (PNat.lt_add_one_iff.mp hright)) hleft

/-- Exercise 3.12: The dictionary-order predecessor criterion, together with the eight
companion conclusions below, answers all parts of the exercise. -/
theorem «dictionaryHasImmediatePredecessor_iff and eight companion theorems» (p : Dictionary) :
    (∃ q : Dictionary, q ⋖ p) ↔ 1 < (ofLex p).2 := by
  -- The cross-fiber cover case is impossible because `ℕ+` has no maximal element.
  constructor
  · rintro ⟨q, hq⟩
    rw [Prod.Lex.covBy_iff] at hq
    rcases hq with hq | hq
    · exact (pnatHasImmediatePredecessor_iff (ofLex p).2).mp ⟨(ofLex q).2, hq.2⟩
    · exact False.elim (hq.2.1.not_lt (PNat.lt_add_one_iff.mpr le_rfl))
  · intro hp
    obtain ⟨r, hr⟩ := (pnatHasImmediatePredecessor_iff (ofLex p).2).mpr hp
    refine ⟨toLex ((ofLex p).1, r), ?_⟩
    rw [Prod.Lex.covBy_iff]
    exact Or.inl ⟨rfl, hr⟩

/-- Companion to Exercise 3.12 (1): A pair in the dictionary order has an immediate
predecessor exactly when its second coordinate is greater than `1`. -/
theorem dictionaryHasImmediatePredecessor_iff (p : Dictionary) :
    (∃ q : Dictionary, q ⋖ p) ↔ 1 < (ofLex p).2 := by
  -- Reuse the aggregate exercise entry point for the first named conclusion.
  exact «dictionaryHasImmediatePredecessor_iff and eight companion theorems» p

/-- Helper for Exercise 3.12: increasing both coordinates by one preserves their integer
difference. -/
private lemma differenceShift_coordinates_eq (q : Difference) :
    (((q.x + 1 : ℕ+) : ℤ) - ((q.y + 1 : ℕ+) : ℤ)) = (q.x : ℤ) - (q.y : ℤ) := by
  -- Normalize the positive-natural additions before integer arithmetic.
  simp only [PNat.add_coe]
  omega

/-- Helper for Exercise 3.12: shifting a difference-ordered pair diagonally upward strictly
increases it. -/
private lemma difference_lt_diagonalShift (q : Difference) :
    q < (⟨q.x + 1, q.y + 1⟩ : Difference) := by
  -- The difference coordinate is fixed and the second coordinate increases.
  rw [Difference.lt_iff]
  right
  exact ⟨differenceShift_coordinates_eq q |>.symm, PNat.lt_add_right q.y 1⟩

/-- Helper for Exercise 3.12: a difference-ordered pair whose coordinates exceed `1` has a
cover on the preceding point of its diagonal. -/
private lemma differenceDiagonal_covBy (p : Difference) (hx : 1 < p.x) (hy : 1 < p.y) :
    ∃ q : Difference, q ⋖ p := by
  -- Decompose both coordinates as successors, then rule out each possible shape of an
  -- intermediate comparison.
  obtain ⟨x, hpx⟩ := PNat.exists_eq_succ_of_ne_one (ne_of_gt hx)
  obtain ⟨y, hpy⟩ := PNat.exists_eq_succ_of_ne_one (ne_of_gt hy)
  refine ⟨⟨x, y⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [Difference.lt_iff, hpx, hpy]
    right
    constructor
    · simp only [PNat.add_coe]
      omega
    · exact PNat.lt_add_right y 1
  · intro c hleft hright
    rw [Difference.lt_iff] at hleft hright
    simp only at hleft
    rw [hpx, hpy] at hright
    simp only [PNat.add_coe] at hright
    rcases hleft with hleft | hleft
    · rcases hright with hright | hright
      · omega
      · omega
    · rcases hright with hright | hright
      · omega
      · exact (not_lt_of_ge (PNat.lt_add_one_iff.mp hright.2)) hleft.2

/-- Helper for Exercise 3.12: the upper endpoint of a cover in the difference-first order
has both coordinates greater than `1`. -/
private lemma Difference.CovBy.coordinates_one_lt {q p : Difference} (h : q ⋖ p) :
    1 < p.x ∧ 1 < p.y := by
  -- If either target coordinate were `1`, the diagonal shift of the lower endpoint would lie
  -- strictly between the two endpoints.
  constructor
  · by_contra hx
    have hpx : p.x = 1 := le_antisymm (le_of_not_gt hx) p.x.property
    let r : Difference := ⟨q.x + 1, q.y + 1⟩
    have hqr : q < r := difference_lt_diagonalShift q
    have hrp : r < p := by
      have hqp := h.lt
      rw [Difference.lt_iff] at hqp ⊢
      simp only [r]
      rw [differenceShift_coordinates_eq]
      rcases hqp with hqp | hqp
      · exact Or.inl hqp
      · have hqxpos : (0 : ℤ) < q.x := by exact_mod_cast q.x.property
        have hqypos : (0 : ℤ) < q.y := by exact_mod_cast q.y.property
        have hpypos : (0 : ℤ) < p.y := by exact_mod_cast p.y.property
        have hqylt : (q.y : ℤ) < p.y := by exact_mod_cast hqp.2
        have hone : (((1 : ℕ+) : ℤ)) = 1 := rfl
        rw [hpx] at hqp
        omega
    exact h.2 hqr hrp
  · by_contra hy
    have hpy : p.y = 1 := le_antisymm (le_of_not_gt hy) p.y.property
    let r : Difference := ⟨q.x + 1, q.y + 1⟩
    have hqr : q < r := difference_lt_diagonalShift q
    have hrp : r < p := by
      have hqp := h.lt
      rw [Difference.lt_iff] at hqp ⊢
      simp only [r]
      rw [differenceShift_coordinates_eq]
      rcases hqp with hqp | hqp
      · exact Or.inl hqp
      · rw [hpy] at hqp
        exact False.elim ((not_lt_of_ge q.y.property) hqp.2)
    exact h.2 hqr hrp

/-- Companion to Exercise 3.12 (2): A pair in the difference-first order has an immediate
predecessor exactly when both coordinates are greater than `1`. -/
theorem differenceHasImmediatePredecessor_iff (p : Difference) :
    (∃ q : Difference, q ⋖ p) ↔ 1 < p.x ∧ 1 < p.y := by
  -- Assemble the diagonal construction and the coordinate obstruction for arbitrary covers.
  constructor
  · rintro ⟨q, hq⟩
    exact Difference.CovBy.coordinates_one_lt hq
  · rintro ⟨hx, hy⟩
    exact differenceDiagonal_covBy p hx hy

/-- Helper for Exercise 3.12: every nonbottom point of the sum-first order has an immediate
predecessor. -/
private lemma sumPredecessor_covBy (p : Sum) (hp : p ≠ ⟨1, 1⟩) : ∃ q : Sum, q ⋖ p := by
  by_cases hy : 1 < p.y
  · obtain ⟨y, hpy⟩ := PNat.exists_eq_succ_of_ne_one (ne_of_gt hy)
    have hsum : p.x + 1 + y = p.x + p.y := by
      rw [hpy]
      ac_rfl
    refine ⟨⟨p.x + 1, y⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [Sum.lt_iff]
      right
      exact ⟨hsum, hpy ▸ PNat.lt_add_right y 1⟩
    · intro c hleft hright
      rw [Sum.lt_iff] at hleft hright
      simp only at hleft
      rcases hleft with hleft | hleft
      · rcases hright with hright | hright
        · exact (hleft.trans hright).ne hsum
        · exact hleft.ne (hsum.trans hright.1.symm)
      · rcases hright with hright | hright
        · exact hright.ne (hleft.1.symm.trans hsum)
        · have hcy : c.y < y + 1 := hpy ▸ hright.2
          exact (not_lt_of_ge (PNat.lt_add_one_iff.mp hcy)) hleft.2
  · have hpy : p.y = 1 := le_antisymm (le_of_not_gt hy) p.y.property
    have hx : 1 < p.x := by
      by_contra hx
      have hpx : p.x = 1 := le_antisymm (le_of_not_gt hx) p.x.property
      apply hp
      cases p
      simp_all
    obtain ⟨x, hpx⟩ := PNat.exists_eq_succ_of_ne_one (ne_of_gt hx)
    have hsum : 1 + x + 1 = p.x + p.y := by
      rw [hpx, hpy]
      ac_rfl
    refine ⟨⟨1, x⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [Sum.lt_iff]
      left
      calc
        1 + x < 1 + x + 1 := PNat.lt_add_right (1 + x) 1
        _ = p.x + p.y := hsum
    · intro c hleft hright
      rw [Sum.lt_iff] at hleft hright
      simp only at hleft
      rcases hleft with hleft | hleft
      · rcases hright with hright | hright
        · have hc : c.x + c.y < 1 + x + 1 := hright.trans_eq hsum.symm
          exact (not_lt_of_ge (PNat.lt_add_one_iff.mp hc)) hleft
        · rw [hpy] at hright
          exact False.elim ((not_lt_of_ge c.y.property) hright.2)
      · rcases hright with hright | hright
        · have heqNat : (1 : ℕ) + x = c.x + c.y := by
            exact_mod_cast hleft.1
          have hcyNat : (c.y : ℕ) ≤ x := by
            have hcxNat : (1 : ℕ) ≤ c.x := c.x.property
            omega
          have hcy : c.y ≤ x := by exact_mod_cast hcyNat
          exact (not_lt_of_ge hcy) hleft.2
        · rw [hpy] at hright
          exact False.elim ((not_lt_of_ge c.y.property) hright.2)

/-- Companion to Exercise 3.12 (3): Every pair except `(1, 1)` in the sum-first order has an
immediate predecessor. -/
theorem sumHasImmediatePredecessor_iff (p : Sum) :
    (∃ q : Sum, q ⋖ p) ↔ p ≠ ⟨1, 1⟩ := by
  -- Nonbottom points use the explicit predecessor construction, while a cover below bottom
  -- contradicts `bot_le`.
  constructor
  · rintro ⟨q, hq⟩ hp
    rw [← Sum.bot_eq] at hp
    rw [hp] at hq
    exact (not_lt_of_ge bot_le) hq.lt
  · exact sumPredecessor_covBy p

/-- Companion to Exercise 3.12 (4): The dictionary order has smallest element `(1, 1)`. -/
theorem dictionaryLeast :
    IsLeast Set.univ (⊥ : Dictionary) := ⟨Set.mem_univ _, fun _ _ ↦ bot_le⟩

/-- Companion to Exercise 3.12 (5): The difference-first order has no smallest element. -/
theorem differenceHasNoLeast :
    ¬ ∃ p : Difference, IsLeast Set.univ p := by
  -- Increasing only the second coordinate strictly lowers the difference coordinate.
  rintro ⟨p, hp⟩
  have hlower : (⟨p.x, p.y + 1⟩ : Difference) < p := by
    rw [Difference.lt_iff]
    left
    simp only [PNat.add_coe]
    have hone : (((1 : ℕ+) : ℤ)) = 1 := rfl
    omega
  exact (not_lt_of_ge (hp.2 (Set.mem_univ _))) hlower

/-- Companion to Exercise 3.12 (6): The sum-first order has smallest element `(1, 1)`. -/
theorem sumLeast :
    IsLeast Set.univ (⊥ : Sum) := ⟨Set.mem_univ _, fun _ _ ↦ bot_le⟩

/-- Helper for Exercise 3.12: an order isomorphism preserves leastness in the universal set. -/
private lemma OrderIso.isLeast_univ_apply_iff {α β : Type*} [Preorder α] [Preorder β]
    (e : α ≃o β) (a : α) :
    IsLeast (fun _ : β ↦ True) (e a) ↔ IsLeast (fun _ : α ↦ True) a := by
  -- Compare arbitrary elements after transporting them through the inverse isomorphism.
  constructor
  · intro h
    refine ⟨Set.mem_univ _, ?_⟩
    intro b hb
    exact e.le_iff_le.mp (h.2 trivial)
  · intro h
    refine ⟨Set.mem_univ _, ?_⟩
    intro b hb
    have hab : a ≤ e.symm b := h.2 trivial
    simpa using e.le_iff_le.mpr hab

/-- Companion to Exercise 3.12 (7): The dictionary and difference-first orders have different
order types. -/
theorem dictionaryNotOrderIsoDifference :
    ¬ Nonempty (Dictionary ≃o Difference) := by
  -- An isomorphism would transport the dictionary bottom to a least difference-ordered pair.
  rintro ⟨e⟩
  apply differenceHasNoLeast
  refine ⟨e ⊥, ?_⟩
  exact (e.isLeast_univ_apply_iff ⊥).mpr dictionaryLeast

/-- Companion to Exercise 3.12 (8): The dictionary and sum-first orders have different order
types. -/
theorem dictionaryNotOrderIsoSum :
    ¬ Nonempty (Dictionary ≃o Sum) := by
  -- The point `(2, 1)` has no dictionary predecessor, but its nonbottom image in the sum order
  -- must have one, and covers transport back through the isomorphism.
  rintro ⟨e⟩
  let d : Dictionary := toLex (2, 1)
  have hdNoPredecessor : ¬ ∃ q : Dictionary, q ⋖ d := by
    rw [dictionaryHasImmediatePredecessor_iff]
    simp [d]
  have hdne : d ≠ ⊥ := by
    intro hd
    have hcoordinates := congrArg (fun z : Dictionary ↦ (ofLex z).1) hd
    have hbot : ofLex (⊥ : Dictionary) = (1, 1) := rfl
    rw [hbot] at hcoordinates
    have hcoordinatesNat := congrArg (fun n : ℕ+ ↦ (n : ℕ)) hcoordinates
    change (2 : ℕ) = 1 at hcoordinatesNat
    omega
  have himage : e d ≠ ⟨1, 1⟩ := by
    rw [← Sum.bot_eq]
    intro he
    apply hdne
    apply e.injective
    rw [he, OrderIso.map_bot]
  obtain ⟨q, hq⟩ := (sumHasImmediatePredecessor_iff (e d)).mpr himage
  apply hdNoPredecessor
  refine ⟨e.symm q, ?_⟩
  simpa using (apply_covBy_apply_iff e.symm).mpr hq

/-- Companion to Exercise 3.12 (9): The difference-first and sum-first orders have different
order types. -/
theorem differenceNotOrderIsoSum :
    ¬ Nonempty (Difference ≃o Sum) := by
  -- Pulling the least sum-ordered point back would create a least difference-ordered point.
  rintro ⟨e⟩
  apply differenceHasNoLeast
  refine ⟨e.symm ⊥, ?_⟩
  exact (e.symm.isLeast_univ_apply_iff ⊥).mpr sumLeast

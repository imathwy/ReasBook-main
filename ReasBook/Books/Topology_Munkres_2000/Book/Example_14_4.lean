module

public import Topology_Munkres_2000.Book.Example_14_4.Topology

public section

open scoped Topology

namespace TwoCopiesPNat

/-- Helper for Example 14.4: the explicit first-copy coordinate is `a n`. -/
private lemma toLex_zero_eq_a (n : ℕ+) : toLex (0, n) = a n := by
  -- Compare the coordinates through the lexicographic equivalence.
  apply ofLex.injective
  simp only [ofLex_toLex, a_apply]

/-- Helper for Example 14.4: the explicit second-copy coordinate is `b n`. -/
private lemma toLex_one_eq_b (n : ℕ+) : toLex (1, n) = b n := by
  -- Compare the coordinates through the lexicographic equivalence.
  apply ofLex.injective
  simp only [ofLex_toLex, b_apply]

/-- Helper for Example 14.4: equality with `a n` is coordinatewise equality with `(0, n)`. -/
private lemma toLex_eq_a_iff (i : Fin 2) (m n : ℕ+) :
    toLex (i, m) = a n ↔ i = 0 ∧ m = n := by
  -- Apply `ofLex` in one direction and reconstruct the point in the other.
  constructor
  · intro h
    have hcoord := congrArg ofLex h
    simpa only [ofLex_toLex, a_apply, Prod.mk.injEq] using hcoord
  · rintro ⟨rfl, rfl⟩
    exact toLex_zero_eq_a _

/-- Helper for Example 14.4: equality with `b n` is coordinatewise equality with `(1, n)`. -/
private lemma toLex_eq_b_iff (i : Fin 2) (m n : ℕ+) :
    toLex (i, m) = b n ↔ i = 1 ∧ m = n := by
  -- Apply `ofLex` in one direction and reconstruct the point in the other.
  constructor
  · intro h
    have hcoord := congrArg ofLex h
    simpa only [ofLex_toLex, b_apply, Prod.mk.injEq] using hcoord
  · rintro ⟨rfl, rfl⟩
    exact toLex_one_eq_b _

/-- Helper for Example 14.4: the lexicographically ordered two copies of `ℕ+` have
`TwoCopiesPNat.a 1` as their least element. -/
theorem least : IsLeast Set.univ (a 1) := by
  -- Expose the two coordinates and compare them lexicographically with `(0, 1)`.
  constructor
  · exact Set.mem_univ _
  · intro x _
    obtain ⟨⟨i, n⟩, rfl⟩ := toLex.surjective x
    simp only [Prod.Lex.le_iff, a_apply, ofLex_toLex]
    by_cases hi : i = 0
    · exact Or.inr ⟨hi.symm, one_le⟩
    · exact Or.inl (by omega)

/-- Helper for Example 14.4: the points `a n` are cofinal below `b 1`. -/
private lemma exists_a_between_lt_b_one (x : TwoCopiesPNat) (hx : x < b 1) :
    ∃ n : ℕ+, x < a n ∧ a n < b 1 := by
  -- A point below `b 1` must lie in the first copy.
  obtain ⟨⟨i, m⟩, rfl⟩ := toLex.surjective x
  simp only [Prod.Lex.lt_iff, b_apply, ofLex_toLex] at hx
  have hi : i = 0 := by
    rcases hx with hi | ⟨hi, hm⟩
    · omega
    · subst i
      exact (not_lt_of_ge one_le hm).elim
  subst i
  -- The successor in the first copy remains below `b 1`.
  refine ⟨m + 1, ?_, ?_⟩
  · simp only [Prod.Lex.lt_iff, a_apply, ofLex_toLex]
    exact Or.inr ⟨trivial, PNat.lt_succ_self m⟩
  · simp only [Prod.Lex.lt_iff, a_apply, b_apply]
    exact Or.inl (by omega)

/-- Helper for Example 14.4: every point `a n` is isolated in the order topology. -/
private lemma isOpen_singleton_a (n : ℕ+) :
    IsOpen ({a n} : Set TwoCopiesPNat) := by
  -- The least point is the open lower ray ending at its successor.
  by_cases hn : n = 1
  · subst n
    have hsingleton : ({a 1} : Set TwoCopiesPNat) = Set.Iio (a (1 + 1)) := by
      ext x
      obtain ⟨⟨i, m⟩, rfl⟩ := toLex.surjective x
      simp only [Set.mem_singleton_iff, Set.mem_Iio, toLex_eq_a_iff,
        Prod.Lex.lt_iff, a_apply, ofLex_toLex]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact Or.inr ⟨rfl, PNat.lt_succ_self 1⟩
      · rintro (hi | ⟨rfl, hm⟩)
        · omega
        · constructor
          · rfl
          · apply Subtype.ext
            change (m : ℕ) = 1
            change (m : ℕ) < 1 + 1 at hm
            have hmpos : 0 < (m : ℕ) := m.property
            omega
    rw [hsingleton]
    exact isOpen_Iio
  · -- Every later point is the unique point between its predecessor and successor.
    obtain ⟨k, rfl⟩ := PNat.exists_eq_succ_of_ne_one hn
    have hsingleton : ({a (k + 1)} : Set TwoCopiesPNat) =
        Set.Ioo (a k) (a (k + 1 + 1)) := by
      ext x
      obtain ⟨⟨i, m⟩, rfl⟩ := toLex.surjective x
      simp only [Set.mem_singleton_iff, Set.mem_Ioo, toLex_eq_a_iff,
        Prod.Lex.lt_iff, a_apply, ofLex_toLex]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨Or.inr ⟨rfl, PNat.lt_succ_self k⟩,
          Or.inr ⟨rfl, PNat.lt_succ_self (k + 1)⟩⟩
      · rintro ⟨hk, hs⟩
        rcases hk with hk | ⟨rfl, hk⟩
        · omega
        · rcases hs with hs | ⟨-, hs⟩
          · omega
          · constructor
            · rfl
            · apply Subtype.ext
              change (m : ℕ) = (k : ℕ) + 1
              change (k : ℕ) < (m : ℕ) at hk
              change (m : ℕ) < (k : ℕ) + 1 + 1 at hs
              omega
    rw [hsingleton]
    exact isOpen_Ioo

/-- Helper for Example 14.4: every point `b n` except `b 1` is isolated. -/
private lemma isOpen_singleton_b_of_ne_one (n : ℕ+) (hn : n ≠ 1) :
    IsOpen ({b n} : Set TwoCopiesPNat) := by
  -- Write `n` as a successor and isolate it between adjacent points in the second copy.
  obtain ⟨k, rfl⟩ := PNat.exists_eq_succ_of_ne_one hn
  have hsingleton : ({b (k + 1)} : Set TwoCopiesPNat) =
      Set.Ioo (b k) (b (k + 1 + 1)) := by
    ext x
    obtain ⟨⟨i, m⟩, rfl⟩ := toLex.surjective x
    simp only [Set.mem_singleton_iff, Set.mem_Ioo, toLex_eq_b_iff,
      Prod.Lex.lt_iff, b_apply, ofLex_toLex]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨Or.inr ⟨rfl, PNat.lt_succ_self k⟩,
        Or.inr ⟨rfl, PNat.lt_succ_self (k + 1)⟩⟩
    · rintro ⟨hk, hs⟩
      rcases hk with hk | ⟨rfl, hk⟩
      · omega
      · rcases hs with hs | ⟨-, hs⟩
        · omega
        · constructor
          · rfl
          · apply Subtype.ext
            change (m : ℕ) = (k : ℕ) + 1
            change (k : ℕ) < (m : ℕ) at hk
            change (m : ℕ) < (k : ℕ) + 1 + 1 at hs
            omega
  rw [hsingleton]
  exact isOpen_Ioo

/-- Helper for Example 14.4: every neighborhood of `b 1` meets the first copy. -/
private lemma exists_a_mem_of_mem_nhds_b_one (U : Set TwoCopiesPNat)
    (hU : U ∈ 𝓝 (b 1)) : ∃ n : ℕ+, a n ∈ U := by
  -- Refine the neighborhood to an interval around `b 1`.
  have hlower : ∃ l, l < b 1 := by
    refine ⟨a 1, ?_⟩
    simp only [Prod.Lex.lt_iff, a_apply, b_apply]
    exact Or.inl (by omega)
  have hupper : ∃ u, b 1 < u := by
    refine ⟨b (1 + 1), ?_⟩
    simp only [Prod.Lex.lt_iff, b_apply]
    exact Or.inr ⟨trivial, PNat.lt_succ_self 1⟩
  obtain ⟨l, u, hlbu, hlu⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' hlower hupper).mp hU
  -- Insert a first-copy point between the lower endpoint and `b 1`.
  obtain ⟨n, hlan, hanb⟩ := exists_a_between_lt_b_one l hlbu.1
  refine ⟨n, hlu ?_⟩
  exact ⟨hlan, hanb.trans hlbu.2⟩

/-- Helper for Example 14.4: in the order topology, the only singleton that is not
open is the singleton containing `TwoCopiesPNat.b 1`. -/
theorem isOpen_singleton_iff (x : TwoCopiesPNat) :
    IsOpen ({x} : Set TwoCopiesPNat) ↔ x ≠ b 1 := by
  constructor
  · intro hx hxb
    subst x
    -- Openness would make the singleton a neighborhood, which must meet the first copy.
    obtain ⟨n, hn⟩ := exists_a_mem_of_mem_nhds_b_one {b 1} (hx.mem_nhds (Set.mem_singleton _))
    have hab : a n = b 1 := Set.mem_singleton_iff.mp hn
    have hcoord := congrArg (fun y : TwoCopiesPNat ↦ (ofLex y).1) hab
    simp only [a_apply, b_apply] at hcoord
    omega
  · intro hx
    -- Classify the point by which copy contains its first coordinate.
    obtain ⟨⟨i, n⟩, rfl⟩ := toLex.surjective x
    by_cases hi : i = 0
    · subst i
      rw [toLex_zero_eq_a]
      exact isOpen_singleton_a n
    · have hi_one : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst i
      rw [toLex_one_eq_b]
      apply isOpen_singleton_b_of_ne_one n
      intro hn
      subst n
      exact hx (toLex_one_eq_b 1)

/-- Helper for Example 14.4: every open neighborhood of `TwoCopiesPNat.b 1` contains
a point from the first copy of the positive integers. -/
theorem exists_a_mem_of_isOpen_of_b_one_mem (U : Set TwoCopiesPNat)
    (hU : IsOpen U) (hb : b 1 ∈ U) :
    ∃ n : ℕ+, a n ∈ U := by
  -- An open set containing `b 1` is a neighborhood of `b 1`.
  exact exists_a_mem_of_mem_nhds_b_one U (hU.mem_nhds hb)

/-- Example 14.4: The order topology on the lexicographically ordered two
copies of the positive integers is not discrete. -/
theorem not_discreteTopology : ¬ DiscreteTopology TwoCopiesPNat := by
  intro hdiscrete
  -- Discreteness would make the exceptional singleton open.
  have hopen : IsOpen ({b 1} : Set TwoCopiesPNat) :=
    discreteTopology_iff_isOpen_singleton.mp hdiscrete (b 1)
  exact (isOpen_singleton_iff (b 1)).mp hopen rfl

end TwoCopiesPNat

module

public import Topology_Munkres_2000.Book.Example_10_1.TwoCopiesPNat

public section

/-- Helper for Exercise 10.3: consecutive positive naturals are related by
the covering relation. -/
lemma PNat.covBy_add_one (n : ℕ+) : n ⋖ n + 1 := by
  -- Consecutive positive naturals have no positive natural strictly between them.
  constructor
  · exact PNat.lt_add_one_iff.mpr le_rfl
  · intro m hnm hmn
    exact (not_lt_of_ge (PNat.add_one_le_iff.mpr hnm)) hmn

/-- Helper for Exercise 10.3: every point in the first copy of `ℕ+` precedes
every point in the second copy. -/
lemma TwoCopiesPNat.a_lt_b (m n : ℕ+) :
    TwoCopiesPNat.a m < TwoCopiesPNat.b n := by
  -- Rewrite the named points to coordinates; the first coordinate decides the order.
  have ha : TwoCopiesPNat.a m = toLex (0, m) := by
    rw [← toLex_ofLex (TwoCopiesPNat.a m), TwoCopiesPNat.a_apply]
  have hb : TwoCopiesPNat.b n = toLex (1, n) := by
    rw [← toLex_ofLex (TwoCopiesPNat.b n), TwoCopiesPNat.b_apply]
  rw [ha, hb]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl Fin.zero_lt_one)

/-- Helper for Exercise 10.3: the first point of the second copy has no
immediate predecessor in `TwoCopiesPNat`. -/
lemma TwoCopiesPNat.not_covBy_b_one (x : TwoCopiesPNat) :
    ¬ x ⋖ TwoCopiesPNat.b 1 := by
  -- Every point above `x` in the first copy leaves room for its successor.
  intro hx
  obtain ⟨⟨i, n⟩, rfl⟩ := toLex.surjective x
  have hb : TwoCopiesPNat.b 1 = toLex (1, 1) := by
    rw [← toLex_ofLex (TwoCopiesPNat.b 1), TwoCopiesPNat.b_apply]
  rw [hb] at hx
  have hlt := hx.1
  simp only [Prod.Lex.toLex_lt_toLex] at hlt
  rcases hlt with hfirst | hsecond
  · have hleft : toLex (i, n) < toLex (i, n + 1) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, PNat.lt_add_one_iff.mpr le_rfl⟩)
    have hright : toLex (i, n + 1) < toLex (1, 1) :=
      Prod.Lex.toLex_lt_toLex.mpr (Or.inl hfirst)
    exact hx.2 hleft hright
  · exact (not_lt_of_ge (show (1 : ℕ+) ≤ n from n.property)) hsecond.2

/-- Helper for Exercise 10.3: a block boundary in `ℕ+ ×ₗ Fin 2` is a cover. -/
lemma pnatFinTwoLex_covBy_boundary (n : ℕ+) :
    toLex (n, (1 : Fin 2)) ⋖ toLex (n + 1, (0 : Fin 2)) := by
  -- Any intermediate point would force a positive natural between `n` and `n + 1`.
  constructor
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (PNat.lt_add_one_iff.mpr le_rfl))
  · intro z hz₁ hz₂
    obtain ⟨⟨m, i⟩, rfl⟩ := toLex.surjective z
    simp only [Prod.Lex.toLex_lt_toLex] at hz₁ hz₂
    rcases hz₁ with hz₁ | hz₁
    · rcases hz₂ with hz₂ | hz₂
      · exact (not_lt_of_ge (PNat.add_one_le_iff.mpr hz₁)) hz₂
      · omega
    · omega

/-- Helper for Exercise 10.3: the two points within each `Fin 2` block are a cover. -/
lemma pnatFinTwoLex_covBy_fiber (n : ℕ+) :
    toLex (n, (0 : Fin 2)) ⋖ toLex (n, (1 : Fin 2)) := by
  -- An intermediate point can neither leave the block nor lie between `0` and `1`.
  constructor
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, Fin.zero_lt_one⟩)
  · intro z hz₁ hz₂
    obtain ⟨⟨m, i⟩, rfl⟩ := toLex.surjective z
    simp only [Prod.Lex.toLex_lt_toLex] at hz₁ hz₂
    rcases hz₁ with hz₁ | hz₁
    · rcases hz₂ with hz₂ | hz₂
      · rw [← PNat.coe_lt_coe] at hz₁ hz₂
        omega
      · rw [hz₂.1] at hz₁
        exact (lt_irrefl _ hz₁)
    · rcases hz₂ with hz₂ | hz₂
      · rw [hz₁.1] at hz₂
        exact (lt_irrefl _ hz₂)
      · omega

/-- Helper for Exercise 10.3: every point of `ℕ+ ×ₗ Fin 2` other than its
least point has an immediate predecessor. -/
lemma exists_covBy_of_ne_min_pnatFinTwoLex (y : ℕ+ ×ₗ Fin 2)
    (hy : y ≠ toLex (1, 0)) :
    ∃ x, x ⋖ y := by
  -- Expose coordinates only while selecting the predecessor.
  obtain ⟨⟨n, i⟩, rfl⟩ := toLex.surjective y
  by_cases hi : i = 0
  · subst i
    have hn : n ≠ 1 := by
      intro hn
      subst n
      exact hy rfl
    obtain ⟨k, rfl⟩ := PNat.exists_eq_succ_of_ne_one hn
    exact ⟨toLex (k, 1), pnatFinTwoLex_covBy_boundary k⟩
  · have hi_one : i = 1 := by omega
    subst i
    exact ⟨toLex (n, 0), pnatFinTwoLex_covBy_fiber n⟩

/-- Helper for Exercise 10.3: the point `toLex (1, 0)` is the least element
of `ℕ+ ×ₗ Fin 2`. -/
lemma pnatFinTwoLex_eq_min_of_le (y : ℕ+ ×ₗ Fin 2)
    (hy : y ≤ toLex (1, 0)) : y = toLex (1, 0) := by
  -- Coordinate comparison forces both coordinates to be their least values.
  obtain ⟨⟨n, i⟩, rfl⟩ := toLex.surjective y
  simp only [Prod.Lex.toLex_le_toLex] at hy
  rcases hy with hy | hy
  · exact ((not_lt_of_ge (show (1 : ℕ+) ≤ n from n.property)) hy).elim
  · have hn : n = 1 := hy.1
    have hi : i = 0 := by omega
    subst n
    subst i
    rfl

/-- Helper for Exercise 10.3: strict order on `TwoCopiesPNat` is characterized
by its concrete non-strict lexicographic order. -/
lemma TwoCopiesPNat.lt_iff_le_not_ge {x y : TwoCopiesPNat} :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  -- Normalize both sides to the two lexicographic coordinate formulas.
  obtain ⟨⟨i, m⟩, rfl⟩ := toLex.surjective x
  obtain ⟨⟨j, n⟩, rfl⟩ := toLex.surjective y
  simp only [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_le_toLex]
  grind

/-- Helper for Exercise 10.3: strict order on `ℕ+ ×ₗ Fin 2` is characterized
by its concrete non-strict lexicographic order. -/
lemma pnatFinTwoLex_lt_iff_le_not_ge {x y : ℕ+ ×ₗ Fin 2} :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  -- Normalize both sides to the two lexicographic coordinate formulas.
  obtain ⟨⟨m, i⟩, rfl⟩ := toLex.surjective x
  obtain ⟨⟨n, j⟩, rfl⟩ := toLex.surjective y
  simp only [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_le_toLex]
  grind

/-- Helper for Exercise 10.3: the inverse of the proposed order isomorphism
preserves strict order. -/
lemma twoCopiesPNat_symm_strictMono (e : TwoCopiesPNat ≃o (ℕ+ ×ₗ Fin 2))
    {x y : ℕ+ ×ₗ Fin 2} (h : x < y) : e.symm x < e.symm y := by
  -- Transport the `≤ ∧ ¬ ≥` characterization through the isomorphism.
  rw [TwoCopiesPNat.lt_iff_le_not_ge]
  have hparts := pnatFinTwoLex_lt_iff_le_not_ge.mp h
  constructor
  · exact e.symm.map_rel_iff'.mpr hparts.1
  · intro hyx
    exact hparts.2 (e.symm.map_rel_iff'.mp hyx)

/-- Helper for Exercise 10.3: the proposed order isomorphism preserves strict
order. -/
lemma twoCopiesPNat_strictMono (e : TwoCopiesPNat ≃o (ℕ+ ×ₗ Fin 2))
    {x y : TwoCopiesPNat} (h : x < y) : e x < e y := by
  -- Transport the `≤ ∧ ¬ ≥` characterization through the isomorphism.
  rw [pnatFinTwoLex_lt_iff_le_not_ge]
  have hparts := TwoCopiesPNat.lt_iff_le_not_ge.mp h
  constructor
  · exact e.map_rel_iff'.mpr hparts.1
  · intro hyx
    exact hparts.2 (e.map_rel_iff'.mp hyx)

/-- Helper for Exercise 10.3: an order isomorphism between the two orders pulls
a cover back through its inverse. -/
lemma covBy_twoCopiesPNat_symm (e : TwoCopiesPNat ≃o (ℕ+ ×ₗ Fin 2))
    {x y : ℕ+ ×ₗ Fin 2} (h : x ⋖ y) : e.symm x ⋖ e.symm y := by
  -- Map a hypothetical intermediate source point forward to contradict the target cover.
  constructor
  · exact twoCopiesPNat_symm_strictMono e h.1
  · intro z hz₁ hz₂
    have h₁ : x < e z := by
      have hz := twoCopiesPNat_strictMono e hz₁
      simpa only [e.apply_symm_apply] using hz
    have h₂ : e z < y := by
      have hz := twoCopiesPNat_strictMono e hz₂
      simpa only [e.apply_symm_apply] using hz
    exact h.2 h₁ h₂

/-- Exercise 10.3: The dictionary orders on `TwoCopiesPNat` and `ℕ+ ×ₗ Fin 2`,
modeling `{1,2} × ℤ₊` and `ℤ₊ × {1,2}`, do not have the same order type. -/
theorem finTwoPnatLex_not_orderIso :
    ¬ Nonempty (TwoCopiesPNat ≃o (ℕ+ ×ₗ Fin 2)) := by
  -- An isomorphism would carry `b 1` to a non-minimal point with a predecessor.
  rintro ⟨e⟩
  have hsource : TwoCopiesPNat.a 1 < TwoCopiesPNat.b 1 :=
    TwoCopiesPNat.a_lt_b 1 1
  have hsourceLe : TwoCopiesPNat.a 1 ≤ TwoCopiesPNat.b 1 := by
    have ha : TwoCopiesPNat.a 1 = toLex (0, 1) := by
      rw [← toLex_ofLex (TwoCopiesPNat.a 1), TwoCopiesPNat.a_apply]
    have hb : TwoCopiesPNat.b 1 = toLex (1, 1) := by
      rw [← toLex_ofLex (TwoCopiesPNat.b 1), TwoCopiesPNat.b_apply]
    rw [ha, hb]
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inl Fin.zero_lt_one)
  have hle : e (TwoCopiesPNat.a 1) ≤ e (TwoCopiesPNat.b 1) :=
    e.map_rel_iff'.mpr hsourceLe
  have hsourceNe : TwoCopiesPNat.a 1 ≠ TwoCopiesPNat.b 1 := by
    intro hab
    have hcoords := congrArg ofLex hab
    simp only [TwoCopiesPNat.a_apply, TwoCopiesPNat.b_apply] at hcoords
    have hfirst := congrArg Prod.fst hcoords
    exact Fin.zero_ne_one hfirst
  have hne : e (TwoCopiesPNat.b 1) ≠ toLex (1, 0) := by
    intro he
    rw [he] at hle
    have ha : e (TwoCopiesPNat.a 1) = toLex (1, 0) :=
      pnatFinTwoLex_eq_min_of_le _ hle
    exact hsourceNe (e.injective (ha.trans he.symm))
  obtain ⟨y, hy⟩ := exists_covBy_of_ne_min_pnatFinTwoLex _ hne
  have hpull : e.symm y ⋖ TwoCopiesPNat.b 1 := by
    have h := covBy_twoCopiesPNat_symm e hy
    simpa only [e.symm_apply_apply] using h
  exact TwoCopiesPNat.not_covBy_b_one _ hpull

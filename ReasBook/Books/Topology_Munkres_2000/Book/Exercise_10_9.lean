module

public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.Data.PNat.Basic

public section

/-- Helper for Exercise 10.9: membership in the relevant colexicographic section is
equivalent to vanishing at every coordinate from `n` onward. -/
private lemma mem_antidictionarySection_iff (n : ℕ) (x : Colex (ℕ →₀ ℕ)) :
    x ∈ Set.Iio (toColex (Finsupp.single n 1) : Colex (ℕ →₀ ℕ)) ↔
      ∀ i, n ≤ i → x i = 0 := by
  -- A colex witness can only occur at the singleton's nonzero coordinate.
  constructor
  · intro hx
    have hx' : x < toColex (Finsupp.single n 1) := by
      simpa only [Set.mem_Iio] using hx
    rw [Finsupp.Colex.lt_iff] at hx'
    obtain ⟨i, htail, hcoord⟩ := hx'
    have hin : i = n := by
      by_contra hne
      simp [hne] at hcoord
    subst i
    intro i hi
    rcases hi.eq_or_lt with rfl | hlt
    · simpa using hcoord
    · simpa [ne_of_gt hlt] using htail i hlt
  · intro htail
    -- Conversely, coordinate `n` is strictly below `1`, while all later coordinates agree.
    have hx' : x < toColex (Finsupp.single n 1) := by
      rw [Finsupp.Colex.lt_iff]
      refine ⟨n, ?_, ?_⟩
      · intro i hi
        rw [htail i hi.le]
        simp [ne_of_gt hi]
      · rw [htail n le_rfl]
        simp
    simpa only [Set.mem_Iio] using hx'

/-- Helper for Exercise 10.9: read the finite nonzero prefix in reverse index order
and translate natural coordinates to positive naturals. -/
private def antidictionarySectionCoordinates (n : ℕ) :
    Set.Iio (toColex (Finsupp.single n 1) : Colex (ℕ →₀ ℕ)) → Lex (Fin n → ℕ+) :=
  fun x ↦ toLex (fun i ↦ OrderIso.pnatIsoNat.symm (x.1 (Fin.rev i).val))

/-- Helper for Exercise 10.9: the reversed finite-coordinate map is bijective. -/
private lemma antidictionarySectionCoordinates_bijective (n : ℕ) :
    Function.Bijective (antidictionarySectionCoordinates n) := by
  classical
  -- Equality of all finite coordinates, together with tail vanishing, recovers the finsupp.
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply ofColex.injective
    ext i
    by_cases hi : i < n
    · let j : Fin n := ⟨i, hi⟩
      have hcoord := congrFun (congrArg ofLex hxy) (Fin.rev j)
      have hnat := congrArg OrderIso.pnatIsoNat hcoord
      change x.1 (Fin.rev (Fin.rev j)).val = y.1 (Fin.rev (Fin.rev j)).val at hnat
      rw [Fin.rev_rev] at hnat
      exact hnat
    · have hxn : x.1 i = 0 :=
        (mem_antidictionarySection_iff n x.1).mp x.2 i (Nat.le_of_not_gt hi)
      have hyn : y.1 i = 0 :=
        (mem_antidictionarySection_iff n y.1).mp y.2 i (Nat.le_of_not_gt hi)
      rw [hxn, hyn]
  · intro g
    -- Extend the prescribed finite coordinates by zero outside `Fin n`.
    let finiteCoordinates : Fin n →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm
        (fun i ↦ OrderIso.pnatIsoNat (ofLex g (Fin.rev i)))
    let raw : ℕ →₀ ℕ := Finsupp.embDomain Fin.valEmbedding finiteCoordinates
    have hraw : ∀ i, n ≤ i → raw i = 0 := by
      intro i hi
      apply Finsupp.embDomain_notin_range
      intro hirange
      obtain ⟨j, hj⟩ := hirange
      rw [← hj] at hi
      exact (Nat.not_le_of_lt j.isLt) hi
    have hmem : toColex raw ∈
        Set.Iio (toColex (Finsupp.single n 1) : Colex (ℕ →₀ ℕ)) :=
      (mem_antidictionarySection_iff n (toColex raw)).mpr hraw
    refine ⟨⟨toColex raw, hmem⟩, ?_⟩
    apply ofLex.injective
    funext i
    have hrawCoordinate : raw (Fin.rev i).val =
        OrderIso.pnatIsoNat (ofLex g i) := by
      calc
        raw (Fin.rev i).val = finiteCoordinates (Fin.rev i) := by
          exact Finsupp.embDomain_apply_self Fin.valEmbedding finiteCoordinates (Fin.rev i)
        _ = OrderIso.pnatIsoNat (ofLex g i) := by
          simp [finiteCoordinates]
    change OrderIso.pnatIsoNat.symm (raw (Fin.rev i).val) = ofLex g i
    rw [hrawCoordinate, OrderIso.symm_apply_apply]

/-- Helper for Exercise 10.9: reversed finite coordinates identify lexicographic
comparison with the original colexicographic comparison. -/
private lemma antidictionarySectionCoordinates_lt_iff (n : ℕ)
    (x y : Set.Iio (toColex (Finsupp.single n 1) : Colex (ℕ →₀ ℕ))) :
    antidictionarySectionCoordinates n x < antidictionarySectionCoordinates n y ↔ x < y := by
  -- A least differing reversed coordinate is the greatest differing original coordinate.
  constructor
  · intro hxy
    change ∃ j, (∀ k, k < j →
      OrderIso.pnatIsoNat.symm (x.1 (Fin.rev k).val) =
        OrderIso.pnatIsoNat.symm (y.1 (Fin.rev k).val)) ∧
      OrderIso.pnatIsoNat.symm (x.1 (Fin.rev j).val) <
        OrderIso.pnatIsoNat.symm (y.1 (Fin.rev j).val) at hxy
    obtain ⟨j, heq, hlt⟩ := hxy
    have hcoord : x.1 (Fin.rev j).val < y.1 (Fin.rev j).val := by
      exact OrderIso.pnatIsoNat.symm.lt_iff_lt.mp hlt
    have hcolex : x.1 < y.1 := by
      rw [Finsupp.Colex.lt_iff]
      refine ⟨(Fin.rev j).val, ?_, hcoord⟩
      intro i hi
      by_cases hin : i < n
      · let k : Fin n := ⟨i, hin⟩
        have hrev : Fin.rev k < j := by
          change Fin.rev j < k at hi
          exact Fin.rev_lt_iff.mp hi
        have heq' := heq (Fin.rev k) hrev
        change OrderIso.pnatIsoNat.symm (x.1 (Fin.rev (Fin.rev k)).val) =
          OrderIso.pnatIsoNat.symm (y.1 (Fin.rev (Fin.rev k)).val) at heq'
        rw [Fin.rev_rev] at heq'
        exact OrderIso.pnatIsoNat.symm.injective heq'
      · have hxn : x.1 i = 0 :=
          (mem_antidictionarySection_iff n x.1).mp x.2 i (Nat.le_of_not_gt hin)
        have hyn : y.1 i = 0 :=
          (mem_antidictionarySection_iff n y.1).mp y.2 i (Nat.le_of_not_gt hin)
        rw [hxn, hyn]
    exact hcolex
  · intro hxy
    have hcolex : x.1 < y.1 := hxy
    rw [Finsupp.Colex.lt_iff] at hcolex
    obtain ⟨i, heq, hlt⟩ := hcolex
    have hin : i < n := by
      by_contra hni
      have hxn : x.1 i = 0 :=
        (mem_antidictionarySection_iff n x.1).mp x.2 i (Nat.le_of_not_gt hni)
      have hyn : y.1 i = 0 :=
        (mem_antidictionarySection_iff n y.1).mp y.2 i (Nat.le_of_not_gt hni)
      rw [hxn, hyn] at hlt
      exact (Nat.lt_irrefl 0 hlt)
    let j : Fin n := ⟨i, hin⟩
    change ∃ k, (∀ l, l < k →
      OrderIso.pnatIsoNat.symm (x.1 (Fin.rev l).val) =
        OrderIso.pnatIsoNat.symm (y.1 (Fin.rev l).val)) ∧
      OrderIso.pnatIsoNat.symm (x.1 (Fin.rev k).val) <
        OrderIso.pnatIsoNat.symm (y.1 (Fin.rev k).val)
    refine ⟨Fin.rev j, ?_, ?_⟩
    · intro k hk
      have hindex : i < (Fin.rev k).val := by
        change j < Fin.rev k
        exact Fin.lt_rev_iff.mp hk
      have heq' := heq (Fin.rev k).val hindex
      change OrderIso.pnatIsoNat.symm (x.1 (Fin.rev k).val) =
        OrderIso.pnatIsoNat.symm (y.1 (Fin.rev k).val)
      exact congrArg OrderIso.pnatIsoNat.symm heq'
    · rw [Fin.rev_rev]
      exact OrderIso.pnatIsoNat.symm.lt_iff_lt.mpr hlt

/-- Exercise 10.9 (1): Under the coordinate translation `f i = x_(i+1) - 1`,
eventually-`1` positive-integer sequences are finitely supported functions. The
strict section below `toColex (Finsupp.single n 1)` in antidictionary order has
the same order type as `Fin n → ℕ+` in dictionary order. -/
theorem antidictionarySectionOrderType (n : ℕ) :
    Nonempty
      (Set.Iio (toColex (Finsupp.single n 1) : Colex (ℕ →₀ ℕ)) ≃o
        Lex (Fin n → ℕ+)) := by
  -- Package the coordinate bijection with the strict-order comparison already proved.
  let coordinateEquiv :=
    Equiv.ofBijective (antidictionarySectionCoordinates n)
      (antidictionarySectionCoordinates_bijective n)
  refine ⟨{ toEquiv := coordinateEquiv, map_rel_iff' := ?_ }⟩
  intro x y
  constructor
  · intro hxy
    rcases lt_or_eq_of_le hxy with hlt | heq
    · exact le_of_lt ((antidictionarySectionCoordinates_lt_iff n x y).mp hlt)
    · exact le_of_eq (coordinateEquiv.injective heq)
  · intro hxy
    rcases lt_or_eq_of_le hxy with hlt | heq
    · exact le_of_lt ((antidictionarySectionCoordinates_lt_iff n x y).mpr hlt)
    · subst y
      exact le_rfl

/- Exercise 10.9 (2): The antidictionary order on eventually-`1`
positive-integer sequences is a well-order. -/
#check (inferInstance : IsWellOrder (Colex (ℕ →₀ ℕ)) (· < ·))

module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.EquivFin

public section

universe u

/-- Helper for Theorem 6.2: an equivalence with `Fin n` identifies a set's
finite cardinality with `n`. -/
private lemma ncard_eq_of_equivFin {α : Type u} {A : Set α} {n : ℕ}
    (e : A ≃ Fin n) : A.ncard = n := by
  -- Pass from the cardinality of the subtype to the set cardinality.
  simpa only [Nat.card_coe_set_eq] using Nat.card_eq_of_equiv_fin e

/-- If `A` is equivalent to `Fin n`, every proper subset `B` of `A` has
cardinality strictly less than `n`. -/
theorem ncard_lt_of_sSubset_of_equivFin {α : Type u} {A B : Set α} {n : ℕ}
    (hA : Nonempty (A ≃ Fin n)) (hBA : B ⊂ A) : B.ncard < n := by
  -- The equivalence makes the ambient set finite with cardinality `n`.
  obtain ⟨eA⟩ := hA
  have hAfinType : Finite A := eA.finite_iff.mpr inferInstance
  have hAfinite : A.Finite := Set.finite_coe_iff.mpr hAfinType
  -- Strict inclusion strictly decreases the finite cardinality.
  simpa only [ncard_eq_of_equivFin eA] using Set.ncard_lt_ncard hBA hAfinite

/-- The first conclusion of Theorem 6.2: a proper subset of a set equivalent to
`Fin n` is not equivalent to the same `Fin n`. -/
theorem noEquivFinOfSSubset {α : Type u} {A B : Set α} {n : ℕ}
    (hA : Nonempty (A ≃ Fin n)) (hBA : B ⊂ A) : ¬ Nonempty (B ≃ Fin n) := by
  -- A competing equivalence for `B` would turn the strict inequality into `n < n`.
  intro hB
  obtain ⟨eB⟩ := hB
  have hlt := ncard_lt_of_sSubset_of_equivFin hA hBA
  rw [ncard_eq_of_equivFin eB] at hlt
  exact (Nat.lt_irrefl n) hlt

/-- The second conclusion of Theorem 6.2: a nonempty proper subset of a set
equivalent to `Fin n` is equivalent to `Fin m` for some positive `m < n`. -/
theorem existsEquivFinLtOfNonemptySSubset {α : Type u} {A B : Set α} {n : ℕ}
    (hA : Nonempty (A ≃ Fin n)) (hBA : B ⊂ A) (hB : B.Nonempty) :
    ∃ m : ℕ, 0 < m ∧ m < n ∧ Nonempty (B ≃ Fin m) := by
  -- Inherit finiteness from `A`, and choose the canonical index `B.ncard`.
  obtain ⟨eA⟩ := hA
  have hAfinType : Finite A := eA.finite_iff.mpr inferInstance
  have hAfinite : A.Finite := Set.finite_coe_iff.mpr hAfinType
  have hBfinite : B.Finite := hAfinite.subset hBA.subset
  have hpositive : 0 < B.ncard := (Set.ncard_pos hBfinite).mpr hB
  have hsmaller : B.ncard < n :=
    ncard_lt_of_sSubset_of_equivFin ⟨eA⟩ hBA
  letI : Finite B := Set.finite_coe_iff.mpr hBfinite
  letI : Fintype B := Fintype.ofFinite B
  have eB : B ≃ Fin B.ncard := by
    simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using Fintype.equivFin B
  -- Package the cardinality, its bounds, and the canonical equivalence.
  refine ⟨B.ncard, hpositive, hsmaller, ?_⟩
  exact ⟨eB⟩

/-- Theorem 6.2. A proper subset of a set equivalent to `Fin n` is not
equivalent to `Fin n`; if it is nonempty, it is equivalent to `Fin m` for some
positive `m < n`. -/
theorem noEquivFinAndExistsEquivFinLtOfNonemptySSubset
    {α : Type u} {A B : Set α} {n : ℕ}
    (hA : Nonempty (A ≃ Fin n)) (hBA : B ⊂ A) :
    ¬ Nonempty (B ≃ Fin n) ∧
      (B.Nonempty → ∃ m : ℕ, 0 < m ∧ m < n ∧ Nonempty (B ≃ Fin m)) := by
  -- Combine the two conclusions while keeping nonemptiness conditional.
  constructor
  · exact noEquivFinOfSSubset hA hBA
  · intro hB
    exact existsEquivFinLtOfNonemptySSubset hA hBA hB

module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Int.Lemmas
public import Mathlib.Order.OrderIsoNat

public section

universe u

variable {A : Type u} [LinearOrder A]

/-- Helper for Exercise 10.4: absolute value reverses strict order on the negative integers. -/
private lemma negativeIntegerNatAbs_strictAnti :
    StrictAnti (fun z : {z : ℤ // z < 0} ↦ z.1.natAbs) := by
  -- Both integers lie in `Set.Iic 0`, so the standard antitonicity theorem applies.
  intro a b hab
  exact Int.strictAntiOn_natAbs (le_of_lt a.property) (le_of_lt b.property) hab

/-- Helper for Exercise 10.4: a strictly decreasing natural sequence yields an
order-embedded copy of the negative integers. -/
private lemma negativeIntegerEmbeddingOfStrictAnti (f : ℕ → A) (hf : StrictAnti f) :
    Nonempty ({z : ℤ // z < 0} ↪o A) := by
  -- Reindex the decreasing sequence by the order-reversing absolute-value map.
  have hmono : StrictMono (fun z : {z : ℤ // z < 0} ↦ f z.1.natAbs) := by
    intro a b hab
    exact hf (negativeIntegerNatAbs_strictAnti hab)
  exact ⟨OrderEmbedding.ofStrictMono (fun z ↦ f z.1.natAbs) hmono⟩

/-- Part (1) of Exercise 10.4: A linear order fails to be well ordered exactly when it
contains an order-embedded copy of the negative integers. The range of the
embedding is the subset with the same order type. -/
theorem notWellFoundedLT_iff_negativeIntegerEmbedding :
    ¬ WellFoundedLT A ↔ Nonempty ({z : ℤ // z < 0} ↪o A) := by
  constructor
  · -- A failure of well-foundedness supplies an infinite strictly descending chain.
    intro hnot
    classical
    have hrel : ¬ WellFounded ((· < ·) : A → A → Prop) := by
      intro hwellFounded
      exact hnot ⟨hwellFounded⟩
    rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff] at hrel
    obtain ⟨chain, hchain⟩ := hrel
    exact negativeIntegerEmbeddingOfStrictAnti chain (strictAnti_nat_of_succ_lt hchain)
  · -- The canonical enumeration of negative integers gives a forbidden descending chain.
    rintro ⟨e⟩ hwellFounded
    letI : WellFoundedLT A := hwellFounded
    have hnegative (n : ℕ) : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    let negativeInteger (n : ℕ) : {z : ℤ // z < 0} := ⟨Int.negSucc n, hnegative n⟩
    apply not_strictAnti_of_wellFoundedLT (fun n ↦ e (negativeInteger n))
    apply strictAnti_nat_of_succ_lt
    intro n
    rw [e.lt_iff_lt]
    simp [negativeInteger, Int.negSucc_eq]
    omega

/-- Helper for Exercise 10.4: the range of a negative-integer order embedding
is not well founded in its induced order. -/
private lemma rangeOfNegativeIntegerEmbedding_notWellFoundedLT
    (e : {z : ℤ // z < 0} ↪o A) : ¬ WellFoundedLT (Set.range e) := by
  -- Factor the embedding through its range without changing any order comparisons.
  have hrange (z : {z : ℤ // z < 0}) : e z ∈ Set.range e := Set.mem_range_self z
  have hmono : StrictMono (fun z : {z : ℤ // z < 0} ↦ (⟨e z, hrange z⟩ : Set.range e)) := by
    intro a b hab
    exact e.strictMono hab
  let rangeEmbedding : {z : ℤ // z < 0} ↪o Set.range e :=
    OrderEmbedding.ofStrictMono (fun z ↦ ⟨e z, hrange z⟩) hmono
  exact notWellFoundedLT_iff_negativeIntegerEmbedding.mpr ⟨rangeEmbedding⟩

/-- Exercise 10.4 (2): A linear order is well ordered if every countable subset
is well ordered in its induced order. -/
theorem wellFoundedLT_of_countableSubsets
    (h : ∀ s : Set A, s.Countable → WellFoundedLT s) : WellFoundedLT A := by
  -- Otherwise part (1) gives a countable range whose induced order is not well founded.
  by_contra hnot
  obtain ⟨e⟩ := notWellFoundedLT_iff_negativeIntegerEmbedding.mp hnot
  exact rangeOfNegativeIntegerEmbedding_notWellFoundedLT e
    (h (Set.range e) (Set.countable_range e))

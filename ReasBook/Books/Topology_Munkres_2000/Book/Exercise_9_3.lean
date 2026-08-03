module

public import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.FinRange
public import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Cardinal.NatCard

public section

private def freshSequence {A : Type u} [DecidableEq A]
    (emb : (n : ℕ+) → Fin n ↪ A) : ℕ → A :=
  Nat.strongRec fun n previous ↦
    let candidates : List (Fin (n + 1)) := List.finRange (n + 1)
    let fresh : Fin (n + 1) → Bool := fun i ↦
      decide (∀ j : Fin n, emb (Nat.succPNat n) i ≠ previous j j.isLt)
    let fallback : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    emb (Nat.succPNat n) ((candidates.find? fresh).getD fallback)

/-- Helper for Exercise 9.3: among `n + 1` embedded values, one avoids any
prescribed family of `n` previous values. -/
private theorem exists_finEmbedding_value_ne {A : Type u} {n : ℕ}
    (e : Fin (n + 1) ↪ A) (previous : Fin n → A) :
    ∃ i : Fin (n + 1), ∀ j : Fin n, e i ≠ previous j := by
  -- If every candidate collided with a previous value, the collision indices
  -- would inject `Fin (n + 1)` into `Fin n`.
  classical
  by_contra noFresh
  push Not at noFresh
  let collision : Fin (n + 1) → Fin n := fun i ↦
    Fin.find (fun j ↦ e i = previous j) (noFresh i)
  have collision_spec (i : Fin (n + 1)) : e i = previous (collision i) := by
    exact Fin.find_spec (noFresh i)
  have collision_injective : Function.Injective collision := by
    intro i k hik
    apply e.injective
    calc
      e i = previous (collision i) := collision_spec i
      _ = previous (collision k) := congrArg previous hik
      _ = e k := (collision_spec k).symm
  have card_le := Fintype.card_le_of_injective collision collision_injective
  simp only [Fintype.card_fin] at card_le
  exact Nat.not_succ_le_self n card_le

/-- Helper for Exercise 9.3: if a Boolean predicate holds somewhere in a list,
then it holds at the result of `find?`, independently of the fallback value. -/
private theorem List.find?_getD_eq_true_of_exists {α : Type u} (l : List α)
    (p : α → Bool) (fallback : α) (h : ∃ x, x ∈ l ∧ p x = true) :
    p ((l.find? p).getD fallback) = true := by
  -- A failed search would contradict the supplied satisfying list member.
  cases search : l.find? p with
  | none =>
      obtain ⟨x, hx, hpx⟩ := h
      have search_none : ∀ y ∈ l, ¬p y = true := List.find?_eq_none.mp search
      exact False.elim ((search_none x hx) hpx)
  | some x =>
      simpa only [search, Option.getD_some] using List.find?_some search

/-- Helper for Exercise 9.3: `freshSequence` at stage `n` is the first
candidate from the next finite embedding that avoids all earlier stages. -/
private theorem freshSequence_eq {A : Type u} [DecidableEq A]
    (emb : (n : ℕ+) → Fin n ↪ A) (n : ℕ) :
    freshSequence emb n =
      emb (Nat.succPNat n)
        (((List.finRange (n + 1)).find? fun i ↦
          decide (∀ j : Fin n, emb (Nat.succPNat n) i ≠ freshSequence emb j)).getD
            ⟨0, Nat.zero_lt_succ n⟩) := by
  -- The recursive predecessor supplied by `strongRec` is definitionally the
  -- already constructed value of `freshSequence`.
  unfold freshSequence
  rw [Nat.strongRec_eq]
  rfl

/-- Helper for Exercise 9.3: every term of `freshSequence` differs from all
terms at strictly earlier indices. -/
private theorem freshSequence_ne_of_lt {A : Type u} [DecidableEq A]
    (emb : (n : ℕ+) → Fin n ↪ A) {m n : ℕ} (hmn : m < n) :
    freshSequence emb n ≠ freshSequence emb m := by
  -- The finite pigeonhole lemma supplies a candidate satisfying the search
  -- predicate used by the recurrence equation.
  rw [freshSequence_eq]
  obtain ⟨i, hi⟩ := exists_finEmbedding_value_ne
    (emb (Nat.succPNat n)) (fun j ↦ freshSequence emb j)
  have candidateExists :
      ∃ i, i ∈ List.finRange (n + 1) ∧
        decide (∀ j : Fin n, emb (Nat.succPNat n) i ≠ freshSequence emb j) = true := by
    refine ⟨i, List.mem_finRange i, decide_eq_true_iff.mpr hi⟩
  have selectedFresh := List.find?_getD_eq_true_of_exists
    (List.finRange (n + 1))
    (fun i ↦ decide (∀ j : Fin n,
      emb (Nat.succPNat n) i ≠ freshSequence emb j))
    ⟨0, Nat.zero_lt_succ n⟩ candidateExists
  have avoidsPrevious : ∀ j : Fin n,
      emb (Nat.succPNat n)
        (((List.finRange (n + 1)).find? fun i ↦
          decide (∀ k : Fin n, emb (Nat.succPNat n) i ≠ freshSequence emb k)).getD
            ⟨0, Nat.zero_lt_succ n⟩) ≠ freshSequence emb j :=
    decide_eq_true_iff.mp selectedFresh
  exact avoidsPrevious ⟨m, hmn⟩

/-- Exercise 9.3: the recursively selected fresh values form an injective
sequence in `A`. -/
private theorem freshSequence_injective {A : Type u} [DecidableEq A]
    (emb : (n : ℕ+) → Fin n ↪ A) :
    Function.Injective (freshSequence emb) := by
  -- Unequal indices are ordered, and the later stage is fresh over the earlier.
  intro m n hmn
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact freshSequence_ne_of_lt emb hlt hmn.symm
  · exact freshSequence_ne_of_lt emb hgt hmn

private noncomputable def classicalFreshSequence {A : Type u}
    (emb : (n : ℕ+) → Fin n ↪ A) : ℕ → A :=
  @freshSequence A (Classical.decEq A) emb

private theorem classicalFreshSequence_injective {A : Type u}
    (emb : (n : ℕ+) → Fin n ↪ A) :
    Function.Injective (classicalFreshSequence emb) :=
  @freshSequence_injective A (Classical.decEq A) emb

/-- The infinitude conclusion of Exercise 9.3: a type admitting a specified
embedding of every positive finite initial segment is infinite. -/
theorem infinite_of_finEmbeddings {A : Type u}
    (emb : (n : ℕ+) → Fin n ↪ A) : Infinite A := by
  rw [← not_finite_iff_infinite]
  intro finite
  have card_le := Finite.card_le_of_embedding (emb (Nat.succPNat (Nat.card A)))
  rw [Nat.card_fin] at card_le
  exact Nat.not_succ_le_self _ card_le

/-- The explicit construction requested in Exercise 9.3: the specified family of finite
embeddings determines an embedding of the positive integers into `A` by repeatedly taking
the first unused value in the next finite embedding. This finite-stage construction does not
choose a member from an arbitrary family of nonempty sets. -/
noncomputable def positiveEmbeddingOfFinEmbeddings {A : Type u}
    (emb : (n : ℕ+) → Fin n ↪ A) : ℕ+ ↪ A :=
  { toFun := fun n ↦ classicalFreshSequence emb n.natPred
    inj' := (classicalFreshSequence_injective emb).comp PNat.natPred_injective }

module

public import Topology_Munkres_2000.Book.Definition_7_2
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.PNat.Interval

public section

/- Exercise 7.5 (1): The type of functions from a two-element set to the positive
integers is countable. -/
#check (inferInstance : Countable (Fin 2 → ℕ+))

/- Exercise 7.5 (2): For each positive integer `n`, the type of functions from an
`n`-element set to the positive integers is countable. -/
#check (fun _ : ℕ+ ↦ inferInstance : ∀ n : ℕ+, Countable (Fin n → ℕ+))

/- Exercise 7.5 (3): The tagged union over positive integers `n` of the function
types `Fin n → ℕ+` is countable. -/
#check (inferInstance : Countable (Σ n : ℕ+, Fin n → ℕ+))

/-- Helper for Exercise 7.5: a countably indexed function space is uncountable when
its codomain admits a fixed-point-free endomorphism. -/
lemma piUncountableOfFixedPointFree {ι α : Type*} [Nonempty α]
    (e : ι ≃ ℕ) (next : α → α) (hnext : ∀ x, next x ≠ x) :
    Uncountable (ι → α) := by
  -- Diagonalize against an arbitrary proposed enumeration of the function space.
  rw [uncountable_iff_forall_not_surjective]
  intro enumeration henumeration
  let diagonal : ι → α := fun i ↦ next (enumeration (e i) i)
  obtain ⟨k, hk⟩ := henumeration diagonal
  -- At the coordinate corresponding to `k`, equality contradicts fixed-point-freeness.
  have hcoordinate := congrFun hk (e.symm k)
  have heq : e (e.symm k) = k := e.apply_symm_apply k
  dsimp [diagonal] at hcoordinate
  rw [heq] at hcoordinate
  exact hnext (enumeration k (e.symm k)) hcoordinate.symm

/-- Helper for Exercise 7.5: sequences with a prescribed tail are determined by
their values on the finite initial segment before the tail begins. -/
lemma fixedTailSequencesCountable {α : Type*} [Countable α] (c : α) (N : ℕ+) :
    Countable {f : ℕ+ → α // ∀ n ≥ N, f n = c} := by
  let restrict : {f : ℕ+ → α // ∀ n ≥ N, f n = c} → ({n : ℕ+ // n < N} → α) :=
    fun f n ↦ f.1 n.1
  -- Equality on the finite prefix, together with the common tail, determines a sequence.
  have hrestrict : Function.Injective restrict := by
    intro f g hfg
    apply Subtype.ext
    funext n
    by_cases hn : n < N
    · have hvalue := congrFun hfg ⟨n, hn⟩
      exact hvalue
    · rw [f.2 n (le_of_not_gt hn), g.2 n (le_of_not_gt hn)]
  exact hrestrict.countable

/-- Helper for Exercise 7.5: sequences eventually equal to a fixed value form a
countable type. -/
lemma eventuallyEqSequencesCountable {α : Type*} [Countable α] (c : α) :
    Countable {f : ℕ+ → α // ∃ N : ℕ+, ∀ n ≥ N, f n = c} := by
  let fixedTail (N : ℕ+) : Set (ℕ+ → α) := {f | ∀ n ≥ N, f n = c}
  -- Each fixed threshold gives a countable family by finite-prefix restriction.
  have hfixedTail : ∀ N, (fixedTail N).Countable := by
    intro N
    exact @Countable.to_set _ (fixedTail N) (fixedTailSequencesCountable c N)
  have hunion : (⋃ N, fixedTail N).Countable := Set.countable_iUnion hfixedTail
  -- Membership in the union is exactly eventual equality to `c`.
  have heq : (⋃ N, fixedTail N) = {f | ∃ N : ℕ+, ∀ n ≥ N, f n = c} := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, fixedTail]
  rw [heq] at hunion
  exact hunion.to_subtype

/-- Helper for Exercise 7.5: eventually constant sequences over a countable type
form a countable type. -/
lemma eventuallyConstantSequencesCountable {α : Type*} [Countable α] :
    Countable {f : ℕ+ → α // ∃ c : α, ∃ N : ℕ+, ∀ n ≥ N, f n = c} := by
  let eventuallyEq (c : α) : Set (ℕ+ → α) :=
    {f | ∃ N : ℕ+, ∀ n ≥ N, f n = c}
  -- For each possible constant, the corresponding eventual-equality family is countable.
  have heventuallyEq : ∀ c, (eventuallyEq c).Countable := by
    intro c
    exact @Countable.to_set _ (eventuallyEq c) (eventuallyEqSequencesCountable c)
  have hunion : (⋃ c, eventuallyEq c).Countable := Set.countable_iUnion heventuallyEq
  -- Taking the union over all constants yields precisely the eventually constant sequences.
  have heq : (⋃ c, eventuallyEq c) =
      {f | ∃ c : α, ∃ N : ℕ+, ∀ n ≥ N, f n = c} := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, eventuallyEq]
  rw [heq] at hunion
  exact hunion.to_subtype

/-- Part (4) of Exercise 7.5: the type of positive-integer-valued sequences indexed
by the positive integers is uncountable. -/
instance positiveSequences_uncountable : Uncountable (ℕ+ → ℕ+) := by
  let next : ℕ+ → ℕ+ :=
    fun n ↦ Equiv.pnatEquivNat.symm (Equiv.pnatEquivNat n + 1)
  -- Transporting successor on `ℕ` gives a fixed-point-free map on positive integers.
  have hnext : ∀ n, next n ≠ n := by
    intro n hn
    have hnat := congrArg Equiv.pnatEquivNat hn
    simp only [next, Equiv.apply_symm_apply] at hnat
    omega
  exact piUncountableOfFixedPointFree Equiv.pnatEquivNat next hnext

/-- Part (5) of Exercise 7.5: the type of binary sequences indexed by the positive
integers is uncountable. -/
instance binaryPositiveSequences_uncountable : Uncountable (ℕ+ → Fin 2) := by
  -- Swapping the two binary values supplies the fixed-point-free diagonal map.
  have hswap : ∀ x : Fin 2, Equiv.swap (0 : Fin 2) 1 x ≠ x := by
    intro x
    simpa [Equiv.swap_apply_ne_self_iff] using (Fin.eq_zero_or_eq_succ x)
  exact piUncountableOfFixedPointFree Equiv.pnatEquivNat (Equiv.swap 0 1) hswap

/-- Part (6) of Exercise 7.5: the type of binary sequences on the positive integers
that are zero from some positive index onward is countable. -/
instance eventuallyZeroBinarySequences_countable :
    Countable {f : ℕ+ → Fin 2 // ∃ N : ℕ+, ∀ n ≥ N, f n = 0} := by
  -- Specialize the generic eventual-equality result to the binary value zero.
  exact eventuallyEqSequencesCountable 0

/-- Part (7) of Exercise 7.5: the type of positive-integer-valued sequences that
equal `1` from some positive index onward is countable. -/
instance eventuallyOnePositiveSequences_countable :
    Countable {f : ℕ+ → ℕ+ // ∃ N : ℕ+, ∀ n ≥ N, f n = 1} := by
  -- Specialize the generic eventual-equality result to the positive integer one.
  exact eventuallyEqSequencesCountable 1

/-- Part (8) of Exercise 7.5: the type of positive-integer-valued sequences that are
constant from some positive index onward is countable. -/
instance eventuallyConstantPositiveSequences_countable :
    Countable {f : ℕ+ → ℕ+ // ∃ c N : ℕ+, ∀ n ≥ N, f n = c} := by
  -- The generic countable-union theorem applies because the possible constants are countable.
  exact eventuallyConstantSequencesCountable (α := ℕ+)

/- Exercise 7.5 (9): The type of two-element finite subsets of the positive integers
is countable. -/
#check (inferInstance : Countable {s : Finset ℕ+ // s.card = 2})

/- Exercise 7.5 (10): The type of finite subsets of the positive integers is
countable. -/
#check (inferInstance : Countable (Finset ℕ+))

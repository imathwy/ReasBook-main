module

public import Topology_Munkres_2000.Book.Definition_11_3.GreedyChain
public import Mathlib.Data.PNat.Basic

public section

/-- Definition 11.3. The indicator of the elements accepted by the greedy chain
construction for the relation `r` and enumeration `a`. -/
noncomputable def greedyChainIndicator {A : Type u} (r : A → A → Prop) (a : ℕ+ → A) :
    ℕ+ → Fin 2 :=
  GreedyChain.indicator r (· < ·) a

/-- The greedy chain indicator accepts exactly the elements comparable with every
earlier accepted element. -/
theorem greedyChainIndicator_eq_zero_iff {A : Type u} (r : A → A → Prop)
    (a : ℕ+ → A) (i : ℕ+) :
    greedyChainIndicator r a i = 0 ↔
      ∀ j : ℕ+, j < i → greedyChainIndicator r a j = 0 →
        Relation.SymmGen r (a i) (a j) := by
  -- The imported module exposes the recursive equation as the definition's public interface.
  exact GreedyChain.indicator_eq_zero_iff r (fun j i : ℕ+ ↦ j < i) a i

/-- The greedy chain indicator accepts the first enumerated element. -/
theorem greedyChainIndicator_one {A : Type u} (r : A → A → Prop) (a : ℕ+ → A) :
    greedyChainIndicator r a 1 = 0 := by
  -- At the first index there are no earlier elements to test for comparability.
  rw [greedyChainIndicator_eq_zero_iff]
  intro j hj
  exact (not_lt_of_ge (show 1 ≤ j from bot_le) hj).elim

/-- The initial value and recursive acceptance condition uniquely determine the
greedy chain indicator. -/
theorem greedyChainIndicator_unique {A : Type u} (r : A → A → Prop) (a : ℕ+ → A)
    (h : ℕ+ → Fin 2) (h_one : h 1 = 0)
    (h_step : ∀ (i : ℕ+), 1 < i →
      (h i = 0 ↔ ∀ j : ℕ+, j < i → h j = 0 → Relation.SymmGen r (a i) (a j))) :
    h = greedyChainIndicator r a := by
  -- Compare the two indicators pointwise by well-founded induction on the index.
  funext i
  apply WellFoundedLT.induction i
  intro i ih
  by_cases hi : i = 1
  · subst i
    rw [h_one, greedyChainIndicator_one]
  · -- Earlier values agree by induction, so the recursive zero tests are equivalent.
    have hzero : h i = 0 ↔ greedyChainIndicator r a i = 0 := by
      calc
        h i = 0 ↔ ∀ j : ℕ+, j < i → h j = 0 → Relation.SymmGen r (a i) (a j) :=
          h_step i (lt_of_le_of_ne bot_le (Ne.symm hi))
        _ ↔ ∀ j : ℕ+, j < i → greedyChainIndicator r a j = 0 →
            Relation.SymmGen r (a i) (a j) := by
          constructor
          · intro hcomp j hji hj
            exact hcomp j hji ((ih j hji).symm ▸ hj)
          · intro hcomp j hji hj
            exact hcomp j hji ((ih j hji) ▸ hj)
        _ ↔ greedyChainIndicator r a i = 0 :=
          (greedyChainIndicator_eq_zero_iff r a i).symm
    -- Elements of `Fin 2` are determined by whether they equal zero.
    omega

/-- The subset consisting of the elements accepted by the greedy chain indicator. -/
noncomputable def greedyChain {A : Type u} (r : A → A → Prop) (a : ℕ+ → A) : Set A :=
  GreedyChain.set r (fun i j : ℕ+ ↦ i < j) a

/-- Membership in the greedy chain is witnessed by an accepted index. -/
theorem mem_greedyChain {A : Type u} (r : A → A → Prop) (a : ℕ+ → A) (x : A) :
    x ∈ greedyChain r a ↔
      ∃ i : ℕ+, greedyChainIndicator r a i = 0 ∧ a i = x := by
  -- The imported module exposes image membership as the definition's public interface.
  exact GreedyChain.mem_set r (fun j i : ℕ+ ↦ j < i) a x

/-- Helper for Definition 11.3: the elements accepted by the greedy indicator form a chain. -/
lemma greedyChain_isChain {A : Type u} (r : A → A → Prop) [IsStrictOrder A r]
    (a : ℕ+ → A) : IsChain r (greedyChain r a) := by
  -- Represent both chain elements by accepted indices in the enumeration.
  intro x hx y hy hxy
  rw [mem_greedyChain] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  have hij : i ≠ j := by
    intro hij
    apply hxy
    rw [hij]
  -- The later accepted index was tested against the earlier accepted index.
  obtain hij | hji := lt_or_gt_of_ne hij
  · exact Or.symm ((greedyChainIndicator_eq_zero_iff r a j).mp hj i hij hi)
  · exact (greedyChainIndicator_eq_zero_iff r a i).mp hi j hji hj

/-- Helper for Definition 11.3: a rejected index has an earlier accepted incomparable index. -/
lemma existsEarlierAccepted_not_symmGen_of_rejected {A : Type u} (r : A → A → Prop)
    (a : ℕ+ → A) (i : ℕ+) (hi : greedyChainIndicator r a i ≠ 0) :
    ∃ j : ℕ+, j < i ∧ greedyChainIndicator r a j = 0 ∧
      ¬ Relation.SymmGen r (a i) (a j) := by
  classical
  -- Rejection is the negation of universal comparability with earlier accepted indices.
  have hnot : ¬∀ j : ℕ+, j < i → greedyChainIndicator r a j = 0 →
      Relation.SymmGen r (a i) (a j) := by
    intro hcomp
    exact hi ((greedyChainIndicator_eq_zero_iff r a i).mpr hcomp)
  push Not at hnot
  exact hnot

/-- A surjective enumeration of a strict partial order produces a maximal chain. -/
theorem greedyChain_isMaxChain {A : Type u} (r : A → A → Prop) [IsStrictOrder A r]
    (a : ℕ+ → A) (ha : Function.Surjective a) :
    IsMaxChain r (greedyChain r a) := by
  -- Chainhood is the invariant maintained by every greedy acceptance step.
  refine ⟨greedyChain_isChain r a, ?_⟩
  intro t ht hsub
  apply Set.Subset.antisymm hsub
  intro x hx
  obtain ⟨i, rfl⟩ := ha x
  by_contra hnot
  have hi : greedyChainIndicator r a i ≠ 0 := by
    intro hi
    exact hnot ((mem_greedyChain r a (a i)).mpr ⟨i, hi, rfl⟩)
  -- A rejected enumerated element has an accepted incomparable predecessor.
  obtain ⟨j, hji, hj, hinc⟩ :=
    existsEarlierAccepted_not_symmGen_of_rejected r a i hi
  have haj : a j ∈ t := hsub ((mem_greedyChain r a (a j)).mpr ⟨j, hj, rfl⟩)
  have hane : a i ≠ a j := by
    intro hae
    apply hnot
    exact (mem_greedyChain r a (a i)).mpr ⟨j, hj, hae.symm⟩
  -- The alleged superchain makes those two distinct elements comparable, a contradiction.
  exact hinc (ht hx haj hane)


end

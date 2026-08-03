module

public import Topology_Munkres_2000.Book.Definition_8_1.RecursionFormula

public section

universe u

/-- Helper for Theorem 8.4: the function obtained by well-founded recursion on positive integers. -/
private def positiveRecursiveValue
    {A : Type u} (a₀ : A)
    (ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A) :
    ℕ+ → A :=
  -- The recursive step uses precisely the values on the strict initial section.
  WellFoundedLT.fix fun i previous ↦
    if hi : 1 < i then ρ hi (fun j ↦ previous j j.property) else a₀

/-- Helper for Theorem 8.4: the well-founded recursive function has the prescribed initial value. -/
private lemma positiveRecursiveValue_one
    {A : Type u} (a₀ : A)
    (ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A) :
    positiveRecursiveValue a₀ ρ 1 = a₀ := by
  -- Unfold one recursive step and select the initial-value branch.
  dsimp only [positiveRecursiveValue]
  rw [WellFoundedLT.fix_eq]
  simp only [lt_self_iff_false, ↓reduceDIte]

/-- Helper for Theorem 8.4: every later value is computed from its strict initial history. -/
private lemma positiveRecursiveValue_eq_of_one_lt
    {A : Type u} (a₀ : A)
    (ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A)
    (i : ℕ+) (hi : 1 < i) :
    positiveRecursiveValue a₀ ρ i =
      ρ hi ((Set.Iio i).restrict (positiveRecursiveValue a₀ ρ)) := by
  -- Unfold one recursive step and identify its predecessor family with restriction.
  dsimp only [positiveRecursiveValue]
  rw [WellFoundedLT.fix_eq]
  rw [dif_pos hi]
  congr 1

namespace Function

/-- Helper for Theorem 8.4: two functions satisfying the same positive recursion
formula are equal. -/
private lemma IsPositiveRecursionFormula.eq
    {A : Type u} {a₀ : A}
    {ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A}
    {f g : ℕ+ → A}
    (hf : f.IsPositiveRecursionFormula a₀ ρ)
    (hg : g.IsPositiveRecursionFormula a₀ ρ) :
    f = g := by
  -- Strong induction reduces equality at an index to equality on its strict history.
  funext i
  induction i using PNat.strongInductionOn with
  | _ i ih =>
      have h_one_le : (1 : ℕ+) ≤ i := one_le
      rcases eq_or_lt_of_le h_one_le with hi | hi
      · rw [← hi]
        exact hf.eq_one.trans hg.eq_one.symm
      · rw [hf.eq_of_one_lt i hi, hg.eq_of_one_lt i hi]
        -- The induction hypothesis identifies the two restricted histories pointwise.
        congr 1
        funext j
        exact ih j j.property

end Function

/-- Theorem 8.4 (Principle of recursive definition). Given an initial value and
a rule for every nonempty initial history of positive integers, there is a
unique function satisfying the resulting recursion. -/
theorem existsUnique_positiveRecursive
    (A : Type u) (a₀ : A)
    (ρ : ∀ {i : ℕ+}, 1 < i → (Set.Iio i → A) → A) :
    ∃! h : ℕ+ → A, h.IsPositiveRecursionFormula a₀ ρ := by
  -- Package the two computation rules, then invoke induction-based uniqueness.
  refine ⟨positiveRecursiveValue a₀ ρ, ?_, ?_⟩
  · exact Function.IsPositiveRecursionFormula.mk
      (positiveRecursiveValue_one a₀ ρ)
      (positiveRecursiveValue_eq_of_one_lt a₀ ρ)
  · intro g hg
    exact hg.eq (Function.IsPositiveRecursionFormula.mk
      (positiveRecursiveValue_one a₀ ρ)
      (positiveRecursiveValue_eq_of_one_lt a₀ ρ))

end

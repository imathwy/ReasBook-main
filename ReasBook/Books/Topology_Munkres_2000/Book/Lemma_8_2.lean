module

public import Topology_Munkres_2000.Book.Theorem_8_1.LeastUnused
public import Mathlib.Data.PNat.Basic

public section

/-- Helper for Lemma 8.2: pointwise agreement below a common index gives equality of
the ranges used before that index in two finite intervals. -/
private lemma earlierRange_eq_of_eqOn_lt
    (C : Set ℕ+) (n m i : ℕ+)
    (f : Set.Icc 1 n → C) (g : Set.Icc 1 m → C)
    (hiₙ : i ∈ Set.Icc 1 n) (hiₘ : i ∈ Set.Icc 1 m)
    (hEq : ∀ (j : ℕ+) (hjₙ : j ∈ Set.Icc 1 n) (hjₘ : j ∈ Set.Icc 1 m),
      j < i → f ⟨j, hjₙ⟩ = g ⟨j, hjₘ⟩) :
    f '' Set.Iio ⟨i, hiₙ⟩ = g '' Set.Iio ⟨i, hiₘ⟩ := by
  -- Transport each earlier index across the two interval domains.
  ext y
  constructor
  · rintro ⟨j, hji, rfl⟩
    have hjₘ : (j : ℕ+) ∈ Set.Icc 1 m :=
      ⟨j.property.1, le_trans (le_of_lt hji) hiₘ.2⟩
    refine ⟨⟨j, hjₘ⟩, ?_, ?_⟩
    · exact hji
    · exact (hEq j j.property hjₘ hji).symm
  · rintro ⟨j, hji, rfl⟩
    have hjₙ : (j : ℕ+) ∈ Set.Icc 1 n :=
      ⟨j.property.1, le_trans (le_of_lt hji) hiₙ.2⟩
    refine ⟨⟨j, hjₙ⟩, ?_, ?_⟩
    · exact hji
    · exact hEq j hjₙ j.property hji

/-- Helper for Lemma 8.2: least-unused selections with the same earlier range choose
the same current value. -/
private lemma Function.IsLeastUnused.eqAt_of_earlierRange_eq
    {ι κ α : Type*} [Preorder ι] [Preorder κ] [PartialOrder α]
    {f : ι → α} {g : κ → α} (hf : f.IsLeastUnused) (hg : g.IsLeastUnused)
    {i : ι} {j : κ} (hRange : f '' Set.Iio i = g '' Set.Iio j) :
    f i = g j := by
  -- Rewrite the unused sets to a common set and use uniqueness of its least element.
  exact IsLeast.unique (hf.at i) (hRange.symm ▸ hg.at j)

/-- Lemma 8.2. Two finite functions satisfying the recursion that selects at each
positive index the least element of `C` not used at an earlier index agree on
their common domain. -/
theorem recursiveLeastUnused_eqOn
    (C : Set ℕ+) (n m : ℕ+)
    (f : Set.Icc 1 n → C) (g : Set.Icc 1 m → C)
    (hf : f.IsLeastUnused) (hg : g.IsLeastUnused)
    (i : ℕ+) (hiₙ : i ∈ Set.Icc 1 n) (hiₘ : i ∈ Set.Icc 1 m) :
    f ⟨i, hiₙ⟩ = g ⟨i, hiₘ⟩ := by
  -- Strong induction turns the least-counterexample argument into agreement below `i`.
  induction i using PNat.strongInductionOn with
  | _ i ih =>
      have hRange : f '' Set.Iio ⟨i, hiₙ⟩ = g '' Set.Iio ⟨i, hiₘ⟩ := by
        apply earlierRange_eq_of_eqOn_lt C n m i f g hiₙ hiₘ
        intro j hjₙ hjₘ hji
        exact ih j hji hjₙ hjₘ
      -- Equal earlier ranges make the two recursion clauses select the same least value.
      exact hf.eqAt_of_earlierRange_eq hg hRange

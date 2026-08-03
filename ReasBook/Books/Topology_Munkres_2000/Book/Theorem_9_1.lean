module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.TFAE
public import Mathlib.Data.PNat.Equiv
public import Topology_Munkres_2000.Book.Corollary_6_3

public section

universe u

namespace Set

/-- Helper for Theorem 9.1: an injection from the positive integers yields an
injective, non-surjective self-map. -/
private lemma existsInjectiveNotSurjectiveOfInjectivePNat {X : Type u}
    (f : ℕ+ → X) (hf : Function.Injective f) :
    ∃ g : X → X, Function.Injective g ∧ ¬ Function.Surjective g := by
  classical
  -- Reindex the given sequence by `ℕ`, then shift its range forward by one.
  let e : ℕ ↪ X :=
    ⟨fun n ↦ f (Equiv.pnatEquivNat.symm n),
      hf.comp Equiv.pnatEquivNat.symm.injective⟩
  let r : Set.range e ≃ ℕ := (Equiv.ofInjective e e.injective).symm
  let g : X → X := fun x ↦
    if hx : x ∈ Set.range e then e (r ⟨x, hx⟩ + 1) else x
  refine ⟨g, ?_, ?_⟩
  · -- The shifted range and its fixed complement cannot collide.
    intro x y hxy
    by_cases hx : x ∈ Set.range e
    · by_cases hy : y ∈ Set.range e
      · simp only [g, hx, hy, ↓reduceDIte] at hxy
        have hr : r ⟨x, hx⟩ = r ⟨y, hy⟩ :=
          Nat.add_right_cancel (e.injective hxy)
        exact congrArg Subtype.val (r.injective hr)
      · simp only [g, hx, hy, ↓reduceDIte] at hxy
        exact (hy ⟨r ⟨x, hx⟩ + 1, hxy⟩).elim
    · by_cases hy : y ∈ Set.range e
      · simp only [g, hx, hy, ↓reduceDIte] at hxy
        exact (hx ⟨r ⟨y, hy⟩ + 1, hxy.symm⟩).elim
      · simpa only [g, hx, hy, ↓reduceDIte] using hxy
  · -- The first term of the sequence has no preimage under the shift.
    intro hg
    obtain ⟨x, hx⟩ := hg (e 0)
    by_cases hxr : x ∈ Set.range e
    · simp only [g, hxr, ↓reduceDIte] at hx
      have hn : r ⟨x, hxr⟩ + 1 = 0 := e.injective hx
      omega
    · simp only [g, hxr, ↓reduceDIte] at hx
      exact hxr ⟨0, hx.symm⟩

/-- Helper for Theorem 9.1: an injective non-surjective self-map of a set
identifies it with a proper subset of itself. -/
private lemma existsEquivSSubsetOfInjectiveNotSurjective {α : Type u} {A : Set α}
    (g : A → A) (hg : Function.Injective g) (hgs : ¬ Function.Surjective g) :
    ∃ B : Set α, B ⊂ A ∧ Nonempty (A ≃ B) := by
  classical
  -- Use the ambient range of the self-map as the desired subset.
  let q : A → α := fun a ↦ g a
  let B : Set α := Set.range q
  have hBA : B ⊆ A := by
    rintro y ⟨x, rfl⟩
    exact (g x).property
  have hBne : B ≠ A := by
    intro hBAeq
    apply hgs
    intro y
    have hy : (y : α) ∈ B := hBAeq.symm ▸ y.property
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    exact Subtype.ext hx
  have hBproper : B ⊂ A := by
    refine ⟨hBA, ?_⟩
    intro hAB
    exact hBne (Subset.antisymm hBA hAB)
  refine ⟨B, hBproper, ?_⟩
  -- Injectivity is preserved when the subtype map is viewed in the ambient type.
  have hq : Function.Injective q := by
    intro x y hxy
    exact hg (Subtype.ext hxy)
  exact ⟨Equiv.ofInjective q hq⟩

/-- Helper for Theorem 9.1: a set equivalent to a proper subset of itself is
infinite. -/
private lemma infiniteOfEquivSSubset {α : Type u} {A B : Set α}
    (hBA : B ⊂ A) (h : Nonempty (A ≃ B)) : A.Infinite := by
  -- Corollary 6.3 rules out such an equivalence for finite sets.
  rw [← Set.not_finite]
  intro hA
  exact hA.not_equiv_ssubset hBA h

/-- Theorem 9.1. For a set `A`, the existence of an injection from the positive
integers into `A`, an equivalence of `A` with a proper subset of itself, and
infinitude of `A` are equivalent. -/
theorem infinite_tfae {α : Type u} (A : Set α) :
    List.TFAE [
      ∃ f : ℕ+ → A, Function.Injective f,
      ∃ B : Set α, B ⊂ A ∧ Nonempty (A ≃ B),
      A.Infinite] := by
  tfae_have 1 → 2 := by
    rintro ⟨f, hf⟩
    obtain ⟨g, hg, hgs⟩ := existsInjectiveNotSurjectiveOfInjectivePNat f hf
    exact existsEquivSSubsetOfInjectiveNotSurjective g hg hgs
  tfae_have 2 → 3 := by
    rintro ⟨B, hBA, h⟩
    exact infiniteOfEquivSSubset hBA h
  tfae_have 3 → 1 := by
    intro hA
    -- An infinite subtype has a canonical embedding of `ℕ`; reindex by `ℕ+`.
    let e : ℕ ↪ A := hA.natEmbedding A
    refine ⟨fun n ↦ e (Equiv.pnatEquivNat n), ?_⟩
    exact e.injective.comp Equiv.pnatEquivNat.injective
  tfae_finish

/-- A set is infinite if and only if it admits an injection from the positive integers. -/
theorem infinite_iff_exists_injective_pnat {α : Type u} (A : Set α) :
    A.Infinite ↔ ∃ f : ℕ+ → A, Function.Injective f := by
  -- Extract the first and third statements from the proved equivalence list.
  exact (infinite_tfae A).out 2 0

/-- A set is infinite if and only if it is equivalent to a proper subset of itself. -/
theorem infinite_iff_exists_equiv_ssubset {α : Type u} (A : Set α) :
    A.Infinite ↔ ∃ B : Set α, B ⊂ A ∧ Nonempty (A ≃ B) := by
  -- Extract the second and third statements from the proved equivalence list.
  exact (infinite_tfae A).out 2 1

end Set

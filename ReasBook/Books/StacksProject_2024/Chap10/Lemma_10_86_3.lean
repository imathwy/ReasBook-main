import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

private theorem nonempty_sections_of_surjective_nat_inverse_system
    (F : ℕᵒᵖ ⥤ Type v)
    [∀ n : ℕᵒᵖ, Nonempty (F.obj n)]
    (hSurj : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)).op)) :
    F.sections.Nonempty := by
  classical
  choose preimage hpreimage using hSurj
  let a : ∀ n : ℕ, F.obj (op n) := fun n ↦ by
    induction n with
    | zero => exact Classical.choice inferInstance
    | succ n ih => exact preimage n ih
  have ha_succ : ∀ n : ℕ,
      F.map (homOfLE (Nat.le_add_right n 1)).op (a (n + 1)) = a n := by
    intro n
    exact hpreimage n (a n)
  have ha_compat : ∀ {j i : ℕ} (h : j ≤ i), F.map (homOfLE h).op (a i) = a j := by
    intro j i h
    induction h with
    | refl => simp
    | @step i h ih =>
        calc
          F.map (homOfLE (Nat.le.step h)).op (a (i + 1))
              = F.map (homOfLE h).op (F.map (homOfLE (Nat.le_add_right i 1)).op (a (i + 1))) := by
                  rw [show (homOfLE (Nat.le.step h)).op =
                    (homOfLE (Nat.le_add_right i 1)).op ≫ (homOfLE h).op by rfl]
                  simp [FunctorToTypes.map_comp_apply]
          _ = F.map (homOfLE h).op (a i) := by rw [ha_succ i]
          _ = a j := ih
  refine ⟨fun n ↦ a (unop n), ?_⟩
  intro i j f
  cases i
  cases j
  simpa using ha_compat (leOfHom f.unop)

-- Proof sketch: pass from `A` to the canonical owner subfunctor `A.toEventualRanges`, which is
-- pointwise nonempty and has surjective transition maps by the Mittag-Leffler hypothesis. Then use
-- the countable cofinal functor `ℕᵒᵖ ⥤ OrderDual I` to reduce to a sequential inverse system, and
-- construct a compatible thread recursively along the surjective successor maps.
/-- Lemma 10.86.3: if a directed inverse system of nonempty sets over a countable preorder satisfies
the Mittag-Leffler condition, then its inverse limit is nonempty. -/
theorem nonempty_sections_of_countable_mittagLeffler_inverse_system
    {I : Type u} [Preorder I] [IsDirectedOrder I] [Countable I]
    (A : OrderDual I ⥤ Type v) (hML : A.IsMittagLeffler) [∀ i : OrderDual I, Nonempty (A.obj i)] :
    A.sections.Nonempty := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      let _ : IsEmpty (OrderDual I) := by simpa using hI
      fconstructor <;> apply isEmptyElim
  | inr _ =>
      let _ : Countable (OrderDual I) := by simpa using (inferInstance : Countable I)
      let seqF : ℕᵒᵖ ⥤ OrderDual I := IsCofiltered.sequentialFunctor (OrderDual I)
      let B : ℕᵒᵖ ⥤ Type v := seqF ⋙ A.toEventualRanges
      haveI : ∀ n : ℕᵒᵖ, Nonempty (B.obj n) := fun n ↦ A.toEventualRanges_nonempty hML (seqF.obj n)
      have hB : B.sections.Nonempty := by
        apply nonempty_sections_of_surjective_nat_inverse_system
        intro n
        simpa [B, seqF] using
          A.surjective_toEventualRanges hML (seqF.map (homOfLE (Nat.le_add_right n 1)).op)
      let sB : B.sections := ⟨hB.some, hB.some_mem⟩
      obtain ⟨s, _⟩ := (Functor.bijective_sectionsPrecomp seqF A.toEventualRanges).surjective sB
      exact ⟨(A.toEventualRangesSectionsEquiv s).1, (A.toEventualRangesSectionsEquiv s).2⟩

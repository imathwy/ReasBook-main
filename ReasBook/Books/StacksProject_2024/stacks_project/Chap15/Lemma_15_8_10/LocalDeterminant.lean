import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Ring.NonZeroDivisors
import StacksProject_2024.stacks_project.Chap15.Definition_15_8_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_8_9
import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal

open scoped FittingIdeal

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
variable {k : ℕ} {f : R}

/-- Helper for Lemma 15.8.10: any surjective finite free presentation computes the same principal
`k`th Fitting ideal as the intrinsic owner `Fit[R]_(k)(M)`. -/
lemma presentationFittingIdeal_eq_principalIdeal_of_fittingIdeal_eq_principalIdeal
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (hfitk : Fit[R]_(k)(M) = principalIdeal f) :
    presentationFittingIdeal R M k π = principalIdeal f := by
  -- Rewrite the presentation-level ideal through the intrinsic Fitting ideal first.
  calc
    presentationFittingIdeal R M k π = Fit[R]_(k)(M) := by
      symm
      exact fittingIdeal_eq_presentationFittingIdeal (R := R) (M := M) k π hπ
    _ = principalIdeal f := hfitk

/-- Helper for Lemma 15.8.10: once the selected local matrix is expressed in the reindexed normal
form from Lemma `15.8.9`, each lower-block adjugate entry is already known to lie in `(f)` from
the intrinsic Fitting-ideal hypothesis. -/
lemma selected_minor_lower_block_entry_mem_principal_of_fittingIdeal_eq_principalIdeal
    (hfitk : Fit[R]_(k)(M) = principalIdeal f)
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (rows : Fin (n - k) ↪ Fin n) (cols : Fin (n - k) ↪ LinearMap.ker π)
    (rowComp : Fin k ↪ Fin n) (eRows : Fin (n - k) ⊕ Fin k ≃ Fin n)
    (heRows_left : ∀ i, eRows (Sum.inl i) = rows i)
    (heRows_right : ∀ j, eRows (Sum.inr j) = rowComp j)
    (A0 : Matrix (Fin (n - k) ⊕ Fin k) (Fin (n - k)) R)
    (hA0 :
      A0 = Matrix.reindex eRows.symm (Equiv.refl _)
        (fun r t ↦ ((cols t : LinearMap.ker π) : Fin n → R) r))
    (i : Fin k) (j : Fin (n - k)) :
    (A0.toRows₂ * A0.toRows₁.adjugate) i j ∈ principalIdeal f := by
  -- Convert the intrinsic hypothesis to the presentation-level owner before reusing Lemma 15.8.9.
  have hπfit :
      presentationFittingIdeal R M k π = principalIdeal f :=
    presentationFittingIdeal_eq_principalIdeal_of_fittingIdeal_eq_principalIdeal
      (R := R) (M := M) (k := k) (f := f) π hπ hfitk
  -- The reindexed selected-minor API from Lemma 15.8.9 gives the desired membership directly.
  exact lower_block_entries_mem_principal_of_selected_presentation_minor
    (R := R) (M := M) (k := k) (f := f)
    π hπfit rows cols rowComp eRows heRows_left heRows_right A0 hA0 i j

/-- Helper for Lemma 15.8.10: in the local determinant-trick normal form, the remaining source
step is to upgrade lower-block membership in `(f)` to literal vanishing by combining the
preceding-Fitting-ideal hypothesis with regularity of `f`. -/
theorem selected_minor_lower_block_entry_eq_zero_of_precedingFittingIdeal_eq_bot
    (hf : f ∈ nonZeroDivisors R)
    (hfitk : Fit[R]_(k)(M) = principalIdeal f)
    (hprecedingFitk : precedingFittingIdeal R M k = ⊥)
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π)
    (rows : Fin (n - k) ↪ Fin n) (cols : Fin (n - k) ↪ LinearMap.ker π)
    (rowComp : Fin k ↪ Fin n) (eRows : Fin (n - k) ⊕ Fin k ≃ Fin n)
    (heRows_left : ∀ i, eRows (Sum.inl i) = rows i)
    (heRows_right : ∀ j, eRows (Sum.inr j) = rowComp j)
    (A0 : Matrix (Fin (n - k) ⊕ Fin k) (Fin (n - k)) R)
    (hA0 :
      A0 = Matrix.reindex eRows.symm (Equiv.refl _)
        (fun r t ↦ ((cols t : LinearMap.ker π) : Fin n → R) r))
    (i : Fin k) (j : Fin (n - k)) :
    (A0.toRows₂ * A0.toRows₁.adjugate) i j = 0 := by
  -- Route correction: the unresolved source step is no longer hidden in the main theorem.
  -- It should be proved here by expressing the row-replacement determinant as a predecessor minor,
  -- using `hprecedingFitk` to force that larger minor to vanish, and then cancelling the final
  -- factor of `f` with the regularity hypothesis `hf`.
  sorry

end

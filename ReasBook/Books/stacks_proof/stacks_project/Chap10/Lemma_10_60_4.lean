import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

-- Layering for this item:
-- * source-facing: the maximal-ideal supremum formula in `WithBot ℕ∞`.
-- * core/canonical owner: `Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim` and
--   `Ideal.sup_primeHeight_eq_ringKrullDim`.
-- * bridge/view: lift those `ℕ∞`-valued owner equalities to `WithBot ℕ∞`, and handle the
--   subsingleton ring case separately.
-- Primitive data are just `[CommRing R]`; the displayed suprema are derived from
-- `Ideal.primeHeight`.

private theorem iSup_eq_bot_of_subsingleton
    (P : Ideal R → Prop) (f : ∀ I : Ideal R, P I → WithBot ℕ∞)
    (hP : ∀ ⦃I : Ideal R⦄, P I → I ≠ ⊤) [Subsingleton R] :
    (⨆ (I : Ideal R) (hI : P I), f I hI) = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine iSup_le fun I ↦ iSup_le fun hI ↦ ?_
  exact (hP hI (Subsingleton.elim I ⊤)).elim

private theorem withBot_iSup_eq_ringKrullDim {P : Ideal R → Prop} [Nontrivial R]
    (f : ∀ I : Ideal R, P I → ℕ∞)
    (hP : (↑(⨆ (I : Ideal R) (hI : P I), f I hI) : WithBot ℕ∞) = ringKrullDim R)
    (hne : Nonempty { I : Ideal R // P I }) :
    (⨆ (I : Ideal R) (hI : P I), (f I hI : WithBot ℕ∞)) = ringKrullDim R := by
  letI := hne
  simpa [iSup_subtype', WithBot.coe_iSup (OrderTop.bddAbove _)] using hP

/-- Lemma 10.60.4: the Krull dimension of `R` is the supremum of the heights of its maximal
prime ideals. This is stated in `WithBot ℕ∞`, so it also covers the subsingleton case, where both
sides are `⊥`. -/
@[stacks 00KG]
theorem ringKrullDim_eq_iSup_primeHeight_maximal :
    (⨆ (I : Ideal R) (_ : I.IsMaximal), (I.primeHeight : WithBot ℕ∞)) = ringKrullDim R := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      haveI := hR
      rw [ringKrullDim_eq_bot_of_subsingleton]
      simpa using iSup_eq_bot_of_subsingleton Ideal.IsMaximal
        (fun (I : Ideal R) (hI : I.IsMaximal) ↦
          (@Ideal.primeHeight _ _ I hI.isPrime : WithBot ℕ∞))
        (fun {I} hI ↦ Ideal.IsMaximal.ne_top hI)
  | inr hR =>
      haveI := hR
      obtain ⟨M, hM⟩ := Ideal.exists_maximal R
      exact withBot_iSup_eq_ringKrullDim
        (fun I hI ↦ @Ideal.primeHeight _ _ I hI.isPrime)
        Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim ⟨⟨M, hM⟩⟩

/-- Lemma 10.60.4, bridge/view form: the Krull dimension of `R` is also the supremum of the
heights of all prime ideals. This is the companion canonical equality
`Ideal.sup_primeHeight_eq_ringKrullDim`, extended to the subsingleton case. -/
@[stacks 00KG]
theorem ringKrullDim_eq_iSup_primeHeight :
    (⨆ (I : Ideal R) (_ : I.IsPrime), (I.primeHeight : WithBot ℕ∞)) = ringKrullDim R := by
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      haveI := hR
      rw [ringKrullDim_eq_bot_of_subsingleton]
      simpa using iSup_eq_bot_of_subsingleton Ideal.IsPrime
        (fun (I : Ideal R) (hI : I.IsPrime) ↦
          (@Ideal.primeHeight _ _ I hI : WithBot ℕ∞))
        (fun {I} hI ↦ Ideal.IsPrime.ne_top hI)
  | inr hR =>
      haveI := hR
      obtain ⟨M, hM⟩ := Ideal.exists_maximal R
      exact withBot_iSup_eq_ringKrullDim
        (fun I hI ↦ @Ideal.primeHeight _ _ I hI)
        Ideal.sup_primeHeight_eq_ringKrullDim ⟨⟨M, hM.isPrime⟩⟩

end

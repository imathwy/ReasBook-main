import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum TopologicalSpace

section

variable {R : Type u} [CommRing R] [Nontrivial R]

/- Lemma 10.21.4 is a `bridge/view` item. Its owner abstractions are
`PrimeSpectrum.isIdempotentElemEquivClopens` for clopen subsets of `Spec(R)` and
`connectedSpace_iff_clopen` for connectedness. The theorem below is the source-facing unpacking of
those canonical declarations. -/
/-- Lemma 10.21.4: for a nonzero commutative ring `R`, the prime spectrum `Spec(R)` is connected if
and only if every idempotent of `R` is trivial. -/
@[stacks 00EF]
theorem primeSpectrum_connectedSpace_iff_idempotents_trivial :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  let eToClopen : {e : R // IsIdempotentElem e} ≃o Clopens (PrimeSpectrum R) :=
    isIdempotentElemEquivClopens
  have htrivial :
      (∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) ↔
        ∀ s : Clopens (PrimeSpectrum R), s = ⊥ ∨ s = ⊤ := by
    constructor
    · intro htriv s
      let e := eToClopen.symm s
      rcases htriv e.1 e.2 with he | he
      · left
        have he' : e = eToClopen.symm ⊥ := by
          rw [isIdempotentElemEquivClopens_symm_bot]
          ext
          exact he
        exact eToClopen.symm.injective he'
      · right
        have he' : e = eToClopen.symm ⊤ := by
          rw [isIdempotentElemEquivClopens_symm_top]
          ext
          exact he
        exact eToClopen.symm.injective he'
    · intro hclopen e he
      let e' : {e : R // IsIdempotentElem e} := ⟨e, he⟩
      rcases hclopen (eToClopen e') with hs | hs
      · left
        have he' : e' = eToClopen.symm ⊥ := by
          simpa using congrArg eToClopen.symm hs
        simpa [eToClopen] using congrArg Subtype.val he'
      · right
        have he' : e' = eToClopen.symm ⊤ := by
          simpa using congrArg eToClopen.symm hs
        simpa [eToClopen] using congrArg Subtype.val he'
  constructor
  · intro hconn
    exact htrivial.mpr fun s ↦ by
      rcases (connectedSpace_iff_clopen.mp hconn).2 s s.isClopen with hs | hs
      · left
        exact Clopens.ext hs
      · right
        exact Clopens.ext hs
  · intro htriv
    refine connectedSpace_iff_clopen.mpr ?_
    refine ⟨nonempty_iff_nontrivial.mpr inferInstance, fun s hs ↦ ?_⟩
    rcases htrivial.mp htriv ⟨s, hs⟩ with ht | ht
    · left
      simpa using congrArg (fun u : Clopens (PrimeSpectrum R) ↦ (u : Set (PrimeSpectrum R))) ht
    · right
      simpa using congrArg (fun u : Clopens (PrimeSpectrum R) ↦ (u : Set (PrimeSpectrum R))) ht

end

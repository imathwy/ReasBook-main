import Mathlib
import StacksProject_2024.Chap10.IdempotentMap
import StacksProject_2024.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

namespace RingHom

/-- If the kernel of a ring map is locally nilpotent, then every idempotent in the image lifts
uniquely to an idempotent in the source. This is the chapter-level `bridge/view` from the
source-facing kernel condition `(ker f).IsLocallyNilpotent` to the canonical mathlib owner theorem
`existsUnique_isIdempotentElem_eq_of_ker_isNilpotent`. -/
theorem existsUnique_isIdempotentElem_eq_of_ker_isLocallyNilpotent
    {S : Type u} [Ring S] (f : R →+* S) (hker : (ker f).IsLocallyNilpotent)
    (e : S) (he : e ∈ f.range) (he' : IsIdempotentElem e) :
    ∃! e' : R, IsIdempotentElem e' ∧ f e' = e := by
  refine existsUnique_isIdempotentElem_eq_of_ker_isNilpotent f ?_ e he he'
  simpa [Ideal.mk_ker] using (Ideal.isLocallyNilpotent_iff (ker f)).mp hker

end RingHom

/-- Lemma 10.32.6: if `I` is locally nilpotent, then the quotient map `R → R ⧸ I` induces a
bijection on idempotents. This is the `source-facing` quotient statement; the unique-lift
formulation is a companion obtained by unpacking this induced map on the canonical idempotent
subtype. -/
theorem quotientMap_idempotents_bijective_of_isLocallyNilpotent {I : Ideal R}
    (hI : I.IsLocallyNilpotent) :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := by
  constructor
  · intro e₁ e₂ h
    apply Subtype.ext
    obtain ⟨e, he, huniq⟩ :=
      RingHom.existsUnique_isIdempotentElem_eq_of_ker_isLocallyNilpotent
        (Ideal.Quotient.mk I) (by simpa [Ideal.mk_ker] using hI) (Ideal.Quotient.mk I e₁.1)
        (Ideal.Quotient.mk_surjective _) (e₁.2.map (Ideal.Quotient.mk I))
    exact (huniq _ ⟨e₁.2, rfl⟩).trans
      (huniq _ ⟨e₂.2, by simpa using (congrArg Subtype.val h).symm⟩).symm
  · intro e
    obtain ⟨e', he', -⟩ :=
      RingHom.existsUnique_isIdempotentElem_eq_of_ker_isLocallyNilpotent
        (Ideal.Quotient.mk I) (by simpa [Ideal.mk_ker] using hI) e.1
        (Ideal.Quotient.mk_surjective _) e.2
    refine ⟨⟨e', he'.1⟩, ?_⟩
    exact Subtype.ext he'.2

/-- Companion formulation of Lemma 10.32.6: bijectivity of the quotient-induced map on
idempotents means precisely that every idempotent of `R ⧸ I` has a unique idempotent lift to
`R`. -/
theorem existsUnique_idempotent_lift_quotient_of_isLocallyNilpotent {I : Ideal R}
    (hI : I.IsLocallyNilpotent) (e : R ⧸ I) (he : IsIdempotentElem e) :
    ∃! e' : R, IsIdempotentElem e' ∧ Ideal.Quotient.mk I e' = e := by
  have hbij : Function.Bijective (Ideal.Quotient.mk I).idempotentMap :=
    quotientMap_idempotents_bijective_of_isLocallyNilpotent hI
  obtain ⟨e', he'⟩ := hbij.2 ⟨e, he⟩
  refine ⟨e'.1, ⟨e'.2, by simpa using congrArg Subtype.val he'⟩, ?_⟩
  intro y hy
  have hy' : (Ideal.Quotient.mk I).idempotentMap ⟨y, hy.1⟩ = ⟨e, he⟩ := by
    exact Subtype.ext hy.2
  exact (congrArg Subtype.val <| hbij.1 (he'.trans hy'.symm)).symm

end

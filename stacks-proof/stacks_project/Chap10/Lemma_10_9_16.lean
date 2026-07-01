import Mathlib.RingTheory.Localization.Ideal

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] (S : Submonoid A)

/- Lemma 10.9.16: every ideal `I'` of `Localization S` is the localization of its inverse image
in `A`, namely
`Ideal.map (algebraMap A (Localization S)) (Ideal.comap (algebraMap A (Localization S)) I') = I'`.
This is exactly the canonical theorem `IsLocalization.map_comap` specialized to ideals of
`Localization S`. -/
#check (IsLocalization.map_comap S (Localization S))

end

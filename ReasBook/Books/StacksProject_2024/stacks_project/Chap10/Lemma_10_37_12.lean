import StacksProject_2024.stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNormalRing R]

/- Lemma 10.37.12: a normal ring is integrally closed in its total ring of fractions.

This is a `bridge/view` item: the source-facing hypothesis is the project notion
`IsNormalRing R`, while the canonical owner abstraction for the conclusion is mathlib's
`IsIntegrallyClosed R`. The primitive data are the prime-localization normality conditions
packaged by `IsNormalRing`; integrally closedness in the total fraction ring is derived API. -/
-- Proof sketch: let `x` lie in the total ring of fractions of `R` and be integral over `R`.
-- For each prime ideal `p`, its image in `Localization.AtPrime p` is integral over that
-- localization, hence belongs to it because `IsNormalRing R` gives a normal domain there. The
-- corresponding denominator ideal is therefore not contained in any prime ideal, so it is the
-- unit ideal and `x` already lies in `R`.
/-- Lemma 10.37.12: a normal ring is integrally closed in its total ring of fractions. -/
theorem isIntegrallyClosed_of_isNormalRing : IsIntegrallyClosed R := sorry

instance : IsIntegrallyClosed R := isIntegrallyClosed_of_isNormalRing

end

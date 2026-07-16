import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_90_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

/-- Example 10.90.2: a valuation ring is coherent. The owner abstraction is
`IsCoherentRing`; finite presentation of finitely generated ideals is derived from this instance. -/
@[stacks 0EWV]
instance valuationRing_isCoherentRing : IsCoherentRing A where
  toCoherent :=
    { toFinite := by infer_instance
      finitePresentation_submodule := by
        intro I hI
        have hI' : I.FG := by
          simpa [Module.Finite.iff_fg] using hI
        letI : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hI'
        by_cases h : I = ⊥
        · subst h
          infer_instance
        · exact Module.FinitePresentation.of_equiv (Ideal.isoBaseOfIsPrincipal h) }

end

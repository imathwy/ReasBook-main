import Mathlib
import StacksProject_2024.Chap10.Definition_10_151_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: `Algebra.Unramified R S` is defined as the conjunction of the two typeclass facts
-- `Algebra.FormallyUnramified R S` and `Algebra.FiniteType R S`, so this is the direct
-- constructor/eliminator equivalence for that class.
/-- Lemma 10.151.2 (1): a ring map is unramified exactly when it is formally unramified and of
finite type. -/
theorem unramified_iff_formallyUnramified_and_finiteType :
    Unramified R S ↔ FormallyUnramified R S ∧ FiniteType R S := by
  constructor
  · intro h
    exact ⟨h.formallyUnramified, h.finiteType⟩
  · rintro ⟨hform, hft⟩
    exact ⟨hform, hft⟩

-- Proof sketch: by definition, `Algebra.GUnramified R S` extends the owner predicate
-- `Algebra.Unramified R S` together with `Algebra.FinitePresentation R S`; combine that with the
-- previous clause characterizing `Unramified R S` by formal unramifiedness and finite type.
/-- Lemma 10.151.2 (2): a ring map is G-unramified exactly when it is formally unramified and of
finite presentation. -/
theorem gUnramified_iff_formallyUnramified_and_finitePresentation :
    GUnramified R S ↔ FormallyUnramified R S ∧ FinitePresentation R S := by
  constructor
  · intro h
    exact ⟨h.toUnramified.formallyUnramified, h.toFinitePresentation⟩
  · rintro ⟨hform, hfp⟩
    letI : FormallyUnramified R S := hform
    letI : FinitePresentation R S := hfp
    exact inferInstance

end Algebra

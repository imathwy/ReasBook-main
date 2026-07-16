import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u
universe v

section

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- Lemma 10.37.17: the colimit of a directed system of normal rings is a normal ring. -/
-- Proof sketch: for a prime ideal `p` of `colimit F`, compare `Localization.AtPrime p` with the
-- filtered colimit of the localizations of the stages at the induced prime ideals. Each of those
-- localizations is a normal domain by the stagewise assumption, so the problem reduces to the
-- domain case. Then any element of the fraction field of the colimit ring that is integral over
-- the colimit comes from some stage together with a monic polynomial relation there, and
-- normality of that stage forces the element to lie in the stage ring, hence in the colimit.
theorem isNormalRing_of_isColimit_filtered_system
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ j, IsNormalRing (F.obj j)] :
    IsNormalRing c.pt := by
  sorry

/-- Filtered colimits of diagrams of normal rings carry the canonical normal-ring instance. -/
instance (F : J ⥤ CommRingCat.{u}) [HasColimit F] [∀ j, IsNormalRing (F.obj j)] :
    IsNormalRing ↑(colimit F) := by
  simpa using
    isNormalRing_of_isColimit_filtered_system F (colimit.cocone F) (colimit.isColimit F)

end

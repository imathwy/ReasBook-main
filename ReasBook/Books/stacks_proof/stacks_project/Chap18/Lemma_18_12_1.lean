import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 18.12.1: for a site presentation of a morphism of topoi by a continuous functor
`F : C ⥤ D` and a map of sheaves of rings `φ : \mathcal O' \to F_* \mathcal O`, the direct image
of sheaves of `\mathcal O`-modules is the canonical functor
`SheafOfModules.pushforward φ : Mod(\mathcal O) ⥤ Mod(\mathcal O')`. Its type already records
that the underlying sheaf of sets is pushed forward and that the construction is functorial in the
module sheaf. -/
recall SheafOfModules.pushforward

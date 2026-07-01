import Mathlib
import stacks_project.Chap10.Definition_10_82_1

open CategoryTheory Limits MonoidalCategory

universe u

namespace CategoryTheory
namespace ShortComplex

variable {R : Type u} [CommRing R]

namespace Splitting

-- Proof sketch: a splitting is preserved by the additive tensor functor `tensorLeft N`; applying
-- `ShortComplex.Splitting.shortExact` after tensoring gives short exactness for every `N`.
/-- A splitting of a short complex of `R`-modules makes it universally exact. -/
theorem universallyExact {S : ShortComplex (ModuleCat R)}
    (s : S.Splitting) : S.UniversallyExact := sorry

end Splitting

variable {J : Type u} [Category J] [IsFiltered J]

-- Proof sketch: for each `N`, tensor-left by `N` preserves colimits, so
-- `(colimit F).map (tensorLeft N)` identifies with the colimit of the tensorized diagram; exact
-- filtered colimits in `ModuleCat R` then preserve the short exactness supplied by `hF`.
/-- Example 10.82.2: the colimit of a directed system of universally exact short exact sequences of
`R`-modules is universally exact. -/
theorem universallyExact_colimit_of_isFiltered
    (F : J ⥤ ShortComplex (ModuleCat R))
    (hF : ∀ j, (F.obj j).UniversallyExact) :
    (colimit F).UniversallyExact := sorry

-- Proof sketch: each stage is universally exact by `Splitting.universallyExact`, applied to a
-- chosen stagewise splitting, and the previous theorem preserves universal exactness under
-- filtered colimits.
/-- A directed colimit of split short exact sequences of `R`-modules is universally exact. -/
theorem universallyExact_colimit_of_split_system
    (F : J ⥤ ShortComplex (ModuleCat R))
    (hF : ∀ j, Nonempty ((F.obj j).Splitting)) :
    (colimit F).UniversallyExact := sorry

end ShortComplex
end CategoryTheory

import Mathlib
import StacksProject_2024.Chap29.Definition_29_29_1
import StacksProject_2024.Chap29.Lemma_29_28_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / verified owner check:
- `lean_leansearch` surfaced nearby composition APIs for smooth morphisms and flat morphisms, but no
  pre-existing scheme-level owner for composition of `RelativeDimensionLE`/`RelativeDimension`;
- local project precedent verifies the source-facing owners `RelativeDimensionLE`, `RelativeDimension`,
  and the pointwise composition lemmas in `Chap29/Lemma_29_28_2.lean`, so the present item is best
  formalized as companion composition theorems for those existing owners.
-/

variable {X Y Z : Scheme.{u}} {d e : ℕ}

/-- Lemma 29.29.3 (1): if `f : X ⟶ Y` has relative dimension at most `d` and `g : Y ⟶ Z` has
relative dimension at most `e`, then `f ≫ g` has relative dimension at most `d + e`. -/
@[stacks 02NL]
theorem relativeDimensionLE_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [RelativeDimensionLE f d] [RelativeDimensionLE g e] :
    RelativeDimensionLE (f ≫ g) (d + e) := sorry

/-- Lemma 29.29.3 (2): if `f : X ⟶ Y` has relative dimension `d`, `g : Y ⟶ Z` has relative
dimension `e`, and `f` is flat, then `f ≫ g` has relative dimension `d + e`. -/
@[stacks 02NL]
theorem relativeDimension_comp_of_flat
    (f : X ⟶ Y) (g : Y ⟶ Z) [RelativeDimension f d] [RelativeDimension g e] [Flat f] :
    RelativeDimension (f ≫ g) (d + e) := sorry

end Scheme.Hom
end AlgebraicGeometry

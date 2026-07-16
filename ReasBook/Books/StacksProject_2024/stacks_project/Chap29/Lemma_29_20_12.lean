import StacksProject_2024.stacks_project.Chap29.Definition_29_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` recalled mathlib's composition instance
  `AlgebraicGeometry.instLocallyQuasiFiniteCompScheme`;
- local Chapter 29 defines the source-facing global owner `Scheme.Hom.QuasiFinite` as
  quasi-compact plus local quasi-finiteness.
- The Stacks tag evidence is consistent: item tag `01TL` and source URL
  `https://stacks.math.columbia.edu/tag/01TL`.
-/

/-- Lemma 29.20.12 (1): the composition of two locally quasi-finite morphisms of schemes is
locally quasi-finite. -/
@[stacks 01TL]
theorem locallyQuasiFinite_comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyQuasiFinite f) (hg : LocallyQuasiFinite g) :
    LocallyQuasiFinite (f ≫ g) := sorry

/-- Lemma 29.20.12 (2): the composition of two quasi-finite morphisms of schemes is
quasi-finite. -/
@[stacks 01TL]
theorem quasiFinite_comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : QuasiFinite f) (hg : QuasiFinite g) :
    QuasiFinite (f ≫ g) := sorry

end Scheme.Hom
end AlgebraicGeometry

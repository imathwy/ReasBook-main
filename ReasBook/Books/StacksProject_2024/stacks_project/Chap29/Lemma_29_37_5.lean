import StacksProject_2024.stacks_project.Chap29.Lemma_29_37_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced affine-scheme and affine-morphism API, confirming the affine-base
  owner `IsAffine S`.
- Nearby Chapter 29 files use the relative ampleness owner `RelativelyAmple`, while Chapter 28
  defines the absolute invertible-module ampleness owner as `Scheme.Modules.IsAmple`.
- The Stacks tag evidence is consistent: item tag `01VK` and source URL
  `https://stacks.math.columbia.edu/tag/01VK`.
-/

/-- Lemma 29.37.5: if the base scheme `S` is affine, then an invertible
`\mathcal O_X`-module is `f`-relatively ample if and only if it is ample on `X`. -/
@[stacks 01VK]
theorem relativelyAmple_iff_isAmple_of_isAffine
    [IsAffine S] [Scheme.Modules.Invertible L] :
    RelativelyAmple f L ↔ Scheme.Modules.IsAmple L := sorry

end

end AlgebraicGeometry

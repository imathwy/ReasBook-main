import Mathlib
import StacksProject_2024.Chap26.Definition_26_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the canonical scheme owners
-- `IsOpenImmersion`, `IsClosedImmersion`, `IsImmersion`, and the exact closed-then-open
-- factorization theorem `IsImmersion.isImmersion_iff_exists`; nearby Chapter 26 files identify
-- the locally-ringed-space closed-immersion owner as
-- `LocallyRingedSpace.IsClosedImmersion f.toLRSHom`.

/-- Definition 26.10.2 (1): a morphism of schemes is an open immersion exactly when it is an
open immersion of locally ringed spaces. -/
@[stacks 01IO]
theorem isOpenImmersion_iff_toLRSHom_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ LocallyRingedSpace.IsOpenImmersion f.toLRSHom := sorry

/-- Definition 26.10.2 (2): an open subscheme of a scheme `X` is represented by an open set
`U : X.Opens`, whose associated scheme `U.toScheme` includes into `X` by an open immersion. -/
@[stacks 01IO]
theorem openSubscheme_ι_isOpenImmersion
    {X : Scheme.{u}} (U : X.Opens) :
    IsOpenImmersion U.ι := sorry

/-- Definition 26.10.2 (3): a morphism of schemes is a closed immersion exactly when it is a
closed immersion of locally ringed spaces. -/
@[stacks 01IO]
theorem isClosedImmersion_iff_toLRSHom_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsClosedImmersion f ↔ LocallyRingedSpace.IsClosedImmersion f.toLRSHom := sorry

/-- Definition 26.10.2 (4): a closed subscheme represented by an ideal sheaf datum `I` has
underlying scheme `I.subscheme`, and its inclusion is a closed immersion of locally ringed
spaces. -/
@[stacks 01IO]
theorem closedSubscheme_ι_toLRSHom_isClosedImmersion
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    LocallyRingedSpace.IsClosedImmersion I.subschemeι.toLRSHom := sorry

/-- Definition 26.10.2 (5): a morphism of schemes is an immersion, or locally closed immersion,
exactly when it factors as a closed immersion followed by an open immersion. -/
@[stacks 01IO]
theorem isImmersion_iff_exists_closedImmersion_openImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsImmersion f ↔
      ∃ (Z : Scheme.{u}) (i : X ⟶ Z) (_ : IsClosedImmersion i)
        (j : Z ⟶ Y) (_ : IsOpenImmersion j),
        i ≫ j = f := sorry

end AlgebraicGeometry

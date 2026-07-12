import Mathlib
import StacksProject_2024.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled `FormallyUnramified.isOpenImmersion_diagonal` and
  `FormallyUnramified.instOfIsOpenImmersionDiagonalScheme`, the canonical scheme diagonal bridge.
- Local Chapter 29 precedent in `Lemma_29_35_9.lean` provides the source-facing owners
  `Unramified` and `GUnramified`.
-/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Lemma 29.35.13 (1): if `f` is unramified, then the diagonal morphism
`X ⟶ X ×_S X` is an open immersion. -/
@[stacks 02GE]
theorem isOpenImmersion_diagonal_of_unramified (f : X ⟶ S) [Unramified f] :
    IsOpenImmersion (pullback.diagonal f) := sorry

/-- Lemma 29.35.13 (2): if `f` is locally of finite type and its diagonal morphism
`X ⟶ X ×_S X` is an open immersion, then `f` is unramified. -/
@[stacks 02GE]
theorem unramified_of_locallyOfFiniteType_of_isOpenImmersion_diagonal
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsOpenImmersion (pullback.diagonal f)] :
    Unramified f := sorry

/-- Lemma 29.35.13 (3): if `f` is locally of finite presentation and its diagonal morphism
`X ⟶ X ×_S X` is an open immersion, then `f` is G-unramified. -/
@[stacks 02GE]
theorem gUnramified_of_locallyOfFinitePresentation_of_isOpenImmersion_diagonal
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [IsOpenImmersion (pullback.diagonal f)] :
    GUnramified f := sorry

end AlgebraicGeometry

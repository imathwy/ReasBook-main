import Mathlib
import StacksProject_2024.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` was unavailable in this session; local Chapter 29 precedent
uses `Unramified`, `GUnramified`, and `LocallyOfFiniteType` as the scheme-morphism owners. -/

variable {X Y S : Scheme.{u}}

/-- Lemma 29.35.16 (1): let `f : X ⟶ Y` be a morphism of schemes over `S`, exhibited by
`g : Y ⟶ S`. If `X` is unramified over `S`, i.e. if the composite `f ≫ g` is unramified, then
`f` is unramified. -/
@[stacks 02GG]
theorem unramified_of_comp_over_base
    (f : X ⟶ Y) (g : Y ⟶ S) [Unramified (f ≫ g)] :
    Unramified f := sorry

/-- Lemma 29.35.16 (2): let `f : X ⟶ Y` be a morphism of schemes over `S`, exhibited by
`g : Y ⟶ S`. If `X` is G-unramified over `S`, i.e. if the composite `f ≫ g` is G-unramified, and
`Y` is locally of finite type over `S`, then `f` is G-unramified. -/
@[stacks 02GG]
theorem gUnramified_of_comp_over_base
    (f : X ⟶ Y) (g : Y ⟶ S) [GUnramified (f ≫ g)] [LocallyOfFiniteType g] :
    GUnramified f := sorry

end AlgebraicGeometry

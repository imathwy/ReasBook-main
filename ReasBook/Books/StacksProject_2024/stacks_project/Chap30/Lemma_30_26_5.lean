import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` returned `AlgebraicGeometry.IsProper`,
-- `AlgebraicGeometry.UniversallyClosed`, `Scheme.Hom.isClosedMap`, and the properness
-- decomposition theorem `AlgebraicGeometry.isProper_iff`. Nearby Chapter 30 precedent represents
-- a closed subset proper over a base by the properness of its `vanishingIdeal` closed subscheme.

/-- Lemma 30.26.5 (1): if `X` and `Y` are locally of finite type over `S`, `f : X ⟶ Y`
is a morphism over `S`, `Y` is separated over `S`, and `Z ⊆ X` is closed and proper over
`S`, then the set-theoretic image `f(Z)` is closed in `Y`. -/
@[stacks 0CYQ]
theorem closedSubset_image_isClosed_of_isSeparated_over_base
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [IsSeparated pY] (Z : TopologicalSpace.Closeds X)
    [IsProper ((vanishingIdeal Z).subschemeι ≫ pX)] :
    IsClosed (f '' (Z : Set X)) := sorry

/-- Lemma 30.26.5 (2): if `X` and `Y` are locally of finite type over `S`, `f : X ⟶ Y`
is a morphism over `S`, `Y` is separated over `S`, and `Z ⊆ X` is closed and proper over
`S`, then the closed image `f(Z) ⊆ Y`, with its reduced closed-subscheme structure, is proper
over `S`. -/
@[stacks 0CYQ]
theorem closedSubset_image_isProper_of_isSeparated_over_base
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [IsSeparated pY] (Z : TopologicalSpace.Closeds X)
    [IsProper ((vanishingIdeal Z).subschemeι ≫ pX)]
    (hImage_closed : IsClosed (f '' (Z : Set X))) :
    IsProper
      ((vanishingIdeal (⟨f '' (Z : Set X), hImage_closed⟩ : TopologicalSpace.Closeds Y)).subschemeι ≫
        pY) := sorry

/-- Lemma 30.26.5 (3): if `X` and `Y` are locally of finite type over `S`, `f : X ⟶ Y`
is a universally closed morphism over `S`, and `Z ⊆ X` is closed and proper over `S`, then
the set-theoretic image `f(Z)` is closed in `Y`. -/
@[stacks 0CYQ]
theorem closedSubset_image_isClosed_of_universallyClosed
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [UniversallyClosed f] (Z : TopologicalSpace.Closeds X)
    [IsProper ((vanishingIdeal Z).subschemeι ≫ pX)] :
    IsClosed (f '' (Z : Set X)) := sorry

/-- Lemma 30.26.5 (4): if `X` and `Y` are locally of finite type over `S`, `f : X ⟶ Y`
is a universally closed morphism over `S`, and `Z ⊆ X` is closed and proper over `S`, then
the closed image `f(Z) ⊆ Y`, with its reduced closed-subscheme structure, is proper over `S`. -/
@[stacks 0CYQ]
theorem closedSubset_image_isProper_of_universallyClosed
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [UniversallyClosed f] (Z : TopologicalSpace.Closeds X)
    [IsProper ((vanishingIdeal Z).subschemeι ≫ pX)]
    (hImage_closed : IsClosed (f '' (Z : Set X))) :
    IsProper
      ((vanishingIdeal (⟨f '' (Z : Set X), hImage_closed⟩ : TopologicalSpace.Closeds Y)).subschemeι ≫
        pY) := sorry

/-- Lemma 30.26.5 (5): if `X` and `Y` are locally of finite type over `S`, `f : X ⟶ Y`
is a proper morphism over `S`, and `Z ⊆ Y` is closed and proper over `S`, then the closed
inverse image `f⁻¹(Z) ⊆ X`, with its reduced closed-subscheme structure, is proper over `S`. -/
@[stacks 0CYQ]
theorem closedSubset_preimage_isProper_of_isProper
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [IsProper f] (Z : TopologicalSpace.Closeds Y)
    [IsProper ((vanishingIdeal Z).subschemeι ≫ pY)] :
    IsProper ((vanishingIdeal (Z.preimage f.base.hom.2)).subschemeι ≫ pX) := sorry

end AlgebraicGeometry

import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_31_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry
open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the algebraic cotangent-base-change owners
-- `Ideal.mapCotangent` and `Ideal.toCotangent_surjective`; local Chapter 29 precedent verifies
-- that the scheme-side conormal comparison map is currently recorded in `Lemma_29_31_3` only as a
-- morphism existence statement. The source item is therefore formalized as existence of an epi
-- comparison map, and under flatness existence of an isomorphism, for the same source and target.

section

variable {Z X Z' X' : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z') (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z') CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z').HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z').HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z') AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z').WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z') CommRingCat.{u})]

/-- Lemma 29.31.4 (1): for a fiber product square of schemes
`Z ⟶ X`, `Z' ⟶ X'` with horizontal closed immersions, the conormal comparison morphism of
Lemma 29.31.3 is surjective. Since the comparison morphism is currently recorded only
existentially, this is formalized as existence of an epi map
`f^* \mathcal C_{Z'/X'} \to \mathcal C_{Z/X}`. -/
@[stacks 0473]
theorem exists_epi_immersionConormalMap_of_isPullback
    (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : IsPullback f i i' g) :
    ∃ φ : ((Scheme.Modules.pullback f).obj (immersionConormalSheaf i') ⟶
      immersionConormalSheaf i), Epi φ := sorry

/-- Lemma 29.31.4 (2): in the same fiber product situation, if `g : X ⟶ X'` is flat, then the
conormal comparison morphism of Lemma 29.31.3 is an isomorphism. Since the comparison morphism is
currently recorded only existentially, this is formalized as existence of an isomorphism
`f^* \mathcal C_{Z'/X'} \to \mathcal C_{Z/X}`. -/
@[stacks 0473]
theorem exists_isIso_immersionConormalMap_of_isPullback_of_flat
    (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i'] [Flat g]
    (sq : IsPullback f i i' g) :
    ∃ φ : ((Scheme.Modules.pullback f).obj (immersionConormalSheaf i') ⟶
      immersionConormalSheaf i), IsIso φ := sorry

end

end AlgebraicGeometry

import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_31_3

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced categorical exactness APIs such as
-- `CategoryTheory.IsPullback.exact_shortComplex'`; local project inspection of
-- `Chap17/Lemma_17_22_7.lean` and nearby conormal files verifies that the appropriate scheme-module
-- surface for a three-term sequence ending in `0` is a `ShortComplex` together with
-- `.Exact ∧ Epi` on the right map.

section

variable {X Y Z : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Y).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u})]

/-- Lemma 29.31.5: for immersions of schemes `Z ⟶ Y ⟶ X`, there is a canonical exact sequence
`i^* \mathcal C_{Y/X} ⟶ \mathcal C_{Z/X} ⟶ \mathcal C_{Z/Y} ⟶ 0`. Since the comparison maps from
Lemma 29.31.3 are currently recorded only existentially, this is formalized as existence of
comparison morphisms in `Z.Modules` whose associated short complex is exact and whose right map is
epimorphic. -/
@[stacks 062S]
theorem exists_exact_immersionConormalSequence
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    ∃ φ : ((Scheme.Modules.pullback i).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf (i ≫ j)),
      ∃ ψ : (immersionConormalSheaf (i ≫ j) ⟶ immersionConormalSheaf i),
        ∃ hφψ : φ ≫ ψ = 0, (ShortComplex.mk φ ψ hφψ).Exact ∧ Epi ψ := sorry

end

end AlgebraicGeometry

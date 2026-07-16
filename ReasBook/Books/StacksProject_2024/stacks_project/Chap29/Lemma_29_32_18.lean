import StacksProject_2024.stacks_project.Chap29.Lemma_29_32_15

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced general immersion infrastructure; local Chapter 29
-- precedent fixes the scheme-level conormal and relative-differential surfaces as
-- `immersionConormalSheaf`, `Ω[f.toShHom]`, `RingedSpace.Hom.pullback`, and `ShortComplex`
-- exactness with an epimorphic final map.

section

variable {Z X Y : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

/-- Lemma 29.32.18: let
`Z ⟶ X ⟶ Y` be morphisms of schemes, with the maps
`i : Z ⟶ X` and `i ≫ f : Z ⟶ Y` immersions. Then there is a canonical exact sequence
`\mathcal C_{Z/Y} ⟶ \mathcal C_{Z/X} ⟶ i^* \Omega_{X/Y} ⟶ 0`; the first map is the conormal
comparison map from Lemma 29.31.3 and the second map is the conormal-to-differentials map from
Lemma 29.32.15. In the current project these canonical comparison maps are represented by
existential morphisms whose associated short complex is exact and whose right map is epimorphic. -/
@[stacks 067L]
theorem exists_exact_immersionConormalToPullbackDifferentialsSequence
    (i : Z ⟶ X) (f : X ⟶ Y) [IsImmersion i] [IsImmersion (i ≫ f)] :
    ∃ φ : immersionConormalSheaf (i ≫ f) ⟶ immersionConormalSheaf i,
      ∃ ψ : immersionConormalSheaf i ⟶
          (RingedSpace.Hom.pullback i.toShHom).obj Ω[f.toShHom],
        ∃ hφψ : φ ≫ ψ = 0, (ShortComplex.mk φ ψ hφψ).Exact ∧ Epi ψ := sorry

end

end AlgebraicGeometry

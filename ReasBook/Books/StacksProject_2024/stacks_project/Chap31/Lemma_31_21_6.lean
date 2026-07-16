import Mathlib
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap29.Lemma_29_31_5
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

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

-- Semantic recall: `lean_leansearch` surfaced generic `ShortComplex` splitting/exactness API.
-- Local Chapter 29/31 precedent fixes conormal sheaves as `immersionConormalSheaf` and expresses
-- the canonical sequence of Lemma 29.31.5 through existential comparison morphisms.

/-- Lemma 31.21.6: let `Z ⟶ Y ⟶ X` be immersions of schemes. If `Z ⟶ Y` is
`H_1`-regular, then the canonical conormal sequence
`0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` from Lemma 29.31.5 is exact and locally split. In the
current project this is expressed by comparison morphisms whose `ShortComplex` is short exact and
whose induced stalk complexes admit splittings. -/
@[stacks 063N]
theorem exists_shortExact_stalkwiseSplit_immersionConormalSequence_of_isH1RegularImmersion
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion j] [IsH1RegularImmersion i] :
    ∃ φ : ((Scheme.Modules.pullback i).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf (i ≫ j)),
      ∃ ψ : (immersionConormalSheaf (i ≫ j) ⟶ immersionConormalSheaf i),
        ∃ hφψ : φ ≫ ψ = 0,
          (ShortComplex.mk φ ψ hφψ).ShortExact ∧
            ∀ z : Z,
              ∃ hz : RingedSpace.moduleStalkHom z φ ≫ RingedSpace.moduleStalkHom z ψ = 0,
                Nonempty
                  ((ShortComplex.mk
                    (RingedSpace.moduleStalkHom z φ)
                    (RingedSpace.moduleStalkHom z ψ)
                    hz).Splitting) := sorry

end

end AlgebraicGeometry

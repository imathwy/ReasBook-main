import Mathlib
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap29.Lemma_29_31_5
import StacksProject_2024.Chap31.Definition_31_21_1

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the generic immersion and `ShortComplex` owners, but
-- not a dedicated sheaf-level “locally split conormal sequence” predicate. Local Chapter 29/31
-- precedent therefore fixes the conormal-sequence owner from `Lemma_29_31_5.lean`, and the local
-- splitting hypothesis is expressed stalkwise via `RingedSpace.moduleStalkHom` and
-- `ShortComplex.Splitting`.

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

/-- The conormal sequence of immersions `Z ⟶ Y ⟶ X` is exact and stalkwise split if the canonical
comparison maps from Lemma 29.31.5 form an exact sequence in `Z.Modules` and the induced sequence
on every stalk of `Z` admits a splitting. This is the source-faithful replacement in the current
project for the source hypothesis that the conormal sequence is exact and locally split. -/
def immersionConormalSequenceExactStalkwiseSplit
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] : Prop :=
  ∃ φ : ((Scheme.Modules.pullback i).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf (i ≫ j)),
    ∃ ψ : (immersionConormalSheaf (i ≫ j) ⟶ immersionConormalSheaf i),
      ∃ hφψ : φ ≫ ψ = 0,
        (ShortComplex.mk φ ψ hφψ).Exact ∧ Epi ψ ∧
          ∀ z : Z,
            ∃ hz : RingedSpace.moduleStalkHom z φ ≫ RingedSpace.moduleStalkHom z ψ = 0,
              Nonempty
                ((ShortComplex.mk
                  (RingedSpace.moduleStalkHom z φ)
                  (RingedSpace.moduleStalkHom z ψ)
                  hz).Splitting)

omit [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
  [HasWeakSheafify (Opens.grothendieckTopology ↥Y) (Type u)] in
/-- Companion expansion for `immersionConormalSequenceExactStalkwiseSplit`. -/
theorem immersionConormalSequenceExactStalkwiseSplit_iff
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    immersionConormalSequenceExactStalkwiseSplit i j ↔
      ∃ φ : ((Scheme.Modules.pullback i).obj (immersionConormalSheaf j) ⟶
          immersionConormalSheaf (i ≫ j)),
        ∃ ψ : (immersionConormalSheaf (i ≫ j) ⟶ immersionConormalSheaf i),
          ∃ hφψ : φ ≫ ψ = 0,
            (ShortComplex.mk φ ψ hφψ).Exact ∧ Epi ψ ∧
              ∀ z : Z,
                ∃ hz : RingedSpace.moduleStalkHom z φ ≫ RingedSpace.moduleStalkHom z ψ = 0,
                  Nonempty
                    ((ShortComplex.mk
                      (RingedSpace.moduleStalkHom z φ)
                      (RingedSpace.moduleStalkHom z ψ)
                      hz).Splitting) :=
  Iff.rfl

/-- Lemma 31.21.8 (1): let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes. Assume `j` is
locally of finite presentation and that the conormal sequence of Lemma 29.31.5 is exact and
locally split. If `j ∘ i` is a quasi-regular immersion, then `i` is a quasi-regular immersion. In
the current project, the local splitting hypothesis is expressed by
`immersionConormalSequenceExactStalkwiseSplit i j`. -/
@[stacks 068Z]
theorem isQuasiRegularImmersion_of_comp_of_conormalSequenceExactStalkwiseSplit
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    [LocallyOfFinitePresentation j]
    (hconormal : immersionConormalSequenceExactStalkwiseSplit i j)
    [IsQuasiRegularImmersion (i ≫ j)] :
    IsQuasiRegularImmersion i := sorry

/-- Lemma 31.21.8 (2): let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes. Assume `j` is
locally of finite presentation and that the conormal sequence of Lemma 29.31.5 is exact and
locally split. If `j ∘ i` is an `H_1`-regular immersion, then `i` is an `H_1`-regular immersion.
In the current project, the local splitting hypothesis is expressed by
`immersionConormalSequenceExactStalkwiseSplit i j`. -/
@[stacks 068Z]
theorem isH1RegularImmersion_of_comp_of_conormalSequenceExactStalkwiseSplit
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    [LocallyOfFinitePresentation j]
    (hconormal : immersionConormalSequenceExactStalkwiseSplit i j)
    [IsH1RegularImmersion (i ≫ j)] :
    IsH1RegularImmersion i := sorry

/-- Lemma 31.21.8 (3): let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes. Assume `j` is
locally of finite presentation and that the conormal sequence of Lemma 29.31.5 is exact and
locally split. If both `j` and `j ∘ i` are Koszul-regular immersions, then `i` is a
Koszul-regular immersion. In the current project, the local splitting hypothesis is expressed by
`immersionConormalSequenceExactStalkwiseSplit i j`. -/
@[stacks 068Z]
theorem isKoszulRegularImmersion_of_comp_of_conormalSequenceExactStalkwiseSplit
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    [LocallyOfFinitePresentation j]
    (hconormal : immersionConormalSequenceExactStalkwiseSplit i j)
    [IsKoszulRegularImmersion j] [IsKoszulRegularImmersion (i ≫ j)] :
    IsKoszulRegularImmersion i := sorry

end

end AlgebraicGeometry

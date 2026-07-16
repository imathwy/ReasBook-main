import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced only generic immersion composition API. Local
-- Chapter 31 precedent fixes regular immersions as `IsRegularImmersion`, and Lemma 31.21.8 fixes
-- the conormal sequence owner as `immersionConormalSequenceExactStalkwiseSplit`.

/-- A morphism of schemes is a regular immersion in a neighbourhood of the point `z` if its
restriction to some open neighbourhood of `z` in the source is a regular immersion. -/
def IsRegularImmersionNear {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) : Prop :=
  ∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ i)

/-- Companion expansion for `IsRegularImmersionNear`. -/
theorem isRegularImmersionNear_iff {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    IsRegularImmersionNear i z ↔
      ∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ i) := sorry

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

/-- The conormal sequence of immersions `Z ⟶ Y ⟶ X` is exact and split in a neighbourhood of
`z` if the canonical conormal comparison maps are exact and epimorphic, and the induced stalk
sequence admits splittings at every point of some open neighbourhood of `z`. -/
def immersionConormalSequenceExactStalkwiseSplitNear
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z) : Prop :=
  ∃ φ : ((Scheme.Modules.pullback i).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf (i ≫ j)),
    ∃ ψ : (immersionConormalSheaf (i ≫ j) ⟶ immersionConormalSheaf i),
      ∃ hφψ : φ ≫ ψ = 0,
        (ShortComplex.mk φ ψ hφψ).Exact ∧ Epi ψ ∧
          ∃ U : Z.Opens, z ∈ U ∧
            ∀ z' : Z, z' ∈ U →
              ∃ hz : RingedSpace.moduleStalkHom z' φ ≫ RingedSpace.moduleStalkHom z' ψ = 0,
                Nonempty
                  ((ShortComplex.mk
                    (RingedSpace.moduleStalkHom z' φ)
                    (RingedSpace.moduleStalkHom z' ψ)
                    hz).Splitting)

/-- Companion expansion for `immersionConormalSequenceExactStalkwiseSplitNear`. -/
theorem immersionConormalSequenceExactStalkwiseSplitNear_iff
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z) :
    immersionConormalSequenceExactStalkwiseSplitNear i j z ↔
      ∃ φ : ((Scheme.Modules.pullback i).obj (immersionConormalSheaf j) ⟶
          immersionConormalSheaf (i ≫ j)),
        ∃ ψ : (immersionConormalSheaf (i ≫ j) ⟶ immersionConormalSheaf i),
          ∃ hφψ : φ ≫ ψ = 0,
            (ShortComplex.mk φ ψ hφψ).Exact ∧ Epi ψ ∧
              ∃ U : Z.Opens, z ∈ U ∧
                ∀ z' : Z, z' ∈ U →
                  ∃ hz : RingedSpace.moduleStalkHom z' φ ≫
                      RingedSpace.moduleStalkHom z' ψ = 0,
                    Nonempty
                      ((ShortComplex.mk
                        (RingedSpace.moduleStalkHom z' φ)
                        (RingedSpace.moduleStalkHom z' ψ)
                        hz).Splitting) := sorry

/-- The first clause in the local regular-immersion comparison: both factors are regular
immersions near the relevant points. -/
def regularImmersionNearFactors (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z) : Prop :=
  IsRegularImmersionNear i z ∧ IsRegularImmersionNear j (i.base z)

/-- Companion expansion for `regularImmersionNearFactors`. -/
theorem regularImmersionNearFactors_iff (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z) :
    regularImmersionNearFactors i j z ↔
      IsRegularImmersionNear i z ∧ IsRegularImmersionNear j (i.base z) := sorry

/-- The second clause in the local regular-immersion comparison: the first factor and composite
are regular immersions near `z`. -/
def regularImmersionNearSourceComposite (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z) : Prop :=
  IsRegularImmersionNear i z ∧ IsRegularImmersionNear (i ≫ j) z

/-- Companion expansion for `regularImmersionNearSourceComposite`. -/
theorem regularImmersionNearSourceComposite_iff (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z) :
    regularImmersionNearSourceComposite i j z ↔
      IsRegularImmersionNear i z ∧ IsRegularImmersionNear (i ≫ j) z := sorry

/-- The third clause in the local regular-immersion comparison: the composite is regular near `z`
and the conormal sequence is split exact near `z`. -/
def regularImmersionNearCompositeConormal
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z) : Prop :=
  IsRegularImmersionNear (i ≫ j) z ∧ immersionConormalSequenceExactStalkwiseSplitNear i j z

/-- Companion expansion for `regularImmersionNearCompositeConormal`. -/
theorem regularImmersionNearCompositeConormal_iff
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z) :
    regularImmersionNearCompositeConormal i j z ↔
      IsRegularImmersionNear (i ≫ j) z ∧
        immersionConormalSequenceExactStalkwiseSplitNear i j z := sorry

/-- Lemma 31.21.9: let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes, let `z : Z`,
`y = i(z)`, and `x = j(y)`. If `X` is locally Noetherian, then the following are equivalent:
`i` is a regular immersion near `z` and `j` is a regular immersion near `y`; `i` and `j ∘ i` are
regular immersions near `z`; and `j ∘ i` is a regular immersion near `z` while the conormal
sequence `0 ⟶ i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` is split exact near `z`. -/
@[stacks 0690]
theorem isRegularImmersionNear_tfae_of_comp_and_conormal
    [IsLocallyNoetherian X] (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    (z : Z) :
    List.TFAE
      [ regularImmersionNearFactors i j z,
        regularImmersionNearSourceComposite i j z,
        regularImmersionNearCompositeConormal i j z ] := sorry

end

end AlgebraicGeometry

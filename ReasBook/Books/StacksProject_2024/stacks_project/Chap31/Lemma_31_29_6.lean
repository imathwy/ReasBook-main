import StacksProject_2024.stacks_project.Chap10.Definition_10_78_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.stacks_project.Chap28.Definition_28_7_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced only generic open-immersion infrastructure; local
-- Chapter 31 precedent fixes the rank-one reflexive setup through `IsReflexive`,
-- the generic-stalk owner `Module.FiniteLocallyFreeOfRank`, the reflexive hull construction, and
-- the affine-morphism owner `IsAffineHom U.ι`.

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/-- The set of points where a section induces an isomorphism on stalks, used as the local
section-trivializing locus for the affine criterion in Lemma 31.29.6. -/
def rankOneReflexiveSectionIsoLocusForAffineCriterion {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) : Set X :=
  {x : X | IsIso (RingedSpace.moduleStalkHom x s)}

/-- The recursive sequence
`\mathcal O_X, \mathcal F, \mathcal F^{[2]}, \mathcal F^{[3]}, ...` used in the affine
criterion of Lemma 31.29.6. -/
def rankOneReflexiveSectionPowerForAffineCriterion (ℱ : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | 1 => ℱ
  | n + 2 => reflexiveHull (ℱ ⊗ rankOneReflexiveSectionPowerForAffineCriterion ℱ (n + 1))

/-- The transition maps in the section-power sequence used for the affine criterion. -/
noncomputable def rankOneReflexiveSectionPowerMapForAffineCriterion {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) :
    ∀ n : ℕ, rankOneReflexiveSectionPowerForAffineCriterion ℱ n ⟶
      rankOneReflexiveSectionPowerForAffineCriterion ℱ (n + 1)
  | 0 => s
  | n + 1 =>
      (λ_ (rankOneReflexiveSectionPowerForAffineCriterion ℱ (n + 1))).inv ≫
        tensorHom s (𝟙 (rankOneReflexiveSectionPowerForAffineCriterion ℱ (n + 1))) ≫
          toReflexiveHull (ℱ ⊗ rankOneReflexiveSectionPowerForAffineCriterion ℱ (n + 1))

/-- The morphism `\mathcal O_X ⟶ \mathcal F^{[n]}` representing the `n`th power of a section in
the reflexive tensor-power sequence of Lemma 31.29.6. -/
noncomputable def rankOneReflexiveSectionPowerMorphismForAffineCriterion {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) :
    ∀ n : ℕ, 𝟙_ X.Modules ⟶ rankOneReflexiveSectionPowerForAffineCriterion ℱ n
  | 0 => 𝟙 _
  | n + 1 =>
      rankOneReflexiveSectionPowerMorphismForAffineCriterion s n ≫
        rankOneReflexiveSectionPowerMapForAffineCriterion s n

/-- The stalk element denoted `s^n ∈ \mathcal F^{[n]}_x`, obtained by applying the `n`th
power morphism to the unit element of `\mathcal O_{X,x}`. -/
noncomputable def rankOneReflexiveSectionPowerStalkElementForAffineCriterion {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) (n : ℕ) (x : X) :
    ((TopCat.Presheaf.stalk
      (rankOneReflexiveSectionPowerForAffineCriterion ℱ n).val.presheaf x : AddCommGrpCat) :
      Type u) :=
  letI : MonoidalCategory (SheafOfModules X.ringCatSheaf) :=
    inferInstanceAs (MonoidalCategory X.Modules)
  RingedSpace.moduleStalkMap x
    ((SheafOfModules.unitIsoTensorUnit : 𝒪X ≅ 𝟙_ X.Modules).hom ≫
      rankOneReflexiveSectionPowerMorphismForAffineCriterion s n)
    ((RingedSpace.unitStalkLinearEquiv x).symm (1 : X.presheaf.stalk x))

/-- The successor stalk power is obtained from the previous one by the stalk map of multiplication
by the original section. -/
theorem rankOneReflexiveSectionPowerStalkElementForAffineCriterion_succ {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) (n : ℕ) (x : X) :
    rankOneReflexiveSectionPowerStalkElementForAffineCriterion s (n + 1) x =
      RingedSpace.moduleStalkMap x (rankOneReflexiveSectionPowerMapForAffineCriterion s n)
        (rankOneReflexiveSectionPowerStalkElementForAffineCriterion s n x) := sorry

/-- Lemma 31.29.6: for the rank-one coherent reflexive setup and section-power notation of this
section. The inclusion morphism
`j : U ⟶ X` is affine if and only if for every `x ∈ X \ U` there is an `n > 0` such that
`s^n ∈ \mathfrak m_x \mathcal F^{[n]}_x`. -/
@[stacks 0EBR]
theorem isAffineHom_iff_forall_complement_exists_sectionPowerStalkElement_mem_maximalIdeal_smul
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ]
    (hℱrank : Module.FiniteLocallyFreeOfRank (X.presheaf.stalk (genericPoint X))
      ((TopCat.Presheaf.stalk ℱ.val.presheaf (genericPoint X) : AddCommGrpCat) :
        Type u) 1)
    (s : 𝟙_ X.Modules ⟶ ℱ) (U : X.Opens)
    (hU : (U : Set X) = rankOneReflexiveSectionIsoLocusForAffineCriterion s) :
    IsAffineHom U.ι ↔
      ∀ x : X, x ∉ (U : Set X) →
        ∃ n : ℕ, 0 < n ∧
          rankOneReflexiveSectionPowerStalkElementForAffineCriterion s n x ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
              (⊤ : Submodule (X.presheaf.stalk x)
                ((TopCat.Presheaf.stalk
                  (rankOneReflexiveSectionPowerForAffineCriterion ℱ n).val.presheaf x :
                    AddCommGrpCat) : Type u)) := sorry

end AlgebraicGeometry.Scheme.Modules

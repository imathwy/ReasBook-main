import Mathlib.CategoryTheory.Retract
import StacksProject_2024.stacks_project.Chap22.Lemma_22_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]

-- Semantic recall hits: the cochain-complex analogue
-- `admissibleMono_factorization_through_biproduct_mappingCone_id` in `Lemma_22_7_4` provides the
-- canonical factorization pattern. Here the split projection/section data should reuse the
-- canonical owner `Retract`, while the source-facing extra clause remains the homotopy condition
-- recorded by `Homotopic`.

/-- Helper for Lemma 22.27.6: a retraction in `Comp(𝒜)` whose reverse composite is homotopic to
the identity on the source. -/
structure HomotopyRetract (x y : Comp R A) where
  /-- The underlying retract data: `y` is a retract of `x` with projection `x ⟶ y`. -/
  retract : Retract y x
  /-- The reverse composite is homotopic to the identity on the source. -/
  projection_comp_splitting_homotopic :
    Homotopic (x : A) (x : A) (retract.r ≫ retract.i) (𝟙 x)

namespace HomotopyRetract

variable {x y : Comp R A}

/-- The projection map exhibited by a `HomotopyRetract`. -/
abbrev projection (h : HomotopyRetract x y) : x ⟶ y :=
  h.retract.r

/-- The section of the projection exhibited by a `HomotopyRetract`. -/
abbrev splitting (h : HomotopyRetract x y) : y ⟶ x :=
  h.retract.i

@[simp] theorem splitting_comp_projection (h : HomotopyRetract x y) :
    h.splitting ≫ h.projection = 𝟙 y :=
  h.retract.retract

/-- The projection followed by the section is homotopic to the identity on the source. -/
theorem projection_comp_splitting_homotopic_id (h : HomotopyRetract x y) :
    Homotopic (x : A) (x : A) (h.projection ≫ h.splitting) (𝟙 x) :=
  h.projection_comp_splitting_homotopic

/-- The projection of a `HomotopyRetract` is a split epimorphism. -/
instance isSplitEpi_projection (h : HomotopyRetract x y) : IsSplitEpi h.projection :=
  IsSplitEpi.mk' ⟨h.splitting, h.splitting_comp_projection⟩

/-- The section of a `HomotopyRetract` is a split monomorphism. -/
instance isSplitMono_splitting (h : HomotopyRetract x y) : IsSplitMono h.splitting :=
  IsSplitMono.mk' ⟨h.projection, h.splitting_comp_projection⟩

/-- The projection of a `HomotopyRetract` lies in the canonical morphism property
`Comp.homotopyEquivalences`. -/
instance projection_homotopyEquivalences (h : HomotopyRetract x y) :
    Comp.homotopyEquivalences h.projection := by
  change IsIso h.projection.inK
  exact CategoryTheory.IsIso.mk ⟨h.splitting.inK, by
    calc
      h.projection.inK ≫ h.splitting.inK = (h.projection ≫ h.splitting).inK := by
        simpa using ((Comp.inKFunctor : Comp R A ⥤ K R A).map_comp h.projection h.splitting).symm
      _ = ((𝟙 x : x ⟶ x)).inK :=
        CompHom.toHomotopyClass_eq_of_homotopic h.projection_comp_splitting_homotopic_id
      _ = 𝟙 x.inK := rfl, by
    calc
      h.splitting.inK ≫ h.projection.inK = (h.splitting ≫ h.projection).inK := by
        simpa using ((Comp.inKFunctor : Comp R A ⥤ K R A).map_comp h.splitting h.projection).symm
      _ = ((𝟙 y : y ⟶ y)).inK := by
        simpa using congrArg CompHom.toHomotopyClass h.splitting_comp_projection
      _ = 𝟙 y.inK := rfl⟩

end HomotopyRetract

/-- The underlying morphism of a `HomotopyRetract` is its projection. -/
instance instCoeOutHomotopyRetract (x y : Comp R A) :
    CoeOut (HomotopyRetract x y) (x ⟶ y) where
  coe h := h.projection

/-- Lemma 22.27.6: in Situation `22.27.2`, every morphism `α : x ⟶ y` in `Comp(𝒜)` factors
through an admissible monomorphism `x ⟶ ỹ`, and the projection `ỹ ⟶ y` admits a section whose
reverse composite is homotopic to the identity on `ỹ`. -/
@[stacks 09QM]
theorem exists_admissibleMono_factorization
    [HasShift (Comp R A) ℤ]
    [HasAdmissibleCones R A]
    {x y : Comp R A}
    (α : x ⟶ y) :
    ∃ (tildeY : Comp R A) (tildeα : x ⟶ tildeY) (r : HomotopyRetract tildeY y),
      IsAdmissibleMono compForgetToDegreeZero tildeα ∧ tildeα ≫ r.projection = α := sorry

end

import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_23_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_20_2
import StacksProject_2024.stacks_project.Chap31.«31_20_0_3»

open AlgebraicGeometry
open CategoryTheory
open Opposite
open RingTheory
open RingTheory.Sequence
open SheafOfModules.RingedSite (idealSectionIdeal)
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)

-- Semantic recall: `lean_leansearch` did not surface a direct sheaf-level owner for the
-- finite-locally-free conormal condition or for the symmetric-power comparison maps. The
-- source-facing predicates below therefore reuse the Chapter 31 regular-ideal-sheaf owners
-- `idealSheafStalkIdeal`, `idealQuotientSupport`, `idealSectionToRingSection`,
-- `IsGeneratedByIdealSectionFamilyOn`, together with `SheafOfModules.IsFiniteType`,
-- `Ideal.Cotangent`, and `quasiRegularIdealAssociatedGradedPolynomialMap`.

/-- If `f` generates `I` on `U`, then every restricted member of `f` lies in the corresponding
section ideal on any smaller open `V ⟶ U`. -/
theorem restrictedIdealSectionFamily_mem_idealSectionIdeal
    (I : Subobject 𝒪X) {U : Opens X} {r : ℕ}
    (f : Fin r → (I : ModX).val.obj (op U))
    (hgen : IsGeneratedByIdealSectionFamilyOn I U f)
    {V : Opens X} (i : V ⟶ U) (j : Fin r) :
    idealSectionToRingSection I V (((I : ModX).val.map i.op).hom (f j)) ∈
      idealSectionIdeal I (op V) := by
  rw [hgen i]
  exact Ideal.subset_span ⟨j, rfl⟩

/-- A finite family of local ideal-sheaf sections trivializes the conormal quotients on `U` when,
after restriction to every smaller open `V ⟶ U`, their cotangent classes form a basis of
`\mathcal J(V) / \mathcal J(V)^2` over `\mathcal O_X(V) / \mathcal J(V)`. -/
def idealSectionCotangentBasisOn
    (I : Subobject 𝒪X) (U : Opens X) {r : ℕ}
    (f : Fin r → (I : ModX).val.obj (op U))
    (hgen : IsGeneratedByIdealSectionFamilyOn I U f) :
    Prop :=
  ∀ ⦃V : Opens X⦄ (i : V ⟶ U),
    ∃ b : Module.Basis (Fin r)
        (X.presheaf.obj (op V) ⧸ idealSectionIdeal I (op V))
        ((idealSectionIdeal I (op V)).Cotangent),
      ∀ j,
        b j =
          Ideal.toCotangent (idealSectionIdeal I (op V))
            ⟨idealSectionToRingSection I V (((I : ModX).val.map i.op).hom (f j)),
              restrictedIdealSectionFamily_mem_idealSectionIdeal
                I f hgen i j⟩

/-- Companion expansion for `idealSectionCotangentBasisOn`. -/
theorem idealSectionCotangentBasisOn_iff
    (I : Subobject 𝒪X) (U : Opens X) {r : ℕ}
    (f : Fin r → (I : ModX).val.obj (op U))
    (hgen : IsGeneratedByIdealSectionFamilyOn I U f) :
    idealSectionCotangentBasisOn I U f hgen ↔
      ∀ ⦃V : Opens X⦄ (i : V ⟶ U),
        ∃ b : Module.Basis (Fin r)
            (X.presheaf.obj (op V) ⧸ idealSectionIdeal I (op V))
            ((idealSectionIdeal I (op V)).Cotangent),
          ∀ j,
            b j =
              Ideal.toCotangent (idealSectionIdeal I (op V))
                ⟨idealSectionToRingSection I V (((I : ModX).val.map i.op).hom (f j)),
                  restrictedIdealSectionFamily_mem_idealSectionIdeal
                    I f hgen i j⟩ :=
  Iff.rfl

/-- A finite family of local ideal-sheaf sections satisfies the associated-graded polynomial
criterion on `U` when, after restriction to every smaller open `V ⟶ U`, the canonical map from
the polynomial algebra on the chosen generators to the associated graded ring of
`idealSectionIdeal I (op V)` is bijective. This is the coordinate form of the symmetric-power
comparison in Lemma 31.20.4. -/
def idealSectionAssociatedGradedPolynomialCriterionOn
    (I : Subobject 𝒪X) (U : Opens X) {r : ℕ}
    (f : Fin r → (I : ModX).val.obj (op U))
    (hgen : IsGeneratedByIdealSectionFamilyOn I U f) :
    Prop :=
  ∀ ⦃V : Opens X⦄ (i : V ⟶ U),
    Function.Bijective
      (quasiRegularIdealAssociatedGradedPolynomialMap
        (idealSectionIdeal I (op V))
        (fun j ↦
          ⟨idealSectionToRingSection I V (((I : ModX).val.map i.op).hom (f j)),
            restrictedIdealSectionFamily_mem_idealSectionIdeal
              I f hgen i j⟩))

/-- Companion expansion for
`idealSectionAssociatedGradedPolynomialCriterionOn`. -/
theorem idealSectionAssociatedGradedPolynomialCriterionOn_iff
    (I : Subobject 𝒪X) (U : Opens X) {r : ℕ}
    (f : Fin r → (I : ModX).val.obj (op U))
    (hgen : IsGeneratedByIdealSectionFamilyOn I U f) :
    idealSectionAssociatedGradedPolynomialCriterionOn I U f hgen ↔
      ∀ ⦃V : Opens X⦄ (i : V ⟶ U),
        Function.Bijective
          (quasiRegularIdealAssociatedGradedPolynomialMap
            (idealSectionIdeal I (op V))
            (fun j ↦
              ⟨idealSectionToRingSection I V (((I : ModX).val.map i.op).hom (f j)),
                  restrictedIdealSectionFamily_mem_idealSectionIdeal
                    I f hgen i j⟩)) :=
  Iff.rfl

/-- The local coordinate form of the source condition that `\mathcal J / \mathcal J^2` is finite
locally free over `\mathcal O_X / \mathcal J`: near every point of the support of
`\mathcal O_X / \mathcal J`, there is a finite family of ideal-sheaf sections which generates the
ideal sheaf and gives a basis of the conormal quotients on all smaller opens. -/
def idealSheafConormalFiniteLocallyFreeCriterion
    (I : Subobject 𝒪X) : Prop :=
  ∀ x ∈ idealQuotientSupport I,
    ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
      ∃ hgen : IsGeneratedByIdealSectionFamilyOn I U f,
        idealSectionCotangentBasisOn I U f hgen

/-- Companion expansion for `idealSheafConormalFiniteLocallyFreeCriterion`. -/
theorem idealSheafConormalFiniteLocallyFreeCriterion_iff
    (I : Subobject 𝒪X) :
    idealSheafConormalFiniteLocallyFreeCriterion I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
          ∃ hgen : IsGeneratedByIdealSectionFamilyOn I U f,
            idealSectionCotangentBasisOn I U f hgen :=
  Iff.rfl

/-- The local coordinate form of the source condition that the canonical symmetric/conormal
algebra map is an isomorphism: near every point of the support of `\mathcal O_X / \mathcal J`,
there is a finite family of ideal-sheaf sections which generates the ideal sheaf and yields
bijective associated-graded polynomial maps on all smaller opens. -/
def idealSheafAssociatedGradedPolynomialCriterion
    (I : Subobject 𝒪X) : Prop :=
  ∀ x ∈ idealQuotientSupport I,
    ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
      ∃ hgen : IsGeneratedByIdealSectionFamilyOn I U f,
        idealSectionAssociatedGradedPolynomialCriterionOn I U f hgen

/-- Companion expansion for `idealSheafAssociatedGradedPolynomialCriterion`. -/
theorem idealSheafAssociatedGradedPolynomialCriterion_iff
    (I : Subobject 𝒪X) :
    idealSheafAssociatedGradedPolynomialCriterion I ↔
      ∀ x ∈ idealQuotientSupport I,
        ∃ (U : Opens X) (_ : x ∈ U) (r : ℕ) (f : Fin r → (I : ModX).val.obj (op U)),
          ∃ hgen : IsGeneratedByIdealSectionFamilyOn I U f,
            idealSectionAssociatedGradedPolynomialCriterionOn I U f hgen :=
  Iff.rfl

/-- Lemma 31.20.4: for an ideal sheaf `\mathcal J \subset \mathcal O_X` on a locally ringed
space, quasi-regularity is equivalent to finite type together with the source conditions that
`\mathcal J / \mathcal J^2` is finite locally free over `\mathcal O_X / \mathcal J` and that the
canonical symmetric-power maps onto `\mathcal J^n / \mathcal J^{n + 1}` are isomorphisms for all
`n \ge 0`, expressed here through the local coordinate predicates above. -/
@[stacks 063H]
theorem isQuasiRegularIdealSheaf_iff_isFiniteType_and_conormalFiniteLocallyFreeCriterion_and_associatedGradedPolynomialCriterion
    (I : Subobject 𝒪X) :
    IsQuasiRegularIdealSheaf I ↔
      (Subobject.underlying.obj I).IsFiniteType ∧
        idealSheafConormalFiniteLocallyFreeCriterion I ∧
          idealSheafAssociatedGradedPolynomialCriterion I := sorry

end AlgebraicGeometry.RingedSpace

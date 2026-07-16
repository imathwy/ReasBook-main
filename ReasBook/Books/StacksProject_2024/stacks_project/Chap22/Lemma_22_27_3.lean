import StacksProject_2024.stacks_project.Chap22.Situation_22_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable [CompBoundaryMap R A]

-- Semantic recall hits: `lean_leansearch` returned the cochain-complex owner
-- `CochainComplex.mappingCone.trianglehMapOfHomotopy`, and local Chapter 22 precedent
-- `Lemma_22_27_5` fixes the source-facing API here as an existence theorem for the third cone map
-- together with strict `CommSq` compatibilities on the cone legs.

/-- Lemma 22.27.3: for a homotopy-commutative square in `Comp(𝒜)` and chosen admissible cones
`C₁` on `f₁` and `C₂` on `f₂`, there exists a morphism `c : c(f₁) ⟶ c(f₂)` compatible with the
maps `yᵢ ⟶ c(fᵢ)` and `c(fᵢ) ⟶ xᵢ[1]`. Only the boundary-map owner from Situation `22.27.2` is
needed here, since the cones themselves are already explicit data. Passing to `K(𝒜)`, the
components `(a, b, c)` therefore give the induced morphism between the associated cone triangles. -/
@[stacks 09P7]
theorem exists_coneMap_of_homotopyCommSquare
    {x₁ y₁ x₂ y₂ : Comp R A}
    {f₁ : x₁ ⟶ y₁}
    {f₂ : x₂ ⟶ y₂}
    (C₁ : AdmissibleCone f₁)
    (C₂ : AdmissibleCone f₂)
    {a : x₁ ⟶ x₂}
    {b : y₁ ⟶ y₂}
    (hcomm : Homotopic x₁.obj y₂.obj (f₁ ≫ b) (a ≫ f₂)) :
    ∃ c : C₁.obj ⟶ C₂.obj,
      CommSq C₁.toCone b c C₂.toCone ∧
        CommSq C₁.toShift c (a⟦(1 : ℤ)⟧') C₂.toShift := sorry

/-- Companion API for Lemma `22.27.3`: a strict cone map compatible with the admissible cone legs
induces the corresponding commutative squares in `K(𝒜)`. -/
theorem coneMap_inKCompat
    {x₁ y₁ x₂ y₂ : Comp R A}
    {f₁ : x₁ ⟶ y₁}
    {f₂ : x₂ ⟶ y₂}
    (C₁ : AdmissibleCone f₁)
    (C₂ : AdmissibleCone f₂)
    {a : x₁ ⟶ x₂}
    {b : y₁ ⟶ y₂}
    {c : C₁.obj ⟶ C₂.obj}
    (hcone : CommSq C₁.toCone b c C₂.toCone)
    (hshift : CommSq C₁.toShift c (a⟦(1 : ℤ)⟧') C₂.toShift) :
    CommSq C₁.toCone.inK b.inK c.inK C₂.toCone.inK ∧
      CommSq C₁.toShift.inK c.inK (a⟦(1 : ℤ)⟧').inK C₂.toShift.inK := by
  constructor
  · refine CommSq.mk ?_
    change (C₁.toCone ≫ c).toHomotopyClass = (b ≫ C₂.toCone).toHomotopyClass
    exact congrArg CompHom.toHomotopyClass hcone.w
  · refine CommSq.mk ?_
    change (C₁.toShift ≫ (a⟦(1 : ℤ)⟧')).toHomotopyClass = (c ≫ C₂.toShift).toHomotopyClass
    exact congrArg CompHom.toHomotopyClass hshift.w

/-- Bridge/view form of Lemma `22.27.3`: the cone map can be chosen so that its image in `K(𝒜)`
is compatible with the two cone legs. This is the category-theoretic shape used later for
triangle-morphism arguments. -/
theorem exists_coneMap_inKCompat_of_homotopyCommSquare
    {x₁ y₁ x₂ y₂ : Comp R A}
    {f₁ : x₁ ⟶ y₁}
    {f₂ : x₂ ⟶ y₂}
    (C₁ : AdmissibleCone f₁)
    (C₂ : AdmissibleCone f₂)
    {a : x₁ ⟶ x₂}
    {b : y₁ ⟶ y₂}
    (hcomm : Homotopic x₁.obj y₂.obj (f₁ ≫ b) (a ≫ f₂)) :
    ∃ c : C₁.obj ⟶ C₂.obj,
      CommSq C₁.toCone.inK b.inK c.inK C₂.toCone.inK ∧
        CommSq C₁.toShift.inK c.inK (a⟦(1 : ℤ)⟧').inK C₂.toShift.inK := by
  obtain ⟨c, hcone, hshift⟩ := exists_coneMap_of_homotopyCommSquare C₁ C₂ hcomm
  exact ⟨c, coneMap_inKCompat C₁ C₂ hcone hshift⟩

end

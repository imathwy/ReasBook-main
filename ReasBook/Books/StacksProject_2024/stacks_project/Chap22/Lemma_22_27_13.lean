import StacksProject_2024.Chap22.Lemma_22_27_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable [CompBoundaryMap R A]

-- Semantic recall hits: `lean_leansearch` returned the canonical homotopy-category comparison
-- theorem `HomotopyCategory.Pretriangulated.isomorphic_distinguished`, and the local companion
-- [22_27_13_1] exposes the same mapping-cone comparison in the genuine homotopy category of
-- cochain complexes. In the current Chapter 22 API, the source statement is therefore recorded by
-- a comparison morphism in `Comp(𝒜)` together with the canonical morphism property
-- `Comp.homotopyEquivalences` and the two induced comparison squares in `K(𝒜)`.

/-- Lemma 22.27.13 (1): in Situation `22.27.2`, for an admissible short exact sequence
`x ⟶ y ⟶ z` in `Comp(𝒜)` and a chosen admissible cone on the first map `α : x ⟶ y`, there is a
homotopy equivalence from the cone object to `z` whose class in `K(𝒜)` identifies the cone triangle
`x ⟶ y ⟶ c(α) ⟶ x[1]` with the triangle attached to the short exact sequence through the two
canonical comparison squares
`x ⟶ y ⟶ z ⟶ x[1]`. -/
@[stacks 09QU]
theorem exists_homotopyEquivalence_and_triangleComparison_of_shortComplexSplitting
    (S : ShortComplex (Comp R A))
    (σ : S.Splitting)
    (C : AdmissibleCone S.f) :
    ∃ c : C.obj ⟶ S.X₃, Comp.homotopyEquivalences c ∧
      CommSq C.toCone.inK (𝟙 (S.X₂.inK)) c.inK S.g.inK ∧
        CommSq c.inK (𝟙 (C.obj.inK)) (CompBoundaryMap.boundary σ).inK C.toShift.inK := by
  sorry

/-- Lemma 22.27.13 (2): in Situation `22.27.2`, let `α : x ⟶ y` factor through an admissible
monomorphism `α̃ : x ⟶ ỹ` with homotopy-equivalence projection `ỹ ⟶ y`, and let
`x ⟶ ỹ ⟶ z` be an admissible short exact sequence extending `α̃`. Then the
triangle attached to that short exact sequence is isomorphic in `K(𝒜)` to the cone triangle of
`α`, via the canonical comparison squares on the second and third morphisms. -/
@[stacks 09QU]
theorem exists_homotopyEquivalence_and_triangleComparison_of_factorization
    (S : ShortComplex (Comp R A))
    (σ : S.Splitting)
    {y : Comp R A}
    {α : S.X₁ ⟶ y}
    (r : HomotopyRetract S.X₂ y)
    (hfactor : S.f ≫ r.projection = α)
    (C : AdmissibleCone α) :
    ∃ c : S.X₃ ⟶ C.obj, Comp.homotopyEquivalences c ∧
      CommSq S.g.inK r.projection.inK c.inK C.toCone.inK ∧
        CommSq c.inK (𝟙 (S.X₃.inK)) C.toShift.inK (CompBoundaryMap.boundary σ).inK := by
  sorry

end

import StacksProject_2024.stacks_project.Chap22.Lemma_22_27_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasAdmissibleCones R A]

-- Semantic recall hits: the Chapter 22 comparison owner
-- `exists_homotopyEquivalence_and_triangleComparison_of_shortComplexSplitting` compares any
-- splitting of a fixed admissible short exact sequence with the same admissible cone triangle of
-- the first map. The source-facing independence-of-splitting statement should therefore be proved
-- by comparing both chosen boundary morphisms to that common cone boundary in `K(𝒜)`, not by
-- postulating an external class `δ`. The ambient assumption is only
-- `[HasAdmissibleCones R A]`, since that canonical owner already fixes the compatible shift and
-- boundary-map data used below.

/- Source/core/bridge triage:
- `source-facing`: the independence of the connecting morphism attached to a split admissible short
  exact sequence from the choice of splitting in the homotopy category `K(𝒜)`;
- `core/canonical`: the homotopy-class owner `HomotopyClass`;
- `bridge/view`: the cone-triangle comparison
  `exists_homotopyEquivalence_and_triangleComparison_of_shortComplexSplitting`, and the homotopy
  statement below extracted from equality in `K(𝒜)` by the quotient bridge
  `CompHom.homotopic_of_toHomotopyClass_eq`.
-/

/- Lemma `22.27.9`: for a fixed admissible short exact sequence
`x ⟶ y ⟶ z` in `Comp(𝒜)`, the connecting morphism in `K(𝒜)` is independent of the chosen
splitting. In the current Chapter 22 API, both boundary maps are compared to the same admissible
cone boundary for `x ⟶ y`, and the split-epimorphism structure on `y ⟶ z` cancels the auxiliary
comparison isomorphisms. -/
@[stacks 09QQ]
theorem boundary_eq_in_K_of_splittings
    {S : ShortComplex (Comp R A)}
    (σ σ' : S.Splitting) :
    (CompBoundaryMap.boundary σ).toHomotopyClass =
      (CompBoundaryMap.boundary σ').toHomotopyClass :=
by
  sorry

/-- Companion bridge: the boundary morphisms attached to two splittings of the same admissible
short exact sequence in `Comp(𝒜)` are homotopic, because their classes in `K(𝒜)` agree by
`boundary_eq_in_K_of_splittings`. -/
theorem boundary_homotopic_of_splittings
    {S : ShortComplex (Comp R A)}
    (σ σ' : S.Splitting) :
    Homotopic S.X₃.obj (S.X₁⟦(1 : ℤ)⟧).obj
      (CompBoundaryMap.boundary σ) (CompBoundaryMap.boundary σ') :=
  CompHom.homotopic_of_toHomotopyClass_eq
    (boundary_eq_in_K_of_splittings σ σ')

end

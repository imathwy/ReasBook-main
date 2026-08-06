import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4

open CategoryTheory Limits

noncomputable section

universe u

/-- The singular cohomology group `H^p(X; R)` realized as the degree-`p` homology of the singular
cochain complex obtained by applying `ChainComplex.linearYonedaObj` to the singular chain complex
of `X` with coefficients in `R`. -/
abbrev rSingularCohomology
    (R : Type u) [CommRing R] (X : TopCat.{u}) (p : ℕ) : ModuleCat.{u} R :=
  ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of.{u} R R)).obj X).linearYonedaObj R (ModuleCat.of.{u} R R)).homology p

/-- Unfolding `rSingularCohomology R X p` recovers the degree-`p` homology object of
the linear dual singular cochain complex of `X` with coefficients in `R`. -/
theorem rSingularCohomology_def
    (R : Type u) [CommRing R] (X : TopCat.{u}) (p : ℕ) :
    rSingularCohomology R X p =
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of.{u} R R)).obj X).linearYonedaObj R (ModuleCat.of.{u} R R)).homology p :=
  rfl

namespace rSingularCohomology

/-- Pullback on `rSingularCohomology R _ p` induced by a map of spaces. -/
abbrev map
    (R : Type u) [CommRing R] {X Y : TopCat.{u}} (f : X ⟶ Y) (p : ℕ) :
    rSingularCohomology R Y p ⟶ rSingularCohomology R X p :=
  HomologicalComplex.homologyMap
    ((HomologicalComplex.unopEquivalence (ModuleCat.{u} R) (ComplexShape.down ℕ)).functor.map
      (Opposite.op
        ((((CategoryTheory.linearYoneda R (ModuleCat.{u} R)).obj
              (ModuleCat.of.{u} R R)).rightOp.mapHomologicalComplex
            (ComplexShape.down ℕ)).map
          ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
                (ModuleCat.of.{u} R R)).map f)))))
    p

end rSingularCohomology

section

variable (R : Type u) [CommRing R]
variable {X : TopCat.{u}}

/-- Degree `p` of the singular chain complex is the coproduct of copies of `R` indexed by
`singularSimplex p X`. -/
private theorem singularChainComplex_degree_eq_coproduct
    (X : TopCat.{u}) (p : ℕ) :
    ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
          (ModuleCat.of.{u} R R)).obj X).X p) =
      ∐ fun _ : singularSimplex p X ↦ ModuleCat.of.{u} R R := sorry

/-- The source-facing singular `p`-cochain on simplices determines the corresponding element of
the dualized cochain complex `singularCochainComplex R X` in degree `p`. -/
private noncomputable def singularCochainToCochainComplex
    (X : TopCat.{u}) (p : ℕ) (φ : singularCochains R X p) :
    (singularCochainComplex R X).X p :=
  (singularCochainComplex_X R X p).symm ▸
    ((singularChainComplex_degree_eq_coproduct R X p).symm ▸
      (CategoryTheory.Limits.Sigma.desc
        (fun σ : singularSimplex p X ↦
          ModuleCat.ofHom (LinearMap.mulRight R (φ σ)))))

/-- A cocycle in the source-facing cochain model determines a cycle in
`(singularCochainComplex R X).sc p`. -/
private theorem singularCocycle_isCycle
    (X : TopCat.{u}) (p : ℕ) (φ : singularCocycles R X p) :
    (((singularCochainComplex R X).sc p).g)
        (singularCochainToCochainComplex R X p φ.1) = 0 := sorry

/-- A source-facing singular cohomology cocycle determines its class in
`rSingularCohomology R X p`. -/
private noncomputable def singularCocycleToRSingularCohomology
    (X : TopCat.{u}) (p : ℕ) (φ : singularCocycles R X p) :
    rSingularCohomology R X p :=
  (singularCochainComplex R X).homologyπ p
    (((singularCochainComplex R X).sc p).cyclesMk
      (singularCochainToCochainComplex R X p φ.1)
      (singularCocycle_isCycle R X p φ))

/-- Equivalent cocycle representatives determine the same class in `rSingularCohomology R X p`.
-/
private theorem singularCocycleToRSingularCohomology_quotient
    (X : TopCat.{u}) (p : ℕ) {φ ψ : singularCocycles R X p}
    (h : singularCohomologyRel R X φ ψ) :
    singularCocycleToRSingularCohomology R X p φ =
      singularCocycleToRSingularCohomology R X p ψ := sorry

/-- The canonical comparison map from the quotient-model singular cohomology classes of
Chapter 18 to the cochain-complex homology owner `rSingularCohomology`. -/
noncomputable def singularCohomologyClassToRSingularCohomology
    (X : TopCat.{u}) (p : ℕ) :
    singularCohomologyClasses R X p → rSingularCohomology R X p :=
  Quotient.lift
    (singularCocycleToRSingularCohomology R X p)
    fun _ _ h ↦ singularCocycleToRSingularCohomology_quotient R X p h

/-- Applying `singularCohomologyClassToRSingularCohomology` to a represented cocycle class gives
the corresponding class in `rSingularCohomology R X p`. -/
theorem singularCohomologyClassToRSingularCohomology_mk
    (X : TopCat.{u}) (p : ℕ) (φ : singularCocycles R X p) :
    singularCohomologyClassToRSingularCohomology R X p
        (Quotient.mk (singularCohomologySetoid R X p) φ) =
      singularCocycleToRSingularCohomology R X p φ := sorry

end

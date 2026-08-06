import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Construction_17_1_2

noncomputable section

open AlgebraicTopology
open CategoryTheory
open scoped CapProduct Topology

universe u

-- Semantic recall via `lean_leansearch` only surfaced the ambient singular homology/cohomology
-- owners, while local Chapter 20 precedent fixes `singularCapProduct`, `rSingularHomology`, and
-- `IsRFundamentalClassFor` as the source-facing API for capping with a fundamental class.

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/-- The Chapter 20 constant-coefficient owner is canonically the ordinary unit `R`-module. -/
private noncomputable def constantCoefficientModuleIsoUnit :
    constantCoefficientModule R ≅ ModuleCat.of.{u} R R :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift R ≃ₗ[R] R)

/-- The Chapter 20 owner `rSingularHomology R n X` is canonically the degree-`n` homology of
`rSingularChainComplex R X`. -/
private noncomputable def rSingularHomologyIsoChainComplexHomology
    (X : TopCat.{u}) (n : ℕ) :
    rSingularHomology R n X ≅ (rSingularChainComplex R X).homology n :=
  (((singularHomologyFunctor (ModuleCat.{u} R) n).mapIso constantCoefficientModuleIsoUnit).app X)

/-- The canonical map from constant-coefficient singular homology to the coefficient-homology
owner `singularHomologyWithCoefficients R X (ModuleCat.of R R) n`, obtained by tensoring with the
unit module `R` and applying Construction 17.1.2. -/
noncomputable def rSingularHomologyToUnitCoefficientHomology
    (X : TopCat.{u}) (n : ℕ) :
    rSingularHomology R n X ⟶
      singularHomologyWithCoefficients R X (ModuleCat.of.{u} R R) n :=
  (rSingularHomologyIsoChainComplexHomology X n).hom ≫
    ModuleCat.ofHom
      (TensorProduct.rid R ((rSingularChainComplex R X).homology n)).symm.toLinearMap ≫
    homologyTensorComparison R (rSingularChainComplex R X) (ModuleCat.of.{u} R R) n

/-- Applying `rSingularHomologyToUnitCoefficientHomology R X n` to `z` tensors `z` with `1 : R`
after transporting `z` to `(rSingularChainComplex R X).homology n`, and then descends via
`homologyTensorComparison`. -/
@[simp] theorem rSingularHomologyToUnitCoefficientHomology_apply
    (X : TopCat.{u}) (n : ℕ) (z : rSingularHomology R n X) :
    rSingularHomologyToUnitCoefficientHomology X n z =
      homologyTensorComparison R
          (rSingularChainComplex R X)
          (ModuleCat.of.{u} R R) n
        ((TensorProduct.rid R ((rSingularChainComplex R X).homology n)).symm
          ((rSingularHomologyIsoChainComplexHomology X n).hom z)) := rfl

variable {M : Type u} [TopologicalSpace M]

/-- Construction 20.2.2. Capping with a top-degree class `z ∈ H_n(M; R)` specializes the cap
product to a degree-`p` map
`H^p(M; R) → singularHomologyWithCoefficients R (TopCat.of M) (ModuleCat.of R R) (n - p)`.
When `M` carries a compact `R`-orientation and `z` is a compatible fundamental class, this is the
source duality map `D(α) = α ∩ z`. -/
abbrev capWithFundamentalClass
    (z : rSingularHomology R n (TopCat.of.{u} M)) (p : ℕ) :
    rSingularCohomology R (TopCat.of.{u} M) p →ₗ[R]
      singularHomologyWithCoefficients R (TopCat.of.{u} M) (ModuleCat.of.{u} R R) (n - p) :=
  LinearMap.flip
    (singularCapProduct R (TopCat.of.{u} M) (ModuleCat.of.{u} R R) p n)
    (rSingularHomologyToUnitCoefficientHomology (TopCat.of.{u} M) n z)

/-- Applying `capWithFundamentalClass z p` to `α` recovers the cap-product formula
`α ∩ z`. -/
@[simp] theorem capWithFundamentalClass_apply
    (z : rSingularHomology R n (TopCat.of.{u} M)) (p : ℕ)
    (α : rSingularCohomology R (TopCat.of.{u} M) p) :
    capWithFundamentalClass z p α =
      α ∩ rSingularHomologyToUnitCoefficientHomology (TopCat.of.{u} M) n z := rfl

end

import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Construction_17_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.SingularCohomology

open AlgebraicTopology CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

/-- The singular chain complex `C_*(X; R)` with coefficients in the constant `R`-module `R`. -/
abbrev rSingularChainComplex
    (R : Type u) [CommRing R] (X : TopCat.{u}) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of.{u} R R)).obj X)

/-- Unfolding `rSingularChainComplex R X` recovers the singular chain complex functor evaluated at
`X` with coefficients in the constant module `R`. -/
@[simp] theorem rSingularChainComplex_def
    (R : Type u) [CommRing R] (X : TopCat.{u}) :
    rSingularChainComplex R X =
      (((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of.{u} R R)).obj X) :=
  rfl

/-- Singular homology `H_q(X; M)` with coefficients in the `R`-module `M`, realized as the
degree-`q` homology of the singular chain complex of `X` tensored with `M` concentrated in degree
`0`. -/
abbrev singularHomologyWithCoefficients
    (R : Type u) [CommRing R] (X : TopCat.{u}) (M : ModuleCat.{u} R) (q : ℕ) :
    ModuleCat.{u} R :=
  homologyWithCoefficients R (rSingularChainComplex R X) M q

/-- Unfolding `singularHomologyWithCoefficients R X M q` recovers the degree-`q` homology of the
singular chain complex of `X` tensored with `M` in degree `0`. -/
@[simp] theorem singularHomologyWithCoefficients_def
    (R : Type u) [CommRing R] (X : TopCat.{u}) (M : ModuleCat.{u} R) (q : ℕ) :
    singularHomologyWithCoefficients R X M q =
      homologyWithCoefficients R (rSingularChainComplex R X) M q :=
  rfl

namespace singularHomologyWithCoefficients

/-- Pushforward on `singularHomologyWithCoefficients R _ M q` induced by a map of spaces. -/
abbrev map
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) {X Y : TopCat.{u}}
    (f : X ⟶ Y) (q : ℕ) :
    singularHomologyWithCoefficients R X M q ⟶
      singularHomologyWithCoefficients R Y M q :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.mapBifunctorMap
      ((((singularChainComplexFunctor (ModuleCat.{u} R)).obj
            (ModuleCat.of.{u} R R)).map f))
      (𝟙 (coefficientComplex R M))
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{u} R))
      (ComplexShape.down ℕ))
    q

end singularHomologyWithCoefficients

section

variable (R : Type u) [CommRing R] (X : TopCat.{u}) (M : ModuleCat.{u} R) (p q : ℕ)

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial MonoidalCategory

private abbrev singularChainComplex :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  rSingularChainComplex R X

private abbrev singularCoefficientChainComplex :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  singularChainComplex R X ⊗ coefficientComplex R M

/-- The front `p`-face of a singular `q`-simplex, when `p ≤ q`, is obtained from
`singularFrontFace X p (q - p)` after rewriting `q = p + (q - p)`. -/
private def singularFrontFaceOfLE
    (p q : ℕ) (h : p ≤ q) :
    singularSimplex q X → singularSimplex p X :=
  fun σ ↦ singularFrontFace X p (q - p) ((Nat.add_sub_of_le h).symm ▸ σ)

/-- The complementary back face of a singular `q`-simplex, when `p ≤ q`, is obtained from
`singularBackFace X p (q - p)` after rewriting `q = p + (q - p)`. -/
private def singularBackFaceOfLE
    (p q : ℕ) (h : p ≤ q) :
    singularSimplex q X → singularSimplex (q - p) X :=
  fun σ ↦ singularBackFace X p (q - p) ((Nat.add_sub_of_le h).symm ▸ σ)

/-- The chain-level cap operator in degree `q`, defined on singular `q`-chains by evaluating a
degree-`p` cochain on the front face and keeping the complementary back face. For `q < p`, the
output is the zero map into degree `q - p = 0`. -/
private noncomputable def singularChainDegreeCap
    (p q : ℕ) (φ : singularCochains R X p) :
    singularChainDegree R X q ⟶ singularChainDegree R X (q - p) :=
  if h : p ≤ q then
    (singularChainDegreeIsoCoproduct R X q).hom ≫
      Limits.Sigma.desc (fun σ : singularSimplex q X ↦
        ModuleCat.ofHom (LinearMap.mulRight R (φ (singularFrontFaceOfLE X p q h σ))) ≫
          Limits.Sigma.ι
            (fun _ : singularSimplex (q - p) X ↦ ModuleCat.of.{u} R R)
            (singularBackFaceOfLE X p q h σ) ≫
          (singularChainDegreeIsoCoproduct R X (q - p)).inv)
  else
    0

/-- The degree-`q` component of the coefficient-chain cap operator is obtained by tensoring the
chain-level cap map with `M` and inserting it into the unique nonzero summand of
`singularCoefficientChainComplex R X M`. -/
private noncomputable def singularCapDegreeMap
    (p q : ℕ) (φ : singularCochains R X p) :
    (singularCoefficientChainComplex R X M).X q ⟶
      (singularCoefficientChainComplex R X M).X (q - p) :=
  HomologicalComplex.mapBifunctorDesc <|
    fun i₁ i₂ h ↦
      match i₂ with
      | 0 =>
          by
            have hi : i₁ = q := by simpa using h
            subst i₁
            simpa [singularChainDegree, singularCoefficientChainComplex, coefficientComplex] using
              ((singularChainDegreeCap R X p q φ) ⊗ₘ 𝟙 M) ≫
                ιTensorObj
                  (singularChainComplex R X)
                  (coefficientComplex R M)
                  (q - p) 0 (q - p) rfl
      | _ + 1 => 0

/-- The cap operator sends cycles to cycles in the coefficient singular chain complex. -/
private theorem singularCapCocycleToCycles_d_eq_zero
    (p q : ℕ)
    (φ : ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.K) :
    ((singularCoefficientChainComplex R X M).iCycles q ≫
        singularCapDegreeMap R X M p q
          ((singularCochainComplexDegreeEquiv R X p) φ.1)) ≫
      (singularCoefficientChainComplex R X M).d (q - p)
        ((ComplexShape.down ℕ).next (q - p)) =
    0 := sorry

/-- A cocycle representative acts on coefficient cycles by the chain-level cap construction. -/
private noncomputable def singularCapCocycleToCycles
    (p q : ℕ)
    (φ : ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.K) :
    (singularCoefficientChainComplex R X M).cycles q ⟶
      (singularCoefficientChainComplex R X M).cycles (q - p) :=
  (singularCoefficientChainComplex R X M).liftCycles
    ((singularCoefficientChainComplex R X M).iCycles q ≫
      singularCapDegreeMap R X M p q
        ((singularCochainComplexDegreeEquiv R X p) φ.1))
    ((ComplexShape.down ℕ).next (q - p))
    rfl
    (singularCapCocycleToCycles_d_eq_zero R X M p q φ)

/-- The concrete map from coefficient cycles in degree `q` to the concrete left-homology model in
degree `q - p`, induced by a cocycle representative of degree `p`. -/
private noncomputable def singularCapCocycleToHomologyAux
    (p q : ℕ)
    (φ : ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.K) :
    ((singularCoefficientChainComplex R X M).sc q).moduleCatLeftHomologyData.K ⟶
      ((singularCoefficientChainComplex R X M).sc (q - p)).moduleCatLeftHomologyData.H :=
  ((singularCoefficientChainComplex R X M).sc q).moduleCatCyclesIso.inv ≫
    singularCapCocycleToCycles R X M p q φ ≫
    (singularCoefficientChainComplex R X M).homologyπ (q - p) ≫
    ((singularCoefficientChainComplex R X M).sc (q - p)).moduleCatHomologyIso.hom

/-- Boundaries act trivially under `singularCapCocycleToHomologyAux`, so the cap construction
descends from cycles to homology in the right variable. -/
private theorem singularCapCocycleToHomologyAux_boundary_zero
    (p q : ℕ)
    (φ : ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.K) :
    ((singularCoefficientChainComplex R X M).sc q).moduleCatLeftHomologyData.f' ≫
      singularCapCocycleToHomologyAux R X M p q φ =
    0 := sorry

/-- For a cocycle representative `φ`, the right-variable cap operation descends to a morphism on
coefficient homology. -/
private noncomputable def singularCapCocycleToHomology
    (p q : ℕ)
    (φ : ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.K) :
    ((singularCoefficientChainComplex R X M).sc q).moduleCatLeftHomologyData.H ⟶
      ((singularCoefficientChainComplex R X M).sc (q - p)).moduleCatLeftHomologyData.H :=
  ((singularCoefficientChainComplex R X M).sc q).moduleCatLeftHomologyData.descH
    (singularCapCocycleToHomologyAux R X M p q φ)
    (singularCapCocycleToHomologyAux_boundary_zero R X M p q φ)

/-- Additivity of the homology-level cap operator in the cocycle representative. -/
private theorem singularCapCocycleLinear_map_add
    (p q : ℕ)
    (φ ψ : ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.K) :
    (singularCapCocycleToHomology R X M p q (φ + ψ)).hom =
      (singularCapCocycleToHomology R X M p q φ).hom +
        (singularCapCocycleToHomology R X M p q ψ).hom := sorry

/-- Scalar compatibility of the homology-level cap operator in the cocycle representative. -/
private theorem singularCapCocycleLinear_map_smul
    (p q : ℕ) (a : R)
    (φ : ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.K) :
    (singularCapCocycleToHomology R X M p q (a • φ)).hom =
      a • (singularCapCocycleToHomology R X M p q φ).hom := sorry

/-- The coefficient-homology linear target of the cap construction on quotient-model homology. -/
private abbrev singularCapLinearTarget
    (p q : ℕ) :=
  ((singularCoefficientChainComplex R X M).sc q).moduleCatLeftHomologyData.H →ₗ[R]
    ((singularCoefficientChainComplex R X M).sc (q - p)).moduleCatLeftHomologyData.H

/-- The coefficient-homology linear target viewed as an `R`-module object. -/
private abbrev singularCapLinearTargetObj
    (p q : ℕ) :
    ModuleCat.{u} R :=
  ModuleCat.of.{u} R (singularCapLinearTarget R X M p q)

/-- A cocycle representative acts on quotient-model coefficient homology by a linear map. -/
private noncomputable def singularCapCocycleLinear
    (p q : ℕ) :
    ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.K ⟶
      singularCapLinearTargetObj R X M p q :=
  ModuleCat.ofHom
    { toFun := fun φ ↦
        (singularCapCocycleToHomology R X M p q φ).hom
      map_add' := by
        intro φ ψ
        exact singularCapCocycleLinear_map_add R X M p q φ ψ
      map_smul' := by
        intro a φ
        exact singularCapCocycleLinear_map_smul R X M p q a φ }

/-- Coboundaries act trivially under `singularCapCocycleLinear`, so the cap construction descends
from cocycles to cohomology in the left variable. -/
private theorem singularCapCocycleLinear_boundary_zero
    (p q : ℕ) :
    ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.f' ≫
      singularCapCocycleLinear R X M p q =
    0 := sorry

/-- The quotient-model cap operator obtained by descending `singularCapCocycleLinear` to
`rSingularCohomology R X p`. -/
private noncomputable def singularCapLinearDesc
    (p q : ℕ) :
    rSingularCohomology R X p ⟶
      singularCapLinearTargetObj R X M p q :=
  ((singularCochainComplex R X).sc p).moduleCatHomologyIso.hom ≫
    ((singularCochainComplex R X).sc p).moduleCatLeftHomologyData.descH
      (singularCapCocycleLinear R X M p q)
      (singularCapCocycleLinear_boundary_zero R X M p q)

/-- Additivity of the public cap product in the cohomology variable. -/
private theorem singularCapProduct_map_add
    (p q : ℕ)
    (α β : rSingularCohomology R X p) :
    ((singularCapLinearDesc R X M p q).hom (α + β)) =
      (((singularCapLinearDesc R X M p q).hom α)) +
        (((singularCapLinearDesc R X M p q).hom β)) := sorry

/-- Scalar compatibility of the public cap product in the cohomology variable. -/
private theorem singularCapProduct_map_smul
    (p q : ℕ) (a : R)
    (α : rSingularCohomology R X p) :
    ((singularCapLinearDesc R X M p q).hom (a • α)) =
      a • (((singularCapLinearDesc R X M p q).hom α)) := sorry

/-- The morphism on `H_q(X; M)` induced by capping with `α ∈ H^p(X; R)`. -/
private noncomputable def singularCapProductHom
    (p q : ℕ) (α : rSingularCohomology R X p) :
    singularHomologyWithCoefficients R X M q ⟶
      singularHomologyWithCoefficients R X M (q - p) :=
  ((singularCoefficientChainComplex R X M).sc q).moduleCatHomologyIso.hom ≫
    ModuleCat.ofHom ((singularCapLinearDesc R X M p q).hom α) ≫
    ((singularCoefficientChainComplex R X M).sc (q - p)).moduleCatHomologyIso.inv

/-- Definition 20.2.1. The singular cap product is the degreewise pairing
`H^p(X; R) ⊗ H_q(X; M) → H_(q - p)(X; M)` induced from the chain-level evaluation morphism of
Construction 17.5.2 together with the front-face and complementary-face restriction operators of
Construction 18.3.2. -/
noncomputable def singularCapProduct
    (p q : ℕ) :
    rSingularCohomology R X p →ₗ[R]
      singularHomologyWithCoefficients R X M q →ₗ[R]
        singularHomologyWithCoefficients R X M (q - p) :=
  { toFun := fun α ↦
      (singularCapProductHom R X M p q α).hom
    map_add' := by
      intro α β
      sorry
    map_smul' := by
      intro a α
      sorry }

namespace rSingularCohomology

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {M : ModuleCat.{u} R} {p q : ℕ}

/-- The quotient-level singular cap product. -/
abbrev cap (α : rSingularCohomology R X p) (z : singularHomologyWithCoefficients R X M q) :
    singularHomologyWithCoefficients R X M (q - p) :=
  singularCapProduct R X M p q α z

/-- The abbreviation `cap` is definitionally the underlying singular cap product. -/
@[simp] theorem cap_eq_singularCapProduct
    (α : rSingularCohomology R X p)
    (z : singularHomologyWithCoefficients R X M q) :
    cap α z = singularCapProduct R X M p q α z :=
  rfl

/-- Source-facing cap-product notation for `singularCapProduct`. -/
scoped[CapProduct] infixr:70 " ∩ " => rSingularCohomology.cap

end rSingularCohomology

open scoped CapProduct

/-- Applying `singularCapProduct R X M p q` recovers the source-facing cap-product notation. -/
@[simp] theorem singularCapProduct_eq_cap
    (α : rSingularCohomology R X p)
    (z : singularHomologyWithCoefficients R X M q) :
    singularCapProduct R X M p q α z = α ∩ z :=
  rfl

#check chainHomEvaluation_spec
#check singularFrontFace
#check singularBackFace

end

import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Construction_17_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.SingularCohomology

noncomputable section

open AlgebraicTopology CategoryTheory MonoidalCategory
open scoped Manifold Topology

-- Semantic recall via `lean_leansearch` surfaced only generic bilinear-pairing APIs, while local
-- Chapter 17/18/20 search fixes the canonical ingredients for this item as
-- `singularCohomologyCup`, `singularCohomologyClassToIntegralSingularCohomology`, and the
-- Chapter 20 fundamental-class API. The public Construction 20.1.4 declaration is therefore
-- attached only to the manifold, fundamental class, and degree, while the implementation descends
-- the chain-level cup product and cochain evaluation maps through the canonical homology quotients.

/-- The singular cochain complex `Hom(C_*(X; ℤ), ℤ)` realizing integral singular cohomology. -/
private abbrev integralSingularCochainComplex (X : TopCat) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  singularCochainComplex ℤ X

/-- The integral singular chain complex `C_*(X; ℤ)` underlying the Chapter 20 integral homology
and cohomology constructions. -/
abbrev integralSingularChainComplex (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X)

/-- The Chapter 20 coefficient owner `constantCoefficientModule ℤ` is canonically the ordinary
unit `ℤ`-module. -/
noncomputable def constantCoefficientModuleIsoInt :
    constantCoefficientModule ℤ ≅ ModuleCat.of ℤ ℤ :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ)

/-- The chapter owner `rSingularHomology ℤ p X` is canonically identified with the degree-`p`
homology of `integralSingularChainComplex X`. -/
noncomputable def rSingularHomologyIsoIntegralSingularHomology
    (X : TopCat) (p : ℕ) :
    rSingularHomology ℤ p X ≅ (integralSingularChainComplex X).homology p :=
  (((singularHomologyFunctor (ModuleCat ℤ) p).mapIso constantCoefficientModuleIsoInt).app X)

/-- A chain-level comparison morphism from the tensor product of the integral singular chain
complexes of `X` and `Y` to the integral singular chain complex of `X × Y`. -/
abbrev integralSingularChainComplexProductComparison (X Y : TopCat) : Type :=
  (integralSingularChainComplex X ⊗ integralSingularChainComplex Y) ⟶
    integralSingularChainComplex (TopCat.of (X × Y))

/-- The singular-homology cross product induced by a chosen chain-level product comparison. -/
noncomputable def rSingularHomologyCrossProduct
    {X Y : TopCat} {p q : ℕ}
    [HomologicalComplex.HasHomology (integralSingularChainComplex X) p]
    [HomologicalComplex.HasHomology (integralSingularChainComplex Y) q]
    [HomologicalComplex.HasHomology
      ((integralSingularChainComplex X ⊗ integralSingularChainComplex Y)) (p + q)]
    [HomologicalComplex.HasHomology
      (integralSingularChainComplex (TopCat.of (X × Y))) (p + q)]
    (productComparison : integralSingularChainComplexProductComparison X Y) :
    (rSingularHomology ℤ p X ⊗ rSingularHomology ℤ q Y) ⟶
      rSingularHomology ℤ (p + q) (TopCat.of (X × Y)) :=
  let homologyIsoX := rSingularHomologyIsoIntegralSingularHomology X p
  let homologyIsoY := rSingularHomologyIsoIntegralSingularHomology Y q
  let homologyIsoProd :=
    rSingularHomologyIsoIntegralSingularHomology (TopCat.of (X × Y)) (p + q)
  let crossProduct :
      (integralSingularChainComplex X).homology p ⊗
          (integralSingularChainComplex Y).homology q ⟶
        ((integralSingularChainComplex X) ⊗
            integralSingularChainComplex Y).homology (p + q) :=
    chainComplexHomologyCrossProduct
  let productHomologyMap :
      ((integralSingularChainComplex X) ⊗
          integralSingularChainComplex Y).homology (p + q) ⟶
        (integralSingularChainComplex (TopCat.of (X × Y))).homology (p + q) :=
    HomologicalComplex.homologyMap productComparison (p + q)
  (homologyIsoX.hom ⊗ₘ homologyIsoY.hom) ≫ crossProduct ≫ productHomologyMap ≫ homologyIsoProd.inv

/-- Integral singular cohomology of `X`, realized as the degree-`n` homology of the singular
cochain complex `Hom(C_*(X; ℤ), ℤ)`. -/
abbrev integralSingularCohomology (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  singularCohomology X n

/-- `integralSingularCohomology X n` is the Chapter 18 owner `singularCohomology X n`. -/
theorem integralSingularCohomology_eq_singularCohomology (X : TopCat) (n : ℕ) :
    integralSingularCohomology X n = singularCohomology X n :=
  rfl

/-- Unfolding `integralSingularCohomology X n` recovers the degree-`n` homology of the canonical
integral singular cochain complex of `X`. -/
theorem integralSingularCohomology_def (X : TopCat) (n : ℕ) :
    integralSingularCohomology X n = (integralSingularCochainComplex X).homology n :=
  rfl

/-- The canonical comparison map from quotient-model singular cohomology classes to the local
integral singular cohomology owner used in Construction 20.1.4. -/
abbrev singularCohomologyClassToIntegralSingularCohomology
    (X : TopCat) (p : ℕ) :
    singularCohomologyClasses ℤ X p → integralSingularCohomology X p :=
  singularCohomologyClassToRSingularCohomology ℤ X p

/-- Applying `singularCohomologyClassToIntegralSingularCohomology` to a represented cocycle class
gives the corresponding class in `integralSingularCohomology X p`. -/
theorem singularCohomologyClassToIntegralSingularCohomology_mk
    (X : TopCat) (p : ℕ) (φ : singularCocycles ℤ X p) :
    singularCohomologyClassToIntegralSingularCohomology X p
        (Quotient.mk (singularCohomologySetoid ℤ X p) φ) =
      singularCohomologyClassToRSingularCohomology ℤ X p
        (Quotient.mk (singularCohomologySetoid ℤ X p) φ) := by
  rfl

/-- A degree-`p` element of the integral singular cochain complex determines the corresponding
source-facing singular `p`-cochain. -/
private noncomputable def integralCochainComplexToSingularCochain
    (X : TopCat) (p : ℕ) (x : (integralSingularCochainComplex X).X p) :
    singularCochains ℤ X p :=
  singularCochainComplexDegreeEquiv ℤ X p x

private abbrev integralCochainCycleModel (X : TopCat) (p : ℕ) :=
  ((integralSingularCochainComplex X).sc p).moduleCatLeftHomologyData.K

private abbrev integralCochainHomologyModel (X : TopCat) (p : ℕ) :=
  ((integralSingularCochainComplex X).sc p).moduleCatLeftHomologyData.H

private abbrev integralChainCycleModel (X : TopCat) (p : ℕ) :=
  ((integralSingularChainComplex X).sc p).moduleCatLeftHomologyData.K

private abbrev integralChainHomologyModel (X : TopCat) (p : ℕ) :=
  ((integralSingularChainComplex X).sc p).moduleCatLeftHomologyData.H

/-- A chosen cycle in `integralSingularCochainComplex X` determines a source-facing singular
cocycle representative in the same degree. -/
private theorem integralCycleToSingularCocycle_isClosed
    (X : TopCat) (p : ℕ) (φ : (integralSingularCochainComplex X).cycles p) :
    singularCochainCoboundary ℤ X p
        (integralCochainComplexToSingularCochain X p
          (((integralSingularCochainComplex X).iCycles p).hom φ)) = 0 := sorry

/-- A chosen cycle representative in `integralSingularCochainComplex X` determines a source-facing
singular cocycle in degree `p`. -/
private noncomputable def integralCycleToSingularCocycle
    (X : TopCat) (p : ℕ) (φ : (integralSingularCochainComplex X).cycles p) :
    singularCocycles ℤ X p :=
  ⟨integralCochainComplexToSingularCochain X p
      (((integralSingularCochainComplex X).iCycles p).hom φ),
    integralCycleToSingularCocycle_isClosed X p φ⟩

/-- A cocycle in the source-facing singular model determines a cycle in the canonical integral
singular cochain complex. -/
private theorem singularCocycleToIntegralCycle_isCycle
    (X : TopCat) (p : ℕ) (φ : singularCocycles ℤ X p) :
    (((integralSingularCochainComplex X).sc p).g
        ((singularCochainComplexDegreeEquiv ℤ X p).symm φ.1)) = 0 := sorry

/-- A source-facing singular cocycle determines the corresponding cycle in the canonical integral
singular cochain complex. -/
private noncomputable def singularCocycleToIntegralCycle
    (X : TopCat) (p : ℕ) (φ : singularCocycles ℤ X p) :
    (integralSingularCochainComplex X).cycles p :=
  ((integralSingularCochainComplex X).sc p).cyclesMk
    ((singularCochainComplexDegreeEquiv ℤ X p).symm φ.1)
    (singularCocycleToIntegralCycle_isCycle X p φ)

/-- The quotient-model cycles of `integralSingularCochainComplex X` determine source-facing
singular cocycles via the canonical cycles isomorphism. -/
private noncomputable def integralCocycleModelToSingularCocycle
    (X : TopCat) (p : ℕ) (φ : integralCochainCycleModel X p) :
    singularCocycles ℤ X p :=
  integralCycleToSingularCocycle X p
    (((integralSingularCochainComplex X).sc p).moduleCatCyclesIso.inv φ)

/-- For a fixed cocycle model in degree `p`, cupping with it sends degree-`q` cycle models to
degree-`p + q` cycle models. -/
private noncomputable def integralCupCocycleToCycles
    (X : TopCat) (p q : ℕ) (φ : integralCochainCycleModel X p) :
    (integralSingularCochainComplex X).cycles q ⟶
      (integralSingularCochainComplex X).cycles (p + q) :=
  ModuleCat.ofHom
    { toFun := fun ψ ↦
        singularCocycleToIntegralCycle X (p + q)
          (singularCohomologyCupRepresentative ℤ X p q
            (integralCocycleModelToSingularCocycle X p φ)
            (integralCycleToSingularCocycle X q ψ))
      map_add' := by
        intro ψ₁ ψ₂
        sorry
      map_smul' := by
        intro m ψ
        sorry }

/-- The concrete map induced by cupping with a fixed degree-`p` cocycle model descends from
degree-`q` cycles to the concrete left-homology model in degree `p + q`. -/
private noncomputable def integralCupCocycleToHomologyAux
    (X : TopCat) (p q : ℕ) (φ : integralCochainCycleModel X p) :
    integralCochainCycleModel X q ⟶ integralCochainHomologyModel X (p + q) :=
  ((integralSingularCochainComplex X).sc q).moduleCatCyclesIso.inv ≫
    integralCupCocycleToCycles X p q φ ≫
    (integralSingularCochainComplex X).homologyπ (p + q) ≫
    ((integralSingularCochainComplex X).sc (p + q)).moduleCatHomologyIso.hom

/-- Boundaries in degree `q` act trivially under cupping with a fixed degree-`p` cocycle model,
so the right-variable cup construction descends to homology. -/
private theorem integralCupCocycleToHomologyAux_boundary_zero
    (X : TopCat) (p q : ℕ) (φ : integralCochainCycleModel X p) :
    ((integralSingularCochainComplex X).sc q).moduleCatLeftHomologyData.f' ≫
      integralCupCocycleToHomologyAux X p q φ =
    0 := sorry

/-- For a fixed degree-`p` cocycle model, cupping defines a morphism on degree-`q` cohomology. -/
private noncomputable def integralCupCocycleToHomology
    (X : TopCat) (p q : ℕ) (φ : integralCochainCycleModel X p) :
    integralCochainHomologyModel X q ⟶ integralCochainHomologyModel X (p + q) :=
  ((integralSingularCochainComplex X).sc q).moduleCatLeftHomologyData.descH
    (integralCupCocycleToHomologyAux X p q φ)
    (integralCupCocycleToHomologyAux_boundary_zero X p q φ)

/-- Additivity of the homology-level cup operator in the left cocycle model. -/
private theorem integralCupCocycleToHomology_map_add
    (X : TopCat) (p q : ℕ)
    (φ ψ : integralCochainCycleModel X p) :
    (integralCupCocycleToHomology X p q (φ + ψ)).hom =
      (integralCupCocycleToHomology X p q φ).hom +
        (integralCupCocycleToHomology X p q ψ).hom := sorry

/-- Scalar compatibility of the homology-level cup operator in the left cocycle model. -/
private theorem integralCupCocycleToHomology_map_smul
    (X : TopCat) (p q : ℕ) (m : ℤ)
    (φ : integralCochainCycleModel X p) :
    (integralCupCocycleToHomology X p q (m • φ)).hom =
      m • (integralCupCocycleToHomology X p q φ).hom := sorry

/-- The homology-linear target of the cup construction on quotient-model cohomology. -/
private abbrev integralCupLinearTarget (X : TopCat) (p q : ℕ) :=
  integralCochainHomologyModel X q →ₗ[ℤ] integralCochainHomologyModel X (p + q)

/-- The homology-linear target of the cup construction, viewed as a `ℤ`-module object. -/
private abbrev integralCupLinearTargetObj (X : TopCat) (p q : ℕ) :
    ModuleCat ℤ :=
  ModuleCat.of ℤ (integralCupLinearTarget X p q)

/-- A degree-`p` cocycle model acts on degree-`q` quotient-model cohomology by cupping. -/
private noncomputable def integralCupCocycleLinear
    (X : TopCat) (p q : ℕ) :
    integralCochainCycleModel X p ⟶ integralCupLinearTargetObj X p q :=
  ModuleCat.ofHom
    { toFun := fun φ ↦
        (integralCupCocycleToHomology X p q φ).hom
      map_add' := by
        intro φ ψ
        exact integralCupCocycleToHomology_map_add X p q φ ψ
      map_smul' := by
        intro m φ
        exact integralCupCocycleToHomology_map_smul X p q m φ }

/-- Coboundaries act trivially under `integralCupCocycleLinear`, so the cup construction descends
from cocycles to cohomology in the left variable. -/
private theorem integralCupCocycleLinear_boundary_zero
    (X : TopCat) (p q : ℕ) :
    ((integralSingularCochainComplex X).sc p).moduleCatLeftHomologyData.f' ≫
      integralCupCocycleLinear X p q =
    0 := sorry

/-- The canonical degree-`0` unit class in `integralSingularCohomology X`, obtained by
transporting the Chapter 18 quotient-model unit class along the canonical comparison map. -/
noncomputable def integralSingularCohomologyOneClass
    (X : TopCat) :
    integralSingularCohomology X 0 :=
  singularCohomologyClassToIntegralSingularCohomology X 0
    (singularCohomologyOneClass ℤ X)

/-- The canonical cup product on `integralSingularCohomology X`, realized by descending the
cochain-level cup product through the cohomology quotients in both variables. -/
noncomputable def integralSingularCohomologyCup
    (X : TopCat) (p q : ℕ) :
    integralSingularCohomology X p →ₗ[ℤ]
      integralSingularCohomology X q →ₗ[ℤ]
        integralSingularCohomology X (p + q) :=
  let cupDesc :
      integralSingularCohomology X p ⟶ integralCupLinearTargetObj X p q :=
    ((integralSingularCochainComplex X).sc p).moduleCatHomologyIso.hom ≫
      ((integralSingularCochainComplex X).sc p).moduleCatLeftHomologyData.descH
        (integralCupCocycleLinear X p q)
        (integralCupCocycleLinear_boundary_zero X p q)
  { toFun := fun α ↦
      (((integralSingularCochainComplex X).sc (p + q)).moduleCatHomologyIso.inv.hom).comp
        (((cupDesc.hom α).comp
          (((integralSingularCochainComplex X).sc q).moduleCatHomologyIso.hom.hom)))
    map_add' := by
      intro α β
      sorry
    map_smul' := by
      intro m α
      sorry }

/-- The complementary-degree cup-product map to top degree on `integralSingularCohomology X`,
obtained by specializing the canonical internal cup product to total degree `n`. -/
private noncomputable def integralCupProductToTop
    (X : TopCat) (n : ℕ) (p : ℕ) (hpn : p ≤ n) :
    integralSingularCohomology X p →ₗ[ℤ]
      integralSingularCohomology X (n - p) →ₗ[ℤ]
        integralSingularCohomology X n :=
  cast
    (congrArg
      (fun k ↦
        integralSingularCohomology X p →ₗ[ℤ]
          integralSingularCohomology X (n - p) →ₗ[ℤ]
            integralSingularCohomology X k)
      (Nat.add_sub_of_le hpn))
    (integralSingularCohomologyCup X p (n - p))

/-- Evaluating a degree-`n` cocycle model on degree-`n` cycle models gives the canonical linear
map from quotient-model singular homology to `ℤ`. -/
private noncomputable def integralKroneckerCocycleToCycles
    (X : TopCat) (n : ℕ) (φ : integralCochainCycleModel X n) :
    (integralSingularChainComplex X).cycles n ⟶ ModuleCat.of ℤ ℤ :=
  ModuleCat.ofHom
    ((((integralSingularCochainComplex X).iCycles n).hom
        (((integralSingularCochainComplex X).sc n).moduleCatCyclesIso.inv φ)).hom.comp
      ((integralSingularChainComplex X).iCycles n).hom)

/-- Boundaries act trivially under evaluation by a fixed degree-`n` cocycle model, so the
Kronecker construction descends from cycles to homology in the right variable. -/
private theorem integralKroneckerCocycleToHomologyAux_boundary_zero
    (X : TopCat) (n : ℕ) (φ : integralCochainCycleModel X n) :
    ((integralSingularChainComplex X).sc n).moduleCatLeftHomologyData.f' ≫
      (((integralSingularChainComplex X).sc n).moduleCatCyclesIso.inv ≫
        integralKroneckerCocycleToCycles X n φ) =
    0 := sorry

/-- A fixed degree-`n` cocycle model induces the canonical evaluation morphism on degree-`n`
integral singular homology. -/
private noncomputable def integralKroneckerCocycleToHomology
    (X : TopCat) (n : ℕ) (φ : integralCochainCycleModel X n) :
    integralChainHomologyModel X n ⟶ ModuleCat.of ℤ ℤ :=
  ((integralSingularChainComplex X).sc n).moduleCatLeftHomologyData.descH
    (((integralSingularChainComplex X).sc n).moduleCatCyclesIso.inv ≫
      integralKroneckerCocycleToCycles X n φ)
    (integralKroneckerCocycleToHomologyAux_boundary_zero X n φ)

/-- Additivity of the homology-level Kronecker operator in the cocycle model. -/
private theorem integralKroneckerCocycleToHomology_map_add
    (X : TopCat) (n : ℕ)
    (φ ψ : integralCochainCycleModel X n) :
    (integralKroneckerCocycleToHomology X n (φ + ψ)).hom =
      (integralKroneckerCocycleToHomology X n φ).hom +
        (integralKroneckerCocycleToHomology X n ψ).hom := sorry

/-- Scalar compatibility of the homology-level Kronecker operator in the cocycle model. -/
private theorem integralKroneckerCocycleToHomology_map_smul
    (X : TopCat) (n : ℕ) (m : ℤ)
    (φ : integralCochainCycleModel X n) :
    (integralKroneckerCocycleToHomology X n (m • φ)).hom =
      m • (integralKroneckerCocycleToHomology X n φ).hom := sorry

/-- The homology-linear target of the canonical integral Kronecker construction. -/
private abbrev integralKroneckerLinearTarget (X : TopCat) (n : ℕ) :=
  integralChainHomologyModel X n →ₗ[ℤ] ℤ

/-- The homology-linear target of the canonical integral Kronecker construction, viewed as a
`ℤ`-module object. -/
private abbrev integralKroneckerLinearTargetObj (X : TopCat) (n : ℕ) :
    ModuleCat ℤ :=
  ModuleCat.of ℤ (integralKroneckerLinearTarget X n)

/-- A degree-`n` cocycle model determines the canonical evaluation map on quotient-model top
homology. -/
private noncomputable def integralKroneckerCocycleLinear
    (X : TopCat) (n : ℕ) :
    integralCochainCycleModel X n ⟶ integralKroneckerLinearTargetObj X n :=
  ModuleCat.ofHom
    { toFun := fun φ ↦
        (integralKroneckerCocycleToHomology X n φ).hom
      map_add' := by
        intro φ ψ
        exact integralKroneckerCocycleToHomology_map_add X n φ ψ
      map_smul' := by
        intro m φ
        exact integralKroneckerCocycleToHomology_map_smul X n m φ }

/-- Coboundaries act trivially under `integralKroneckerCocycleLinear`, so the integral Kronecker
pairing descends canonically from cocycles to cohomology. -/
private theorem integralKroneckerCocycleLinear_boundary_zero
    (X : TopCat) (n : ℕ) :
    ((integralSingularCochainComplex X).sc n).moduleCatLeftHomologyData.f' ≫
      integralKroneckerCocycleLinear X n =
    0 := sorry

/-- The canonical degree-`n` integral Kronecker pairing on `integralSingularCohomology X n`,
obtained by descending cochain evaluation through the cohomology and homology quotients. -/
private noncomputable def canonicalIntegralKroneckerPairing
    (X : TopCat) (n : ℕ) :
    integralSingularCohomology X n →ₗ[ℤ]
      rSingularHomology ℤ n X →ₗ[ℤ] ℤ :=
  let kroneckerDesc :
      integralSingularCohomology X n ⟶ integralKroneckerLinearTargetObj X n :=
    ((integralSingularCochainComplex X).sc n).moduleCatHomologyIso.hom ≫
      ((integralSingularCochainComplex X).sc n).moduleCatLeftHomologyData.descH
        (integralKroneckerCocycleLinear X n)
        (integralKroneckerCocycleLinear_boundary_zero X n)
  let integralHomologyToCycleModel :
      (integralSingularChainComplex X).homology n →ₗ[ℤ] integralChainHomologyModel X n :=
    ((integralSingularChainComplex X).sc n).moduleCatHomologyIso.hom.hom
  let rHomologyToIntegralHomology :
      rSingularHomology ℤ n X →ₗ[ℤ] integralChainHomologyModel X n :=
    integralHomologyToCycleModel.comp
      (rSingularHomologyIsoIntegralSingularHomology X n).hom.hom
  { toFun := fun α ↦
      (kroneckerDesc.hom α).comp rHomologyToIntegralHomology
    map_add' := by
      intro α β
      sorry
    map_smul' := by
      intro m α
      sorry }

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = n)]

/-- A chosen complementary-degree bilinear pairing on integral singular cohomology and a chosen
degree-`n` Kronecker pairing with a top homology class `z` produce a scalar-valued bilinear
pairing by evaluation on `z`. -/
private noncomputable def cupProductFundamentalClassPairingAux
    (z : rSingularHomology ℤ n (TopCat.of M))
    (cupProductToTop :
      (p : ℕ) → p ≤ n →
        integralSingularCohomology (TopCat.of M) p →ₗ[ℤ]
          integralSingularCohomology (TopCat.of M) (n - p) →ₗ[ℤ]
            integralSingularCohomology (TopCat.of M) n)
    (kroneckerPairing :
      integralSingularCohomology (TopCat.of M) n →ₗ[ℤ]
        rSingularHomology ℤ n (TopCat.of M) →ₗ[ℤ] ℤ)
    (p : ℕ) (hpn : p ≤ n) :
    integralSingularCohomology (TopCat.of M) p →ₗ[ℤ]
      integralSingularCohomology (TopCat.of M) (n - p) →ₗ[ℤ] ℤ where
  toFun α := (LinearMap.flip kroneckerPairing z).comp (cupProductToTop p hpn α)
  map_add' := by
    intro α₁ α₂
    simpa using
      (congrArg (fun f ↦ (LinearMap.flip kroneckerPairing z).comp f)
        ((cupProductToTop p hpn).map_add α₁ α₂)).trans
        (LinearMap.comp_add (cupProductToTop p hpn α₁) (cupProductToTop p hpn α₂)
          (LinearMap.flip kroneckerPairing z))
  map_smul' := by
    intro m α
    ext β
    sorry

/-- A chosen complementary-degree cup-product map to top degree on `integralSingularCohomology X`
realizes the canonical singular cup product when it agrees with
`singularCohomologyCup ℤ X p (n - p)` after transport along
`singularCohomologyClassToIntegralSingularCohomology`. -/
private def IsCanonicalIntegralCupProductToTop
    (X : TopCat)
    (n : ℕ)
    (cupProductToTop :
      (p : ℕ) → p ≤ n →
        integralSingularCohomology X p →ₗ[ℤ]
          integralSingularCohomology X (n - p) →ₗ[ℤ]
            integralSingularCohomology X n) : Prop :=
  ∀ p : ℕ,
    ∀ hpn : p ≤ n,
      ∀ α : singularCohomologyClasses ℤ X p,
      ∀ β : singularCohomologyClasses ℤ X (n - p),
        cupProductToTop p hpn
            (singularCohomologyClassToIntegralSingularCohomology X p α)
            (singularCohomologyClassToIntegralSingularCohomology X (n - p) β) =
          cast
            (congrArg (fun k ↦ (integralSingularCohomology X k : Type _))
              (Nat.add_sub_of_le hpn))
            (singularCohomologyClassToIntegralSingularCohomology X (p + (n - p))
              (singularCohomologyCup ℤ X p (n - p) α β))

/-- Applying `hcup : IsCanonicalIntegralCupProductToTop X n cupProductToTop` to complementary
degrees `p ≤ n` identifies the chosen map with the canonical singular cup product after transport
to `integralSingularCohomology`. -/
private theorem IsCanonicalIntegralCupProductToTop.apply
    {X : TopCat} {n : ℕ}
    {cupProductToTop :
      (p : ℕ) → p ≤ n →
        integralSingularCohomology X p →ₗ[ℤ]
          integralSingularCohomology X (n - p) →ₗ[ℤ]
            integralSingularCohomology X n}
    (hcup : IsCanonicalIntegralCupProductToTop X n cupProductToTop)
    (p : ℕ) (hpn : p ≤ n)
    (α : singularCohomologyClasses ℤ X p)
    (β : singularCohomologyClasses ℤ X (n - p)) :
    cupProductToTop p hpn
        (singularCohomologyClassToIntegralSingularCohomology X p α)
        (singularCohomologyClassToIntegralSingularCohomology X (n - p) β) =
      cast
        (congrArg (fun k ↦ (integralSingularCohomology X k : Type _))
          (Nat.add_sub_of_le hpn))
        (singularCohomologyClassToIntegralSingularCohomology X (p + (n - p))
          (singularCohomologyCup ℤ X p (n - p) α β)) := by
  exact hcup p hpn α β

/-- A chosen degree-`n` bilinear pairing on `integralSingularCohomology X n` and
`rSingularHomology ℤ n X` realizes the canonical integral Kronecker pairing when it evaluates
represented cohomology and homology classes by applying the underlying cocycle to the underlying
cycle. -/
def IsCanonicalIntegralKroneckerPairing
    (X : TopCat)
    (n : ℕ)
    (kroneckerPairing :
      integralSingularCohomology X n →ₗ[ℤ]
        rSingularHomology ℤ n X →ₗ[ℤ] ℤ) : Prop :=
  ∀ φ : (integralSingularCochainComplex X).cycles n,
      ∀ c : (integralSingularChainComplex X).cycles n,
        kroneckerPairing
            ((integralSingularCochainComplex X).homologyπ n φ)
            ((rSingularHomologyIsoIntegralSingularHomology X n).inv
              ((integralSingularChainComplex X).homologyπ n c)) =
          (((integralSingularCochainComplex X).iCycles n).hom φ).hom
            (((integralSingularChainComplex X).iCycles n).hom c)

/-- Applying `hkr : IsCanonicalIntegralKroneckerPairing X n kroneckerPairing` to represented
cohomology and homology classes identifies the chosen pairing with cocycle evaluation on the
corresponding cycle. -/
theorem IsCanonicalIntegralKroneckerPairing.apply
    {X : TopCat} {n : ℕ}
    {kroneckerPairing :
      integralSingularCohomology X n →ₗ[ℤ]
        rSingularHomology ℤ n X →ₗ[ℤ] ℤ}
    (hkr : IsCanonicalIntegralKroneckerPairing X n kroneckerPairing)
    (φ : (integralSingularCochainComplex X).cycles n)
    (c : (integralSingularChainComplex X).cycles n) :
    kroneckerPairing
        ((integralSingularCochainComplex X).homologyπ n φ)
        ((rSingularHomologyIsoIntegralSingularHomology X n).inv
          ((integralSingularChainComplex X).homologyπ n c)) =
      (((integralSingularCochainComplex X).iCycles n).hom φ).hom
        (((integralSingularChainComplex X).iCycles n).hom c) := sorry

/-- Evaluating the canonical cup product of complementary-degree integral singular cohomology
classes on a chosen class `z ∈ H_n(M; ℤ)` yields a bilinear pairing
`H^p(M; ℤ) ⊗ H^(n - p)(M; ℤ) → ℤ`. When `z` is a fundamental class for an orientation on `M`,
this is the pairing of Construction 20.1.4. -/
noncomputable def cupProductTopHomologyClassPairing
    (z : rSingularHomology ℤ n (TopCat.of M))
    (p : ℕ) (hpn : p ≤ n) :
    integralSingularCohomology (TopCat.of M) p →ₗ[ℤ]
      integralSingularCohomology (TopCat.of M) (n - p) →ₗ[ℤ] ℤ :=
  cupProductFundamentalClassPairingAux
    z
    (integralCupProductToTop (TopCat.of M) n)
    (canonicalIntegralKroneckerPairing (TopCat.of M) n)
    p hpn

/-- If `z` is a fundamental class, then applying `cupProductTopHomologyClassPairing z p hpn` to
the canonical integral singular cohomology classes attached to singular cocycles agrees with the
value of any canonical degree-`n` Kronecker pairing on the transported cup product class. -/
theorem cupProductTopHomologyClassPairing_apply
    (z : rSingularHomology ℤ n (TopCat.of M))
    (p : ℕ) (hpn : p ≤ n)
    (kroneckerPairing :
      integralSingularCohomology (TopCat.of M) n →ₗ[ℤ]
        rSingularHomology ℤ n (TopCat.of M) →ₗ[ℤ] ℤ)
    (hkr : IsCanonicalIntegralKroneckerPairing (TopCat.of M) n kroneckerPairing)
    (α : singularCohomologyClasses ℤ (TopCat.of M) p)
    (β : singularCohomologyClasses ℤ (TopCat.of M) (n - p)) :
    cupProductTopHomologyClassPairing
        z p hpn
        (singularCohomologyClassToIntegralSingularCohomology (TopCat.of M) p α)
        (singularCohomologyClassToIntegralSingularCohomology (TopCat.of M) (n - p) β) =
      kroneckerPairing
        (cast
          (congrArg (fun k ↦ (integralSingularCohomology (TopCat.of M) k : Type _))
            (Nat.add_sub_of_le hpn))
          (singularCohomologyClassToIntegralSingularCohomology
            (TopCat.of M) (p + (n - p))
            (singularCohomologyCup ℤ (TopCat.of M) p (n - p) α β))) z := sorry

end

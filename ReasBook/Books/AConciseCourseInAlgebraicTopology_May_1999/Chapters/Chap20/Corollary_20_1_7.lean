import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.SingularCohomology

open AlgebraicTopology CategoryTheory
open scoped Manifold Topology

noncomputable section

universe u

-- `LinearMap.IsPerfPair` is the canonical owner for nonsingularity of a scalar-valued bilinear
-- pairing. In Chapter 20, the source-facing pairing is the cup product followed by evaluation on
-- a specified compatible fundamental class of an oriented compact manifold, expressed on
-- `rSingularCohomology`.

section

variable {R : Type u} [Field R]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = n)]

/-- A singular cocycle determines a cycle in the cochain-complex owner
`singularCochainComplex R X`. -/
private theorem singularCocycleToRSingularCohomology_isCycle
    (X : TopCat.{u}) (p : ℕ) (φ : singularCocycles R X p) :
    (((singularCochainComplex R X).sc p).g
        ((singularCochainComplexDegreeEquiv R X p).symm φ.1)) = 0 := sorry

/-- A source-facing cocycle determines its class in `rSingularCohomology R X p`. -/
private noncomputable def singularCocycleToRSingularCohomology
    (X : TopCat.{u}) (p : ℕ) (φ : singularCocycles R X p) :
    rSingularCohomology R X p :=
  (singularCochainComplex R X).homologyπ p
    (((singularCochainComplex R X).sc p).cyclesMk
      ((singularCochainComplexDegreeEquiv R X p).symm φ.1)
      (singularCocycleToRSingularCohomology_isCycle X p φ))

/-- A chosen cycle in `singularCochainComplex R X` determines a source-facing singular cocycle. -/
private theorem rCycleToSingularCocycle_isClosed
    (X : TopCat.{u}) (p : ℕ) (φ : (singularCochainComplex R X).cycles p) :
    singularCochainCoboundary R X p
        (singularCochainComplexDegreeEquiv R X p
          (((singularCochainComplex R X).iCycles p).hom φ)) = 0 := sorry

/-- A chosen cycle representative in `singularCochainComplex R X` determines a singular cocycle in
degree `p`. -/
private noncomputable def rCycleToSingularCocycle
    (X : TopCat.{u}) (p : ℕ) (φ : (singularCochainComplex R X).cycles p) :
    singularCocycles R X p :=
  ⟨singularCochainComplexDegreeEquiv R X p
      (((singularCochainComplex R X).iCycles p).hom φ),
    rCycleToSingularCocycle_isClosed X p φ⟩

/-- A cohomology class in `rSingularCohomology R X p` admits a chosen cycle representative in
`singularCochainComplex R X`. -/
private noncomputable def rSingularCohomologyRepresentative
    (X : TopCat.{u}) (p : ℕ) (α : rSingularCohomology R X p) :
    (singularCochainComplex R X).cycles p :=
  Classical.choose
    ((ModuleCat.epi_iff_surjective ((singularCochainComplex R X).homologyπ p)).1
      inferInstance α)

/-- A class of `rSingularCohomology R X p` yields a represented singular cohomology class by
choosing a cycle representative in `singularCochainComplex R X`. -/
private noncomputable def rSingularCohomologyClassRepresentative
    (X : TopCat.{u}) (p : ℕ) (α : rSingularCohomology R X p) :
    singularCohomologyClasses R X p :=
  Quotient.mk (singularCohomologySetoid R X p)
    (rCycleToSingularCocycle X p (rSingularCohomologyRepresentative X p α))

/-- The canonical coefficient object `constantCoefficientModule R` is the unit `R`-module up to
the tautological `ULift` linear equivalence. -/
private noncomputable def constantCoefficientModuleIsoUnit :
    constantCoefficientModule R ≅ ModuleCat.of.{u} R R :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift R ≃ₗ[R] R)

/-- The chapter owner `rSingularHomology R p X` is canonically identified with the degree-`p`
homology of `rSingularChainComplex R X`. -/
private noncomputable def rSingularHomologyIsoChainComplexHomology
    (X : TopCat.{u}) (p : ℕ) :
    rSingularHomology R p X ≅ (rSingularChainComplex R X).homology p :=
  (((singularHomologyFunctor (ModuleCat.{u} R) p).mapIso constantCoefficientModuleIsoUnit).app X)

/-- A homology class in `rSingularHomology R p X` admits a chosen cycle representative in the
singular chain complex `rSingularChainComplex X`. -/
private noncomputable def rSingularHomologyRepresentative
    (X : TopCat.{u}) (p : ℕ) (z : rSingularHomology R p X) :
    (rSingularChainComplex R X).cycles p :=
  Classical.choose
    ((ModuleCat.epi_iff_surjective ((rSingularChainComplex R X).homologyπ p)).1
      inferInstance ((rSingularHomologyIsoChainComplexHomology X p).hom z))

/-- The complementary-degree cup-product map to top degree on `rSingularCohomology R X`, formed
by transporting the Chapter 18 cup product on `singularCohomologyClasses` to the Chapter 20 owner
`rSingularCohomology`. -/
private noncomputable def rSingularCupProductToTop
    (X : TopCat.{u}) (p : ℕ) (hpn : p ≤ n) :
    rSingularCohomology R X p →ₗ[R]
      rSingularCohomology R X (n - p) →ₗ[R] rSingularCohomology R X n :=
  { toFun := fun α ↦
      { toFun := fun β ↦
          cast
            (congrArg (fun k ↦ (rSingularCohomology R X k : Type _))
              (Nat.add_sub_of_le hpn))
            (singularCohomologyClassToRSingularCohomology R X (p + (n - p))
              (singularCohomologyCup R X p (n - p)
                (rSingularCohomologyClassRepresentative X p α)
                (rSingularCohomologyClassRepresentative X (n - p) β)))
        map_add' := sorry
        map_smul' := sorry }
    map_add' := sorry
    map_smul' := sorry }

/-- A chosen complementary-degree bilinear pairing on `rSingularCohomology R X` realizes the
canonical singular cup product in total degree `n` when it agrees with
`singularCohomologyCup R X p (n - p)` after transport along
`singularCohomologyClassToRSingularCohomology`. -/
private def IsCanonicalRSingularCupProductToTop
    (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ)
    (cupProductToTop :
      (p : ℕ) → p ≤ n →
        rSingularCohomology R X p →ₗ[R]
          rSingularCohomology R X (n - p) →ₗ[R] rSingularCohomology R X n) : Prop :=
  ∀ (p : ℕ) (hpn : p ≤ n) (α : singularCohomologyClasses R X p)
      (β : singularCohomologyClasses R X (n - p)),
    cupProductToTop p hpn
        (singularCohomologyClassToRSingularCohomology R X p α)
        (singularCohomologyClassToRSingularCohomology R X (n - p) β) =
      cast
        (congrArg (fun k ↦ (rSingularCohomology R X k : Type _))
          (Nat.add_sub_of_le hpn))
        (singularCohomologyClassToRSingularCohomology R X (p + (n - p))
          (singularCohomologyCup R X p (n - p) α β))

/-- Applying `hcup : IsCanonicalRSingularCupProductToTop R X n cupProductToTop` to complementary
degrees `p ≤ n` identifies the chosen pairing with the canonical singular cup product after
transport to `rSingularCohomology`. -/
private theorem IsCanonicalRSingularCupProductToTop.apply
    {R : Type u} [Field R] {X : TopCat.{u}} {n : ℕ}
    {cupProductToTop :
      (p : ℕ) → p ≤ n →
        rSingularCohomology R X p →ₗ[R]
          rSingularCohomology R X (n - p) →ₗ[R] rSingularCohomology R X n}
    (hcup : IsCanonicalRSingularCupProductToTop R X n cupProductToTop)
    (p : ℕ) (hpn : p ≤ n)
    (α : singularCohomologyClasses R X p)
    (β : singularCohomologyClasses R X (n - p)) :
    cupProductToTop p hpn
        (singularCohomologyClassToRSingularCohomology R X p α)
        (singularCohomologyClassToRSingularCohomology R X (n - p) β) =
      cast
        (congrArg (fun k ↦ (rSingularCohomology R X k : Type _))
          (Nat.add_sub_of_le hpn))
        (singularCohomologyClassToRSingularCohomology R X (p + (n - p))
          (singularCohomologyCup R X p (n - p) α β)) := sorry

/-- The scalar-valued Kronecker pairing on `rSingularCohomology R X p` and `rSingularHomology R p
X`, defined privately by choosing representatives and evaluating the resulting cochain on the
resulting cycle. -/
private noncomputable def rSingularKroneckerPairing
    (X : TopCat.{u}) (p : ℕ) :
    rSingularCohomology R X p →ₗ[R] rSingularHomology R p X →ₗ[R] R :=
  { toFun := fun α ↦
      { toFun := fun z ↦
          ((singularCochainComplex_X R X p ▸
              (((singularCochainComplex R X).iCycles p).hom
                (rSingularCohomologyRepresentative X p α))).hom)
            (((rSingularChainComplex R X).iCycles p).hom
              (rSingularHomologyRepresentative X p z))
        map_add' := sorry
        map_smul' := sorry }
    map_add' := sorry
    map_smul' := sorry }

/-- A chosen degree-`n` bilinear pairing on `rSingularCohomology R X n` and
`rSingularHomology R n X` realizes the canonical singular Kronecker pairing when it evaluates
represented cohomology and homology classes by applying the underlying cochain to the underlying
cycle. -/
def IsCanonicalRSingularKroneckerPairing
    (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ)
    (kroneckerPairing :
      rSingularCohomology R X n →ₗ[R]
        rSingularHomology R n X →ₗ[R] R) : Prop :=
  ∀ (φ : (singularCochainComplex R X).cycles n) (c : (rSingularChainComplex R X).cycles n),
    kroneckerPairing
        ((singularCochainComplex R X).homologyπ n φ)
        ((rSingularHomologyIsoChainComplexHomology X n).inv
          ((rSingularChainComplex R X).homologyπ n c)) =
      ((singularCochainComplex_X R X n ▸
          (((singularCochainComplex R X).iCycles n).hom φ)).hom)
        (((rSingularChainComplex R X).iCycles n).hom c)

/-- Applying `hkr : IsCanonicalRSingularKroneckerPairing R X n kroneckerPairing` to represented
cohomology and homology classes identifies the chosen pairing with cochain evaluation on the
corresponding cycle. -/
theorem IsCanonicalRSingularKroneckerPairing.apply
    {R : Type u} [Field R] {X : TopCat.{u}} {n : ℕ}
    {kroneckerPairing :
      rSingularCohomology R X n →ₗ[R]
        rSingularHomology R n X →ₗ[R] R}
    (hkr : IsCanonicalRSingularKroneckerPairing R X n kroneckerPairing)
    (φ : (singularCochainComplex R X).cycles n)
    (c : (rSingularChainComplex R X).cycles n) :
    kroneckerPairing
        ((singularCochainComplex R X).homologyπ n φ)
        ((rSingularHomologyIsoChainComplexHomology X n).inv
          ((rSingularChainComplex R X).homologyπ n c)) =
      ((singularCochainComplex_X R X n ▸
          (((singularCochainComplex R X).iCycles n).hom φ)).hom)
        (((rSingularChainComplex R X).iCycles n).hom c) := sorry

/-- The representative-based cup product to top degree realizes the canonical singular cup
product after transport to `rSingularCohomology`. -/
private theorem rSingularCupProductToTop_isCanonical
    (X : TopCat.{u}) (n : ℕ) :
    IsCanonicalRSingularCupProductToTop R X n
      (fun p hpn ↦ rSingularCupProductToTop X p hpn) := sorry

/-- The representative-based Kronecker pairing realizes the canonical singular cochain evaluation
pairing on represented classes. -/
private theorem rSingularKroneckerPairing_isCanonical
    (X : TopCat.{u}) (n : ℕ) :
    IsCanonicalRSingularKroneckerPairing R X n
      (rSingularKroneckerPairing X n) := sorry

/-- A chosen complementary-degree cup-product pairing on `rSingularCohomology R X` and a chosen
degree-`n` Kronecker pairing with a top homology class `z` produce a scalar-valued bilinear
pairing by evaluation on `z`. -/
private noncomputable def poincareDualityCohomologyPairingAux
    (X : TopCat.{u})
    (z : rSingularHomology R n X)
    (cupProductToTop :
      (p : ℕ) → p ≤ n →
        rSingularCohomology R X p →ₗ[R]
          rSingularCohomology R X (n - p) →ₗ[R] rSingularCohomology R X n)
    (kroneckerPairing :
      rSingularCohomology R X n →ₗ[R]
        rSingularHomology R n X →ₗ[R] R)
    (p : ℕ) (hpn : p ≤ n) :
    rSingularCohomology R X p →ₗ[R]
      rSingularCohomology R X (n - p) →ₗ[R] R where
  toFun α := (LinearMap.flip kroneckerPairing z).comp (cupProductToTop p hpn α)
  map_add' := sorry
  map_smul' := sorry

/-- The cup-product/evaluation pairing on `rSingularCohomology R (TopCat.of M)` attached to the
specified top homology class `z`, obtained by taking the
complementary-degree cup product and then evaluating the resulting degree-`n` class on `z`. -/
noncomputable def poincareDualityCohomologyPairing
    (z : rSingularHomology R n (TopCat.of.{u} M)) (p : ℕ) (hpn : p ≤ n) :
    rSingularCohomology R (TopCat.of.{u} M) p →ₗ[R]
      rSingularCohomology R (TopCat.of.{u} M) (n - p) →ₗ[R] R :=
  poincareDualityCohomologyPairingAux
    (TopCat.of.{u} M) z
    (fun q hqn ↦ rSingularCupProductToTop (TopCat.of.{u} M) q hqn)
    (rSingularKroneckerPairing (TopCat.of.{u} M) n) p hpn

omit [CompactSpace M] in
/-- Evaluating `poincareDualityCohomologyPairing z p hpn` on source-facing singular cohomology
classes agrees with any canonical degree-`n` Kronecker pairing applied to the transported cup
product class. -/
theorem poincareDualityCohomologyPairing_apply
    [CompactSpace M] (z : rSingularHomology R n (TopCat.of.{u} M)) (p : ℕ) (hpn : p ≤ n)
    (kroneckerPairing :
      rSingularCohomology R (TopCat.of.{u} M) n →ₗ[R]
        rSingularHomology R n (TopCat.of.{u} M) →ₗ[R] R)
    (hkr : IsCanonicalRSingularKroneckerPairing R (TopCat.of.{u} M) n kroneckerPairing)
    (α : singularCohomologyClasses R (TopCat.of.{u} M) p)
    (β : singularCohomologyClasses R (TopCat.of.{u} M) (n - p)) :
    poincareDualityCohomologyPairing z p hpn
        (singularCohomologyClassToRSingularCohomology R (TopCat.of.{u} M) p α)
        (singularCohomologyClassToRSingularCohomology R (TopCat.of.{u} M) (n - p) β) =
      kroneckerPairing
        (cast
          (congrArg (fun k ↦ (rSingularCohomology R (TopCat.of.{u} M) k : Type _))
            (Nat.add_sub_of_le hpn))
          (singularCohomologyClassToRSingularCohomology R (TopCat.of.{u} M) (p + (n - p))
            (singularCohomologyCup R (TopCat.of.{u} M) p (n - p) α β))) z := sorry

/-- The cup-product/evaluation pairing attached to an intrinsic `R`-fundamental class is
nonsingular. Here "nonsingular" is formalized by the canonical typeclass
`LinearMap.IsPerfPair`. -/
instance poincareDualityCohomologyPairing_isPerfPair
    (z : rSingularHomology R n (TopCat.of.{u} M))
    [Fact (IsRFundamentalClass R n M z)]
    (p : ℕ) (hpn : p ≤ n) :
    (poincareDualityCohomologyPairing z p hpn).IsPerfPair := sorry

end

section

variable {R : Type u} [Field R]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = n)]

omit [CompactSpace M] in
/-- Corollary 20.1.7. If `z` is an `R`-fundamental class compatible with the oriented manifold
`o`, then the cup-product/evaluation pairing
`poincareDualityCohomologyPairing z p hpn : H^p(M; R) ⊗ H^(n - p)(M; R) → R` is nonsingular.
Here "nonsingular" is formalized by the canonical typeclass `LinearMap.IsPerfPair`. -/
theorem poincareDualityCohomologyPairing_isPerfPair_of_isRFundamentalClassFor
    [CompactSpace M] (o : ROrientedManifold R I n M)
    (z : rSingularHomology R n (TopCat.of.{u} M))
    (hz : IsRFundamentalClassFor o z) (p : ℕ) (hpn : p ≤ n) :
    (poincareDualityCohomologyPairing z p hpn).IsPerfPair := by
  let _ : Fact (IsRFundamentalClass R n M z) := ⟨hz.isRFundamentalClass⟩
  infer_instance

end

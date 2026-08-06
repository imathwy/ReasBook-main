import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Corollary_20_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.ModTwoSingularCohomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

open AlgebraicTopology CategoryTheory
open scoped DirectSum Manifold SingularChains Topology

noncomputable section

section

variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [CompactSpace M]
variable [IsManifold (𝓡 n) ⊤ M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]
variable
  [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]

private abbrev modTwoSingularCochainComplex (X : TopCat) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.linearYonedaObj (C_*(X)) ℤ (ModuleCat.of ℤ (ZMod 2))

private theorem modTwoSingularCochainComplex_X (X : TopCat) (n : ℕ) :
    (modTwoSingularCochainComplex X).X n =
      ModuleCat.of ℤ ((C_*(X)).X n ⟶ ModuleCat.of ℤ (ZMod 2)) := by
  rfl

private noncomputable def singularCoproductToZModTwoHomEquiv
    (A : Type) :
    ((∐ fun _ : A ↦ ModuleCat.of ℤ ℤ) ⟶ ModuleCat.of ℤ (ZMod 2)) ≃ₗ[ℤ]
      ModuleCat.of ℤ (A → ZMod 2) where
  toFun φ := fun a ↦ φ ((Limits.Sigma.ι (fun _ : A ↦ ModuleCat.of ℤ ℤ) a) 1)
  map_add' := by sorry
  map_smul' := by sorry
  invFun f :=
    Limits.Sigma.desc fun a ↦
      ModuleCat.ofHom
        { toFun := fun m ↦ m • f a
          map_add' := by
            intro m₁ m₂
            simp [add_smul]
          map_smul' := by
            intro m₁ m₂
            simp [mul_smul] }
  left_inv := by
    sorry
  right_inv := by
    sorry

private noncomputable def modTwoSingularCochainComplexDegreeEquiv
    (X : TopCat) (n : ℕ) :
    (modTwoSingularCochainComplex X).X n ≃ₗ[ℤ]
      ModuleCat.of ℤ (singularSimplex n X → ZMod 2) where
  toFun φ :=
    let φ' :
        ModuleCat.of ℤ (singularChainDegree ℤ X n ⟶ ModuleCat.of ℤ (ZMod 2)) :=
      show ModuleCat.of ℤ (singularChainDegree ℤ X n ⟶ ModuleCat.of ℤ (ZMod 2)) from
        modTwoSingularCochainComplex_X X n ▸ φ
    singularCoproductToZModTwoHomEquiv (singularSimplex n X)
      ((singularChainDegreeIsoCoproduct ℤ X n).inv ≫ φ')
  map_add' := by sorry
  map_smul' := by sorry
  invFun f :=
    show (modTwoSingularCochainComplex X).X n from
      (modTwoSingularCochainComplex_X X n).symm ▸
        ((singularChainDegreeIsoCoproduct ℤ X n).hom ≫
          (singularCoproductToZModTwoHomEquiv (singularSimplex n X)).symm f)
  left_inv := by sorry
  right_inv := by sorry

private theorem modTwoSingularCycleToSingularCocycle_isClosed
    (X : TopCat) (n : ℕ) (φ : (modTwoSingularCochainComplex X).cycles n) :
    singularCochainCoboundary (ZMod 2) X n
        (modTwoSingularCochainComplexDegreeEquiv X n
          (((modTwoSingularCochainComplex X).iCycles n).hom φ)) = 0 := by
  sorry

private noncomputable def modTwoSingularCycleToSingularCocycle
    (X : TopCat) (n : ℕ) (φ : (modTwoSingularCochainComplex X).cycles n) :
    singularCocycles (ZMod 2) X n :=
  ⟨modTwoSingularCochainComplexDegreeEquiv X n
      (((modTwoSingularCochainComplex X).iCycles n).hom φ),
    modTwoSingularCycleToSingularCocycle_isClosed X n φ⟩

private noncomputable def modTwoSingularCohomologyRepresentative
    (X : TopCat) (n : ℕ) (α : modTwoSingularCohomology X n) :
    (modTwoSingularCochainComplex X).cycles n :=
  Classical.choose
    ((ModuleCat.epi_iff_surjective ((modTwoSingularCochainComplex X).homologyπ n)).1
      inferInstance α)

private noncomputable def modTwoSingularCohomologyToRSingularCohomology
    (X : TopCat) (n : ℕ) :
    modTwoSingularCohomology X n →+
      rSingularCohomology (ZMod 2) X n where
  toFun α :=
    singularCohomologyClassToRSingularCohomology (ZMod 2) X n
      (Quotient.mk (singularCohomologySetoid (ZMod 2) X n)
        (modTwoSingularCycleToSingularCocycle X n
          (modTwoSingularCohomologyRepresentative X n α)))
  map_zero' := by
    sorry
  map_add' := by
    intro α β
    sorry

variable (H2 : ModTwoCohomologyTheory)
variable (w : StiefelWhitneyClassFamily H2)

/-- The partition-indexed monomial in the tangential Stiefel-Whitney classes of `M`, viewed in the
canonical total mod-`2` cohomology ring of `M`. -/
def tangentialStiefelWhitneyMonomial
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2)
    [CommRing (modTwoCohomologyStar H2 (TopCat.of M))]
    (σ : Nat.Partition n) :
    modTwoCohomologyStar H2 (TopCat.of M) :=
  (σ.parts.map fun i ↦
    (DirectSum.lof ℤ ℕ (fun q ↦ modTwoCohomologyGroup H2 q (TopCat.of M)) i
      (tangentialStiefelWhitneyClass n M H2 w i) :
      modTwoCohomologyStar H2 (TopCat.of M))).prod

/-- The degree-`n` tangential Stiefel-Whitney monomial class of `M` indexed by the partition
`σ`, obtained by projecting the total tangential Stiefel-Whitney monomial to cohomological degree
`n`. -/
abbrev tangentialStiefelWhitneyMonomialClass
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2)
    [CommRing (modTwoCohomologyStar H2 (TopCat.of M))]
    (σ : Nat.Partition n) :
    modTwoCohomologyGroup H2 n (TopCat.of M) :=
  DirectSum.component ℤ ℕ (fun q ↦ modTwoCohomologyGroup H2 q (TopCat.of M)) n
    (tangentialStiefelWhitneyMonomial H2 w σ)

/-- The tangential Stiefel-Whitney number of `M` indexed by the partition `σ`, obtained by
evaluating the degree-`n` tangential Stiefel-Whitney monomial class on a chosen degree-`n`
homology class via the chosen degree-`n` pairing. -/
abbrev tangentialStiefelWhitneyNumber
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2)
    [CommRing (modTwoCohomologyStar H2 (TopCat.of M))]
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2)
    (σ : Nat.Partition n) : ZMod 2 :=
  kroneckerPairing (tangentialStiefelWhitneyMonomialClass H2 w σ) fundamentalClass

namespace CanonicalModTwoCohomologyAlgebra

/-- Evaluate the `σ`-indexed tangential Stiefel-Whitney number using the canonical total mod-`2`
cohomology algebra carried by `A`. This is the explicit bridge from the chosen algebra owner to
the chapter-local characteristic-number API. -/
abbrev tangentialStiefelWhitneyNumber
    {H2' : ModTwoCohomologyTheory}
    (A : CanonicalModTwoCohomologyAlgebra H2' (TopCat.of M))
    (w : StiefelWhitneyClassFamily H2')
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (kroneckerPairing :
      modTwoCohomologyGroup H2' n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2)
    (σ : Nat.Partition n) : ZMod 2 :=
  let _ : CommRing (modTwoCohomologyStar H2' (TopCat.of M)) := A.toCommRing
  _root_.tangentialStiefelWhitneyNumber H2' w fundamentalClass kroneckerPairing σ

end CanonicalModTwoCohomologyAlgebra

/-- A degree-`n` pairing on `modTwoCohomologyGroup H2 n (TopCat.of M)` is compatible with a
canonical Chapter 20 singular Kronecker pairing when it agrees pointwise with transport along the
comparison isomorphism `H2.comparison n (TopCat.of M)` and the Chapter 22 bridge from
`modTwoSingularCohomology` to `rSingularCohomology`. This keeps the public Chapter 23 API at the
Prop/specification level instead of exporting a chosen transported pairing as concrete data. -/
def IsModTwoSingularKroneckerTransport
    (H2 : ModTwoCohomologyTheory)
    (canonicalKroneckerPairing :
      rSingularCohomology (ZMod 2) (TopCat.of M) n →ₗ[ZMod 2]
        rSingularHomology (ZMod 2) n (TopCat.of M) →ₗ[ZMod 2] ZMod 2)
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2) :
    Prop :=
  ∀ α fundamentalClass,
    kroneckerPairing α fundamentalClass =
      canonicalKroneckerPairing
        (modTwoSingularCohomologyToRSingularCohomology (TopCat.of M) n
          (ConcreteCategory.hom ((H2.comparison n (TopCat.of M)).hom) α))
        fundamentalClass

/-- The representative-based transported pairing satisfies
`IsModTwoSingularKroneckerTransport`. This theorem provides the public bridge needed by later
source-facing Chapter 23 statements without exporting the chosen transported pairing itself. -/
theorem exists_modTwoSingularKroneckerTransport
    (H2 : ModTwoCohomologyTheory)
    (canonicalKroneckerPairing :
      rSingularCohomology (ZMod 2) (TopCat.of M) n →ₗ[ZMod 2]
        rSingularHomology (ZMod 2) n (TopCat.of M) →ₗ[ZMod 2] ZMod 2) :
    ∃ kroneckerPairing :
        modTwoCohomologyGroup H2 n (TopCat.of M) →+
          rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2,
      IsModTwoSingularKroneckerTransport H2 canonicalKroneckerPairing kroneckerPairing := by
  classical
  refine ⟨{
      toFun := fun α ↦
        let α' :=
          modTwoSingularCohomologyToRSingularCohomology (TopCat.of M) n
            (ConcreteCategory.hom ((H2.comparison n (TopCat.of M)).hom) α)
        (canonicalKroneckerPairing α').toAddMonoidHom
      map_zero' := by
        sorry
      map_add' := by
        intro α β
        sorry
    }, ?_⟩
  intro α fundamentalClass
  rfl

/-- The explicit chosen-data evaluation of the `σ`-indexed tangential Stiefel-Whitney number of
`M`, formed from a compatible mod-`2` fundamental class, a chosen singular-cohomology
Kronecker pairing on Chapter 20 `rSingularCohomology`, and a fixed canonical total mod-`2`
cohomology algebra on `M`. This remains helper infrastructure; source-facing canonicality and
vanishing statements should use Prop-valued setup predicates in `Lemma_23_4_3.lean`. -/
private abbrev tangentialStiefelWhitneyNumberWithChoices
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (canonicalKroneckerPairing :
      rSingularCohomology (ZMod 2) (TopCat.of M) n →ₗ[ZMod 2]
        rSingularHomology (ZMod 2) n (TopCat.of M) →ₗ[ZMod 2] ZMod 2)
    (σ : Nat.Partition n) : ZMod 2 :=
  A.tangentialStiefelWhitneyNumber w
    fundamentalClass
    (Classical.choose (exists_modTwoSingularKroneckerTransport
      (M := M) (n := n) H2 canonicalKroneckerPairing))
    σ

end

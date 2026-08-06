import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Problem_19_6_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1
import Mathlib.Topology.Homotopy.Contractible

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open SpacePair
open scoped TensorProduct

noncomputable section

universe u v

-- Semantic recall via `lean_leansearch` surfaced only unrelated sheaf-theoretic Mayer-Vietoris
-- APIs. The local Chapter 19 owners for this item are therefore `reducedCohomology`, the
-- singleton-basepoint cup product induced from `RelativeCupProductMap`, the induced
-- `reducedCupProduct` from Problem 19.6.3, and the canonical pair-theory
-- `relativeCohomology` owner from Problem 19.6.2 for auxiliary quotient-model comparisons.

/-- The reduced cup product on `reducedCohomology E` induced by the relative cup product at the
singleton basepoint subset of a based space `X`. -/
noncomputable def reducedCohomologyCup
    (E : ℤ → (Y : TopCat) → Set Y → Type v)
    [∀ q (Y : TopCat) (S : Set Y), AddCommGroup (E q Y S)]
    [∀ q (Y : TopCat) (S : Set Y), Module ℤ (E q Y S)]
    (cupProduct : RelativeCupProductMap E)
    (X : BasedSpace) (p q : ℤ) :
    reducedCohomology E p X ⊗[ℤ] reducedCohomology E q X →ₗ[ℤ]
      reducedCohomology E (p + q) X :=
  Eq.ndrec
    (motive := fun S : Set X.right ↦
      reducedCohomology E p X ⊗[ℤ] reducedCohomology E q X →ₗ[ℤ] E (p + q) X.right S)
    (cupProduct
      ({underTopBasepoint X} : Set X.right)
      ({underTopBasepoint X} : Set X.right)
      p q)
    (by
      ext x
      simp)

/-- Transporting the chosen relative cup product on `E` along the identifications with a bundled
pair cohomology theory produces the corresponding pair-theoretic cup-product family. -/
def relativeCupProductCompatibleWithPairTheory
    (E : ℤ → (Y : TopCat.{u}) → Set Y → Type v)
    [∀ n (Y : TopCat.{u}) (S : Set Y), AddCommGroup (E n Y S)]
    [∀ n (Y : TopCat.{u}) (S : Set Y), Module ℤ (E n Y S)]
    {π : Type u} [AddCommGroup π]
    (pairTheory : PairCohomologyTheory π)
    (pairTheoryComparison :
      ∀ (n : ℤ) (Y : TopCat.{u}) (S : Set Y),
        E n Y S ≃ₗ[ℤ] pairTheory.relativeCohomology n Y S)
    (theoryCup : PairCohomologyTheory.RelativeCupProductMap pairTheory)
    (cupProduct : RelativeCupProductMap E) : Prop :=
  ∀ {Y : TopCat.{u}} (A B : Set Y) (p q : ℤ),
    (theoryCup A B p q).comp
        (TensorProduct.map
          (pairTheoryComparison p Y A).toLinearMap
          (pairTheoryComparison q Y B).toLinearMap) =
      (pairTheoryComparison (p + q) Y (A ∪ B)).toLinearMap.comp (cupProduct A B p q)

/-- For a contractible open cover as in Problem 19.6.4, the chosen quotient model for `X/(A ∪ B)`
has trivial positive-degree reduced cohomology. This is the Mayer-Vietoris vanishing input used
to deduce the cup-product consequence on `underTopOfPoint X x₀`, under the ambient Chapter 19
pair-cohomology-theory assumptions and while keeping the quotient identification data explicit. -/
private theorem unionReducedSubsingleton_of_contractible_cover
    (E : ℤ → (Y : TopCat) → Set Y → Type v)
    [∀ n (Y : TopCat) (S : Set Y), AddCommGroup (E n Y S)]
    [∀ n (Y : TopCat) (S : Set Y), Module ℤ (E n Y S)]
    {π : Type u} [AddCommGroup π]
    (pairTheory : PairCohomologyTheory π)
    (pairTheoryComparison :
      ∀ (n : ℤ) (Y : TopCat.{u}) (S : Set Y),
        E n Y S ≃ₗ[ℤ] pairTheory.relativeCohomology n Y S)
    (X : TopCat.{u}) (A B : Set X)
    (hcover : A ∪ B = Set.univ)
    (hAopen : IsOpen A) (hBopen : IsOpen B)
    [ContractibleSpace A] [ContractibleSpace B]
    (x₀ : X) (hx₀ : x₀ ∈ A ∩ B)
    (XAuB : BasedSpace)
    (idAuB : ReducedQuotientIdentification pairTheory X (A ∪ B) XAuB)
    {n : ℤ} (hn : 0 < n) :
    Subsingleton (reducedCohomology E n XAuB) := sorry

/-- Problem 19.6.4. If `X = A ∪ B` with `A` and `B` contractible open subspaces and with a chosen
point `x₀ ∈ A ∩ B` used to view `X` as the based space `underTopOfPoint X x₀`, then the positive-
degree reduced cup product `reducedCohomologyCup E cupProduct (underTopOfPoint X x₀)` is zero,
for a chosen relative cup product compatible with the ambient Chapter 18 pair cohomology theory
used in the Mayer-Vietoris argument. -/
theorem reducedCohomology_cup_eq_zero_of_contractible_cover
    (E : ℤ → (Y : TopCat) → Set Y → Type v)
    [∀ n (Y : TopCat) (S : Set Y), AddCommGroup (E n Y S)]
    [∀ n (Y : TopCat) (S : Set Y), Module ℤ (E n Y S)]
    {π : Type u} [AddCommGroup π]
    (pairTheory : PairCohomologyTheory π)
    (pairTheoryComparison :
      ∀ (n : ℤ) (Y : TopCat.{u}) (S : Set Y),
        E n Y S ≃ₗ[ℤ] pairTheory.relativeCohomology n Y S)
    (theoryCup : PairCohomologyTheory.RelativeCupProductMap pairTheory)
    (cupProduct : RelativeCupProductMap E)
    (hCupTheory :
      relativeCupProductCompatibleWithPairTheory
        E pairTheory pairTheoryComparison theoryCup cupProduct)
    (X : TopCat.{u}) (A B : Set X)
    (hcover : A ∪ B = Set.univ)
    (hAopen : IsOpen A) (hBopen : IsOpen B)
    [ContractibleSpace A] [ContractibleSpace B]
    (x₀ : X) (hx₀ : x₀ ∈ A ∩ B)
    {p q : ℤ} (hp : 0 < p) (hq : 0 < q)
    (α : reducedCohomology E p (underTopOfPoint X x₀))
    (β : reducedCohomology E q (underTopOfPoint X x₀)) :
    reducedCohomologyCup E cupProduct (underTopOfPoint X x₀) p q
      (TensorProduct.tmul ℤ α β) = 0 := sorry

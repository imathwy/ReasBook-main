import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Definition_21_2_2

open AlgebraicTopology CategoryTheory
open ROrientedManifold
open scoped Manifold
open scoped TensorProduct

noncomputable section

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {K : Type} [TopologicalSpace K] {J : ModelWithCorners ℝ F K} [J.Boundaryless]
variable {n m : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable {N : Type} [TopologicalSpace N] [ChartedSpace K N] [CompactSpace N]
variable [Fact (Module.finrank ℝ E = n)]
variable [Fact (Module.finrank ℝ F = m)]

local instance finrankProdFact : Fact (Module.finrank ℝ (E × F) = n + m) :=
  ⟨by
    have hE : Module.finrank ℝ E = n := Fact.out
    have hF : Module.finrank ℝ F = m := Fact.out
    calc
      Module.finrank ℝ (E × F) = Module.finrank ℝ E + Module.finrank ℝ F :=
        Module.finrank_prod
      _ = n + m := by rw [hE, hF]⟩

namespace ROrientedManifold

/-- Source-facing predicate: the orientation `oProd` on `M × N` is the product orientation induced
from `oM` and `oN` when some chain-level product comparison induces a singular-homology cross
product carrying the tensor product of the canonical fundamental classes of the factors to the
canonical fundamental class of `oProd`.

Chapter 20 currently exposes the comparison datum through the owner
`integralSingularChainComplexProductComparison`, but does not yet export a distinguished global
choice of such a comparison. This predicate therefore keeps the source-facing orientation statement
while internalizing the supporting comparison datum as existential `Prop` content. -/
def IsProductOrientation
    (oM : ROrientedManifold ℤ I n M)
    (oN : ROrientedManifold ℤ J m N)
    (oProd : ROrientedManifold ℤ (ModelWithCorners.prod I J) (n + m) (M × N)) : Prop :=
  ∃ productComparison :
      integralSingularChainComplexProductComparison (TopCat.of M) (TopCat.of N),
    rSingularHomologyCrossProduct productComparison
        (canonicalRFundamentalClass oM ⊗ₜ[ℤ] canonicalRFundamentalClass oN) =
      canonicalRFundamentalClass oProd

theorem IsProductOrientation.of_eq
    {oM : ROrientedManifold ℤ I n M}
    {oN : ROrientedManifold ℤ J m N}
    {oProd : ROrientedManifold ℤ (ModelWithCorners.prod I J) (n + m) (M × N)}
    (productComparison :
      integralSingularChainComplexProductComparison (TopCat.of M) (TopCat.of N))
    (hproduct :
      rSingularHomologyCrossProduct productComparison
          (canonicalRFundamentalClass oM ⊗ₜ[ℤ] canonicalRFundamentalClass oN) =
        canonicalRFundamentalClass oProd) :
    oM.IsProductOrientation oN oProd :=
  ⟨productComparison, hproduct⟩

theorem IsProductOrientation.elim
    {oM : ROrientedManifold ℤ I n M}
    {oN : ROrientedManifold ℤ J m N}
    {oProd : ROrientedManifold ℤ (ModelWithCorners.prod I J) (n + m) (M × N)}
    (hoProd : oM.IsProductOrientation oN oProd)
    {P : Prop}
    (h :
      ∀ productComparison :
          integralSingularChainComplexProductComparison (TopCat.of M) (TopCat.of N),
        rSingularHomologyCrossProduct productComparison
            (canonicalRFundamentalClass oM ⊗ₜ[ℤ] canonicalRFundamentalClass oN) =
          canonicalRFundamentalClass oProd →
        P) :
    P := by
  rcases hoProd with ⟨productComparison, hproduct⟩
  exact h productComparison hproduct

theorem IsProductOrientation.exists_productComparison
    {oM : ROrientedManifold ℤ I n M}
    {oN : ROrientedManifold ℤ J m N}
    {oProd : ROrientedManifold ℤ (ModelWithCorners.prod I J) (n + m) (M × N)}
    (hoProd : oM.IsProductOrientation oN oProd) :
    ∃ productComparison :
        integralSingularChainComplexProductComparison (TopCat.of M) (TopCat.of N),
      rSingularHomologyCrossProduct productComparison
          (canonicalRFundamentalClass oM ⊗ₜ[ℤ] canonicalRFundamentalClass oN) =
        canonicalRFundamentalClass oProd :=
  hoProd

end ROrientedManifold

/-- Lemma 21.2.5. The index is multiplicative under products:
`I(M × N) = I(M) I(N)`.

The repository already exposes the product-side proof ingredients through the cellular
product-chain comparison of Theorem 13.4.1, the homology cross product from Construction 17.2.1,
and the Kunneth short exact sequence of Theorem 17.2.2. Since the current repository does not yet
export a distinguished Chapter 20 product comparison on integral singular chains, the source-facing
product-orientation content is recorded by the predicate `oM.IsProductOrientation oN oProd`,
asserting that some such comparison sends the tensor product of the canonical fundamental classes
of `oM` and `oN` to the canonical fundamental class of `oProd`. -/
theorem manifoldIndex_prod
    (oM : ROrientedManifold ℤ I n M)
    (oN : ROrientedManifold ℤ J m N)
    (oProd : ROrientedManifold ℤ (ModelWithCorners.prod I J) (n + m) (M × N))
    (hoProd : oM.IsProductOrientation oN oProd) :
    manifoldIndex oProd = manifoldIndex oM * manifoldIndex oN := sorry

end

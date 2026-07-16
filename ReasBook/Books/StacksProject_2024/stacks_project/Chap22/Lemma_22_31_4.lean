import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import StacksProject_2024.stacks_project.Chap19.HomComplexPrecomp
import StacksProject_2024.stacks_project.Chap22.Lemma_22_22_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomotopyCategory
open CochainComplex.HomComplex
open CochainComplex.HomComplex.CohomologyClass
open CategoryTheory.CochainComplex (homComplexPrecomp)

noncomputable section

universe u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [Ring R]

local notation "DGMod" => CochainComplex (ModuleCat R) ℤ
local notation "KQ" => HomotopyCategory.quotient (ModuleCat R) (up ℤ)

-- Semantic recall hits: `CategoryTheory.Abelian.Ext.homLinearEquiv`,
-- `CochainComplex.HomComplex.homologyAddEquiv`, and
-- `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`.  Local Chapter 22 precedent
-- represents DG modules by cochain complexes, so the checked surface below records the two
-- source proof steps: Hom-complex cohomology computes morphisms in the homotopy category, and
-- Lemma `22.22.3` transports those morphisms to the derived category after a K-injective
-- resolution.

variable (N I : DGMod) (n : ℤ)

/- Lemma 22.31.4 (1): for a differential graded `(A, B)`-bimodule `N`, the degree-`n`
cohomology of the Hom complex `Hom^•(N, I)` is the canonical Hom-complex bridge to shifted
morphisms out of `N` in the homotopy category, namely the direct composite
`(homologyAddEquiv N I n).trans homAddEquiv`. -/
#check (homologyAddEquiv N I n).trans homAddEquiv

/- Lemma 22.31.4 (2): the localization map from shifted morphisms in the homotopy category to the
corresponding derived-category morphisms is exactly the K-injective comparison map from
`Lemma_22_22_3`. -/
#check derivedHomEquivOfKInjectiveResolution

/-- Lemma 22.31.4 (3): the canonical Hom-complex cohomology bridge is functorial in `N` with
respect to precomposition. The map on cohomology is induced by
`homComplexPrecomp`, and the map on the shifted-Hom side is the
contravariant preadditive-coyoneda map induced by
`KQ.map f`, so the resulting naturality statement is a commutative square. -/
@[stacks 0CS5]
theorem homComplex_homologyAddEquiv_naturality_left
    {N N' I : DGMod} (f : N ⟶ N') (n : ℤ) :
    CommSq
      (HomologicalComplex.homologyMap (homComplexPrecomp f) n)
      (((homologyAddEquiv N' I n).trans homAddEquiv).toAddCommGrpIso.hom)
      (((homologyAddEquiv N I n).trans homAddEquiv).toAddCommGrpIso.hom)
      ((preadditiveCoyoneda.map (((KQ).map f).op)).app ((KQ).obj (I⟦n⟧))) := by
  sorry

end CochainComplex

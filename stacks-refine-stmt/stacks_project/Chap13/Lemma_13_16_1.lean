import Mathlib
import stacks_project.Chap13.Lemma_13_14_3
import stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "Q" => HomotopyCategory.quotient 𝒜 (up ℤ)
local notation "H" => DerivedCategory.homologyFunctor ℬ

/- Domain-style sampling:
- primary domain: pointwise right derived functors on homotopy categories together with the
  canonical t-structure boundedness predicates on cochain complexes and derived categories;
- sampled owner declarations:
  `CategoryTheory.rightDerivedValue`,
  `CategoryTheory.rightDerivedValueMap`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `CochainComplex.isGE_iff`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`;
- owner abstraction:
  `source-facing`: the three lemmas about derived boundedness and truncation;
  `core/canonical`: `rightDerivedValue`, `rightDerivedValueMap`, and `IsGE`;
  `bridge/view`: the cohomology-vanishing reformulation below. -/

-- Proof sketch: replace `K` by a bounded-below complex quasi-isomorphic to it using
-- Lemma 13.15.5, observe that applying `F` termwise to such a bounded-below representative stays
-- zero in degrees below `a`, and use the cofinality description of the pointwise right derived
-- value to conclude the same vanishing for `RF(K)`.
/-- Lemma 13.16.1 (1): if a cochain complex `K` is bounded below by `a` in the canonical
cohomological sense and the right derived functor of `K(\mathcal A) ⥤ D(\mathcal B)` induced by
`F` is defined at `K`, then `RF(K)` is bounded below by the same integer `a`. -/
theorem rightDerivedValue_isGE_of_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (hGE : K.IsGE a)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)] :
    (rightDerivedValue Qis KtoD ((Q).obj K)).IsGE a := sorry

/-- Companion to Lemma 13.16.1 (1): the canonical bounded-below conclusion implies the textbook
degreewise vanishing statement for cohomology in every degree `< a`. -/
theorem rightDerivedValue_isZero_homology_below_of_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (hGE : K.IsGE a)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)]
    (i : ℤ) (hi : i < a) :
    IsZero ((H i).obj (rightDerivedValue Qis KtoD ((Q).obj K))) := sorry

-- Proof sketch: compare `K.truncLE a`, `K`, and `K.truncGE (a + 1)` by the standard truncation
-- triangle, transport pointwise right-derived existence across that triangle, and then use the
-- long exact cohomology sequence together with part (1) applied to `K.truncGE (a + 1)`.
/-- Lemma 13.16.1 (2): if the right derived functor induced by `F` is defined at `K` and at
`τ_{\le a}K`, then the canonical map `RF(τ_{\le a}K) ⟶ RF(K)` induces an isomorphism on
cohomology in every degree `i ≤ a`. -/
theorem rightDerivedValue_homologyMap_isIso_of_truncLE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)]
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj (K.truncLE a))]
    (i : ℤ) (hi : i ≤ a) :
    IsIso
      ((H i).map (rightDerivedValueMap Qis KtoD ((Q).map (K.ιTruncLE a)))) := sorry

end

end CategoryTheory

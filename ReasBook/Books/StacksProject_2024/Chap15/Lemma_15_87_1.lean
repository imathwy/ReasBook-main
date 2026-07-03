import Mathlib
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap13.Lemma_13_32_2
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap19.Proposition_19_6_1
import StacksProject_2024.Chap15.«15_87_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

local notation "Ab" => AddCommGrpCat
local notation "AbSeq" => SequentialInverseSystem Ab
local notation "Qish" => HomotopyCategory.quasiIso AbSeq (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived (lim : AbSeq ⥤ Ab)
local notation "RightAcyclic" =>
  IsRightAcyclicForAdditiveFunctor (lim : AbSeq ⥤ Ab)

-- Proof sketch: apply the explicit embedding of an arbitrary inverse system into a
-- Mittag-Leffler inverse system from the Stacks Project argument, and use the preceding
-- Mittag-Leffler acyclicity statement to see that the target of that monomorphism is right
-- acyclic for `lim`.
/-- The Chapter `13` right-acyclicity owner for inverse limit on sequential inverse systems of
abelian groups has monomorphic envelopes. -/
instance abelianGroupLimit_rightAcyclic_hasMonoEmbedding :
    HasMonoEmbedding RightAcyclic where
  exists_mono A := by
    sorry

-- Proof sketch: this is the Stacks Project vanishing statement `R^p lim = 0` for `p > 1`,
-- expressed as vanishing of the positive cohomology of `R lim(A[0])`.
/-- For an inverse system of abelian groups, the cohomology objects `H^p(R lim(A[0]))` vanish in
degrees strictly greater than `1`. -/
theorem abelianGroupInverseLimit_rightDerived_isZero_of_one_lt
    (A : AbSeq) (p : ℕ) (hp : 1 < p) :
    IsZero (R^p lim((DerivedCategory.singleFunctor AbSeq 0).obj A)) :=
  sorry

-- Proof sketch: the Stacks Project identifies the degree-zero object `A[0]` in the derived
-- category with the standard Milnor triangle built from the two products `∏ A_n` and the
-- difference map `(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))`.
/-- Applying `R lim` to an inverse system of abelian groups viewed in degree `0` yields the
standard derived-limit object characterized by the Milnor triangle, equivalently by the two-term
complex `\prod A_n \to \prod A_n` in degrees `0` and `1`. -/
theorem abelianGroupDerivedInverseLimit_isDerivedLimit_of_inverseSystem
    (A : AbSeq) :
    CategoryTheory.IsDerivedLimit
      (A ⋙ DerivedCategory.singleFunctor Ab 0)
      (R lim((DerivedCategory.singleFunctor AbSeq 0).obj A)) :=
  sorry

-- Proof sketch: for a Mittag-Leffler inverse system, the Stacks Project identifies the
-- obstruction group `R^1 lim` with zero; the higher derived functors already vanish above degree
-- `1`, so all positive right-derived functors vanish and the system is right acyclic for `lim`.
/-- A Mittag-Leffler inverse system of abelian groups is right acyclic for inverse limit. -/
theorem abelianGroupLimit_rightAcyclic_of_isMittagLeffler
    (A : AbSeq) (hA : SequentialInverseSystem.IsMittagLeffler A) :
    RightAcyclic A := sorry

-- Proof sketch: specialize Lemma 13.32.2 to the inverse-limit functor, using the preceding
-- `HasMonoEmbedding RightAcyclic` instance together with the vanishing of `R^2 lim`.
/-- Every cochain complex of inverse systems of abelian groups is quasi-isomorphic to one whose
terms are right acyclic for inverse limit. -/
theorem exists_quasiIso_to_termwise_abelianGroupLimit_rightAcyclic
    (K : CochainComplex AbSeq ℤ) :
    ∃ (L : CochainComplex AbSeq ℤ) (α : K ⟶ L), QuasiIso α ∧ ∀ i : ℤ, RightAcyclic (L.X i) :=
  sorry

-- Proof sketch: this is Lemma 13.32.2 specialized to the inverse-limit functor. Once each term
-- `K.X i` is right acyclic for `lim`, the ordinary termwise inverse-limit complex computes the
-- chosen derived inverse limit in the canonical Chapter 13 sense
-- `Functor.ComputesRightDerivedAt`.
/-- Lemma 15.87.1: if each degree `K^p = (K_n^p)` of a cochain complex of inverse systems of
abelian groups is right acyclic for inverse limit, then the homotopy-category class of `K`
computes `R lim(K)`, formalized by the canonical Chapter `13` owner
`Functor.ComputesRightDerivedAt` for `mapHomotopyCategoryToDerived`. Equivalently, the canonical
comparison map from the ordinary termwise inverse-limit complex to the chosen derived inverse
limit is an isomorphism, so `R lim(K)` is represented by the complex whose degree-`p` term is
`\varprojlim_n K_n^p`. -/
theorem abelianGroupDerivedInverseLimit_computes_of_termwise_rightAcyclic
    (K : CochainComplex AbSeq ℤ) (hK : ∀ i : ℤ, RightAcyclic (K.X i)) :
    Functor.ComputesRightDerivedAt KtoD Qish
      ((HomotopyCategory.quotient AbSeq (up ℤ)).obj K) :=
  sorry

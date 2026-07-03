import Mathlib
import stacks_project.Chap13.Definition_13_18_1
import stacks_project.Chap13.Lemma_13_14_15
import stacks_project.Chap13.Lemma_13_15_2
import stacks_project.Chap13.Definition_13_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜]
  [Category.{v₂} 𝒟]

variable (F : K⁺(𝒜) ⥤ 𝒟)

/- Domain-style sampling for Lemma 13.20.1:
- primary domain: bounded-below injective cochain complexes and right-derived computation /
  acyclicity for additive functors on bounded-below and unbounded homotopy categories;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.PlusWithTermsIn.instIsKInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `Functor.ComputesRightDerivedAt`,
  `computes_right_derived_functor_at_iff_bounded_below`;
- best owner abstraction: part `(1)` is source-facing at the chapter owner
  `CochainComplex.InjectivePlus 𝒜`, with computation exported through the canonical owner
  `Functor.ComputesRightDerivedAt`; part `(2)` is the degree-zero specialization to the Chapter 13
  owner `IsRightAcyclicForAdditiveFunctor`;
- primitive data: a bounded-below injective complex `I : CochainComplex.InjectivePlus 𝒜`, or an
  injective object `I : 𝒜`;
- derived API: the computation statement at `((HomotopyCategory.Plus.quotient 𝒜).obj I)` and the
  right-acyclicity statement
  for `I`.

Source/core/bridge triage:
- `source-facing`: the two textbook statements below;
- `core/canonical`: `CochainComplex.InjectivePlus 𝒜`,
  `Functor.ComputesRightDerivedAt`, and `IsRightAcyclicForAdditiveFunctor`;
- `bridge/view`: the canonical K-injective bridge
  `CochainComplex.PlusWithTermsIn.instIsKInjective`, the hom-bijection theorem
  `CochainComplex.IsKInjective.Qh_map_bijective`, and the bounded/unbounded comparison theorem
  `computes_right_derived_functor_at_iff_bounded_below`.
-/

-- Proof sketch: the owner `CochainComplex.InjectivePlus 𝒜` carries the canonical K-injective
-- structure from `CochainComplex.PlusWithTermsIn.instIsKInjective`. Hence the pointwise
-- costructured-arrow diagram over `((HomotopyCategory.Plus.quotient 𝒜).obj I)` is already
-- controlled by the hom-bijection theorem `CochainComplex.IsKInjective.Qh_map_bijective`, so the
-- identity denominator witnesses that `I` computes the right derived functor.
/-- Lemma 13.20.1 (1): a bounded-below cochain complex of injective objects in an abelian
category computes the right derived functor of any functor
`F : K^+(\mathcal A) ⥤ \mathcal D` with respect to quasi-isomorphisms. -/
theorem boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
    (I : CochainComplex.InjectivePlus 𝒜) :
    F.ComputesRightDerivedAt (Qis⁺(𝒜)) ((HomotopyCategory.Plus.quotient 𝒜).obj I) := sorry

end

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

-- Proof sketch: package the degree-zero complex `I[0]` as an object of
-- `CochainComplex.InjectivePlus 𝒜` using the injectivity of `I`, then apply part (1). Use
-- `computes_right_derived_functor_at_iff_bounded_below` to pass from the bounded-below
-- computation to the unbounded pointwise one, then conclude with the Chapter 13 source-facing owner
-- `IsRightAcyclicForAdditiveFunctor`.
/-- Lemma 13.20.1 (2): every injective object of an abelian category is right acyclic for any
additive functor to an abelian category. -/
theorem injective_isRightAcyclicForAdditiveFunctor
    (I : 𝒜) [Injective I] :
    IsRightAcyclicForAdditiveFunctor F I := sorry

end

end CategoryTheory

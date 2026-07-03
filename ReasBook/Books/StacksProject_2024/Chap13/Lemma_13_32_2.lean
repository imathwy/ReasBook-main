import Mathlib
import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Lemma_13_15_5
import StacksProject_2024.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "RightAcyclic" => (fun A : 𝒜 ↦ IsRightAcyclicForAdditiveFunctor F A)

/- Domain-style sampling for Lemma 13.32.2:
- primary domain: unbounded right derived functors of additive functors, right-acyclic objects,
  and derived-category truncation maps;
- sampled owner declarations:
  `IsRightAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasMonoEmbedding`,
  `Functor.HasRightDerivedFunctor`,
  `Functor.totalRightDerived`;
- best owner abstraction: `IsRightAcyclicForAdditiveFunctor F` is the source-facing acyclicity
  owner, and the canonical mono-into-acyclic hypothesis is
  `ObjectProperty.HasMonoEmbedding RightAcyclic`;
- primitive data: the acyclicity object property, the mono-embedding owner for that property, and
  the vanishing hypothesis on `F.rightDerived n` when higher derived functors appear explicitly;
- derived API: existence/computation of the unbounded right derived functor and the truncation
  isomorphism statements below.

Source/core/bridge triage:
- `source-facing`: the six theorems in this file;
- `core/canonical`: `IsRightAcyclicForAdditiveFunctor`, `ObjectProperty.HasMonoEmbedding`,
  `Functor.HasRightDerivedFunctor`, and `Functor.totalRightDerived`;
- `bridge/view`: the truncation morphisms in `DerivedCategory.TStructure`, which remain companions
  to the unbounded right-derived owner rather than a second owner abstraction.
-/

section

variable (n : ℕ)
  [HasMonoEmbedding (fun A : 𝒜 ↦ IsRightAcyclicForAdditiveFunctor F A)]
  [HasInjectiveResolutions 𝒜]
  (hn : ∀ A : 𝒜, IsZero ((F.rightDerived n).obj A))

-- Proof sketch: first use the mono-embedding hypothesis together with the vanishing
-- `R^n F = 0` to deduce by dimension shifting that all higher `R^m F` vanish for `m ≥ n`.
-- Then apply the cofinality criterion of Lemma 13.14.15 to the full subcategory of complexes
-- whose terms satisfy `IsRightAcyclicForAdditiveFunctor`.
/-- Lemma 13.32.2 (1): if the Chapter 13 right-acyclicity owner
`IsRightAcyclicForAdditiveFunctor F` has monomorphic envelopes, formalized by
`ObjectProperty.HasMonoEmbedding (IsRightAcyclicForAdditiveFunctor F)`, and if
`R^nF = 0` for some `n ≥ 0`, then the unbounded right derived functor
`RF : D(\mathcal A) ⥤ D(\mathcal B)` exists. -/
theorem has_unbounded_rightDerivedFunctor_of_mono_into_higherRightDerivedVanishes :
    Functor.HasRightDerivedFunctor KtoD Qis := sorry

-- Proof sketch: replace the given complex by itself in the denominator diagram defining `RF`.
-- Since every term is right acyclic, the Leray acyclicity argument shows that applying `F`
-- termwise already computes the derived value, so the canonical unit is an isomorphism.
/-- Lemma 13.32.2 (2): after choosing the unbounded right derived functor from part (1), any
cochain complex whose terms are right acyclic for `F`, formalized by
`IsRightAcyclicForAdditiveFunctor`, computes `RF`. -/
theorem computes_unbounded_rightDerived_of_termwise_higherRightDerivedVanishes
    [Functor.HasRightDerivedFunctor KtoD Qis]
    (K : CochainComplex 𝒜 ℤ)
    (hK : ∀ i : ℤ, RightAcyclic (K.X i)) :
    Functor.ComputesRightDerivedAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := sorry

-- Proof sketch: apply Lemma 13.32.1 to the cohomological-dimension function
-- `A ↦ max ({0} ∪ { i | R^i F(A) ≠ 0 })`, whose finiteness follows from the assumed vanishing
-- of `R^n F`, and whose zero locus is exactly the class of right-acyclic objects.
/-- Lemma 13.32.2 (3): every cochain complex in `𝒜` admits a quasi-isomorphism into a complex all
of whose terms are right acyclic for `F`, expressed by
`IsRightAcyclicForAdditiveFunctor`. -/
theorem exists_quasiIso_to_termwise_higherRightDerivedVanishes
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : K ⟶ L), QuasiIso α ∧
      ∀ i : ℤ, RightAcyclic (L.X i) := sorry

end

variable [HasDerivedCategory.{w} 𝒜]

-- Proof sketch: apply Lemma 13.16.1 to the truncation triangle for a chosen cochain-complex
-- representative of `E`; the quotient complex has no cohomology in degrees `≤ a`, so `RF`
-- induces an isomorphism on cohomology in those degrees.
/-- Lemma 13.32.2 (4a): for `E ∈ D(\mathcal A)`, the canonical morphism
`RF(τ_{\le a} E) ⟶ RF(E)` induces an isomorphism on `H^i` for every `i ≤ a`. -/
theorem homologyMap_unboundedRightDerived_isIso_of_derivedTruncLE
    [Functor.HasRightDerivedFunctor KtoD Qis]
    (E : DerivedCategory 𝒜) (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((DerivedCategory.homologyFunctor ℬ i).map
        ((Functor.totalRightDerived KtoD Qh Qis).map ((t.truncLEι a).app E))) := sorry

-- Proof sketch: first replace `E` by a quasi-isomorphic complex of right-acyclic objects using
-- part (3). The second spectral sequence for that complex, together with the vanishing
-- `R^n F = 0` and hence `R^m F = 0` for all `m ≥ n`, shows that truncating below degree
-- `b - n + 1` does not affect cohomology in degrees `≥ b`.
/-- Lemma 13.32.2 (4b): assuming the hypotheses of parts (1) and (3), for `E ∈ D(\mathcal A)`
the canonical morphism `RF(E) ⟶ RF(τ_{\ge b - n + 1} E)` induces an isomorphism on `H^i` for
every `i ≥ b`. -/
theorem homologyMap_unboundedRightDerived_isIso_of_derivedTruncGE
    [Functor.HasRightDerivedFunctor KtoD Qis]
    (n : ℕ)
    [HasMonoEmbedding RightAcyclic]
    [HasInjectiveResolutions 𝒜]
    (hn : ∀ A : 𝒜, IsZero ((F.rightDerived n).obj A))
    (E : DerivedCategory 𝒜) (b i : ℤ) (hi : b ≤ i) :
    IsIso
      ((DerivedCategory.homologyFunctor ℬ i).map
        ((Functor.totalRightDerived KtoD Qh Qis).map
          ((t.truncGEπ (b - (n : ℤ) + 1)).app E))) := sorry

-- Proof sketch: combine part (4a) on the left with part (4b) on the right. If `E` has no
-- cohomology outside `[a, b]`, then `τ_{\le a - 1} E = 0` and `τ_{\ge b + 1} E = 0`, so the two
-- truncation isomorphisms force `RF(E)` to have no cohomology outside `[a, b + n - 1]`.
/-- Lemma 13.32.2 (4c): assuming the hypotheses of parts (1) and (3), if
`H^i(E) = 0` for `i ∉ [a, b]`, then `H^i(RF(E)) = 0` for `i ∉ [a, b + n - 1]`. -/
theorem unboundedRightDerivedVanishesOutside_shifted_range
    [Functor.HasRightDerivedFunctor KtoD Qis]
    (n : ℕ)
    [HasMonoEmbedding RightAcyclic]
    [HasInjectiveResolutions 𝒜]
    (hn : ∀ A : 𝒜, IsZero ((F.rightDerived n).obj A))
    (E : DerivedCategory 𝒜) (a b : ℤ)
    (hGE : E.IsGE a) (hLE : E.IsLE b) :
    ((Functor.totalRightDerived KtoD Qh Qis).obj E).IsGE a ∧
      ((Functor.totalRightDerived KtoD Qh Qis).obj E).IsLE (b + (n : ℤ) - 1) := sorry

end

end CategoryTheory

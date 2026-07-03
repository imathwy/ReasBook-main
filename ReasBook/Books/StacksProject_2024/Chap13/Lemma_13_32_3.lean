import Mathlib
import StacksProject_2024.Chap12.Definition_12_5_3
import StacksProject_2024.Chap13.Definition_13_15_3
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
local notation "LeftAcyclic" => IsLeftAcyclicForAdditiveFunctor F

/- Domain-style sampling for Lemma 13.32.3:
- primary domain: unbounded left derived functors of additive functors, left-acyclic objects, and
  derived-category truncation maps;
- sampled owner declarations:
  `IsLeftAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasEpiCover`,
  `Functor.HasLeftDerivedFunctor`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.totalLeftDerived`,
  `H^i`;
- best owner abstraction: `LeftAcyclic` is the source-facing acyclicity owner, and the canonical
  quotient-generating hypothesis is `HasEpiCover LeftAcyclic`;
- primitive data: the acyclicity object property, the epi-cover owner for that property, and the
  vanishing hypothesis on `F.leftDerived n` when higher derived functors appear explicitly;
- derived API: `(mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis`,
  `(mapHomotopyCategoryToDerived F).ComputesLeftDerivedAt Qis`, the total-derived owner
  `(mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis`, and the truncation-isomorphism
  statements below expressed on cohomology via `(H^i)`.

Source/core/bridge triage:
- `source-facing`: the six theorems in this file;
- `core/canonical`: `IsLeftAcyclicForAdditiveFunctor`, `ObjectProperty.HasEpiCover`,
  `Functor.HasLeftDerivedFunctor`, `Functor.ComputesLeftDerivedAt`, `Functor.totalLeftDerived`,
  and `H^i`;
- `bridge/view`: the truncation morphisms in `DerivedCategory.TStructure`, which remain companions
  to the unbounded left-derived owner rather than a second owner abstraction.
-/

section

variable (n : ℕ)
  [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
  [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
  (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))

-- Proof sketch: use the epi-cover hypothesis and the vanishing `L^n F = 0` to dimension-shift
-- higher left derived functors to zero, then apply the dual cofinality criterion to left-acyclic
-- complexes in the homotopy category.
/-- Lemma 13.32.3 (1): if every object of `𝒜` is a quotient of an object that is left acyclic for
the right exact functor `F`, formalized here by the canonical owner
`HasEpiCover LeftAcyclic`, and if
`L^n F = 0` for some `n ≥ 0`, then the unbounded left derived functor exists. -/
theorem has_unbounded_leftDerivedFunctor_of_epi_from_higherLeftDerivedVanishes
    :
    (mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis := sorry

end

-- Proof sketch: a complex of left-acyclic objects already computes the derived value because
-- termwise application of `F` is a left-derived model on such complexes, so the canonical counit
-- comparison is an isomorphism.
/-- Lemma 13.32.3 (2): after choosing the unbounded left derived functor from part (1), any
cochain complex whose terms are left acyclic for `F`, formalized by
`IsLeftAcyclicForAdditiveFunctor`, computes `LF`. -/
theorem computes_unbounded_leftDerived_of_termwise_higherLeftDerivedVanishes
    [(mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis]
    (K : CochainComplex 𝒜 ℤ)
    (hK : ∀ i : ℤ, LeftAcyclic (K.X i)) :
    (mapHomotopyCategoryToDerived F).ComputesLeftDerivedAt Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := sorry

section

variable (n : ℕ)
  [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
  [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
  (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))

-- Proof sketch: construct a quasi-isomorphic replacement by resolving each term by a left-acyclic
-- epi-cover, arranged compatibly with the differentials; the resulting complex maps by a
-- quasi-isomorphism to the original one.
/-- Lemma 13.32.3 (3): every cochain complex in `𝒜` is the target of a quasi-isomorphism from a
cochain complex all of whose terms are left acyclic for `F`, expressed by the canonical owner
`IsLeftAcyclicForAdditiveFunctor`. -/
theorem exists_quasiIso_from_termwise_higherLeftDerivedVanishes
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : L ⟶ K), QuasiIso α ∧
      ∀ i : ℤ, LeftAcyclic (L.X i) := sorry

end

variable [HasDerivedCategory.{w} 𝒜]

-- Proof sketch: first replace `E` by a quasi-isomorphic complex of left-acyclic objects using
-- part (3). The dual spectral-sequence argument shows that truncating above degree `a + n - 1`
-- does not affect the cohomology of `LF(E)` in degrees `≤ a`.
/-- Lemma 13.32.3 (4): assuming the hypotheses of parts (1) and (3), for `E ∈ D(\mathcal A)`
the canonical morphism `LF(τ_{\le a + n - 1} E) ⟶ LF(E)` induces an isomorphism on `H^i` for
every `i ≤ a`. -/
theorem homologyMap_unboundedLeftDerived_isIso_of_derivedTruncLE
    (n : ℕ)
    [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
    [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
    (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))
    (E : DerivedCategory 𝒜) (a i : ℤ) (hi : i ≤ a) :
    let _ : (mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis :=
      has_unbounded_leftDerivedFunctor_of_epi_from_higherLeftDerivedVanishes F
    IsIso
      ((H^i).map
        (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).map
          ((t.truncLEι (a + (n : ℤ) - 1)).app E))) := sorry

-- Proof sketch: apply the left-derived functor to the truncation triangle for a cochain-complex
-- representative of `E`; the quotient complex has no cohomology in degrees `≥ b`, so `LF`
-- preserves cohomology in those degrees.
/-- Lemma 13.32.3 (5): for `E ∈ D(\mathcal A)`, the canonical morphism
`LF(E) ⟶ LF(τ_{\ge b} E)` induces an isomorphism on `H^i` for every `i ≥ b`. -/
theorem homologyMap_unboundedLeftDerived_isIso_of_derivedTruncGE
    [(mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis]
    (E : DerivedCategory 𝒜) (b i : ℤ) (hi : b ≤ i) :
    IsIso
      ((H^i).map
        (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).map
          ((t.truncGEπ b).app E))) := sorry

-- Proof sketch: combine part (4) on the left with part (5) on the right. If `E` has no
-- cohomology outside `[a, b]`, then the truncation isomorphisms identify `LF(E)` with an object
-- whose cohomology is forced to vanish outside `[a - n + 1, b]`.
/-- Lemma 13.32.3 (6): assuming the hypotheses of parts (1) and (3), if
`H^i(E) = 0` for `i ∉ [a, b]`, then `H^i(LF(E)) = 0` for `i ∉ [a - n + 1, b]`. -/
theorem unboundedLeftDerivedVanishesOutside_shifted_range
    (n : ℕ)
    [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
    [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
    (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))
    (E : DerivedCategory 𝒜) (a b : ℤ)
    (hGE : E.IsGE a) (hLE : E.IsLE b) :
    let _ : (mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis :=
      has_unbounded_leftDerivedFunctor_of_epi_from_higherLeftDerivedVanishes F
    (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).obj E).IsGE
      (a - (n : ℤ) + 1) ∧
      (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).obj E).IsLE b := sorry

end

end CategoryTheory

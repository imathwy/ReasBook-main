import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_32_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open HomologicalComplex
open scoped ZeroObject

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.32.1:
- primary domain: cohomological-dimension functions controlling object-property replacements of
  cochain complexes in an abelian category;
- sampled owner declarations:
  `ObjectProperty.ContainsZero`,
  `ObjectProperty.HasMonoEmbedding`,
  `exists_quasiIso_with_terms_in_of_isZero_homology_below`;
- best owner abstraction: the categorical owner is the zero-locus object property
  `fun X ↦ d X = 0`, viewed through the canonical owners `ObjectProperty.ContainsZero` and
  `ObjectProperty.HasMonoEmbedding`; the source-facing public statements should still speak
  directly about the numerical condition `d X = 0`;
- primitive data: the source-facing zero-object equality `d 0 = 0`, the zero-locus
  mono-embedding owner, and the two numerical inequalities on biproducts and short exact
  sequences;
- derived API: the constant-zero example, the shifted-tail condition on cochain complexes, and the
  final quasi-isomorphic replacement theorem with termwise conclusion `d (L.X n) = 0`.

Source/core/bridge triage:
- `source-facing`: `IsCohomologicalDimensionFunction`,
  `ShiftedDimensionTendsToNegInf`, and the quasi-isomorphic replacement theorem;
- `core/canonical`: `ObjectProperty.ContainsZero`, `ObjectProperty.HasMonoEmbedding`,
  `ShortComplex.ShortExact`, and `QuasiIso`;
- `bridge/view`: the internal zero-locus object property `fun X ↦ d X = 0`, used only where
  `ObjectProperty`-based replacement owners are required.
-/

/-- A cohomological-dimension function on an abelian category is a function to `WithTop ℕ` whose
value on the zero object is zero, whose zero locus, viewed as an object property, has monomorphic
envelopes for all objects, whose value on biproducts is bounded by the maximum of the summand
values, and whose value on the cokernel term of a short exact sequence is bounded by the maximum
of the middle value and one less than the left value. -/
class IsCohomologicalDimensionFunction (d : 𝒜 → WithTop ℕ) : Prop where
  zero_eq : d (0 : 𝒜) = 0
  hasMonoEmbedding : HasMonoEmbedding (fun X ↦ d X = 0)
  biprod_le_max (X Y : 𝒜) : d (X ⊞ Y) ≤ max (d X) (d Y)
  shortExact_right_le_max {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)

attribute [instance] IsCohomologicalDimensionFunction.hasMonoEmbedding

namespace IsCohomologicalDimensionFunction

variable {d : 𝒜 → WithTop ℕ} [IsCohomologicalDimensionFunction d]

/-- The zero object is zero-dimensional for a cohomological-dimension function. -/
theorem prop_zero : d (0 : 𝒜) = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  exact hd.zero_eq

instance zeroLocus_containsZero : ContainsZero (fun X : 𝒜 ↦ d X = 0) where
  exists_zero := ⟨0, isZero_zero 𝒜, prop_zero⟩

/-- The zero-dimensional objects for a cohomological-dimension function are closed under binary
biproducts. -/
theorem prop_biprod {X Y : 𝒜} (hX : d X = 0) (hY : d Y = 0) :
    d (X ⊞ Y) = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  change d (X ⊞ Y) = 0
  refine le_antisymm ?_ bot_le
  simpa [hX, hY] using hd.biprod_le_max X Y

/-- If the left and middle terms of a short exact sequence are zero-dimensional, then so is the
right term. -/
theorem prop_X₃_of_shortExact {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : d S.X₁ = 0) (h₂ : d S.X₂ = 0) :
    d S.X₃ = 0 := by
  let hd : IsCohomologicalDimensionFunction d := inferInstance
  change d S.X₃ = 0
  refine le_antisymm ?_ bot_le
  simpa [h₁, h₂] using hd.shortExact_right_le_max hS

end IsCohomologicalDimensionFunction

/-- The constant-zero function is a cohomological-dimension function. -/
instance instIsCohomologicalDimensionFunctionZero :
    IsCohomologicalDimensionFunction (fun _ : 𝒜 ↦ (0 : WithTop ℕ)) where
  zero_eq := by
    simp
  hasMonoEmbedding := by
    refine ⟨fun X ↦ ?_⟩
    exact ⟨X, by simp, 𝟙 X, inferInstance⟩
  biprod_le_max X Y := by
    simp
  shortExact_right_le_max hS := by
    simp

/-- The shifted dimension function `n + d (K.X n)` tends to `-∞` toward negative degrees when,
for every bound `N`, all sufficiently negative terms have finite `d`-value bounded so that
`n + d (K.X n) ≤ N`. -/
def ShiftedDimensionTendsToNegInf
    (d : 𝒜 → WithTop ℕ) (K : CochainComplex 𝒜 ℤ) : Prop :=
  ∀ N : ℤ, ∃ n₀ : ℤ, ∀ n ≤ n₀, ∃ m : ℕ, d (K.X n) = m ∧ n + m ≤ N

-- Proof sketch: first use Lemma 13.15.5 to replace the high-degree tail of `K` by a
-- quasi-isomorphic bounded-below complex of `d = 0` objects. Then perform the textbook elementary
-- replacements in finitely many degrees at a time, using the monomorphic envelope axiom and the
-- short-exact-sequence inequality to decrease the quantity `n + d(K.X n)` until every term has
-- dimension zero.
/-- Lemma 13.32.1: if `d` is a cohomological-dimension function on an abelian category and
`n + d(K.X n)` tends to `-∞` as `n → -∞` in the sense that for every integer bound `N` there is a
lower cutoff below which each `d(K.X n)` is finite and satisfies `n + d(K.X n) ≤ N`, then `K` is
quasi-isomorphic to a cochain complex all of whose terms have `d = 0`. -/
theorem exists_quasiIso_to_termwise_zero_dimension_of_tendsToNegInf_shifted_dimension
    (d : 𝒜 → WithTop ℕ) [IsCohomologicalDimensionFunction d] (K : CochainComplex 𝒜 ℤ)
    (hK : ShiftedDimensionTendsToNegInf d K) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : K ⟶ L), QuasiIso α ∧
      ∀ n : ℤ, d (L.X n) = 0 := sorry

end

/-! ### Lemma_13_32_2 (from Chap13) -/
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

/-! ### Lemma_13_32_3 (from Chap13) -/
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

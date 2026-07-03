import Mathlib
import StacksProject_2024.Chap12.Definition_12_5_3
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Lemma_13_14_15
import StacksProject_2024.Chap13.Lemma_13_15_2
import StacksProject_2024.Chap13.Lemma_13_15_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open Limits
open ComplexShape
open scoped CategoryTheory ZeroObject

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "QisMinus" => boundedAboveHomotopyQuasiIso 𝒜
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F
local notation "single0" => HomotopyCategory.singleFunctor 𝒜 0

/- 
Domain-style sampling for Lemma 13.15.7:
- primary domain: unbounded left-derived acyclicity obtained from bounded-above resolutions by a
  chosen object property `P`;
- sampled owner declarations:
  `ObjectProperty.HasEpiCover`,
  `ObjectProperty.IsClosedUnderSubobjects`,
  `ObjectProperty.prop_X₁_of_shortExact`,
  `Functor.ComputesLeftDerivedAt`,
  `IsLeftAcyclicForAdditiveFunctor`,
  `computesLeftDerivedAt_of_mem_subset` and
  `computes_left_derived_functor_at_iff_bounded_above` from Lemmas `13.14.15` and `13.15.2`;
- best owner abstraction: the source-facing data here is the object property `P` together with the
  quotient-generating hypothesis, the canonical subobject-closure owner for `P`, and the
  short-exact-sequence exactness hypothesis on objects of `P`;
  the target acyclicity notion is the chapter owner `IsLeftAcyclicForAdditiveFunctor`;
- primitive data: `P`, the epi-cover owner for `P`, the canonical subobject-closure owner
  `[P.IsClosedUnderSubobjects]`, and the hypothesis that `F` preserves short exactness on short
  exact sequences whose middle and right terms lie in `P`;
- derived API: the acyclicity statement for the degree-zero object `A[0]` in `K(\mathcal A)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, specialized to objects `A ∈ P`;
- `core/canonical`: `ObjectProperty.HasEpiCover`, `ObjectProperty.IsClosedUnderSubobjects`,
  `Functor.ComputesLeftDerivedAt`, `computesLeftDerivedAt_of_mem_subset`, and
  `IsLeftAcyclicForAdditiveFunctor`;
- `bridge/view`: this theorem, which turns the source-facing object-property hypotheses into the
  canonical unbounded left-acyclicity owner.
-/

private instance containsZero_of_hasEpiCover_and_isClosedUnderSubobjects
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects] :
    P.ContainsZero where
  exists_zero := by
    obtain ⟨Y, hY, _, _⟩ := (inferInstance : P.HasEpiCover).exists_epi (0 : 𝒜)
    exact ⟨(0 : 𝒜), isZero_zero 𝒜, P.prop_of_mono (0 : (0 : 𝒜) ⟶ Y) hY⟩

-- Proof sketch: dualize Lemma 13.15.6. Use quotient resolutions by objects of `P` to replace
-- bounded-above complexes by quasi-isomorphic complexes whose terms lie in `P`; the closure and
-- exactness hypotheses imply that applying `F` preserves exactness on those resolutions. This
-- first yields the bounded-above owner-level acyclicity statement.
/-- If every object of `𝒜` is a quotient of an object of `P`, `P` is closed under subobjects, and
`F` preserves short exactness on short exact sequences whose middle and right terms lie in `P`,
then every object `A ∈ P` is acyclic for the bounded-above left derived functor of `F`. -/
theorem isBoundedAboveLeftAcyclicForAdditiveFunctor_of_mem
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    IsBoundedAboveLeftAcyclicForAdditiveFunctor F A := by
  let _ : MorphismProperty.IsSaturatedMultiplicativeSystem QisMinus := by
    sorry
  let Pminus : ObjectProperty (K⁻(𝒜)) := fun X ↦
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    ∀ n : ℤ, P (K.X n)
  have hP_reaches :
      ∀ X : K⁻(𝒜), ∃ (X' : K⁻(𝒜)) (s : X' ⟶ X), Pminus X' ∧ QisMinus s := by
    intro X
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    obtain ⟨a, hX⟩ := (CochainComplex.minus_iff 𝒜 K).1 X.property
    obtain ⟨Q, α, hα⟩ :=
      exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE P a K hX
    let Xc : Comp⁻(𝒜) := ⟨K, X.property⟩
    have hXeq : (HomotopyCategory.Minus.quotient 𝒜).obj Xc = X := by
      cases X
      rfl
    let X' : K⁻(𝒜) := (HomotopyCategory.Minus.quotient 𝒜).obj (hα.toMinusWithTermsIn : Comp⁻(𝒜))
    let α' : (hα.toMinusWithTermsIn : Comp⁻(𝒜)) ⟶ Xc := ⟨α⟩
    let s : X' ⟶ X := by
      simpa [X', hXeq] using (HomotopyCategory.Minus.quotient 𝒜).map α'
    refine ⟨X', s, ?_, ?_⟩
    · intro n
      simpa [Pminus, X'] using hα.toMinusWithTermsIn.term_mem n
    · change HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map s)
      simpa [s, X', hXeq] using
        (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact hα.quasiIso)
  change Functor.ComputesLeftDerivedAt KminusToDminus QisMinus ((single0Minus 𝒜).obj A)
  have hP_isIso :
      ∀ {X X' : K⁻(𝒜)} (s : X ⟶ X'), Pminus X → Pminus X' → QisMinus s →
        IsIso ((mapBoundedAboveHomotopyCategoryToDerivedAbove F).map s) := by
    sorry
  have hsingle : Pminus ((single0Minus 𝒜).obj A) := by
    have hP0 : P (0 : 𝒜) := by
      obtain ⟨Z, hZ, hPZ⟩ := (inferInstance : P.ContainsZero).exists_zero
      exact P.prop_of_mono hZ.isoZero.inv hPZ
    intro n
    by_cases hn : n = 0
    · subst hn
      simpa [Pminus, HomotopyCategory.quotient_obj_as] using hA
    ·
      let hzero :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A n hn
      exact P.prop_of_mono hzero.isoZero.hom hP0
  simpa [IsBoundedAboveLeftAcyclicForAdditiveFunctor, Pminus] using
    (Functor.computesLeftDerivedAt_of_mem_subset
      KminusToDminus QisMinus Pminus hP_reaches hP_isIso hsingle)

-- Proof sketch: apply the bounded-above theorem above and transport the result to the unbounded
-- owner via the canonical comparison theorem `computes_left_derived_functor_at_iff_bounded_above`.
/-- Lemma 13.15.7: if every object of `𝒜` is a quotient of an object of `P`, and `P` is closed
under subobjects, while `F` preserves short exactness on short exact sequences whose middle and
right terms lie in `P`, then every object `A ∈ P` is acyclic for the pointwise unbounded left
derived functor of `F`, i.e. the degree-zero complex `A[0]` computes that left derived functor. -/
theorem isLeftAcyclicForAdditiveFunctor_of_mem_quotient_generating_subset
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    IsLeftAcyclicForAdditiveFunctor F A := by
  let _ : IsBoundedAboveLeftAcyclicForAdditiveFunctor F A :=
    isBoundedAboveLeftAcyclicForAdditiveFunctor_of_mem F P hF_shortExact A hA
  simpa [IsLeftAcyclicForAdditiveFunctor, IsBoundedAboveLeftAcyclicForAdditiveFunctor] using
    (computes_left_derived_functor_at_iff_bounded_above
      F ((single0Minus 𝒜).obj A)).2 inferInstance

end

end CategoryTheory

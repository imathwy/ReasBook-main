import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_5_3
import stacks_proof.stacks_project.Chap13.Definition_13_15_3
import stacks_proof.stacks_project.Chap13.Proposition_13_14_8
import stacks_proof.stacks_project.Chap13.Lemma_13_15_2
import stacks_proof.stacks_project.Chap13.Lemma_13_15_4

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

/-- Helper for Lemma 13.15.7: the bounded-above homotopy objects whose cochain terms all lie in
`P`. -/
private abbrev termwiseObjectProperty
    (P : ObjectProperty 𝒜) : ObjectProperty (K⁻(𝒜)) :=
  fun X ↦
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    ∀ n : ℤ, P (K.X n)

/-- Helper for Lemma 13.15.7: the degree-zero bounded-above complex on an object of `P` has all
its terms in `P`. -/
private lemma single0Minus_termwise_mem
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (A : 𝒜) (hA : P A) :
    termwiseObjectProperty (𝒜 := 𝒜) P ((single0Minus 𝒜).obj A) := by
  have hP0 : P (0 : 𝒜) := by
    -- First put a zero object of `𝒜` inside `P` using the owner instance above.
    obtain ⟨Z, hZ, hPZ⟩ := (inferInstance : P.ContainsZero).exists_zero
    exact P.prop_of_mono hZ.isoZero.inv hPZ
  -- Then inspect the two shapes of the single-term complex degreewise.
  intro n
  by_cases hn : n = 0
  · subst hn
    simpa [termwiseObjectProperty, HomotopyCategory.quotient_obj_as] using hA
  ·
    let hzero :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A n hn
    exact P.prop_of_mono hzero.isoZero.hom hP0

/-- Helper for Lemma 13.15.7: any bounded-above homotopy object admits a bounded-above
quasi-isomorphic replacement whose cochain terms all lie in `P`. -/
private lemma exists_termwise_resolution_of_boundedAbove
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    (Y : K⁻(𝒜)) :
    ∃ (Q : K⁻(𝒜)) (q : Q ⟶ Y),
      termwiseObjectProperty (𝒜 := 𝒜) P Q ∧ QisMinus q := by
  let K : CochainComplex 𝒜 ℤ := Y.obj.as
  obtain ⟨a, hY⟩ := (CochainComplex.minus_iff 𝒜 K).1 Y.property
  -- Resolve the bounded-above source by a termwise-`P` bounded-above complex.
  obtain ⟨Q, α, hα⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE P a K hY
  let Yc : Comp⁻(𝒜) := ⟨K, Y.property⟩
  have hYeq : (HomotopyCategory.Minus.quotient 𝒜).obj Yc = Y := by
    cases Y
    rfl
  let Qminus : Comp⁻(𝒜) := hα.toMinusWithTermsIn
  let Q' : K⁻(𝒜) := (HomotopyCategory.Minus.quotient 𝒜).obj Qminus
  let α' : Qminus ⟶ Yc := ⟨α⟩
  let q : Q' ⟶ Y := by
    simpa [Q', hYeq] using (HomotopyCategory.Minus.quotient 𝒜).map α'
  refine ⟨Q', q, ?_, ?_⟩
  · -- The replacement source is termwise in `P` by construction.
    intro n
    simpa [termwiseObjectProperty, Q'] using hα.toMinusWithTermsIn.term_mem n
  · -- The replacement map remains a bounded-above quasi-isomorphism.
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map q)
    simpa [q, Q', hYeq] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hα.quasiIso)

/-- Helper for Lemma 13.15.7: any denominator into `A[0]` can be refined by one whose source is
termwise in `P`. -/
private lemma refine_denominator_to_single0_termwise_mem
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    (A : 𝒜) {Y : K⁻(𝒜)}
    (t : Y ⟶ (single0Minus 𝒜).obj A) (ht : QisMinus t) :
    ∃ (Q : K⁻(𝒜)) (q : Q ⟶ Y),
      termwiseObjectProperty (𝒜 := 𝒜) P Q ∧ QisMinus q ∧ QisMinus (q ≫ t) := by
  let K : CochainComplex 𝒜 ℤ := Y.obj.as
  obtain ⟨a, hY⟩ := (CochainComplex.minus_iff 𝒜 K).1 Y.property
  -- Resolve the bounded-above source by a termwise-`P` bounded-above complex.
  obtain ⟨Q, α, hα⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE P a K hY
  let Yc : Comp⁻(𝒜) := ⟨K, Y.property⟩
  have hYeq : (HomotopyCategory.Minus.quotient 𝒜).obj Yc = Y := by
    cases Y
    rfl
  let Qminus : Comp⁻(𝒜) := hα.toMinusWithTermsIn
  let Q' : K⁻(𝒜) := (HomotopyCategory.Minus.quotient 𝒜).obj Qminus
  let α' : Qminus ⟶ Yc := ⟨α⟩
  let q : Q' ⟶ Y := by
    simpa [Q', hYeq] using (HomotopyCategory.Minus.quotient 𝒜).map α'
  refine ⟨Q', q, ?_, ?_, ?_⟩
  · -- The replacement source is termwise in `P` by construction.
    intro n
    simpa [termwiseObjectProperty, Q'] using hα.toMinusWithTermsIn.term_mem n
  · -- The replacement map remains a bounded-above quasi-isomorphism.
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map q)
    simpa [q, Q', hYeq] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hα.quasiIso)
  · -- Compose the refined denominator with the original one.
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      (((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map q) ≫
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map t))
    letI :
        HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map q) := by
      change HomotopyCategory.quasiIso 𝒜 (up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map q)
      simpa [q, Q', hYeq] using
        (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
            (((HomotopyCategory.quotient 𝒜 (up ℤ)).map α)) by
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact hα.quasiIso)
    letI :
        HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map t) := ht
    infer_instance

/-- Helper for Lemma 13.15.7: the identity denominator of `A[0]` admits a termwise-`P`
refinement. -/
private lemma single0Minus_has_termwise_resolution
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    (A : 𝒜) :
    ∃ (Q : K⁻(𝒜)) (s : Q ⟶ (single0Minus 𝒜).obj A),
      termwiseObjectProperty (𝒜 := 𝒜) P Q ∧ QisMinus s := by
  -- The special case `A[0]` is an instance of the general bounded-above termwise resolution.
  simpa using
    exists_termwise_resolution_of_boundedAbove
      (𝒜 := 𝒜) (P := P) ((single0Minus 𝒜).obj A)

/-- Helper for Lemma 13.15.7: a bounded-above quasi-isomorphism `Q ⟶ A[0]` determines the
corresponding object of the structured-arrow indexing category used to compute the pointwise left
derived functor at `A[0]`. -/
private abbrev single0_resolution_index
    (A : 𝒜) {Q : K⁻(𝒜)} (s : Q ⟶ (single0Minus 𝒜).obj A) (hs : QisMinus s) :
    StructuredArrow (QisMinus.Q.obj ((single0Minus 𝒜).obj A)) QisMinus.Q :=
  StructuredArrow.mk ((Localization.isoOfHom QisMinus.Q QisMinus s hs).inv)

/-- Helper for Lemma 13.15.7: if the denominator `s : Q ⟶ A[0]` has all cochain terms in `P`,
then the associated structured-arrow object already lies in the intended termwise-`P`
resolution subcategory. -/
private lemma single0_resolution_index_termwise_mem
    (P : ObjectProperty 𝒜)
    (A : 𝒜) {Q : K⁻(𝒜)} (s : Q ⟶ (single0Minus 𝒜).obj A) (hs : QisMinus s)
    (hQ : termwiseObjectProperty (𝒜 := 𝒜) P Q) :
    termwiseObjectProperty (𝒜 := 𝒜) P
      (single0_resolution_index (𝒜 := 𝒜) A s hs).left := by
  -- The indexing object remembers `Q` as its left vertex, so the termwise hypothesis on `Q`
  -- transports directly to the chosen structured-arrow object.
  simpa [single0_resolution_index] using hQ

/-- Helper for Lemma 13.15.7: an actual bounded-above termwise-`P` resolution of `A[0]`. -/
private structure Single0Resolution
    (P : ObjectProperty 𝒜) (A : 𝒜) where
  /-- The bounded-above source complex of the resolution. -/
  Q : K⁻(𝒜)
  /-- The actual denominator `Q ⟶ A[0]`. -/
  arrow : Q ⟶ (single0Minus 𝒜).obj A
  /-- Every cochain term of `Q` lies in `P`. -/
  termwise_mem : termwiseObjectProperty (𝒜 := 𝒜) P Q
  /-- The denominator is a bounded-above quasi-isomorphism. -/
  quasiIso : QisMinus arrow

/-- Helper for Lemma 13.15.7: any actual source resolution determines the corresponding ambient
structured-arrow object. -/
private abbrev Single0Resolution.index
    (P : ObjectProperty 𝒜) {A : 𝒜} (R : Single0Resolution (𝒜 := 𝒜) P A) :
    StructuredArrow (QisMinus.Q.obj ((single0Minus 𝒜).obj A)) QisMinus.Q :=
  single0_resolution_index (𝒜 := 𝒜) A R.arrow R.quasiIso

/-- Helper for Lemma 13.15.7: the identity denominator on `A[0]` is an actual source
resolution. -/
private abbrev single0_resolution_id
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (A : 𝒜) (hA : P A) :
    Single0Resolution (𝒜 := 𝒜) P A :=
  { Q := (single0Minus 𝒜).obj A
    arrow := 𝟙 ((single0Minus 𝒜).obj A)
    termwise_mem := single0Minus_termwise_mem (𝒜 := 𝒜) (P := P) A hA
    quasiIso := QisMinus.id_mem ((single0Minus 𝒜).obj A) }

/-- Helper for Lemma 13.15.7: the identity source resolution lands in the intended termwise-`P`
ambient subcategory. -/
private lemma single0_resolution_id_termwise_mem
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (A : 𝒜) (hA : P A) :
    termwiseObjectProperty (𝒜 := 𝒜) P
      (Single0Resolution.index (𝒜 := 𝒜) (P := P)
        (single0_resolution_id (𝒜 := 𝒜) (P := P) A hA)).left := by
  -- The identity resolution has source `A[0]`, whose terms were already shown to lie in `P`.
  simpa [single0_resolution_id, Single0Resolution.index] using
    single0Minus_termwise_mem (𝒜 := 𝒜) (P := P) A hA

/-- Helper for Lemma 13.15.7: a bounded-above quasi-isomorphism becomes an isomorphism in
`D^-(\mathcal B)` once both endpoints already compute the bounded-above left derived functor. -/
private theorem map_isIso_of_computesLeftDerivedAt
    {X X' : K⁻(𝒜)} (s : X ⟶ X')
    (hs : QisMinus s)
    (hX : Functor.ComputesLeftDerivedAt KminusToDminus QisMinus X)
    (hX' : Functor.ComputesLeftDerivedAt KminusToDminus QisMinus X') :
    IsIso (KminusToDminus.map s) := by
  let Xₗ : 𝓔ₗ[KminusToDminus, QisMinus] :=
    ⟨X, ComputesLeftDerivedAt.toHasPointwiseLeftDerivedFunctorAt (self := hX)⟩
  let X'ₗ : 𝓔ₗ[KminusToDminus, QisMinus] :=
    ⟨X', ComputesLeftDerivedAt.toHasPointwiseLeftDerivedFunctorAt (self := hX')⟩
  let sₗ : Xₗ ⟶ X'ₗ := s
  have hsₗ : S_𝓔ₗ[KminusToDminus, QisMinus] sₗ := by
    -- The restricted denominator is the same ambient bounded-above quasi-isomorphism.
    change QisMinus s
    exact hs
  have hs_left :
      IsIso
        ((leftDerivedDefinedFunctor KminusToDminus QisMinus).map sₗ) := by
    exact leftDerivedDefinedFunctor_isInvertedBy KminusToDminus QisMinus sₗ hsₗ
  letI : Functor.ComputesLeftDerivedAt KminusToDminus QisMinus X := hX
  letI : Functor.ComputesLeftDerivedAt KminusToDminus QisMinus X' := hX'
  have hsq :=
    Functor.leftDerivedValueMap_comp_of_square QisMinus KminusToDminus s
      (𝟙 X) (𝟙 X')
      (MorphismProperty.id_mem QisMinus X) (MorphismProperty.id_mem QisMinus X')
      s ⟨by simp⟩
  have hcomp :
      IsIso
        (Functor.leftDerivedValueProjection QisMinus KminusToDminus
          (𝟙 X) (MorphismProperty.id_mem QisMinus X) ≫
          KminusToDminus.map s) := by
    -- Compare the map on derived values with the map on the original functor through the
    -- identity-denominator projections on both endpoints.
    rw [hsq.w]
    change IsIso
      ((leftDerivedDefinedFunctor KminusToDminus QisMinus).map sₗ ≫
        Functor.leftDerivedValueProjection QisMinus KminusToDminus
          (𝟙 X') (MorphismProperty.id_mem QisMinus X'))
    infer_instance
  exact
    (isIso_comp_left_iff
      (Functor.leftDerivedValueProjection QisMinus KminusToDminus
        (𝟙 X) (MorphismProperty.id_mem QisMinus X))
      (KminusToDminus.map s)).1 hcomp

/-- Helper for Lemma 13.15.7: if `mapBoundedAboveHomotopyCategory F` sends a bounded-above
denominator to a bounded-above quasi-isomorphism, then the corresponding morphism in
`D^-(\mathcal B)` is invertible. -/
private theorem map_isIso_of_mapped_boundedAbove_quasiIso
    {X Y : K⁻(𝒜)} (s : X ⟶ Y)
    (hs :
      boundedAboveHomotopyQuasiIso ℬ
        ((mapBoundedAboveHomotopyCategory F).map s)) :
    IsIso (KminusToDminus.map s) := by
  -- Once the mapped morphism lies in the bounded-above quasi-isomorphism class, the canonical
  -- localization `K^-(ℬ) ⟶ D^-(ℬ)` inverts it.
  change
    IsIso
      (mapBoundedAboveHomotopyToDerivedAbove.map
        ((mapBoundedAboveHomotopyCategory F).map s))
  exact
    Localization.inverts
      mapBoundedAboveHomotopyToDerivedAbove
      (boundedAboveHomotopyQuasiIso ℬ)
      ((mapBoundedAboveHomotopyCategory F).map s)
      hs

/-- Helper for Lemma 13.15.7: if a denominator `s : X ⟶ Y` already becomes an isomorphism after
applying `KminusToDminus`, then computation of the left derived functor transports from `X` to
`Y`. -/
private theorem computesLeftDerivedAt_of_source_and_map_isIso
    {X Y : K⁻(𝒜)} (s : X ⟶ Y)
    (hs : QisMinus s)
    (hX : Functor.ComputesLeftDerivedAt KminusToDminus QisMinus X)
    (hsIso : IsIso (KminusToDminus.map s)) :
    Functor.ComputesLeftDerivedAt KminusToDminus QisMinus Y := by
  let hX_defined :
      Functor.HasPointwiseLeftDerivedFunctorAt KminusToDminus QisMinus X :=
    ComputesLeftDerivedAt.toHasPointwiseLeftDerivedFunctorAt (self := hX)
  have hY_defined :
      Functor.HasPointwiseLeftDerivedFunctorAt KminusToDminus QisMinus Y :=
    (Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem KminusToDminus QisMinus s hs).1 hX_defined
  letI : Functor.HasPointwiseLeftDerivedFunctorAt KminusToDminus QisMinus Y := hY_defined
  refine ⟨?_⟩
  have hs_left :
      IsIso (Functor.leftDerivedValueMap QisMinus KminusToDminus s) := by
    let Xₗ : 𝓔ₗ[KminusToDminus, QisMinus] := ⟨X, hX_defined⟩
    let Yₗ : 𝓔ₗ[KminusToDminus, QisMinus] := ⟨Y, hY_defined⟩
    let sₗ : Xₗ ⟶ Yₗ := s
    have hsₗ : S_𝓔ₗ[KminusToDminus, QisMinus] sₗ := by
      -- The restricted denominator is the same ambient bounded-above quasi-isomorphism.
      change QisMinus s
      exact hs
    simpa [leftDerivedDefinedFunctor] using
      (leftDerivedDefinedFunctor_isInvertedBy KminusToDminus QisMinus sₗ hsₗ)
  have hsq :=
    Functor.leftDerivedValueMap_comp_of_square QisMinus KminusToDminus s
      (𝟙 X) (𝟙 Y)
      (MorphismProperty.id_mem QisMinus X) (MorphismProperty.id_mem QisMinus Y)
      s ⟨by simp⟩
  have hcomp :
      IsIso
        (Functor.leftDerivedValueMap QisMinus KminusToDminus s ≫
          Functor.leftDerivedValueProjection QisMinus KminusToDminus
            (𝟙 Y) (MorphismProperty.id_mem QisMinus Y)) := by
    -- Compare the target identity projection with the source identity projection through `s`.
    rw [hsq.w]
    change IsIso
      (Functor.leftDerivedValueProjection QisMinus KminusToDminus
        (𝟙 X) (MorphismProperty.id_mem QisMinus X) ≫
          KminusToDminus.map s)
    infer_instance
  exact
    (isIso_comp_left_iff
      (Functor.leftDerivedValueMap QisMinus KminusToDminus s)
      (Functor.leftDerivedValueProjection QisMinus KminusToDminus
        (𝟙 Y) (MorphismProperty.id_mem QisMinus Y))).1 hcomp

/-- Helper for Lemma 13.15.7: if a denominator `s : X ⟶ Y` already becomes an isomorphism after
applying `KminusToDminus`, then computation of the left derived functor also transports from the
target `Y` back to the source `X`. -/
private theorem computesLeftDerivedAt_of_target_and_map_isIso
    {X Y : K⁻(𝒜)} (s : X ⟶ Y)
    (hs : QisMinus s)
    (hY : Functor.ComputesLeftDerivedAt KminusToDminus QisMinus Y)
    (hsIso : IsIso (KminusToDminus.map s)) :
    Functor.ComputesLeftDerivedAt KminusToDminus QisMinus X := by
  let hY_defined :
      Functor.HasPointwiseLeftDerivedFunctorAt KminusToDminus QisMinus Y :=
    ComputesLeftDerivedAt.toHasPointwiseLeftDerivedFunctorAt (self := hY)
  have hX_defined :
      Functor.HasPointwiseLeftDerivedFunctorAt KminusToDminus QisMinus X :=
    (Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem KminusToDminus QisMinus s hs).2
      hY_defined
  letI : Functor.HasPointwiseLeftDerivedFunctorAt KminusToDminus QisMinus X := hX_defined
  letI : Functor.ComputesLeftDerivedAt KminusToDminus QisMinus Y := hY
  refine ⟨?_⟩
  have hs_left :
      IsIso (Functor.leftDerivedValueMap QisMinus KminusToDminus s) := by
    let Xₗ : 𝓔ₗ[KminusToDminus, QisMinus] := ⟨X, hX_defined⟩
    let Yₗ : 𝓔ₗ[KminusToDminus, QisMinus] := ⟨Y, hY_defined⟩
    let sₗ : Xₗ ⟶ Yₗ := s
    have hsₗ : S_𝓔ₗ[KminusToDminus, QisMinus] sₗ := by
      -- The restricted denominator is the same ambient bounded-above quasi-isomorphism.
      change QisMinus s
      exact hs
    simpa [leftDerivedDefinedFunctor] using
      (leftDerivedDefinedFunctor_isInvertedBy KminusToDminus QisMinus sₗ hsₗ)
  have hsq :=
    Functor.leftDerivedValueMap_comp_of_square QisMinus KminusToDminus s
      (𝟙 X) (𝟙 Y)
      (MorphismProperty.id_mem QisMinus X) (MorphismProperty.id_mem QisMinus Y)
      s ⟨by simp⟩
  have hcomp :
      IsIso
        (Functor.leftDerivedValueProjection QisMinus KminusToDminus
          (𝟙 X) (MorphismProperty.id_mem QisMinus X) ≫
          KminusToDminus.map s) := by
    -- Compare the source identity projection with the target one through the denominator `s`.
    rw [hsq.w]
    change IsIso
      (Functor.leftDerivedValueMap QisMinus KminusToDminus s ≫
        Functor.leftDerivedValueProjection QisMinus KminusToDminus
          (𝟙 Y) (MorphismProperty.id_mem QisMinus Y))
    infer_instance
  exact
    (isIso_comp_right_iff
      (Functor.leftDerivedValueProjection QisMinus KminusToDminus
        (𝟙 X) (MorphismProperty.id_mem QisMinus X))
      (KminusToDminus.map s)).1 hcomp

/-- Helper for Lemma 13.15.7: a termwise-`P` bounded-above resolution of `A[0]` is sent to an
bounded-above quasi-isomorphism after applying `F`. -/
private theorem single0_resolution_mapped_quasiIso
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) {Q : K⁻(𝒜)} (s : Q ⟶ (single0Minus 𝒜).obj A)
    (hQ : termwiseObjectProperty (𝒜 := 𝒜) P Q)
    (hs : QisMinus s) :
    boundedAboveHomotopyQuasiIso ℬ
      ((mapBoundedAboveHomotopyCategory F).map s) := by
  -- Route correction: isolate the only remaining homological-algebra step as its own theorem
  -- before returning to the localization-level isomorphism wrapper.
  -- TODO: follow the descending cycle argument from the source: for `n < 0`, use the short exact
  -- rows `0 → Z^n(Q) → Q^n → Z^(n + 1)(Q) → 0`; at degree `0`, use
  -- `0 → Z^0(Q) → Q^0 → A → 0`. Closure of `P` under kernels comes from
  -- `P.prop_X₁_of_shortExact`, and `hF_shortExact` transports exactness after applying `F`.
  let _ := hF_shortExact
  let _ := hA
  let _ := hQ
  let _ := hs
  sorry

/-- Helper for Lemma 13.15.7: a termwise-`P` bounded-above resolution of `A[0]` is sent to an
isomorphism in `D^-(\mathcal B)`. -/
private theorem map_isIso_of_single0_resolution_terms_in
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) {Q : K⁻(𝒜)} (s : Q ⟶ (single0Minus 𝒜).obj A)
    (hQ : termwiseObjectProperty (𝒜 := 𝒜) P Q)
    (hs : QisMinus s) :
    IsIso (KminusToDminus.map s) := by
  -- Proof comment: once the mapped denominator is recognized as a bounded-above quasi-isomorphism,
  -- the bounded-above localization functor inverts it formally.
  have hsMapped :
      boundedAboveHomotopyQuasiIso ℬ
        ((mapBoundedAboveHomotopyCategory F).map s) :=
    single0_resolution_mapped_quasiIso
      (F := F) (P := P) hF_shortExact A hA s hQ hs
  exact map_isIso_of_mapped_boundedAbove_quasiIso (F := F) s hsMapped

/-- Helper for Lemma 13.15.7: a morphism between two termwise-`P` resolutions of `A[0]` becomes
an isomorphism in `D^-(\mathcal B)`. -/
private theorem map_isIso_of_resolution_morphism_over_single0
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A)
    {Q Q' : K⁻(𝒜)} (f : Q ⟶ Q')
    (s : Q ⟶ (single0Minus 𝒜).obj A) (s' : Q' ⟶ (single0Minus 𝒜).obj A)
    (hf : f ≫ s' = s)
    (hQ : termwiseObjectProperty (𝒜 := 𝒜) P Q)
    (hQ' : termwiseObjectProperty (𝒜 := 𝒜) P Q')
    (hs : QisMinus s) (hs' : QisMinus s') :
    IsIso (KminusToDminus.map f) := by
  have hsIso :
      IsIso (KminusToDminus.map s) :=
    map_isIso_of_single0_resolution_terms_in
      (F := F) (P := P) hF_shortExact A hA s hQ hs
  have hs'Iso :
      IsIso (KminusToDminus.map s') :=
    map_isIso_of_single0_resolution_terms_in
      (F := F) (P := P) hF_shortExact A hA s' hQ' hs'
  have hcomp : IsIso (KminusToDminus.map f ≫ KminusToDminus.map s') := by
    rw [← KminusToDminus.map_comp, hf]
    infer_instance
  exact
    (isIso_comp_right_iff
      (KminusToDminus.map f)
      (KminusToDminus.map s')).1 hcomp

/-- Helper for Lemma 13.15.7: the object property on the denominator category of `A[0]`
consisting of resolutions whose source is termwise in `P`. -/
private abbrev good_single0_resolution_property
    (P : ObjectProperty 𝒜) (A : 𝒜) :
    ObjectProperty
      (StructuredArrow (QisMinus.Q.obj ((single0Minus 𝒜).obj A)) QisMinus.Q) :=
  fun U ↦ termwiseObjectProperty (𝒜 := 𝒜) P U.left

/-- Helper for Lemma 13.15.7: the full subcategory of denominators into `A[0]` whose source
complex is termwise in `P`. -/
private abbrev good_single0_resolution_subcategory
    (P : ObjectProperty 𝒜) (A : 𝒜) :=
  (good_single0_resolution_property (𝒜 := 𝒜) (P := P) A).FullSubcategory

/-- Helper for Lemma 13.15.7: the inclusion of the good denominator subcategory into the full
structured-arrow denominator category over `A[0]`. -/
private abbrev good_single0_resolution_subcategory_inclusion
    (P : ObjectProperty 𝒜) (A : 𝒜) :
    good_single0_resolution_subcategory (𝒜 := 𝒜) (P := P) A ⥤
      StructuredArrow (QisMinus.Q.obj ((single0Minus 𝒜).obj A)) QisMinus.Q :=
  ObjectProperty.ι _

/-- Helper for Lemma 13.15.7: the restricted denominator diagram over `A[0]` with source
category the termwise-`P` resolutions. -/
private abbrev good_single0_resolution_diagram
    (P : ObjectProperty 𝒜) (A : 𝒜) :=
  good_single0_resolution_subcategory_inclusion (𝒜 := 𝒜) (P := P) A ⋙
    StructuredArrow.proj (QisMinus.Q.obj ((single0Minus 𝒜).obj A)) QisMinus.Q ⋙
      KminusToDminus

/-- Helper for Lemma 13.15.7: an actual termwise-`P` resolution determines an object of the
restricted denominator subcategory over `A[0]`. -/
private abbrev Single0Resolution.goodIndex
    (P : ObjectProperty 𝒜) {A : 𝒜} (R : Single0Resolution (𝒜 := 𝒜) P A) :
    good_single0_resolution_subcategory (𝒜 := 𝒜) (P := P) A :=
  ⟨R.index (P := P),
    single0_resolution_index_termwise_mem
      (𝒜 := 𝒜) (P := P) A R.arrow R.quasiIso R.termwise_mem⟩

/-- Helper for Lemma 13.15.7: the identity resolution of `A[0]` is an object of the restricted
denominator subcategory. -/
private abbrev single0_resolution_id_goodIndex
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (A : 𝒜) (hA : P A) :
    good_single0_resolution_subcategory (𝒜 := 𝒜) (P := P) A :=
  (single0_resolution_id (𝒜 := 𝒜) (P := P) A hA).goodIndex (P := P)

/-- Helper for Lemma 13.15.7: a left fraction over `A[0]` admits a common-source denominator
square. -/
private theorem left_fraction_exists_source_denominator_square
    (A : 𝒜) {X : K⁻(𝒜)}
    (ψ : QisMinus.LeftFraction ((single0Minus 𝒜).obj A) X) :
    ∃ (Y : K⁻(𝒜)) (s : Y ⟶ (single0Minus 𝒜).obj A) (_ : QisMinus s) (f : Y ⟶ X),
      s ≫ ψ.f = f ≫ ψ.s := by
  -- Proof comment: pass to the opposite category, use the right-fraction square there, and unop
  -- the resulting common-source square back in `K^-(𝒜)`.
  obtain ⟨φ, hφ⟩ := ψ.op.exists_leftFraction
  refine ⟨Opposite.unop φ.Y', φ.s.unop, φ.hs, φ.f.unop, ?_⟩
  simpa using congrArg Quiver.Hom.unop hφ

/-- Helper for Lemma 13.15.7: a commutative denominator square over `A[0]` gives the equality
needed to build the induced morphism in the structured-arrow denominator category. -/
private theorem single0_resolution_index_hom_eq_of_commSq
    (A : 𝒜) {X Y X' : K⁻(𝒜)} (f : X ⟶ X')
    (s : Y ⟶ X) (s' : X' ⟶ (single0Minus 𝒜).obj A)
    (hs : QisMinus s) (hs' : QisMinus s') (f' : Y ⟶ X')
    (sq : CommSq s f' f s') :
    (Localization.isoOfHom QisMinus.Q QisMinus s hs).inv ≫ QisMinus.Q.map f' =
      QisMinus.Q.map f ≫ (Localization.isoOfHom QisMinus.Q QisMinus s' hs').inv := by
  -- Proof comment: localize the square and cancel the two denominator isomorphisms to isolate the
  -- arrow required by `StructuredArrow.homMk`.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom QisMinus.Q QisMinus s hs).inv ≫ k ≫
        (Localization.isoOfHom QisMinus.Q QisMinus s' hs').inv)
    (sq.map QisMinus.Q).w
  simpa [Category.assoc, Localization.isoOfHom_hom] using hsq.symm

/-- Helper for Lemma 13.15.7: every object of the ambient denominator category over `A[0]`
receives a morphism from one coming from an actual bounded-above quasi-isomorphism into `A[0]`. -/
private theorem structuredArrow_exists_hom_from_single0_denominator
    (A : 𝒜)
    (U : StructuredArrow (QisMinus.Q.obj ((single0Minus 𝒜).obj A)) QisMinus.Q) :
    ∃ (Y : K⁻(𝒜)) (s : Y ⟶ (single0Minus 𝒜).obj A) (hs : QisMinus s),
      Nonempty (single0_resolution_index (𝒜 := 𝒜) A s hs ⟶ U) := by
  obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction QisMinus.Q QisMinus U.hom
  obtain ⟨Y, s, hs, f, hsq⟩ :=
    left_fraction_exists_source_denominator_square (𝒜 := 𝒜) A ψ
  refine ⟨Y, s, hs, ?_⟩
  refine ⟨StructuredArrow.homMk f ?_⟩
  -- Proof comment: the common-source square compares the chosen denominator object with the left
  -- fraction representing `U.hom`, and the latter representation is exactly `U.hom`.
  calc
    (Localization.isoOfHom QisMinus.Q QisMinus s hs).inv ≫ QisMinus.Q.map f
        = QisMinus.Q.map ψ.f ≫
            (Localization.isoOfHom QisMinus.Q QisMinus ψ.s ψ.hs).inv := by
          exact
            single0_resolution_index_hom_eq_of_commSq
              (𝒜 := 𝒜) A ψ.f s ψ.s hs ψ.hs f ⟨hsq⟩
    _ = U.hom := by
          simpa [hψ]

/-- Helper for Lemma 13.15.7: the inclusion of the termwise-`P` denominator subcategory is
initial. -/
private theorem termwise_single0_resolution_subcategory_initial
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    (A : 𝒜) :
    Functor.Initial
      (good_single0_resolution_subcategory_inclusion
        (𝒜 := 𝒜) (P := P) A) := by
  let G := good_single0_resolution_property (𝒜 := 𝒜) (P := P) A
  let inclusion := good_single0_resolution_subcategory_inclusion (𝒜 := 𝒜) (P := P) A
  let h :
      ∀ U : StructuredArrow (QisMinus.Q.obj ((single0Minus 𝒜).obj A)) QisMinus.Q,
        ∃ V : G.FullSubcategory, Nonempty (inclusion.obj V ⟶ U) := by
    intro U
    obtain ⟨Y, s, hs, hU⟩ :=
      structuredArrow_exists_hom_from_single0_denominator (𝒜 := 𝒜) A U
    obtain ⟨Q, q, hQ, hq, hqs⟩ :=
      refine_denominator_to_single0_termwise_mem (𝒜 := 𝒜) (P := P) A s hs
    let V :
        good_single0_resolution_subcategory (𝒜 := 𝒜) (P := P) A :=
      ⟨single0_resolution_index (𝒜 := 𝒜) A (q ≫ s) hqs,
        single0_resolution_index_termwise_mem
          (𝒜 := 𝒜) (P := P) A (q ≫ s) hqs hQ⟩
    have hVs :
        V.obj ⟶ single0_resolution_index (𝒜 := 𝒜) A s hs := by
      refine StructuredArrow.homMk q ?_
      -- Proof comment: the refined denominator `(q ≫ s)` maps to the original denominator `s`
      -- through the common-source identity square over `A[0]`.
      exact
        single0_resolution_index_hom_eq_of_commSq
          (𝒜 := 𝒜) A (𝟙 ((single0Minus 𝒜).obj A)) (q ≫ s) s hqs hs q ⟨by simp⟩
    refine ⟨V, ?_⟩
    rcases hU with ⟨α⟩
    exact ⟨hVs ≫ α⟩
  let _ : IsCofiltered G.FullSubcategory :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful inclusion h
  -- Proof comment: once every ambient denominator receives a morphism from a good one, the
  -- fully faithful inclusion is initial by the standard cofiltered full-subcategory criterion.
  exact Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful inclusion h

/-- Helper for Lemma 13.15.7: the fixed object `A[0]` is the real source-facing target of the
textbook argument, so the remaining denominator-category comparison should first show that
`A[0]` itself computes the bounded-above left derived functor. -/
private theorem single0_object_computesLeftDerivedAt_of_termwise_resolution
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A)
    (R : Single0Resolution (𝒜 := 𝒜) P A) :
    Functor.ComputesLeftDerivedAt KminusToDminus QisMinus ((single0Minus 𝒜).obj A) := by
  -- Route correction: compute at the actual textbook object `A[0]` first, then transport that
  -- result back along `R.arrow` only afterwards.
  let inclusion :=
    good_single0_resolution_subcategory_inclusion (𝒜 := 𝒜) (P := P) A
  have hInitial :
      Functor.Initial inclusion :=
    termwise_single0_resolution_subcategory_initial (𝒜 := 𝒜) (P := P) A
  let _ := hF_shortExact
  let _ := hA
  let _ := hInitial
  let _ := inclusion
  let _ := R.goodIndex (P := P)
  let _ :=
    single0_resolution_id_goodIndex (𝒜 := 𝒜) (P := P) A hA
  -- TODO: restrict the structured-arrow limit diagram over `A[0]` to the initial good
  -- denominator subcategory, build the common-refinement essentially constant cone there with
  -- vertex `KminusToDminus.obj R.Q`, and transport its limit back along `Functor.Initial.limitIso`
  -- to identify the identity projection for `A[0]`.
  sorry

/-- Helper for Lemma 13.15.7: once `Q ⟶ A[0]` is a termwise-`P` bounded-above resolution, the
source object `Q` computes the bounded-above left derived functor of `F`. -/
private theorem computesLeftDerivedAt_of_termwise_single0_resolution
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A)
    (R : Single0Resolution (𝒜 := 𝒜) P A) :
    Functor.ComputesLeftDerivedAt KminusToDminus QisMinus R.Q := by
  have hSingle0 :
      Functor.ComputesLeftDerivedAt KminusToDminus QisMinus ((single0Minus 𝒜).obj A) :=
    single0_object_computesLeftDerivedAt_of_termwise_resolution
      (𝒜 := 𝒜) (ℬ := ℬ) (F := F) (P := P) hF_shortExact A hA R
  have hArrowIso :
      IsIso (KminusToDminus.map R.arrow) :=
    map_isIso_of_single0_resolution_terms_in
      (F := F) (P := P) hF_shortExact A hA R.arrow R.termwise_mem R.quasiIso
  -- Proof comment: once `A[0]` computes, the denominator `R.arrow : R.Q ⟶ A[0]` transports that
  -- computation back to the chosen source resolution.
  exact
    computesLeftDerivedAt_of_target_and_map_isIso
      (F := F) R.arrow R.quasiIso hSingle0 hArrowIso

/-- Helper for Lemma 13.15.7: once `Q ⟶ A[0]` is a termwise-`P` bounded-above resolution, the
source object `Q` computes the bounded-above left derived functor of `F`. -/
private theorem computesLeftDerivedAt_of_termwise_single0_resolution_subset
    (P : ObjectProperty 𝒜)
    [P.HasEpiCover]
    [P.IsClosedUnderSubobjects]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₂ → P S.X₃ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) {Q : K⁻(𝒜)} (s : Q ⟶ (single0Minus 𝒜).obj A)
    (hQ : termwiseObjectProperty (𝒜 := 𝒜) P Q)
    (hs : QisMinus s) :
    Functor.ComputesLeftDerivedAt KminusToDminus QisMinus Q := by
  -- Package the raw denominator into the fixed-resolution object used by the source-faithful
  -- structured-arrow comparison theorem above.
  let R : Single0Resolution (𝒜 := 𝒜) P A :=
    { Q := Q
      arrow := s
      termwise_mem := hQ
      quasiIso := hs }
  simpa [R] using
    computesLeftDerivedAt_of_termwise_single0_resolution
      (F := F) (P := P) hF_shortExact A hA R

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
  -- The bounded-above quasi-isomorphism class is already known to be saturated in
  -- Situation 13.15.1, so no local saturation proof is needed here.
  let _ : MorphismProperty.IsSaturatedMultiplicativeSystem QisMinus := inferInstance
  change Functor.ComputesLeftDerivedAt KminusToDminus QisMinus ((single0Minus 𝒜).obj A)
  obtain ⟨Q, s, hQ, hs⟩ :=
    single0Minus_has_termwise_resolution (𝒜 := 𝒜) (P := P) A
  let R : Single0Resolution (𝒜 := 𝒜) P A :=
    { Q := Q
      arrow := s
      termwise_mem := hQ
      quasiIso := hs }
  let hsIso :
      IsIso (KminusToDminus.map R.arrow) :=
    map_isIso_of_single0_resolution_terms_in
      (F := F) (P := P) hF_shortExact A hA R.arrow R.termwise_mem R.quasiIso
  have hQcomp :
      Functor.ComputesLeftDerivedAt KminusToDminus QisMinus R.Q :=
    computesLeftDerivedAt_of_termwise_single0_resolution
      (F := F) (P := P) hF_shortExact A hA R
  -- Once the chosen source resolution computes the bounded-above left derived functor, the
  -- isomorphism result for `s` transports computation from `Q` to the degree-zero complex `A[0]`.
  exact
    computesLeftDerivedAt_of_source_and_map_isIso
      (F := F) R.arrow R.quasiIso hQcomp hsIso

-- Proof sketch: apply the bounded-above theorem above and transport the result to the unbounded
-- owner via the canonical comparison theorem `computes_left_derived_functor_at_iff_bounded_above`.
/-- Lemma 13.15.7: if every object of `𝒜` is a quotient of an object of `P`, and `P` is closed
under subobjects, while `F` preserves short exactness on short exact sequences whose middle and
right terms lie in `P`, then every object `A ∈ P` is acyclic for the pointwise unbounded left
derived functor of `F`, i.e. the degree-zero complex `A[0]` computes that left derived functor. -/
@[stacks 05T9]
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

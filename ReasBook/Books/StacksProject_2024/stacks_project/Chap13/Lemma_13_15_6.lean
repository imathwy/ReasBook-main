import Mathlib
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Lemma_13_14_4
import StacksProject_2024.Chap13.Lemma_13_14_15
import StacksProject_2024.Chap13.Lemma_13_15_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped CategoryTheory ZeroObject

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "QisPlus" => Qis⁺(𝒜)
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F

/- 
Domain-style sampling for Lemma 13.15.6:
- primary domain: bounded-below right-derived acyclicity obtained from bounded-below resolutions
  by a chosen object property `P`;
- sampled owner declarations:
  `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.IsClosedUnderQuotients`,
  `Functor.ComputesRightDerivedAt`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.computesRightDerivedAt_of_mem_subset`;
- best owner abstraction: the source-facing data here is the object property `P` together with the
  exactness hypothesis; the canonical owner for the embedding hypothesis is
  `ObjectProperty.HasMonoEmbedding`, the canonical owner for closure under quotients is
  `ObjectProperty.IsClosedUnderQuotients`, and the target acyclicity notion is the chapter owner
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- primitive data: `P`, the mono-embedding owner for `P`, the quotient-closure owner for `P`,
  and the hypothesis that `F` preserves short exactness on those short complexes;
- derived API: the acyclicity statement for the degree-zero object `A[0]` in `K⁺(𝒜)`.

Source/core/bridge triage:
- `source-facing`: the theorem below, specialized to objects `A ∈ P`;
- `core/canonical`: `ObjectProperty.HasMonoEmbedding`,
  `ObjectProperty.IsClosedUnderQuotients`, `Functor.ComputesRightDerivedAt`, and
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`;
- `bridge/view`: this theorem, which turns the source-facing object-property hypotheses into the
  canonical bounded-below acyclicity owner. -/

-- Proof sketch: apply Lemma 13.15.5 to produce, from any bounded-below complex, a
-- quasi-isomorphic bounded-below complex whose terms lie in `P`. The short-exact-sequence
-- hypotheses first imply that `P` contains a zero object, so Lemma 13.15.5 applies to produce,
-- from any bounded-below complex, a quasi-isomorphic bounded-below complex whose terms lie in
-- `P`. The short-exact-sequence hypotheses imply that applying `F` to such a resolution remains
-- exact, so quasi-isomorphisms between these resolutions become isomorphisms after applying `F`.
-- Lemma 13.14.15 then shows that every degree-zero object `A[0]` with `A ∈ P` computes the
-- pointwise right derived functor.
/-- Lemma 13.15.6: if every object admits a monomorphism into an object of `P`, and if `P` is
stable under the quotients occurring in short exact sequences on which applying `F` stays short
exact, then every object `A` of `P` is acyclic for the bounded-below right derived functor of
`F`, i.e. the degree-zero complex `A[0]` computes that pointwise right derived functor. -/
private instance containsZero_of_hasMonoEmbedding_and_isClosedUnderQuotients
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients] :
    P.ContainsZero where
  exists_zero := by
    obtain ⟨Y, hY, _, _⟩ := (inferInstance : P.HasMonoEmbedding).exists_mono (0 : 𝒜)
    let S : ShortComplex 𝒜 := ShortComplex.mk (𝟙 Y) (0 : Y ⟶ 0) (by simp)
    have hS : S.ShortExact := by
      refine ShortComplex.Splitting.shortExact ?_
      exact
        { r := 𝟙 Y
          s := 0
          f_r := by simp [S]
          s_g := by simp [S]
          id := by simp [S] }
    exact ⟨0, isZero_zero 𝒜, by simpa [S] using P.prop_X₃_of_shortExact hS hY⟩

/-- Helper for Lemma 13.15.6: the bounded-below homotopy objects whose cochain terms lie in
`P`. -/
private abbrev termwiseObjectProperty
    (P : ObjectProperty 𝒜) : ObjectProperty (K⁺(𝒜)) :=
  fun X ↦
    let K : CochainComplex 𝒜 ℤ := X.obj.as
    ∀ n : ℤ, P (K.X n)

/-- Helper for Lemma 13.15.6: the degree-zero bounded-below complex on an object of `P` has all
its terms in `P`. -/
private lemma single0Plus_termwise_mem
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (A : 𝒜) (hA : P A) :
    termwiseObjectProperty (𝒜 := 𝒜) P ((single0Plus 𝒜).obj A) := by
  have hP0 : P (0 : 𝒜) := by
    -- First place a zero object of `𝒜` inside `P`, using the owner instance built above.
    obtain ⟨Z, hZ, hPZ⟩ := (inferInstance : P.ContainsZero).exists_zero
    exact P.prop_of_epi hZ.isoZero.hom hPZ
  -- Then inspect the two shapes of the single-term complex degreewise.
  intro n
  by_cases hn : n = 0
  · subst hn
    simpa [termwiseObjectProperty, HomotopyCategory.quotient_obj_as] using hA
  ·
    let hzero :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A n hn
    exact P.prop_of_epi hzero.isoZero.inv hP0

/-- Helper for Lemma 13.15.6: the degree-zero complex on `A` admits a bounded-below
quasi-isomorphic replacement whose terms all lie in `P`. -/
private lemma single0Plus_has_termwise_resolution
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (A : 𝒜) :
    ∃ (I : K⁺(𝒜)) (s : (single0Plus 𝒜).obj A ⟶ I),
      termwiseObjectProperty (𝒜 := 𝒜) P I ∧ Qis⁺(𝒜) s := by
  sorry

/-- Helper for Lemma 13.15.6: a bounded-below quasi-isomorphism `s : A[0] ⟶ I` determines the
corresponding object of the costructured-arrow indexing category used to compute the pointwise
right derived functor at `A[0]`. -/
private abbrev single0_resolution_index
    (A : 𝒜) {I : K⁺(𝒜)} (s : (single0Plus 𝒜).obj A ⟶ I) (hs : Qis⁺(𝒜) s) :
    CostructuredArrow (Qis⁺(𝒜)).Q ((Qis⁺(𝒜)).Q.obj ((single0Plus 𝒜).obj A)) :=
  CostructuredArrow.mk ((Localization.isoOfHom (Qis⁺(𝒜)).Q (Qis⁺(𝒜)) s hs).inv)

/-- Helper for Lemma 13.15.6: if the denominator `s : A[0] ⟶ I` has all cochain terms in `P`,
then the associated costructured-arrow object already lies in the intended termwise-`P`
resolution subcategory. -/
private lemma single0_resolution_index_termwise_mem
    (P : ObjectProperty 𝒜)
    (A : 𝒜) {I : K⁺(𝒜)} (s : (single0Plus 𝒜).obj A ⟶ I) (hs : Qis⁺(𝒜) s)
    (hI : termwiseObjectProperty (𝒜 := 𝒜) P I) :
    termwiseObjectProperty (𝒜 := 𝒜) P
      (single0_resolution_index (𝒜 := 𝒜) A s hs).left := by
  -- The indexing object remembers `I` as its left vertex, so the termwise hypothesis on `I`
  -- transports directly to the chosen costructured-arrow object.
  simpa [single0_resolution_index] using hI

/-- Helper for Lemma 13.15.6: an actual bounded-below termwise-`P` resolution of `A[0]`. -/
private structure Single0Resolution
    (P : ObjectProperty 𝒜) (A : 𝒜) where
  /-- The bounded-below target complex of the resolution. -/
  I : K⁺(𝒜)
  /-- The actual denominator `A[0] ⟶ I`. -/
  arrow : (single0Plus 𝒜).obj A ⟶ I
  /-- Every cochain term of `I` lies in `P`. -/
  termwise_mem : termwiseObjectProperty (𝒜 := 𝒜) P I
  /-- The denominator is a bounded-below quasi-isomorphism. -/
  quasiIso : Qis⁺(𝒜) arrow

/-- Helper for Lemma 13.15.6: any actual source resolution determines the corresponding ambient
costructured-arrow object. -/
private abbrev Single0Resolution.index
    (P : ObjectProperty 𝒜) {A : 𝒜} (R : Single0Resolution (𝒜 := 𝒜) P A) :
    CostructuredArrow (Qis⁺(𝒜)).Q ((Qis⁺(𝒜)).Q.obj ((single0Plus 𝒜).obj A)) :=
  single0_resolution_index (𝒜 := 𝒜) A R.arrow R.quasiIso

/-- Helper for Lemma 13.15.6: the identity denominator on `A[0]` is an actual source
resolution. -/
private abbrev single0_resolution_id
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (A : 𝒜) (hA : P A) :
    Single0Resolution (𝒜 := 𝒜) P A :=
  { I := (single0Plus 𝒜).obj A
    arrow := 𝟙 ((single0Plus 𝒜).obj A)
    termwise_mem := single0Plus_termwise_mem (𝒜 := 𝒜) (P := P) A hA
    quasiIso := (Qis⁺(𝒜)).id_mem ((single0Plus 𝒜).obj A) }

/-- Helper for Lemma 13.15.6: the identity source resolution lands in the intended termwise-`P`
ambient subcategory. -/
private lemma single0_resolution_id_termwise_mem
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (A : 𝒜) (hA : P A) :
    termwiseObjectProperty (𝒜 := 𝒜) P
      (Single0Resolution.index (𝒜 := 𝒜) (P := P)
        (single0_resolution_id (𝒜 := 𝒜) (P := P) A hA)).left := by
  -- The identity resolution has source `A[0]`, whose terms were already shown to lie in `P`.
  simpa [single0_resolution_id, Single0Resolution.index] using
    single0Plus_termwise_mem (𝒜 := 𝒜) (P := P) A hA

/-- Helper for Lemma 13.15.6: a bounded-below quasi-isomorphism becomes an isomorphism in
`D^+(\mathcal B)` once both endpoints already compute the bounded-below right derived functor. -/
private theorem map_isIso_of_computesRightDerivedAt
    {X X' : K⁺(𝒜)} (s : X ⟶ X')
    (hs : QisPlus s)
    (hX : Functor.ComputesRightDerivedAt KplusToDplus QisPlus X)
    (hX' : Functor.ComputesRightDerivedAt KplusToDplus QisPlus X') :
    IsIso ((KplusToDplus).map s) := by
  sorry

/-- Helper for Lemma 13.15.6: if a denominator `s : X ⟶ Y` already becomes an isomorphism after
applying `KplusToDplus`, then computation of the bounded-below right derived functor transports
from `Y` back to `X`. -/
private theorem computesRightDerivedAt_of_target_and_map_isIso
    {X Y : K⁺(𝒜)} (s : X ⟶ Y)
    (hs : QisPlus s)
    (hY : Functor.ComputesRightDerivedAt KplusToDplus QisPlus Y)
    (hsIso : IsIso ((KplusToDplus).map s)) :
    Functor.ComputesRightDerivedAt KplusToDplus QisPlus X := by
  sorry

/-- Helper for Lemma 13.15.6: once a bounded-below quasi-isomorphic replacement of `A[0]` has
all of its terms in `P`, the source-proof kernel/image induction should show that `A[0]`
computes the right derived functor of `F`. -/
private lemma computesRightDerivedAt_of_single0_resolution
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) {I : K⁺(𝒜)} (s : (single0Plus 𝒜).obj A ⟶ I)
    (hI : termwiseObjectProperty (𝒜 := 𝒜) P I) (hs : Qis⁺(𝒜) s) :
    Functor.ComputesRightDerivedAt (mapBoundedBelowHomotopyCategoryToDerivedBelow F) (Qis⁺(𝒜))
      ((single0Plus 𝒜).obj A) := by
  -- Route correction: the remaining blocker is now the textbook denominator lemma for a single
  -- bounded-below termwise-`P` resolution of `A[0]`, not the earlier over-strong global
  -- quasi-isomorphism statement between arbitrary termwise-`P` complexes.
  -- The added hypothesis `hA : P A` is the source-faithful input for the exceptional degree-0
  -- short exact sequence `0 → A → I^0 / im(d^{-1}) → im(d^0) → 0`.
  let X₀ := (single0Plus 𝒜).obj A
  let R : Single0Resolution (𝒜 := 𝒜) P A :=
    { I := I
      arrow := s
      termwise_mem := hI
      quasiIso := hs }
  let R₀ := single0_resolution_id (𝒜 := 𝒜) (P := P) A hA
  let g := R.index (P := P)
  let g₀ := R₀.index (P := P)
  have hg_mem :
      termwiseObjectProperty (𝒜 := 𝒜) P g.left :=
    single0_resolution_index_termwise_mem (𝒜 := 𝒜) (P := P) A s hs hI
  have hg₀_mem :
      termwiseObjectProperty (𝒜 := 𝒜) P g₀.left :=
    single0_resolution_id_termwise_mem (𝒜 := 𝒜) (P := P) A hA
  -- TODO: prove that the fixed denominator `s : A[0] ⟶ I` becomes an isomorphism in
  -- `D^+(\mathcal B)` by the textbook kernel/image induction on `I`, using `hF_shortExact` and
  -- the termwise-`P` hypothesis `hI`.
  let hsIso :
      IsIso ((KplusToDplus).map s) := by
    sorry
  -- TODO: prove that the chosen resolution target `I` computes the pointwise right derived
  -- functor by restricting the costructured-arrow diagram to the source category of actual
  -- termwise-`P` resolutions of `A[0]`, with the identity resolution as the source-side anchor.
  have hI_compute :
      Functor.ComputesRightDerivedAt KplusToDplus QisPlus I := by
    sorry
  -- Once the fixed target computes and the denominator is inverted by `KplusToDplus`, transport
  -- the computation back along `s`.
  exact
    computesRightDerivedAt_of_target_and_map_isIso
      (F := F) s hs hI_compute hsIso

/-- Lemma 13.15.6: if every object admits a monomorphism into an object of `P`, and if `P` is
stable under the quotients occurring in short exact sequences on which applying `F` stays short
exact, then every object `A` of `P` is acyclic for the bounded-below right derived functor of
`F`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_of_mem
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A := by
  obtain ⟨I, s, hI, hs⟩ :=
    single0Plus_has_termwise_resolution (𝒜 := 𝒜) (P := P) A
  -- The proof now focuses on the single source-style resolution of `A[0]`.
  simpa [IsBoundedBelowRightAcyclicForAdditiveFunctor] using
    computesRightDerivedAt_of_single0_resolution
      (𝒜 := 𝒜) (ℬ := ℬ) (F := F) (P := P) hF_shortExact A hA s hI hs

end

end CategoryTheory

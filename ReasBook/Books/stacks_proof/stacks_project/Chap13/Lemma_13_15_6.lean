import Mathlib
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Lemma_13_15_2
import StacksProject_2024.Chap13.Lemma_13_15_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory ZeroObject

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "QisPlus" => (boundedBelowHomotopyQuasiIso 𝒜)
local notation "single0Plus" => CategoryTheory.single0Plus

/-- Helper for Lemma 13.15.6: mono embeddings together with quotient-closure force `P` to
contain the zero object. -/
private instance containsZero_of_hasMonoEmbedding_and_isClosedUnderQuotients
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients] :
    P.ContainsZero where
  exists_zero := by
    -- Proof comment: embed `0` into an object of `P`, then quotient back to `0`.
    obtain ⟨Y, hY, _, _⟩ := (inferInstance : P.HasMonoEmbedding).exists_mono (0 : 𝒜)
    refine ⟨0, isZero_zero 𝒜, ?_⟩
    exact P.prop_of_epi (0 : Y ⟶ (0 : 𝒜)) hY

/-- Helper for Lemma 13.15.6: the bounded-below homotopy objects whose cochain terms all lie in
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
    -- Proof comment: the local `ContainsZero` instance above already packages a zero object in
    -- `P`, and quotient-closure transports that membership to the chosen zero object of `𝒜`.
    obtain ⟨Z, hZ, hPZ⟩ := (inferInstance : P.ContainsZero).exists_zero
    exact P.prop_of_epi hZ.isoZero.hom hPZ
  -- Proof comment: only degree `0` is nonzero in the single-term complex.
  intro n
  by_cases hn : n = 0
  · subst hn
    simpa [termwiseObjectProperty, HomotopyCategory.quotient_obj_as] using hA
  ·
    let hzero :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A n hn
    exact P.prop_of_epi hzero.isoZero.inv hP0

/-- Helper for Lemma 13.15.6: any bounded-below homotopy object admits a bounded-below
quasi-isomorphic replacement whose cochain terms all lie in `P`. -/
private lemma exists_termwise_resolution_of_boundedBelow
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (Y : K⁺(𝒜)) :
    ∃ (Q : K⁺(𝒜)) (q : Y ⟶ Q),
      termwiseObjectProperty (𝒜 := 𝒜) P Q ∧ QisPlus q := by
  let K : CochainComplex 𝒜 ℤ := Y.obj.as
  obtain ⟨a, hY⟩ := (CochainComplex.plus_iff 𝒜 K).1 Y.property
  -- Proof comment: Lemma 13.15.5 already provides a cochain-level bounded-below replacement
  -- with terms in `P`; we only need to package it back into `K⁺(𝒜)`.
  obtain ⟨Q, α, hα⟩ :=
    exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE P a K hY
  let Yc : Comp⁺(𝒜) := ⟨K, Y.property⟩
  have hYeq : (HomotopyCategory.Plus.quotient 𝒜).obj Yc = Y := by
    cases Y
    rfl
  let Qplus : Comp⁺(𝒜) := hα.toPlusWithTermsIn
  let Q' : K⁺(𝒜) := (HomotopyCategory.Plus.quotient 𝒜).obj Qplus
  let α' : Yc ⟶ Qplus := ⟨α⟩
  let q : Y ⟶ Q' := by
    simpa [Q', hYeq] using (HomotopyCategory.Plus.quotient 𝒜).map α'
  refine ⟨Q', q, ?_, ?_⟩
  · -- Proof comment: the bundled replacement from Lemma 13.15.5 already stores the termwise
    -- `P`-membership facts.
    intro n
    simpa [termwiseObjectProperty, Q'] using hα.toPlusWithTermsIn.term_mem n
  · -- Proof comment: the quotient functor preserves the ambient quasi-isomorphism witness.
    change HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map q)
    simpa [q, Q', hYeq] using
      (show HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
          (((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map α)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hα.quasiIso)

/-- Helper for Lemma 13.15.6: any denominator out of `A[0]` can be refined by one whose target is
termwise in `P`. -/
private lemma refine_target_denominator_to_single0_termwise_mem
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    {A : 𝒜} {Y : K⁺(𝒜)}
    (t : (single0Plus 𝒜).obj A ⟶ Y) (ht : QisPlus t) :
    ∃ (Q : K⁺(𝒜)) (q : Y ⟶ Q),
      termwiseObjectProperty (𝒜 := 𝒜) P Q ∧ QisPlus q ∧ QisPlus (t ≫ q) := by
  obtain ⟨Q, q, hQ, hq⟩ :=
    exists_termwise_resolution_of_boundedBelow (𝒜 := 𝒜) (P := P) Y
  refine ⟨Q, q, hQ, hq, ?_⟩
  -- Proof comment: the refined denominator is the composite of two bounded-below
  -- quasi-isomorphisms, so it is again a bounded-below quasi-isomorphism.
  change HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
    (((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map t) ≫
      ((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map q))
  letI :
      HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map t) := ht
  letI :
      HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
        ((ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map q) := hq
  infer_instance

/-- Helper for Lemma 13.15.6: the degree-zero bounded-below object admits an actual termwise-`P`
resolution. -/
private lemma single0Plus_has_termwise_resolution
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (A : 𝒜) :
    ∃ (Q : K⁺(𝒜)) (s : (single0Plus 𝒜).obj A ⟶ Q),
      termwiseObjectProperty (𝒜 := 𝒜) P Q ∧ QisPlus s := by
  -- Proof comment: this is just the general bounded-below resolution lemma specialized to `A[0]`.
  simpa using
    exists_termwise_resolution_of_boundedBelow
      (𝒜 := 𝒜) (P := P) ((single0Plus 𝒜).obj A)

/-- Helper for Lemma 13.15.6: an actual bounded-below termwise-`P` resolution of `A[0]`. -/
private structure Single0Resolution
    (P : ObjectProperty 𝒜) (A : 𝒜) where
  /-- The bounded-below target complex of the resolution. -/
  Q : K⁺(𝒜)
  /-- The actual denominator `A[0] ⟶ Q`. -/
  arrow : (single0Plus 𝒜).obj A ⟶ Q
  /-- Every cochain term of `Q` lies in `P`. -/
  termwise_mem : termwiseObjectProperty (𝒜 := 𝒜) P Q
  /-- The denominator is a bounded-below quasi-isomorphism. -/
  quasiIso : QisPlus arrow

/-- Helper for Lemma 13.15.6: any morphism in `QisPlus` between bounded-below objects that
already compute the bounded-below right derived functor is inverted by `KplusToDplus`. -/
private theorem map_isIso_of_computesRightDerivedAt
    {X X' : K⁺(𝒜)} (s : X ⟶ X')
    (hs : QisPlus s)
    (hX : Functor.ComputesRightDerivedAt (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus X)
    (hX' :
      Functor.ComputesRightDerivedAt (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus X') :
    IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map s) := by
  let η :=
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerivedUnit
      (boundedBelowHomotopyQuasiIso 𝒜).Q QisPlus
  have hηX :
      IsIso (η.app X) := by
    exact
      (Functor.computesRightDerivedAt_iff
        (F := mapBoundedBelowHomotopyCategoryToDerivedBelow F) (S := QisPlus) (X := X)).1 hX
  have hηX' :
      IsIso (η.app X') := by
    exact
      (Functor.computesRightDerivedAt_iff
        (F := mapBoundedBelowHomotopyCategoryToDerivedBelow F) (S := QisPlus) (X := X')).1 hX'
  have htotal :
      IsIso
        (((mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerived
          (boundedBelowHomotopyQuasiIso 𝒜).Q QisPlus).map
          ((boundedBelowHomotopyQuasiIso 𝒜).Q.map s)) := by
    exact
      Functor.totalRightDerived_map_isIso_of_mem
        (S := QisPlus) (F := mapBoundedBelowHomotopyCategoryToDerivedBelow F) s hs
  let _ : IsIso (η.app X) := hηX
  let _ : IsIso (η.app X') := hηX'
  let _ :
      IsIso
        (((mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerived
          (boundedBelowHomotopyQuasiIso 𝒜).Q QisPlus).map
          ((boundedBelowHomotopyQuasiIso 𝒜).Q.map s)) :=
    htotal
  have hcomp :
      IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map s ≫ η.app X') := by
    -- Proof comment: naturality of the total right-derived unit compares the source map with the
    -- already invertible map on derived values.
    rw [NatTrans.naturality η s]
    infer_instance
  exact
    (isIso_comp_right_iff
      ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map s)
      (η.app X')).1 hcomp

/-- Helper for Lemma 13.15.6: if the image of a bounded-below morphism under
`mapBoundedBelowHomotopyCategory F` is a bounded-below quasi-isomorphism, then its image under
`KplusToDplus` is invertible. -/
private theorem map_isIso_of_mapped_boundedBelow_quasiIso
    {X Y : K⁺(𝒜)} (s : X ⟶ Y)
    (hs :
      boundedBelowHomotopyQuasiIso ℬ
        ((mapBoundedBelowHomotopyCategory F).map s)) :
    IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map s) := by
  -- Proof comment: `KplusToDplus` is the composite
  -- `K^+(\mathcal A) ⟶ K^+(\mathcal B) ⟶ D^+(\mathcal B)`, so the bounded localization inverts
  -- the mapped quasi-isomorphism formally.
  change
    IsIso
      (mapBoundedBelowHomotopyToDerivedBelow.map
        ((mapBoundedBelowHomotopyCategory F).map s))
  have hUnderlying :
      IsIso
        (((HomotopyCategory.plus ℬ).ι ⋙ DerivedCategory.Qh).map
          ((mapBoundedBelowHomotopyCategory F).map s)) := by
    change IsIso
      (DerivedCategory.Qh.map
        ((HomotopyCategory.plus ℬ).ι.map ((mapBoundedBelowHomotopyCategory F).map s)))
    exact
      Localization.inverts
        (DerivedCategory.Qh : K(ℬ) ⥤ D(ℬ))
        (HomotopyCategory.quasiIso ℬ (ComplexShape.up ℤ))
        ((HomotopyCategory.plus ℬ).ι.map ((mapBoundedBelowHomotopyCategory F).map s))
        (by simpa [boundedBelowHomotopyQuasiIso] using hs)
  let ιplus : D⁺(ℬ) ⥤ D(ℬ) := ObjectProperty.ι (DerivedCategory.TStructure.t.plus)
  have hLifted :
      IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map
        ((mapBoundedBelowHomotopyCategory F).map s))) := by
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (DerivedCategory.TStructure.t.plus : ObjectProperty (D(ℬ)))
          ((HomotopyCategory.plus ℬ).ι ⋙ DerivedCategory.Qh)
          (fun K ↦ by simpa using qh_obj_mem_t_plus K))
        ((mapBoundedBelowHomotopyCategory F).map s)).2 hUnderlying)
  let _ :
      IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map
        ((mapBoundedBelowHomotopyCategory F).map s))) := hLifted
  exact
    isIso_of_fully_faithful ιplus
      (mapBoundedBelowHomotopyToDerivedBelow.map
        ((mapBoundedBelowHomotopyCategory F).map s))

/-- Helper for Lemma 13.15.6: if a denominator `s : X ⟶ Y` already becomes an isomorphism after
applying `KplusToDplus`, then computation of the right derived functor transports from the target
`Y` back to the source `X`. -/
private theorem computesRightDerivedAt_of_target_and_map_isIso
    {X Y : K⁺(𝒜)} (s : X ⟶ Y)
    (hs : QisPlus s)
    (hY : Functor.ComputesRightDerivedAt (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus Y)
    (hsIso : IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map s)) :
    Functor.ComputesRightDerivedAt (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus X := by
  let hY_defined :
      Functor.HasPointwiseRightDerivedFunctorAt
        (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus Y :=
    hY.toHasPointwiseRightDerivedFunctorAt
  have hX_defined :
      Functor.HasPointwiseRightDerivedFunctorAt
        (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus X :=
    (Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus s hs).2 hY_defined
  letI :
      Functor.HasPointwiseRightDerivedFunctorAt
        (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus X := hX_defined
  let η :=
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerivedUnit
      (boundedBelowHomotopyQuasiIso 𝒜).Q QisPlus
  have hηY :
      IsIso (η.app Y) := by
    exact
      (Functor.computesRightDerivedAt_iff
        (F := mapBoundedBelowHomotopyCategoryToDerivedBelow F) (S := QisPlus) (X := Y)).1 hY
  have htotal :
      IsIso
        (((mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerived
          (boundedBelowHomotopyQuasiIso 𝒜).Q QisPlus).map
          ((boundedBelowHomotopyQuasiIso 𝒜).Q.map s)) := by
    exact
      Functor.totalRightDerived_map_isIso_of_mem
        (S := QisPlus) (F := mapBoundedBelowHomotopyCategoryToDerivedBelow F) s hs
  let _ : IsIso (η.app Y) := hηY
  let _ :
      IsIso
        (((mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerived
          (boundedBelowHomotopyQuasiIso 𝒜).Q QisPlus).map
          ((boundedBelowHomotopyQuasiIso 𝒜).Q.map s)) :=
    htotal
  let _ : IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map s) := hsIso
  have hcomp :
      IsIso (η.app X ≫
        ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerived
          (boundedBelowHomotopyQuasiIso 𝒜).Q QisPlus).map
          ((boundedBelowHomotopyQuasiIso 𝒜).Q.map s)) := by
    -- Proof comment: naturality rewrites the target unit as the already invertible source map
    -- followed by the target unit.
    rw [← NatTrans.naturality η s]
    infer_instance
  exact
    (Functor.computesRightDerivedAt_iff
      (F := mapBoundedBelowHomotopyCategoryToDerivedBelow F) (S := QisPlus) (X := X)).2
      ((isIso_comp_right_iff
        (η.app X)
        (((mapBoundedBelowHomotopyCategoryToDerivedBelow F).totalRightDerived
          (boundedBelowHomotopyQuasiIso 𝒜).Q QisPlus).map
          ((boundedBelowHomotopyQuasiIso 𝒜).Q.map s))).1 hcomp)

/-- Helper for Lemma 13.15.6: the source-faithful homological core says that a termwise-`P`
bounded-below resolution of `A[0]` is sent to a bounded-below quasi-isomorphism by `F`. -/
private theorem single0ResolutionMappedQuasiIso
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) {Q : K⁺(𝒜)} (s : (single0Plus 𝒜).obj A ⟶ Q)
    (hQ : termwiseObjectProperty (𝒜 := 𝒜) P Q)
    (hs : QisPlus s) :
    boundedBelowHomotopyQuasiIso ℬ
      ((mapBoundedBelowHomotopyCategory F).map s) := by
  -- Route correction: the stale opposite-category shortcut hid the real source argument. The
  -- remaining work is exactly the Stacks degree-by-degree kernel/image induction on the chosen
  -- bounded-below resolution.
  -- TODO: starting from the lowest nonzero degree of `Q`, prove inductively that the cycles and
  -- boundaries lie in `P`; use the short exact rows
  -- `0 → Z^n(Q) → Q^n → B^n(Q) → 0` and the special degree-zero row
  -- `0 → A → Q^0 / B^{-1}(Q) → B^0(Q) → 0`, then apply `hF_shortExact` to deduce exactness after
  -- applying `F` and conclude that `F(A)[0] ⟶ F(Q)` is a quasi-isomorphism.
  let _ := hF_shortExact
  let _ := hA
  let _ := hQ
  let _ := hs
  sorry

/-- Helper for Lemma 13.15.6: if a termwise-`P` bounded-below resolution of `A[0]` is sent to a
bounded-below quasi-isomorphism after applying `F`, then its image in `D^+(\mathcal B)` is an
isomorphism. -/
private theorem map_isIso_of_single0_resolution_terms_in
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) {Q : K⁺(𝒜)} (s : (single0Plus 𝒜).obj A ⟶ Q)
    (hQ : termwiseObjectProperty (𝒜 := 𝒜) P Q)
    (hs : QisPlus s) :
    IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map s) := by
  -- Proof comment: once the mapped denominator is recognized as a bounded-below
  -- quasi-isomorphism, the bounded-below localization inverts it formally.
  have hsMapped :
      boundedBelowHomotopyQuasiIso ℬ
        ((mapBoundedBelowHomotopyCategory F).map s) :=
    single0ResolutionMappedQuasiIso
      (F := F) (P := P) hF_shortExact A hA s hQ hs
  exact map_isIso_of_mapped_boundedBelow_quasiIso (F := F) s hsMapped

/-- Helper for Lemma 13.15.6: once `A[0] ⟶ Q` is a termwise-`P` bounded-below resolution, the
target object `Q` computes the bounded-below right derived functor of `F`. -/
private theorem computesRightDerivedAt_of_termwise_single0_resolution
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A)
    (R : Single0Resolution (𝒜 := 𝒜) P A) :
    Functor.ComputesRightDerivedAt (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus R.Q := by
  -- Route correction: after producing actual termwise-`P` denominators into `A[0]`, the
  -- remaining missing step is the denominator-category finality argument on the good
  -- costructured-arrow subcategory.
  -- TODO: use `refine_target_denominator_to_single0_termwise_mem` to show the full subcategory of
  -- denominators with termwise-`P` targets is final; then make the restricted right-derived
  -- diagram essentially constant with vertex `KplusToDplus.obj R.Q`, using
  -- `map_isIso_of_single0_resolution_terms_in` to compare all transition maps.
  sorry

/-- Lemma 13.15.6: if every object admits a monomorphism into an object of `P`, and if `P` is
stable under the quotients occurring in short exact sequences on which applying `F` stays short
exact, then every object `A` of `P` is acyclic for the bounded-below right derived functor of
`F`. -/
@[stacks 05T8]
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_of_mem
    (P : ObjectProperty 𝒜)
    [P.HasMonoEmbedding]
    [P.IsClosedUnderQuotients]
    (hF_shortExact :
      ∀ ⦃S : ShortComplex 𝒜⦄, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)
    (A : 𝒜) (hA : P A) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A := by
  change
    Functor.ComputesRightDerivedAt
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus ((single0Plus 𝒜).obj A)
  obtain ⟨Q, s, hQ, hs⟩ :=
    single0Plus_has_termwise_resolution (𝒜 := 𝒜) (P := P) A
  let R : Single0Resolution (𝒜 := 𝒜) P A :=
    { Q := Q
      arrow := s
      termwise_mem := hQ
      quasiIso := hs }
  have hQcomp :
      Functor.ComputesRightDerivedAt
        (mapBoundedBelowHomotopyCategoryToDerivedBelow F) QisPlus R.Q :=
    computesRightDerivedAt_of_termwise_single0_resolution
      (F := F) (P := P) hF_shortExact A hA R
  have hsIso :
      IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map R.arrow) :=
    map_isIso_of_single0_resolution_terms_in
      (F := F) (P := P) hF_shortExact A hA R.arrow R.termwise_mem R.quasiIso
  -- Proof comment: once the chosen target resolution computes and the denominator map becomes an
  -- isomorphism in `D^+(\mathcal B)`, computation transports back to the textbook object `A[0]`.
  exact
    computesRightDerivedAt_of_target_and_map_isIso
      (F := F) R.arrow R.quasiIso hQcomp hsIso

end

end CategoryTheory

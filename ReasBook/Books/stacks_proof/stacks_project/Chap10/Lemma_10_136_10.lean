import Mathlib
import StacksProject_2024.Chap10.Definition_10_125_1
import StacksProject_2024.Chap10.Lemma_10_125_6
import StacksProject_2024.Chap10.Lemma_10_135_2
import StacksProject_2024.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

open MvPolynomial
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)

/-
Domain-style sampling:
- primary domain: explicit polynomial presentations under localization away from one element;
- sampled owner declarations:
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.localizationAway`,
  `Algebra.Presentation.localizationAway`,
  `Algebra.Presentation.relation_comp_localizationAway_inl`;
- best owner abstraction:
  `Algebra.IsRelativeGlobalCompleteIntersection` remains the owner of the property, while the
  explicit quotient obtained by adjoining an inverse is the source-facing bridge/view for this
  lemma;
- primitive vs. derived:
  the primitive source-facing data are `h`, `g`, the explicit quotient presentation, and the
  comparison `Localization.Away g ≃ₐ[R] ...`; the relative-global-complete-intersection property
  should then be stated on that displayed quotient ring itself.
-/

local notation "PresentedIdeal" =>
  Ideal.span (Set.range f)

local notation "PresentedAlgebra" =>
  MvPolynomial (Fin n) R ⧸ PresentedIdeal

local notation "LocalizedPresentedAlgebra" =>
  fun h : MvPolynomial (Fin n) R ↦
    MvPolynomial (Fin (n + 1)) R ⧸
      Ideal.span
        (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
          {rename Fin.castSuccEmb h * X (Fin.last n) - 1})

/-- Helper for Chap10 Lemma 10 136 10: use the identity algebra structure on the quotient
presentation to keep localization typeclass search from unfolding the quotient repeatedly. -/
noncomputable local instance instPresentedAlgebraSelfAlgebra :
    Algebra PresentedAlgebra PresentedAlgebra :=
  Algebra.id PresentedAlgebra

/-- Helper for Chap10 Lemma 10 136 10: the self-module structure attached to the identity
algebra structure on the presented quotient. -/
noncomputable local instance instPresentedAlgebraSelfModule :
    Module PresentedAlgebra PresentedAlgebra :=
  Algebra.toModule

/-- Helper for Chap10 Lemma 10 136 10: the distributive action attached to the identity algebra
structure on the presented quotient. -/
noncomputable local instance instPresentedAlgebraSelfDistribMulAction :
    DistribMulAction PresentedAlgebra PresentedAlgebra :=
  Algebra.toModule.toDistribMulAction

/-- Helper for Chap10 Lemma 10 136 10: identify `Unit ⊕ Fin n` with `Fin (n + 1)` so that the
new localization variable lands in the last coordinate. -/
private noncomputable def unitSumFinLastEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) :=
  (Equiv.sumComm Unit (Fin n)).trans <|
    (Equiv.sumCongr (Equiv.refl (Fin n)) (Fintype.equivFin Unit)).trans <|
      finSumFinEquiv

/-- Helper for Chap10 Lemma 10 136 10: the `Unit` summand maps to the last coordinate. -/
private theorem unitSumFinLastEquiv_apply_unit (n : ℕ) :
    unitSumFinLastEquiv n (Sum.inl ()) = Fin.last n := by
  -- Unfold the chosen reindexing equivalence and evaluate it on the unique `Unit` point.
  apply Fin.ext
  simp [unitSumFinLastEquiv]

/-- Helper for Chap10 Lemma 10 136 10: the `Fin n` summand maps to the first `n` coordinates. -/
private theorem unitSumFinLastEquiv_apply_fin (n : ℕ) (i : Fin n) :
    unitSumFinLastEquiv n (Sum.inr i) = Fin.castSucc i := by
  -- The `Fin n` variables survive the reindexing unchanged except for the cast-succ embedding.
  apply Fin.ext
  simp [unitSumFinLastEquiv]

/-- Helper for Chap10 Lemma 10 136 10: the last coordinate comes from the `Unit` summand. -/
private theorem unitSumFinLastEquiv_symm_last (n : ℕ) :
    (unitSumFinLastEquiv n).symm (Fin.last n) = Sum.inl () := by
  apply (unitSumFinLastEquiv n).injective
  simp [unitSumFinLastEquiv_apply_unit]

/-- Helper for Chap10 Lemma 10 136 10: the first `n` coordinates come from the `Fin n` summand. -/
private theorem unitSumFinLastEquiv_symm_castSucc (n : ℕ) (i : Fin n) :
    (unitSumFinLastEquiv n).symm (Fin.castSucc i) = Sum.inr i := by
  apply (unitSumFinLastEquiv n).injective
  simp [unitSumFinLastEquiv_apply_fin]

/-- Helper for Chap10 Lemma 10 136 10: normalize the naive quotient section so it sends `0`
and `-1` to the corresponding constant polynomials. -/
private noncomputable def presentedAlgebraNormalizedSection :
    PresentedAlgebra → MvPolynomial (Fin n) R :=
  let _ : DecidableEq PresentedAlgebra := Classical.decEq _
  fun x ↦
    if x = 0 then
      0
    else if x = -1 then
      -1
    else
      Function.surjInv (Ideal.Quotient.mk_surjective (I := PresentedIdeal)) x

/-- Helper for Chap10 Lemma 10 136 10: the normalized quotient section still lifts every quotient
class in the presented algebra. -/
private theorem quotient_mk_presentedAlgebraNormalizedSection
    (x : PresentedAlgebra) :
    Ideal.Quotient.mk PresentedIdeal (presentedAlgebraNormalizedSection (f := f) x) = x := by
  -- The normalization only changes the chosen representatives of `0` and `-1`.
  classical
  by_cases hx : x = 0
  · simp [presentedAlgebraNormalizedSection, hx]
  · by_cases hneg : x = -1
    · have hone : (1 : PresentedAlgebra) ≠ 0 := by
        intro h1
        apply hx
        calc
          x = -1 := hneg
          _ = 0 := by simpa [h1]
      simp [presentedAlgebraNormalizedSection, hneg, hone]
    · simpa [presentedAlgebraNormalizedSection, hx, hneg] using
        Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := PresentedIdeal)) x

/-- Helper for Chap10 Lemma 10 136 10: the normalized quotient section sends `0` to `0`. -/
private theorem presentedAlgebraNormalizedSection_zero :
    presentedAlgebraNormalizedSection (f := f) (0 : PresentedAlgebra) = 0 := by
  classical
  simp [presentedAlgebraNormalizedSection]

/-- Helper for Chap10 Lemma 10 136 10: the normalized quotient section still maps to `-1` after
applying the quotient map. -/
private theorem quotient_mk_presentedAlgebraNormalizedSection_neg_one :
    Ideal.Quotient.mk PresentedIdeal
      (presentedAlgebraNormalizedSection (f := f) (-1 : PresentedAlgebra)) =
        (-1 : PresentedAlgebra) := by
  -- This is the `x = -1` specialization of the section-lifting property.
  simpa using
    quotient_mk_presentedAlgebraNormalizedSection (f := f) (-1 : PresentedAlgebra)

/-- Helper for Chap10 Lemma 10 136 10: the discrepancy between the normalized `-1` lift and the
constant polynomial `-1` lies in the presentation ideal. -/
private theorem presentedAlgebraNormalizedSection_neg_one_add_one_mem :
    presentedAlgebraNormalizedSection (f := f) (-1 : PresentedAlgebra) + 1 ∈ PresentedIdeal := by
  -- Applying the quotient map shows that this sum is zero in the quotient algebra.
  apply (Ideal.Quotient.eq_zero_iff_mem).1
  have hzero :
      Ideal.Quotient.mk PresentedIdeal
          (presentedAlgebraNormalizedSection (f := f) (-1 : PresentedAlgebra) + 1) = 0 := by
    simpa [map_add] using
      congrArg (fun z : PresentedAlgebra ↦ z + 1)
        (quotient_mk_presentedAlgebraNormalizedSection_neg_one (f := f))
  exact hzero

/-- Helper for Chap10 Lemma 10 136 10: the normalized quotient section differs from any chosen
representative by an element of the presentation ideal. -/
private theorem presentedAlgebraNormalizedSection_sub_mem
    (h : MvPolynomial (Fin n) R) :
    presentedAlgebraNormalizedSection (f := f) (Ideal.Quotient.mk PresentedIdeal h) - h ∈
      PresentedIdeal := by
  -- Applying the quotient map turns the difference into zero, so it lies in the defining ideal.
  apply (Ideal.Quotient.eq_zero_iff_mem).1
  rw [map_sub]
  simpa using sub_eq_zero.mpr
    (quotient_mk_presentedAlgebraNormalizedSection (f := f)
      (Ideal.Quotient.mk PresentedIdeal h))

/-- Helper for Chap10 Lemma 10 136 10: the old presentation relations, renamed into the first
`n` variables, lie in the displayed inverse-adjoining ideal. -/
private theorem rename_castSuccEmb_presentedIdeal_le_displayedIdeal
    (h : MvPolynomial (Fin n) R) :
    Ideal.map (MvPolynomial.rename Fin.castSuccEmb) PresentedIdeal ≤
      Ideal.span
        (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
          {rename Fin.castSuccEmb h * X (Fin.last n) - 1}) := by
  -- Map the span relation-by-relation; each renamed old relation is one of the displayed
  -- generators.
  rw [Ideal.map_span]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨p, hp, rfl⟩
  rcases hp with ⟨i, rfl⟩
  exact Ideal.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)

/-- Helper for Chap10 Lemma 10 136 10: the quotient map from the original presentation to the
displayed inverse-adjoining quotient. -/
private noncomputable def presentedAlgebraToLocalizedPresentedAlgebra
    (h : MvPolynomial (Fin n) R) :
    PresentedAlgebra →ₐ[R] LocalizedPresentedAlgebra h :=
  Ideal.quotientMapₐ
    (Ideal.span
      (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
        {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
    (MvPolynomial.rename Fin.castSuccEmb)
    (Ideal.map_le_iff_le_comap.mp
      (rename_castSuccEmb_presentedIdeal_le_displayedIdeal (f := f) h))

/-- Helper for Chap10 Lemma 10 136 10: the quotient-map bridge sends classes to their renamed
classes. -/
private theorem presentedAlgebraToLocalizedPresentedAlgebra_mk
    (h a : MvPolynomial (Fin n) R) :
    presentedAlgebraToLocalizedPresentedAlgebra (f := f) h
      (Ideal.Quotient.mk PresentedIdeal a) =
        Ideal.Quotient.mk
          (Ideal.span
            (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
              {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
          (rename Fin.castSuccEmb a) := by
  -- This is the computation rule for the quotient map induced by variable renaming.
  rfl

/-- Helper for Chap10 Lemma 10 136 10: in the displayed quotient, the image of `h` is inverted
by the new last variable. -/
private theorem image_presentedAlgebraToLocalizedPresentedAlgebra_mul_last
    (h : MvPolynomial (Fin n) R) :
    presentedAlgebraToLocalizedPresentedAlgebra (f := f) h
        (Ideal.Quotient.mk PresentedIdeal h) *
      Ideal.Quotient.mk
        (Ideal.span
          (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
            {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
        (X (Fin.last n)) =
      1 := by
  -- The last displayed relation is exactly `h * X_last - 1`.
  rw [presentedAlgebraToLocalizedPresentedAlgebra_mk]
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _)]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span (Set.mem_union_right _ rfl)

/-- Helper for Chap10 Lemma 10 136 10: the image of `h` is a unit in the displayed quotient. -/
private theorem isUnit_presentedAlgebraToLocalizedPresentedAlgebra_mk
    (h : MvPolynomial (Fin n) R) :
    IsUnit
      (presentedAlgebraToLocalizedPresentedAlgebra (f := f) h
        (Ideal.Quotient.mk PresentedIdeal h)) := by
  -- The previous multiplication identity provides an explicit inverse.
  rw [isUnit_iff_exists_inv]
  exact
    ⟨Ideal.Quotient.mk
      (Ideal.span
        (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
          {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
      (X (Fin.last n)),
      image_presentedAlgebraToLocalizedPresentedAlgebra_mul_last (f := f) h⟩

/-- Helper for Chap10 Lemma 10 136 10: the displayed quotient is an algebra over the original
presentation quotient through the quotient-map bridge. -/
noncomputable local instance instLocalizedPresentedAlgebraPresentedAlgebraAlgebra
    (h : MvPolynomial (Fin n) R) :
    Algebra PresentedAlgebra (LocalizedPresentedAlgebra h) :=
  (presentedAlgebraToLocalizedPresentedAlgebra (f := f) h).toRingHom.toAlgebra

/-- Helper for Chap10 Lemma 10 136 10: every power of the localized element maps to a unit in the
displayed inverse-adjoining quotient. -/
private theorem isUnit_presentedAlgebraToLocalizedPresentedAlgebra_mem_powers
    (h : MvPolynomial (Fin n) R) :
    ∀ y : Submonoid.powers (Ideal.Quotient.mk PresentedIdeal h),
      IsUnit (presentedAlgebraToLocalizedPresentedAlgebra (f := f) h y) := by
  -- Elements of the away submonoid are powers of the distinguished class, whose image is a unit.
  intro y
  rcases y with ⟨_, m, rfl⟩
  rw [map_pow]
  exact (isUnit_presentedAlgebraToLocalizedPresentedAlgebra_mk (f := f) h).pow m

/-- Helper for Chap10 Lemma 10 136 10: the forward map from the localization away from `h` to the
displayed quotient obtained by adjoining an inverse of `h`. -/
private noncomputable def localizationAwayToLocalizedPresentedAlgebra
    (h : MvPolynomial (Fin n) R) :
    Localization.Away (Ideal.Quotient.mk PresentedIdeal h) →ₐ[R]
      LocalizedPresentedAlgebra h :=
  IsLocalization.liftAlgHom
    (M := Submonoid.powers (Ideal.Quotient.mk PresentedIdeal h))
    (S := Localization.Away (Ideal.Quotient.mk PresentedIdeal h))
    (P := LocalizedPresentedAlgebra h)
    (f := presentedAlgebraToLocalizedPresentedAlgebra (f := f) h)
    (isUnit_presentedAlgebraToLocalizedPresentedAlgebra_mem_powers (f := f) h)

/-- Helper for Chap10 Lemma 10 136 10: the forward localization map agrees with the quotient-map
bridge on elements of the presented quotient. -/
private theorem localizationAwayToLocalizedPresentedAlgebra_algebraMap
    (h : MvPolynomial (Fin n) R) (x : PresentedAlgebra) :
    localizationAwayToLocalizedPresentedAlgebra (f := f) h
      (algebraMap PresentedAlgebra
        (Localization.Away (Ideal.Quotient.mk PresentedIdeal h)) x) =
      presentedAlgebraToLocalizedPresentedAlgebra (f := f) h x := by
  -- This is the defining computation rule for the localization lift on the source algebra.
  simpa [localizationAwayToLocalizedPresentedAlgebra, IsLocalization.liftAlgHom_apply] using
    (IsLocalization.lift_eq
      (M := Submonoid.powers (Ideal.Quotient.mk PresentedIdeal h))
      (S := Localization.Away (Ideal.Quotient.mk PresentedIdeal h))
      (g := (presentedAlgebraToLocalizedPresentedAlgebra (f := f) h).toRingHom)
      (isUnit_presentedAlgebraToLocalizedPresentedAlgebra_mem_powers (f := f) h) x)

/-- Helper for Chap10 Lemma 10 136 10: the forward localization map also has the expected
computation when the source map is written as `Algebra.algHom`. -/
private theorem localizationAwayToLocalizedPresentedAlgebra_algHom
    (h : MvPolynomial (Fin n) R) (x : PresentedAlgebra) :
    localizationAwayToLocalizedPresentedAlgebra (f := f) h
      ((Algebra.algHom R PresentedAlgebra
        (Localization.Away (Ideal.Quotient.mk PresentedIdeal h))) x) =
      presentedAlgebraToLocalizedPresentedAlgebra (f := f) h x := by
  -- This is only a spelling adapter for `IsLocalization.algHom_ext`.
  exact localizationAwayToLocalizedPresentedAlgebra_algebraMap (f := f) h x

/-- Helper for Chap10 Lemma 10 136 10: the evaluator from the displayed polynomial ring to the
away-localization sends old variables to localized quotient variables and the last variable to the
inverse of `h`. -/
private noncomputable def localizationAwayDisplayedEval
    (h : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R]
      Localization.Away (Ideal.Quotient.mk PresentedIdeal h) :=
  MvPolynomial.aeval
    (Fin.lastCases
      (IsLocalization.Away.invSelf (S := Localization.Away (Ideal.Quotient.mk PresentedIdeal h))
        (Ideal.Quotient.mk PresentedIdeal h))
      (fun i : Fin n ↦
        algebraMap PresentedAlgebra
          (Localization.Away (Ideal.Quotient.mk PresentedIdeal h))
          (Ideal.Quotient.mk PresentedIdeal (X i))))

/-- Helper for Chap10 Lemma 10 136 10: evaluation of a renamed old polynomial is the localized
image of its class in the original presented algebra. -/
private theorem localizationAwayDisplayedEval_rename
    (h a : MvPolynomial (Fin n) R) :
    localizationAwayDisplayedEval (f := f) h (rename Fin.castSuccEmb a) =
      algebraMap PresentedAlgebra (Localization.Away (Ideal.Quotient.mk PresentedIdeal h))
        (Ideal.Quotient.mk PresentedIdeal a) := by
  -- Generator extensionality identifies both algebra maps from the old polynomial ring.
  let L := Localization.Away (Ideal.Quotient.mk PresentedIdeal h)
  let evalOld : MvPolynomial (Fin n) R →ₐ[R] L :=
    (localizationAwayDisplayedEval (f := f) h).comp (MvPolynomial.rename Fin.castSuccEmb)
  let quotientOld : MvPolynomial (Fin n) R →ₐ[R] L :=
    (IsScalarTower.toAlgHom R PresentedAlgebra L).comp
      (Ideal.Quotient.mkₐ R PresentedIdeal)
  have hmaps : evalOld = quotientOld := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simp [evalOld, quotientOld, localizationAwayDisplayedEval]
    rfl
  simpa [evalOld, quotientOld] using congrArg (fun φ : MvPolynomial (Fin n) R →ₐ[R] L ↦ φ a) hmaps

/-- Helper for Chap10 Lemma 10 136 10: the displayed inverse-adjoining ideal is killed by the
localization evaluator. -/
private theorem displayedIdeal_le_awayEval_ker
    (h : MvPolynomial (Fin n) R) :
    Ideal.span
        (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
          {rename Fin.castSuccEmb h * X (Fin.last n) - 1}) ≤
      RingHom.ker (localizationAwayDisplayedEval (f := f) h).toRingHom := by
  -- Check the old relations using the original quotient, and the new relation using the
  -- localization inverse.
  rw [Ideal.span_le]
  intro p hp
  change localizationAwayDisplayedEval (f := f) h p = 0
  rcases hp with hp | hp
  · rcases hp with ⟨i, rfl⟩
    have hrel :
        (Ideal.Quotient.mk PresentedIdeal (f i) : PresentedAlgebra) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨i, rfl⟩)
    rw [localizationAwayDisplayedEval_rename]
    rw [hrel, map_zero]
  · rw [Set.mem_singleton_iff.mp hp]
    rw [map_sub, map_mul, map_one]
    rw [localizationAwayDisplayedEval_rename]
    let L := Localization.Away (Ideal.Quotient.mk PresentedIdeal h)
    have hzero :
        algebraMap PresentedAlgebra L (Ideal.Quotient.mk PresentedIdeal h) *
            IsLocalization.Away.invSelf
              (S := L) (Ideal.Quotient.mk PresentedIdeal h) -
          1 = 0 := by
      rw [IsLocalization.Away.mul_invSelf, sub_self]
    simpa only [localizationAwayDisplayedEval, aeval_X, Fin.lastCases_last] using hzero

/-- Helper for Chap10 Lemma 10 136 10: the displayed quotient maps back to the localization by
evaluating the last variable as the inverse of `h`. -/
private noncomputable def localizedPresentedAlgebraToLocalizationAway
    (h : MvPolynomial (Fin n) R) :
    LocalizedPresentedAlgebra h →ₐ[R]
      Localization.Away (Ideal.Quotient.mk PresentedIdeal h) :=
  Ideal.Quotient.liftₐ
    (Ideal.span
      (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
        {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
    (localizationAwayDisplayedEval (f := f) h)
    (fun _a ha ↦ displayedIdeal_le_awayEval_ker (f := f) h ha)

/-- Helper for Chap10 Lemma 10 136 10: the reverse map is computed by the displayed evaluator on
polynomial representatives. -/
private theorem localizedPresentedAlgebraToLocalizationAway_mk
    (h : MvPolynomial (Fin n) R) (a : MvPolynomial (Fin (n + 1)) R) :
    localizedPresentedAlgebraToLocalizationAway (f := f) h
      (Ideal.Quotient.mk
        (Ideal.span
          (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
            {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
        a) =
      localizationAwayDisplayedEval (f := f) h a := by
  -- This is the computation rule for the quotient lift.
  rfl

/-- Helper for Chap10 Lemma 10 136 10: the reverse map after the original quotient-map bridge is
the canonical map into the localization away from `h`. -/
private theorem localizedPresentedAlgebraToLocalizationAway_comp_presentedAlgebraToLocalizedPresentedAlgebra
    (h : MvPolynomial (Fin n) R) (x : PresentedAlgebra) :
    localizedPresentedAlgebraToLocalizationAway (f := f) h
        (presentedAlgebraToLocalizedPresentedAlgebra (f := f) h x) =
      algebraMap PresentedAlgebra
        (Localization.Away (Ideal.Quotient.mk PresentedIdeal h)) x := by
  -- Reduce to a polynomial representative, where the two quotient maps have explicit formulas.
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := PresentedIdeal) x
  rw [presentedAlgebraToLocalizedPresentedAlgebra_mk]
  rw [localizedPresentedAlgebraToLocalizationAway_mk]
  exact localizationAwayDisplayedEval_rename (f := f) h a

/-- Helper for Chap10 Lemma 10 136 10: the reverse-after-bridge computation with the source map
written as `Algebra.algHom`. -/
private theorem localizedPresentedAlgebraToLocalizationAway_comp_presentedAlgebraToLocalizedPresentedAlgebra_algHom
    (h : MvPolynomial (Fin n) R) (x : PresentedAlgebra) :
    localizedPresentedAlgebraToLocalizationAway (f := f) h
        (presentedAlgebraToLocalizedPresentedAlgebra (f := f) h x) =
      (Algebra.algHom R PresentedAlgebra
        (Localization.Away (Ideal.Quotient.mk PresentedIdeal h))) x := by
  -- This is the same bridge computation in the normal form used by localization extensionality.
  exact localizedPresentedAlgebraToLocalizationAway_comp_presentedAlgebraToLocalizedPresentedAlgebra
    (f := f) h x

/-- Helper for Chap10 Lemma 10 136 10: the reverse map composed with the forward localization lift
is the identity on the away-localization. -/
private theorem localizedPresentedAlgebraToLocalizationAway_comp_localizationAwayToLocalizedPresentedAlgebra
    (h : MvPolynomial (Fin n) R) :
    (localizedPresentedAlgebraToLocalizationAway (f := f) h).comp
        (localizationAwayToLocalizedPresentedAlgebra (f := f) h) =
      AlgHom.id R (Localization.Away (Ideal.Quotient.mk PresentedIdeal h)) := by
  -- Localization extensionality reduces the composite identity to the source presented quotient.
  refine IsLocalization.algHom_ext
    (Submonoid.powers (Ideal.Quotient.mk PresentedIdeal h)) ?_
  ext x
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [localizationAwayToLocalizedPresentedAlgebra_algHom]
  exact localizedPresentedAlgebraToLocalizationAway_comp_presentedAlgebraToLocalizedPresentedAlgebra_algHom
      (f := f) h x

/-- Helper for Chap10 Lemma 10 136 10: the quotient-map bridge sends an old variable to the
corresponding displayed old variable. -/
private theorem presentedAlgebraToLocalizedPresentedAlgebra_mk_X_castSucc
    (h : MvPolynomial (Fin n) R) (i : Fin n) :
    presentedAlgebraToLocalizedPresentedAlgebra (f := f) h
        (Ideal.Quotient.mk PresentedIdeal (X i)) =
      Ideal.Quotient.mk
        (Ideal.span
          (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
            {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
        (X (Fin.castSucc i)) := by
  -- This is the variable case of the quotient-map computation rule.
  simpa using presentedAlgebraToLocalizedPresentedAlgebra_mk (f := f) h (X i)

/-- Helper for Chap10 Lemma 10 136 10: the forward localization map sends the canonical inverse of
`h` to the displayed last variable. -/
private theorem localizationAwayToLocalizedPresentedAlgebra_invSelf
    (h : MvPolynomial (Fin n) R) :
    localizationAwayToLocalizedPresentedAlgebra (f := f) h
        (IsLocalization.Away.invSelf
          (S := Localization.Away (Ideal.Quotient.mk PresentedIdeal h))
          (Ideal.Quotient.mk PresentedIdeal h)) =
      Ideal.Quotient.mk
        (Ideal.span
          (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
            {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
        (X (Fin.last n)) := by
  -- Both sides are right inverses to the image of `h`; commutativity gives uniqueness.
  let a :=
    presentedAlgebraToLocalizedPresentedAlgebra (f := f) h
      (Ideal.Quotient.mk PresentedIdeal h)
  let b :=
    localizationAwayToLocalizedPresentedAlgebra (f := f) h
      (IsLocalization.Away.invSelf
        (S := Localization.Away (Ideal.Quotient.mk PresentedIdeal h))
        (Ideal.Quotient.mk PresentedIdeal h))
  let d :=
    Ideal.Quotient.mk
      (Ideal.span
        (Set.range (fun i : Fin c ↦ rename Fin.castSuccEmb (f i)) ∪
          {rename Fin.castSuccEmb h * X (Fin.last n) - 1}))
      (X (Fin.last n))
  have hab : a * b = 1 := by
    -- Apply the forward map to the localization inverse relation.
    have hrel := congrArg (localizationAwayToLocalizedPresentedAlgebra (f := f) h)
        (IsLocalization.Away.mul_invSelf
          (S := Localization.Away (Ideal.Quotient.mk PresentedIdeal h))
          (Ideal.Quotient.mk PresentedIdeal h))
    rw [map_mul, map_one] at hrel
    rw [localizationAwayToLocalizedPresentedAlgebra_algebraMap] at hrel
    exact hrel
  have had : a * d = 1 := by
    -- The displayed quotient relation says the last variable is another inverse of `h`.
    simpa [a, d] using image_presentedAlgebraToLocalizedPresentedAlgebra_mul_last (f := f) h
  calc
    b = 1 * b := by rw [one_mul]
    _ = (a * d) * b := by rw [had]
    _ = d * (a * b) := by rw [mul_comm a d, mul_assoc]
    _ = d * 1 := by rw [hab]
    _ = d := by rw [mul_one]

/-- Helper for Chap10 Lemma 10 136 10: the forward localization lift composed with the reverse
evaluator is the identity on the displayed inverse-adjoining quotient. -/
private theorem localizationAwayToLocalizedPresentedAlgebra_comp_localizedPresentedAlgebraToLocalizationAway
    (h : MvPolynomial (Fin n) R) :
    (localizationAwayToLocalizedPresentedAlgebra (f := f) h).comp
        (localizedPresentedAlgebraToLocalizationAway (f := f) h) =
      AlgHom.id R (LocalizedPresentedAlgebra h) := by
  -- Quotient and polynomial-generator extensionality reduce the identity to old variables and the
  -- single new inverse variable.
  refine Ideal.Quotient.algHom_ext R ?_
  refine MvPolynomial.algHom_ext fun j ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply,
      localizedPresentedAlgebraToLocalizationAway_mk, localizationAwayDisplayedEval,
      aeval_X, Fin.lastCases_last, localizationAwayToLocalizedPresentedAlgebra_invSelf]
  · rw [AlgHom.comp_apply]
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply,
      localizedPresentedAlgebraToLocalizationAway_mk, localizationAwayDisplayedEval,
      aeval_X, Fin.lastCases_castSucc, localizationAwayToLocalizedPresentedAlgebra_algebraMap]
      using presentedAlgebraToLocalizedPresentedAlgebra_mk_X_castSucc (f := f) h i

/-- Chap10 Lemma 10 136 10 support: the canonical localization of the presented quotient is
algebra-equivalent to the displayed quotient obtained by adjoining an inverse variable. -/
private theorem nonempty_localizationAway_presentedAlgebra_algEquiv
    (h : MvPolynomial (Fin n) R) :
    Nonempty (Localization.Away (Ideal.Quotient.mk PresentedIdeal h) ≃ₐ[R]
      LocalizedPresentedAlgebra h) := by
  -- Route correction: instead of comparing the full composed-presentation relation span, build
  -- the two maps directly from the quotient and localization universal properties.
  refine ⟨AlgEquiv.ofAlgHom
    (localizationAwayToLocalizedPresentedAlgebra (f := f) h)
    (localizedPresentedAlgebraToLocalizationAway (f := f) h) ?_ ?_⟩
  · exact localizationAwayToLocalizedPresentedAlgebra_comp_localizedPresentedAlgebraToLocalizationAway
      (f := f) h
  · exact localizedPresentedAlgebraToLocalizationAway_comp_localizationAwayToLocalizedPresentedAlgebra
      (f := f) h

/-- Helper for Chap10 Lemma 10 136 10: relative global complete intersections are preserved by
transport across an algebra equivalence over the base. -/
private theorem isRelativeGlobalCompleteIntersection_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (hA : Algebra.IsRelativeGlobalCompleteIntersection R A) (e : A ≃ₐ[R] B) :
    Algebra.IsRelativeGlobalCompleteIntersection R B := by
  rcases hA.exists_presentation with ⟨n, c, P, hP⟩
  -- Transport the presentation witness through the algebra equivalence.
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P.ofAlgEquiv e) ?_
  intro p hp
  let ep : p.asIdeal.Fiber B ≃ₐ[R] p.asIdeal.Fiber A :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[R] p.asIdeal.ResidueField)
      e.symm
  have hpA : Nonempty (PrimeSpectrum (p.asIdeal.Fiber A)) := by
    -- Nonemptiness of the fiber is invariant under the induced tensor-product equivalence.
    have hp_nontrivial : Nontrivial (p.asIdeal.Fiber B) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    letI : Nontrivial (p.asIdeal.Fiber B) := hp_nontrivial
    have hpA_nontrivial : Nontrivial (p.asIdeal.Fiber A) :=
      RingHom.domain_nontrivial ep.symm.toRingHom
    exact PrimeSpectrum.nonempty_iff_nontrivial.mpr hpA_nontrivial
  -- Compare fiber dimensions across the equivalence, then reuse the source presentation witness.
  calc
    ringKrullDim (p.asIdeal.Fiber B) = ringKrullDim (p.asIdeal.Fiber A) := by
      simpa [ep] using (ringKrullDim_eq_of_ringEquiv ep.toRingEquiv)
    _ = P.dimension := hP p hpA
    _ = (P.ofAlgEquiv e).dimension := by
      exact_mod_cast P.dimension_ofAlgEquiv e

/-- Helper for Chap10 Lemma 10 136 10: membership in a bounded relative-dimension locus can be
shrunk to a basic open still contained in that locus. -/
private theorem exists_basicOpen_subset_relativeDimensionAtLELocus_of_mem
    (q : PrimeSpectrum PresentedAlgebra)
    (hq : q ∈ relativeDimensionAtLELocus R PresentedAlgebra (n - c)) :
    ∃ g : PresentedAlgebra,
      g ∉ q.asIdeal ∧
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) ⊆
          relativeDimensionAtLELocus R PresentedAlgebra (n - c) := by
  -- Start from the owner-level open-neighborhood theorem for the bounded locus.
  obtain ⟨U, hU⟩ :=
    exists_openNhdsOf_mem_relativeDimensionAtLELocus
      (R := R) (S := PresentedAlgebra) (n := n - c) q hq
  -- Refine that open neighborhood by a standard affine basic open around `q`.
  obtain ⟨_, ⟨g, rfl⟩, hq_basic, hbasic_subset⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.1.2 q U.2
  refine ⟨g, ?_, ?_⟩
  · simpa [PrimeSpectrum.mem_basicOpen] using hq_basic
  · intro q' hq'
    exact hU q' (hbasic_subset hq')

/-- Helper for Chap10 Lemma 10 136 10: an equality of relative dimension at a point can be
shrunk to a basic open contained in the corresponding bounded relative-dimension locus. -/
private theorem exists_basicOpen_subset_relativeDimensionAtLELocus_of_relativeDimensionAt_eq
    (q : PrimeSpectrum PresentedAlgebra)
    (hdim : relativeDimensionAt R PresentedAlgebra q = (n - c : WithBot ℕ∞)) :
    ∃ g : PresentedAlgebra,
      g ∉ q.asIdeal ∧
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) ⊆
          relativeDimensionAtLELocus R PresentedAlgebra (n - c) := by
  -- Convert the equality into membership in the bounded locus and use the reusable shrink.
  apply exists_basicOpen_subset_relativeDimensionAtLELocus_of_mem (f := f)
  rw [mem_relativeDimensionAtLELocus]
  rw [hdim]

/-- Helper for Chap10 Lemma 10 136 10: an element congruent to one modulo the ideal extended
from a prime of the base maps to a unit in the corresponding fiber of any target algebra. -/
private theorem isUnit_fiber_tmul_of_quotient_mk_eq_one_of_algebra
    {S : Type*} [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) {g : S}
    (hg : Ideal.Quotient.mk (Ideal.map (algebraMap R S) p.asIdeal) g = 1) :
    IsUnit (1 ⊗ₜ[R] g : p.asIdeal.Fiber S) := by
  -- Compare the quotient by the extended ideal with the tensor by `R / p`.
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p.asIdeal
  have hquot :
      ((1 : R ⧸ p.asIdeal) ⊗ₜ[R] g :
        (R ⧸ p.asIdeal) ⊗[R] S) = 1 := by
    simpa [e] using congrArg e hg
  -- Base-change the equality from `R / p` to the residue field `κ(p)`.
  let φ : (R ⧸ p.asIdeal) →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (R ⧸ p.asIdeal) p.asIdeal.ResidueField
  let Φ : ((R ⧸ p.asIdeal) ⊗[R] S) →ₐ[R]
      (p.asIdeal.ResidueField ⊗[R] S) :=
    Algebra.TensorProduct.map φ (AlgHom.id R S)
  have hfiber_eq_one :
      (1 ⊗ₜ[R] g : p.asIdeal.Fiber S) = 1 := by
    simpa [Φ, φ] using congrArg Φ hquot
  -- Once the fiber image is literally `1`, the unit condition is immediate.
  rw [hfiber_eq_one]
  exact isUnit_one

/-- Helper for Chap10 Lemma 10 136 10: an element congruent to one modulo the ideal extended
from a prime of the base maps to a unit in that fiber. -/
private theorem isUnit_fiber_tmul_of_quotient_mk_eq_one
    (p : PrimeSpectrum R) {g : PresentedAlgebra}
    (hg : Ideal.Quotient.mk (Ideal.map (algebraMap R PresentedAlgebra) p.asIdeal) g = 1) :
    IsUnit (1 ⊗ₜ[R] g : p.asIdeal.Fiber PresentedAlgebra) := by
  -- Specialize the algebra-level fiber-unit criterion to the presented algebra.
  exact isUnit_fiber_tmul_of_quotient_mk_eq_one_of_algebra (R := R) p hg

/-- Helper for Chap10 Lemma 10 136 10: the relative dimension at a point is bounded by the
Krull dimension of the whole fiber over its contraction. -/
private lemma relativeDimensionAt_le_ringKrullDim_fiber_of_comap
    {S : Type*} [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    relativeDimensionAt R S q ≤
      ringKrullDim ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber S) := by
  -- Rewrite relative dimension as the dimension of the local fiber ring.
  calc
    relativeDimensionAt R S q = ringKrullDim (fiberLocalRingAt R S q) := rfl
    _ = ((fiberPrimeAt R S q).asIdeal.height : WithBot ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height
        (fiberPrimeAt R S q).asIdeal (fiberLocalRingAt R S q)]
    _ ≤ ringKrullDim ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.Fiber S) := by
      exact Ideal.height_le_ringKrullDim_of_ne_top (I := (fiberPrimeAt R S q).asIdeal)
        (fiberPrimeAt R S q).isPrime.ne_top

/-- Helper for Chap10 Lemma 10 136 10: the complement of the zero locus of a finite set is the
union of the corresponding basic opens. -/
private lemma compl_zeroLocus_finset_eq_iUnion_basicOpen
    {S : Type*} [CommRing S] (s : Finset S) :
    (PrimeSpectrum.zeroLocus ((s : Set S)) : Set (PrimeSpectrum S))ᶜ =
      ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S)) := by
  classical
  -- A prime avoids the finite set exactly when it avoids at least one element of it.
  ext q
  constructor
  · intro hq
    by_contra hnot
    apply hq
    refine (PrimeSpectrum.mem_zeroLocus q (s : Set S)).2 ?_
    intro a has
    by_contra haq
    exact hnot
      (Set.mem_iUnion.2
        ⟨a, Set.mem_iUnion.2 ⟨has, (PrimeSpectrum.mem_basicOpen a q).2 haq⟩⟩)
  · intro hq
    simp only [Set.mem_iUnion] at hq
    rcases hq with ⟨a, ha⟩
    rcases ha with ⟨has, hqa⟩
    exact fun hz ↦ (PrimeSpectrum.mem_basicOpen a q).1 hqa
      ((PrimeSpectrum.mem_zeroLocus q (s : Set S)).1 hz has)

/-- Helper for Chap10 Lemma 10 136 10: a finite basic-open cover of a closed locus produces a
single basic open inside the cover whose defining element is one modulo the closed ideal. -/
private lemma exists_modEq_one_of_zeroLocus_subset_finite_basicOpen
    {S : Type*} [CommRing S] (J : Ideal S) (s : Finset S)
    (hcover : PrimeSpectrum.zeroLocus (J : Set S) ⊆
      ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S))) :
    ∃ g : S,
      g ∈ Ideal.span (s : Set S) ∧
        Ideal.Quotient.mk J g = 1 ∧
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
            ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S)) := by
  have hdisjoint :
      PrimeSpectrum.zeroLocus ((J ⊔ Ideal.span (s : Set S) : Ideal S) : Set S) = ∅ := by
    -- If a prime contained both `J` and every element of `s`, it would contradict the cover.
    ext q
    constructor
    · intro hq
      have hq_sup : J ⊔ Ideal.span (s : Set S) ≤ q.asIdeal :=
        (PrimeSpectrum.mem_zeroLocus q
          ((J ⊔ Ideal.span (s : Set S) : Ideal S) : Set S)).1 hq
      have hqJ : q ∈ PrimeSpectrum.zeroLocus (J : Set S) := by
        exact (PrimeSpectrum.mem_zeroLocus q (J : Set S)).2 fun x hx ↦
          hq_sup ((le_sup_left : J ≤ J ⊔ Ideal.span (s : Set S)) hx)
      have hs_le : Ideal.span (s : Set S) ≤ q.asIdeal := by
        intro x hx
        exact hq_sup
          ((le_sup_right : Ideal.span (s : Set S) ≤ J ⊔ Ideal.span (s : Set S)) hx)
      have hq_cover := hcover hqJ
      simp only [Set.mem_iUnion] at hq_cover
      rcases hq_cover with ⟨a, ha⟩
      rcases ha with ⟨has, hqa⟩
      exact False.elim
        ((PrimeSpectrum.mem_basicOpen a q).1 hqa (hs_le (Ideal.subset_span has)))
    · intro hq
      cases hq
  have htop : J ⊔ Ideal.span (s : Set S) = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]
    exact hdisjoint
  have hone : (1 : S) ∈ J ⊔ Ideal.span (s : Set S) := by
    rw [htop]
    exact trivial
  rcases (Submodule.mem_sup.mp hone) with ⟨j, hj, g, hg, hjg⟩
  refine ⟨g, hg, ?_, ?_⟩
  · -- The decomposition `1 = j + g` gives `g = 1` in the quotient by `J`.
    have hcong := congrArg (Ideal.Quotient.mk J) hjg
    have hj0 : Ideal.Quotient.mk J j = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hj
    rw [map_add, hj0, zero_add] at hcong
    exact hcong
  · -- Since `g` lies in the span of `s`, any prime avoiding `g` avoids some member of `s`.
    intro q hqg
    by_contra hnot
    have hs_le : Ideal.span (s : Set S) ≤ q.asIdeal := by
      refine Ideal.span_le.mpr ?_
      intro a ha
      by_contra haq
      exact hnot
        (Set.mem_iUnion.2
          ⟨a, Set.mem_iUnion.2 ⟨ha, (PrimeSpectrum.mem_basicOpen a q).2 haq⟩⟩)
    exact (PrimeSpectrum.mem_basicOpen g q).1 hqg (hs_le hg)

/-- Helper for Chap10 Lemma 10 136 10: the quotient presentation of the local fiber ring is
unchanged after localizing the target away from an element. -/
private lemma ringKrullDim_quotient_localizationAway_comap
    {S : Type*} [CommRing S] [Algebra R S]
    (g : S) (qg : PrimeSpectrum (Localization.Away g)) :
    let q := PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg
    ringKrullDim
        ((Localization.AtPrime qg.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
            (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)) =
      ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (Ideal.comap (algebraMap R S) q.asIdeal)) := by
  intro q
  -- Compare the two local rings by localizing first at `g` and then at the pulled-back prime.
  let qI : Ideal S := Ideal.comap (algebraMap S (Localization.Away g)) qg.asIdeal
  have hqI : q.asIdeal = Ideal.comap (AlgEquiv.refl : S ≃ₐ[S] S) qI := by
    have hq : q.asIdeal = qI := by
      simpa [qI, q] using
        (PrimeSpectrum.comap_asIdeal (f := algebraMap S (Localization.Away g)) qg)
    rw [hq]
    exact (Ideal.comap_id qI).symm
  let eSource : Localization.AtPrime q.asIdeal ≃ₐ[S] Localization.AtPrime qI :=
    Localization.localAlgEquiv q.asIdeal qI (AlgEquiv.refl : S ≃ₐ[S] S) hqI
  let eTower : Localization.AtPrime qI ≃ₐ[S] Localization.AtPrime qg.asIdeal :=
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (M := Submonoid.powers g) qg.asIdeal)
  let e : Localization.AtPrime q.asIdeal ≃ₐ[S] Localization.AtPrime qg.asIdeal :=
    eSource.trans eTower
  let Iq : Ideal (Localization.AtPrime q.asIdeal) :=
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
      (Ideal.comap (algebraMap R S) q.asIdeal)
  let Ig : Ideal (Localization.AtPrime qg.asIdeal) :=
    Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
      (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)
  have hbase :
      Ideal.comap (algebraMap R S) q.asIdeal =
        Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal := by
    simpa [q, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap,
      IsScalarTower.algebraMap_eq R S (Localization.Away g)]
  have heR : e.toRingHom.comp (algebraMap R (Localization.AtPrime q.asIdeal)) =
      algebraMap R (Localization.AtPrime qg.asIdeal) := by
    ext r
    change e ((algebraMap R (Localization.AtPrime q.asIdeal)) r) =
      algebraMap R (Localization.AtPrime qg.asIdeal) r
    calc
      e ((algebraMap R (Localization.AtPrime q.asIdeal)) r) =
          e (algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S r)) := by
            rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal)]
      _ = algebraMap S (Localization.AtPrime qg.asIdeal) (algebraMap R S r) := by
            exact e.commutes (algebraMap R S r)
      _ = algebraMap R (Localization.AtPrime qg.asIdeal) r := by
            rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime qg.asIdeal)]
  have hmap : Ig = Ideal.map e.toRingHom Iq := by
    calc
      Ig = Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
          (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal) := rfl
      _ = Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
          (Ideal.comap (algebraMap R S) q.asIdeal) := by
            rw [← hbase]
      _ = Ideal.map (e.toRingHom.comp (algebraMap R (Localization.AtPrime q.asIdeal)))
          (Ideal.comap (algebraMap R S) q.asIdeal) := by
            rw [heR]
      _ = Ideal.map e.toRingHom Iq := by
            rw [Ideal.map_map]
  let eQuot :
      ((Localization.AtPrime q.asIdeal) ⧸ Iq) ≃+*
        ((Localization.AtPrime qg.asIdeal) ⧸ Ig) :=
    Ideal.quotientEquiv Iq Ig e.toRingEquiv hmap
  -- Krull dimension is invariant under the quotient ring equivalence.
  exact (ringKrullDim_eq_of_ringEquiv eQuot).symm

/-- Helper for Chap10 Lemma 10 136 10: relative dimension is unchanged when computed after a
localization away from an element and then pulled back by the localization comap. -/
private lemma relativeDimensionAt_localizationAway_comap
    {S : Type*} [CommRing S] [Algebra R S]
    (g : S) (qg : PrimeSpectrum (Localization.Away g)) :
    relativeDimensionAt R (Localization.Away g) qg =
      relativeDimensionAt R S (PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg) := by
  -- Rewrite both sides as the same quotient of corresponding localizations.
  let q := PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qg
  calc
    relativeDimensionAt R (Localization.Away g) qg =
        ringKrullDim (fiberLocalRingAt R (Localization.Away g) qg) := rfl
    _ = ringKrullDim
        ((Localization.AtPrime qg.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime qg.asIdeal))
            (Ideal.comap (algebraMap R (Localization.Away g)) qg.asIdeal)) := by
          rw [← ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
            (R := R) (S := Localization.Away g) qg]
    _ = ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (Ideal.comap (algebraMap R S) q.asIdeal)) := by
          exact ringKrullDim_quotient_localizationAway_comap (R := R) (S := S) g qg
    _ = ringKrullDim (fiberLocalRingAt R S q) := by
          rw [ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
            (R := R) (S := S) q]
    _ = relativeDimensionAt R S q := rfl

/-- Helper for Chap10 Lemma 10 136 10: the order height of the fiber prime can be read as the
height of the corresponding point in any explicitly named raw prime-spectrum fiber. -/
private lemma fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq
    {S : Type*} [CommRing S] [Algebra R S]
    {p : PrimeSpectrum R} (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Order.height (fiberPrimeAt R S q) =
      Order.height
        (⟨q, hq⟩ : (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' {p}) := by
  -- Replace the named base point by the canonical contraction so the fiber equivalence is
  -- definitionally the one used in `fiberPrimeAt`.
  subst p
  let p0 : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let qOver : ↑(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p0}) := ⟨q, rfl⟩
  let ePre : ↑(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p0}) ≃o
      PrimeSpectrum (p0.asIdeal.Fiber S) :=
    PrimeSpectrum.preimageOrderIsoFiber R S p0
  have heq : ePre qOver = fiberPrimeAt R S q := rfl
  calc
    Order.height (fiberPrimeAt R S q) = Order.height (ePre qOver) := by
      exact congrArg Order.height heq.symm
    _ = Order.height qOver := Order.height_orderIso ePre qOver
    _ =
        Order.height
          (⟨q, rfl⟩ : (PrimeSpectrum.comap (algebraMap R S)) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R S) q}) := rfl

/-- Helper for Chap10 Lemma 10 136 10: pointwise relative-dimension bounds over a fixed base
prime bound the Krull dimension of the whole fiber over that base prime. -/
private lemma ringKrullDim_fiber_le_of_forall_relativeDimensionAt_le
    {S : Type*} [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (d : WithBot ℕ∞)
    (h : ∀ q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap R S) q = p →
      relativeDimensionAt R S q ≤ d) :
    ringKrullDim (p.asIdeal.Fiber S) ≤ d := by
  -- It is enough to bound the height of every maximal ideal of the fiber.
  refine (ringKrullDim_le_iff_isMaximal_height_le d).2 ?_
  intro J hJ
  let qF : PrimeSpectrum (p.asIdeal.Fiber S) := ⟨J, hJ.isPrime⟩
  let ePre : ↑(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) ≃o
      PrimeSpectrum (p.asIdeal.Fiber S) :=
    PrimeSpectrum.preimageOrderIsoFiber R S p
  let qOver := ePre.symm qF
  have hqF_height :
      ((J.height : ℕ∞) : WithBot ℕ∞) = (Order.height qOver : WithBot ℕ∞) := by
    calc
      ((J.height : ℕ∞) : WithBot ℕ∞) = (Order.height qF : WithBot ℕ∞) := by
        rw [Ideal.height_eq_primeHeight]
        rfl
      _ = (Order.height (ePre qOver) : WithBot ℕ∞) := by
        rw [show ePre qOver = qF by simp [qOver, ePre, qF]]
      _ = (Order.height qOver : WithBot ℕ∞) := by
        rw [Order.height_orderIso ePre qOver]
  have hrel_height :
      relativeDimensionAt R S qOver.1 = (Order.height qOver : WithBot ℕ∞) := by
    calc
      relativeDimensionAt R S qOver.1 =
          ringKrullDim (fiberLocalRingAt R S qOver.1) := rfl
      _ = ((fiberPrimeAt R S qOver.1).asIdeal.height : WithBot ℕ∞) := by
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height
            (fiberPrimeAt R S qOver.1).asIdeal (fiberLocalRingAt R S qOver.1)]
      _ = (Order.height (fiberPrimeAt R S qOver.1) : WithBot ℕ∞) := by
          rw [Ideal.height_eq_primeHeight]
          rfl
      _ = (Order.height qOver : WithBot ℕ∞) := by
          rw [fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq
            (R := R) (S := S) qOver.1 qOver.2]
  -- The pointwise bound at the corresponding prime of `S` is exactly the required maximal-height
  -- bound for the fiber.
  have hrel : relativeDimensionAt R S qOver.1 ≤ d := h qOver.1 qOver.2
  rwa [hqF_height, ← hrel_height]

/-- Helper for Chap10 Lemma 10 136 10: a principal open contained in the bounded
relative-dimension locus gives the needed upper bound on every localized fiber. -/
private lemma ringKrullDim_fiber_localizationAway_le_of_basicOpen_subset_relativeDimensionAtLELocus
    (g : PresentedAlgebra)
    (hbasic : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) ⊆
      relativeDimensionAtLELocus R PresentedAlgebra (n - c))
    (p : PrimeSpectrum R) :
    ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) ≤ (n - c : WithBot ℕ∞) := by
  -- Bound each prime in the localized fiber by contracting it to the original principal open.
  refine ringKrullDim_fiber_le_of_forall_relativeDimensionAt_le
    (R := R) (S := Localization.Away g) p (n - c : WithBot ℕ∞) ?_
  intro qg _hqg
  have hq_basic :
      PrimeSpectrum.comap (algebraMap PresentedAlgebra (Localization.Away g)) qg ∈
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) := by
    have hrange :
        PrimeSpectrum.comap (algebraMap PresentedAlgebra (Localization.Away g)) qg ∈
          Set.range (PrimeSpectrum.comap (algebraMap PresentedAlgebra (Localization.Away g))) :=
      ⟨qg, rfl⟩
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hrange
  have hq_le :
      relativeDimensionAt R PresentedAlgebra
          (PrimeSpectrum.comap (algebraMap PresentedAlgebra (Localization.Away g)) qg) ≤
        (n - c : WithBot ℕ∞) :=
    (mem_relativeDimensionAtLELocus (R := R) (S := PresentedAlgebra) (n - c)
      (PrimeSpectrum.comap (algebraMap PresentedAlgebra (Localization.Away g)) qg)).mp
      (hbasic hq_basic)
  rwa [relativeDimensionAt_localizationAway_comap (R := R) (S := PresentedAlgebra) g qg]

/-- Helper for Chap10 Lemma 10 136 10: a principal open contained in the bounded
relative-dimension locus has relative globally complete-intersection localization. -/
private theorem isRelativeGlobalCompleteIntersection_localizationAway_of_basicOpen_subset_relativeDimensionAtLELocus
    (g : PresentedAlgebra)
    (hbasic : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) ⊆
      relativeDimensionAtLELocus R PresentedAlgebra (n - c)) :
    Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  let P : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c) :=
    Algebra.Presentation.naive
  letI : Algebra PresentedAlgebra PresentedAlgebra := Algebra.id PresentedAlgebra
  letI : DistribMulAction PresentedAlgebra PresentedAlgebra :=
    Algebra.toModule.toDistribMulAction
  let locP : Algebra.Presentation PresentedAlgebra (Localization.Away g) Unit Unit :=
    Algebra.Presentation.localizationAway (R := PresentedAlgebra)
      (S := Localization.Away g) (r := g)
  let Q : Algebra.Presentation R (Localization.Away g)
      (Fin (Fintype.card (Unit ⊕ Fin n))) (Fin (Fintype.card (Unit ⊕ Fin c))) :=
    (locP.comp P).reindex
      (Fintype.equivFin (Unit ⊕ Fin n)).symm
      (Fintype.equivFin (Unit ⊕ Fin c)).symm
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := Q) ?_
  intro p hp
  -- The bounded-locus containment gives the upper bound for every fiber of the localization.
  have hupper :
      ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) ≤ (n - c : WithBot ℕ∞) :=
    ringKrullDim_fiber_localizationAway_le_of_basicOpen_subset_relativeDimensionAtLELocus
      (f := f) g hbasic p
  let Qp : Algebra.Presentation p.asIdeal.ResidueField
      (p.asIdeal.Fiber (Localization.Away g))
      (Fin (Fintype.card (Unit ⊕ Fin n))) (Fin (Fintype.card (Unit ⊕ Fin c))) :=
    Q.baseChange p.asIdeal.ResidueField
  rcases presentation_relation_quotient_model Qp with ⟨e⟩
  have hquot_nontrivial :
      Nontrivial
        ((MvPolynomial (Fin (Fintype.card (Unit ⊕ Fin n))) p.asIdeal.ResidueField) ⧸
          Ideal.span (Set.range Qp.relation)) := by
    -- Transport the chosen nonempty fiber through the quotient model of the base-changed
    -- localized presentation.
    let _ : Nontrivial (p.asIdeal.Fiber (Localization.Away g)) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    exact e.toEquiv.nontrivial
  have hrelation :
      ((Fintype.card (Unit ⊕ Fin n) : ℕ) : WithBot ℕ∞) ≤
        ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) +
          Fintype.card (Unit ⊕ Fin c) := by
    -- Krull's height bound applied to the polynomial quotient model gives the complementary
    -- lower bound for the localized fiber.
    let _ :
        Nontrivial
          ((MvPolynomial (Fin (Fintype.card (Unit ⊕ Fin n))) p.asIdeal.ResidueField) ⧸
            Ideal.span (Set.range Qp.relation)) :=
      hquot_nontrivial
    have hrelation_quot :
        ((Fintype.card (Unit ⊕ Fin n) : ℕ) : WithBot ℕ∞) ≤
          ringKrullDim
              ((MvPolynomial (Fin (Fintype.card (Unit ⊕ Fin n))) p.asIdeal.ResidueField) ⧸
                Ideal.span (Set.range Qp.relation)) +
            Fintype.card (Unit ⊕ Fin c) :=
      IsGlobalCompleteIntersection.mvPolynomial_quotient_le_dim_add_relation_count
        (f := Qp.relation)
    simpa [ringKrullDim_eq_of_ringEquiv e.toRingEquiv] using hrelation_quot
  have hbot : ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) ≠ ⊥ := by
    -- A nonempty spectrum makes the fiber nontrivial, so its Krull dimension is not bottom.
    intro hbot'
    let _ : Nontrivial (p.asIdeal.Fiber (Localization.Away g)) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    simpa [hbot'] using
      (ringKrullDim_nonneg_of_nontrivial (R := p.asIdeal.Fiber (Localization.Away g)))
  have htop : ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) ≠ ⊤ := by
    -- The finite upper bound rules out top.
    exact ne_of_lt <| lt_of_le_of_lt hupper <|
      WithBot.coe_lt_coe.mpr (ENat.coe_lt_top (n - c))
  let d : ℕ := ((ringKrullDim (p.asIdeal.Fiber (Localization.Away g))).unbot hbot).toNat
  have hdim : ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) = d := by
    -- Replace the finite `WithBot ℕ∞` dimension by its natural-number representative.
    have hneTop :
        (ringKrullDim (p.asIdeal.Fiber (Localization.Away g))).unbot hbot ≠ ⊤ := by
      intro h
      exact htop (by
        simpa [WithBot.coe_unbot] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) h)
    have hdim' :
        (((ringKrullDim (p.asIdeal.Fiber (Localization.Away g))).unbot hbot) :
            WithBot ℕ∞) = d := by
      simpa [d] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
    calc
      ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) =
          (ringKrullDim (p.asIdeal.Fiber (Localization.Away g))).unbot hbot := by
            exact
              (WithBot.coe_unbot (ringKrullDim (p.asIdeal.Fiber (Localization.Away g))) hbot).symm
      _ = d := hdim'
  have hupper_nat : d ≤ n - c := by
    -- Convert the upper `WithBot` inequality to an ordinary natural-number inequality.
    simpa [hdim] using hupper
  have hrelation_nat : n ≤ d + c := by
    -- The localized presentation has one extra generator and one extra relation; cancel them.
    have hrelation' :
        ((n : ℕ) : WithBot ℕ∞) + 1 ≤ ((d : ℕ) : WithBot ℕ∞) + (c + 1) := by
      simpa [hdim, Fintype.card_sum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        ← WithBot.coe_add] using hrelation
    have hrelation'' :
        ((n : ℕ) : WithBot ℕ∞) + 1 ≤ (d + c : WithBot ℕ∞) + 1 := by
      simpa [← WithBot.coe_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hrelation'
    have hlt : (n : WithBot ℕ∞) < (d + c : WithBot ℕ∞) + 1 :=
      ENat.WithBot.add_one_le_iff.mp hrelation''
    have hle : ((n : ℕ) : WithBot ℕ∞) ≤ ((d : ℕ) : WithBot ℕ∞) + c := by
      simpa using (ENat.WithBot.lt_add_one_iff).mp hlt
    have hle' :
        (((n : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((d + c : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa [← WithBot.coe_add, Nat.cast_add] using hle
    have hle_enat : (n : ℕ∞) ≤ (d + c : ℕ∞) := WithBot.coe_le_coe.mp hle'
    rwa [← ENat.coe_add, ENat.coe_le_coe] at hle_enat
  have hd_eq : d = n - c := by
    -- Source arithmetic: `n ≤ d + c` and `d ≤ n - c` force equality.
    omega
  have hfiber_dim :
      ringKrullDim (p.asIdeal.Fiber (Localization.Away g)) = (n - c : WithBot ℕ∞) := by
    simpa [hd_eq] using hdim
  have hQdim : Q.dimension = n - c := by
    -- The localized presentation adds one generator and one relation to the naive presentation.
    dsimp [Q]
    rw [Algebra.Presentation.dimension_reindex]
    simp [Algebra.Presentation.dimension]
    omega
  simpa [hQdim] using hfiber_dim

/-- Helper for Chap10 Lemma 10 136 10: a closed locus whose fibers have the expected dimension
admits a finite basic-open cover contained in the bounded relative-dimension locus. -/
private lemma exists_finite_basicOpen_cover_zeroLocus_subset_relativeDimensionAtLELocus
    (I : Ideal R)
    (hdim : ∀ p : PrimeSpectrum R,
      I ≤ p.asIdeal →
        Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
          ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ s : Finset PresentedAlgebra,
      PrimeSpectrum.zeroLocus
          (((Ideal.map (algebraMap R PresentedAlgebra) I : Ideal PresentedAlgebra) :
            Set PresentedAlgebra)) ⊆
        ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum PresentedAlgebra)) ∧
      (⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum PresentedAlgebra))) ⊆
        relativeDimensionAtLELocus R PresentedAlgebra (n - c) := by
  classical
  let J : Ideal PresentedAlgebra := Ideal.map (algebraMap R PresentedAlgebra) I
  let Z : Set (PrimeSpectrum PresentedAlgebra) :=
    PrimeSpectrum.zeroLocus ((J : Ideal PresentedAlgebra) : Set PresentedAlgebra)
  have hZcompact : IsCompact Z := by
    -- The closed zero locus is compact inside the affine prime spectrum.
    exact (PrimeSpectrum.isClosed_zeroLocus ((J : Ideal PresentedAlgebra) :
      Set PresentedAlgebra)).isCompact
  have hpoint : ∀ q : Z,
      ∃ g : PresentedAlgebra,
        q.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) ∧
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) ⊆
            relativeDimensionAtLELocus R PresentedAlgebra (n - c) := by
    intro q
    have hJ_le : J ≤ q.1.asIdeal := by
      exact (PrimeSpectrum.mem_zeroLocus q.1 ((J : Ideal PresentedAlgebra) :
        Set PresentedAlgebra)).1 q.2
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R PresentedAlgebra) q.1
    have hI_le : I ≤ p.asIdeal := by
      intro x hx
      have hxmap : algebraMap R PresentedAlgebra x ∈ q.1.asIdeal :=
        hJ_le (Ideal.mem_map_of_mem (algebraMap R PresentedAlgebra) hx)
      simpa [p, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hxmap
    have hp_nonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) := by
      -- The point `q` itself gives a prime of the fiber over its contraction.
      exact ⟨fiberPrimeAt R PresentedAlgebra q.1⟩
    have hq_locus :
        q.1 ∈ relativeDimensionAtLELocus R PresentedAlgebra (n - c) := by
      rw [mem_relativeDimensionAtLELocus]
      calc
        relativeDimensionAt R PresentedAlgebra q.1 ≤
            ringKrullDim
              ((PrimeSpectrum.comap (algebraMap R PresentedAlgebra) q.1).asIdeal.Fiber
                PresentedAlgebra) :=
          relativeDimensionAt_le_ringKrullDim_fiber_of_comap (R := R) q.1
        _ = (n - c : WithBot ℕ∞) := hdim p hI_le hp_nonempty
    obtain ⟨g, hgq, hgsubset⟩ :=
      exists_basicOpen_subset_relativeDimensionAtLELocus_of_mem (f := f) q.1 hq_locus
    exact ⟨g, (PrimeSpectrum.mem_basicOpen g q.1).2 hgq, hgsubset⟩
  choose basicOf hbasic_mem hbasic_subset using hpoint
  obtain ⟨t, ht⟩ :=
    hZcompact.elim_finite_subcover
      (fun q : Z ↦ (PrimeSpectrum.basicOpen (basicOf q) :
        Set (PrimeSpectrum PresentedAlgebra)))
      (fun q ↦ PrimeSpectrum.isOpen_basicOpen)
      (by
        intro q hq
        exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hbasic_mem ⟨q, hq⟩⟩)
  refine ⟨t.image basicOf, ?_, ?_⟩
  · -- Convert the finite subtype-indexed subcover into a finite set of generators.
    intro q hq
    have hqt := ht hq
    simp only [Set.mem_iUnion] at hqt
    rcases hqt with ⟨z, hz⟩
    rcases hz with ⟨hzt, hqz⟩
    exact Set.mem_iUnion.2
      ⟨basicOf z, Set.mem_iUnion.2 ⟨Finset.mem_image.2 ⟨z, hzt, rfl⟩, hqz⟩⟩
  · -- Each selected basic open was chosen inside the bounded relative-dimension locus.
    intro q hq
    simp only [Set.mem_iUnion] at hq
    rcases hq with ⟨a, ha⟩
    rcases ha with ⟨ha_image, hqa⟩
    rcases Finset.mem_image.1 ha_image with ⟨z, _hzt, rfl⟩
    exact hbasic_subset z hqa

/-- Helper for Chap10 Lemma 10 136 10: over a closed subset of the base with constant fiber
dimension, one can choose a principal localization congruent to one modulo that closed subset and
relative globally complete intersection. -/
private theorem exists_relativeGCI_localizationAway_eq_one_mod_ideal_of_closedSet_fiberDimension
    (I : Ideal R)
    (hdim : ∀ p : PrimeSpectrum R,
      I ≤ p.asIdeal →
        Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
          ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ g : PresentedAlgebra,
      Ideal.Quotient.mk (Ideal.map (algebraMap R PresentedAlgebra) I) g = 1 ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  -- Cover the closed locus by finitely many basic opens, all lying in the bounded locus.
  obtain ⟨s, hcover, hbounded⟩ :=
    exists_finite_basicOpen_cover_zeroLocus_subset_relativeDimensionAtLELocus
      (f := f) I hdim
  -- Replace that finite cover by one principal open whose element is `1` modulo the closed ideal.
  obtain ⟨g, _hgspan, hgmod, hgbasic⟩ :=
    exists_modEq_one_of_zeroLocus_subset_finite_basicOpen
      (J := Ideal.map (algebraMap R PresentedAlgebra) I) s hcover
  refine ⟨g, hgmod, ?_⟩
  -- The principal open remains in the bounded locus, so the localized presentation criterion
  -- gives the required relative global complete-intersection localization.
  exact isRelativeGlobalCompleteIntersection_localizationAway_of_basicOpen_subset_relativeDimensionAtLELocus
    (f := f) g (fun q hq ↦ hbounded (hgbasic hq))

/-- Helper for Chap10 Lemma 10 136 10: the exact fiber over one base prime admits a finite
basic-open cover contained in the bounded relative-dimension locus. -/
private lemma exists_finite_basicOpen_cover_fiber_subset_relativeDimensionAtLELocus
    (p : PrimeSpectrum R)
    (hdim : ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ s : Finset PresentedAlgebra,
      {q : PrimeSpectrum PresentedAlgebra |
        PrimeSpectrum.comap (algebraMap R PresentedAlgebra) q = p} ⊆
        ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum PresentedAlgebra)) ∧
      (⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum PresentedAlgebra))) ⊆
        relativeDimensionAtLELocus R PresentedAlgebra (n - c) := by
  classical
  let F : Set (PrimeSpectrum PresentedAlgebra) :=
    (PrimeSpectrum.comap (algebraMap R PresentedAlgebra)) ⁻¹' ({p} : Set (PrimeSpectrum R))
  have hFcompact : IsCompact F := by
    -- The exact fiber is homeomorphic to the spectrum of the algebraic fiber ring.
    let E : Type _ := F
    letI : CompactSpace E :=
      (PrimeSpectrum.preimageHomeomorphFiber R PresentedAlgebra p).symm.compactSpace
    have himage : IsCompact (Subtype.val '' (Set.univ : Set E)) :=
      isCompact_univ.image continuous_subtype_val
    have himage_eq : Subtype.val '' (Set.univ : Set E) = F := by
      ext q
      constructor
      · intro hq
        rcases hq with ⟨z, _hz, rfl⟩
        exact z.2
      · intro hq
        exact ⟨⟨q, hq⟩, Set.mem_univ _, rfl⟩
    simpa [himage_eq] using himage
  have hpoint : ∀ q : F,
      ∃ g : PresentedAlgebra,
        q.1 ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) ∧
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum PresentedAlgebra)) ⊆
            relativeDimensionAtLELocus R PresentedAlgebra (n - c) := by
    intro q
    have hq_locus :
        q.1 ∈ relativeDimensionAtLELocus R PresentedAlgebra (n - c) := by
      rw [mem_relativeDimensionAtLELocus]
      calc
        relativeDimensionAt R PresentedAlgebra q.1 ≤
            ringKrullDim
              ((PrimeSpectrum.comap (algebraMap R PresentedAlgebra) q.1).asIdeal.Fiber
                PresentedAlgebra) :=
          relativeDimensionAt_le_ringKrullDim_fiber_of_comap (R := R) q.1
        _ = ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) := by
          rw [q.2]
        _ = (n - c : WithBot ℕ∞) := hdim
    obtain ⟨g, hgq, hgsubset⟩ :=
      exists_basicOpen_subset_relativeDimensionAtLELocus_of_mem (f := f) q.1 hq_locus
    exact ⟨g, (PrimeSpectrum.mem_basicOpen g q.1).2 hgq, hgsubset⟩
  choose basicOf hbasic_mem hbasic_subset using hpoint
  obtain ⟨t, ht⟩ :=
    hFcompact.elim_finite_subcover
      (fun q : F ↦ (PrimeSpectrum.basicOpen (basicOf q) :
        Set (PrimeSpectrum PresentedAlgebra)))
      (fun q ↦ PrimeSpectrum.isOpen_basicOpen)
      (by
        intro q hq
        exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hbasic_mem ⟨q, hq⟩⟩)
  refine ⟨t.image basicOf, ?_, ?_⟩
  · -- Move from a finite cover indexed by exact-fiber points to the corresponding generators.
    intro q hq
    have hqF : q ∈ F := by
      simpa [F] using hq
    have hqt := ht hqF
    simp only [Set.mem_iUnion] at hqt
    rcases hqt with ⟨z, hz⟩
    rcases hz with ⟨hzt, hqz⟩
    exact Set.mem_iUnion.2
      ⟨basicOf z, Set.mem_iUnion.2 ⟨Finset.mem_image.2 ⟨z, hzt, rfl⟩, hqz⟩⟩
  · -- The pointwise shrink put every selected basic open inside the bounded locus.
    intro q hq
    simp only [Set.mem_iUnion] at hq
    rcases hq with ⟨a, ha⟩
    rcases ha with ⟨ha_image, hqa⟩
    rcases Finset.mem_image.1 ha_image with ⟨z, _hzt, rfl⟩
    exact hbasic_subset z hqa

/-- Helper for Chap10 Lemma 10 136 10: an element in the span of finitely many generators has
principal basic open contained in the union of their basic opens. -/
private lemma basicOpen_subset_iUnion_basicOpen_of_mem_span
    {S : Type*} [CommRing S] (s : Finset S) {g : S}
    (hg : g ∈ Ideal.span (s : Set S)) :
    (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
      ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S)) := by
  -- If a prime avoids none of the finite generators, then it contains their span.
  intro q hqg
  by_contra hnot
  have hs_le : Ideal.span (s : Set S) ≤ q.asIdeal := by
    refine Ideal.span_le.mpr ?_
    intro a ha
    by_contra haq
    exact hnot
      (Set.mem_iUnion.2
        ⟨a, Set.mem_iUnion.2 ⟨ha, (PrimeSpectrum.mem_basicOpen a q).2 haq⟩⟩)
  -- This contradicts that `q` avoids the span element `g`.
  exact (PrimeSpectrum.mem_basicOpen g q).1 hqg (hs_le hg)

/-- Helper for Chap10 Lemma 10 136 10: in the fiber ring, a scalar coming from `R` can be moved
to the right tensor factor as multiplication in `S`. -/
private lemma fiberTmul_algebraMap_mul
    {S : Type*} [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (r : R) (s : S) :
    ((algebraMap R p.asIdeal.ResidueField r) ⊗ₜ[R] s : p.asIdeal.Fiber S) =
      1 ⊗ₜ[R] ((algebraMap R S) r * s) := by
  -- Rewrite the left tensor factor as an algebra-map element and multiply tensors.
  have hcomm :
      (((algebraMap R p.asIdeal.ResidueField r) ⊗ₜ[R] (1 : S)) : p.asIdeal.Fiber S) =
        (1 ⊗ₜ[R] algebraMap R S r : p.asIdeal.Fiber S) := by
    calc
      (((algebraMap R p.asIdeal.ResidueField r) ⊗ₜ[R] (1 : S)) : p.asIdeal.Fiber S) =
          algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)
            (algebraMap R p.asIdeal.ResidueField r) := by
              symm
              simpa using
                (Algebra.TensorProduct.algebraMap_apply
                  (R := R) (S := p.asIdeal.ResidueField) (A := p.asIdeal.ResidueField) (B := S)
                  (r := algebraMap R p.asIdeal.ResidueField r))
      _ = algebraMap R (p.asIdeal.Fiber S) r := by
            rw [IsScalarTower.algebraMap_apply R p.asIdeal.ResidueField (p.asIdeal.Fiber S)]
      _ = (1 ⊗ₜ[R] algebraMap R S r : p.asIdeal.Fiber S) := by
            simpa using (Algebra.TensorProduct.algebraMap_apply' (A := p.asIdeal.ResidueField)
              (B := S) (R := R) r)
  calc
    ((algebraMap R p.asIdeal.ResidueField r) ⊗ₜ[R] s : p.asIdeal.Fiber S) =
        ((((algebraMap R p.asIdeal.ResidueField r) ⊗ₜ[R] (1 : S)) : p.asIdeal.Fiber S) *
          (1 ⊗ₜ[R] s)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp
    _ = (1 ⊗ₜ[R] algebraMap R S r : p.asIdeal.Fiber S) * (1 ⊗ₜ[R] s) := by
          rw [hcomm]
    _ = 1 ⊗ₜ[R] ((algebraMap R S) r * s) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp

/-- Helper for Chap10 Lemma 10 136 10: every element of an algebraic fiber becomes a pure
tensor after multiplication by a base element outside the prime. -/
private lemma fiberElement_clear_denominator
    {S : Type*} [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (x : p.asIdeal.Fiber S) :
    ∃ r ∉ p.asIdeal, ∃ y : S, r • x = 1 ⊗ₜ[R] y := by
  classical
  -- Prove the statement on elementary tensors, then combine denominators under addition.
  refine TensorProduct.induction_on x ?zero ?tmul ?add
  · refine ⟨1, ?_, 0, ?_⟩
    · intro h1
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one p.asIdeal).2 h1)
    · simp
  · intro a s
    let A := R ⧸ p.asIdeal
    obtain ⟨num, den, hden, hfrac⟩ := IsFractionRing.div_surjective A a
    obtain ⟨numR, rfl⟩ := Ideal.Quotient.mk_surjective num
    obtain ⟨denR, rfl⟩ := Ideal.Quotient.mk_surjective den
    have hden_ne :
        (Ideal.Quotient.mk p.asIdeal denR : A) ≠ 0 :=
      (mem_nonZeroDivisors_iff_ne_zero.mp hden)
    have hden_not_mem : denR ∉ p.asIdeal := by
      intro hmem
      exact hden_ne ((Ideal.Quotient.eq_zero_iff_mem).2 hmem)
    have hdenK :
        algebraMap A p.asIdeal.ResidueField (Ideal.Quotient.mk p.asIdeal denR) ≠ 0 := by
      intro hzero
      exact hden_ne (IsFractionRing.to_map_eq_zero_iff.mp hzero)
    have hscalar :
        algebraMap R p.asIdeal.ResidueField denR * a =
          algebraMap R p.asIdeal.ResidueField numR := by
      have hdenAlg :
          algebraMap R A denR = Ideal.Quotient.mk p.asIdeal denR := by
        rw [Ideal.Quotient.algebraMap_eq]
      have hnumAlg :
          algebraMap R A numR = Ideal.Quotient.mk p.asIdeal numR := by
        rw [Ideal.Quotient.algebraMap_eq]
      rw [← hfrac]
      rw [IsScalarTower.algebraMap_apply R A p.asIdeal.ResidueField]
      rw [IsScalarTower.algebraMap_apply R A p.asIdeal.ResidueField]
      rw [hdenAlg, hnumAlg]
      exact mul_div_cancel₀
        (algebraMap A p.asIdeal.ResidueField (Ideal.Quotient.mk p.asIdeal numR)) hdenK
    refine ⟨denR, hden_not_mem, algebraMap R S numR * s, ?_⟩
    calc
      denR • (a ⊗ₜ[R] s : p.asIdeal.Fiber S) =
          (algebraMap R p.asIdeal.ResidueField denR * a) ⊗ₜ[R] s := by
            rw [TensorProduct.smul_tmul']
            simp [Algebra.smul_def]
      _ = (algebraMap R p.asIdeal.ResidueField numR) ⊗ₜ[R] s := by
            rw [hscalar]
      _ = 1 ⊗ₜ[R] (algebraMap R S numR * s) := by
            exact fiberTmul_algebraMap_mul (R := R) p numR s
  · intro x y hx hy
    obtain ⟨rx, hrx, sx, hsx⟩ := hx
    obtain ⟨ry, hry, sy, hsy⟩ := hy
    have hprod : rx * ry ∉ p.asIdeal := by
      intro hmem
      rcases p.isPrime.mem_or_mem hmem with hmem | hmem
      · exact hrx hmem
      · exact hry hmem
    refine ⟨rx * ry, hprod,
      algebraMap R S ry * sx + algebraMap R S rx * sy, ?_⟩
    have hx' :
        (rx * ry) • x = 1 ⊗ₜ[R] (algebraMap R S ry * sx) := by
      calc
        (rx * ry) • x = ry • (rx • x) := by
          rw [mul_comm, mul_smul]
        _ = ry • (1 ⊗ₜ[R] sx : p.asIdeal.Fiber S) := by
          rw [hsx]
        _ = 1 ⊗ₜ[R] (algebraMap R S ry * sx) := by
          calc
            ry • (1 ⊗ₜ[R] sx : p.asIdeal.Fiber S) =
                (algebraMap R p.asIdeal.ResidueField ry) ⊗ₜ[R] sx := by
                  rw [TensorProduct.smul_tmul']
                  simp [Algebra.smul_def]
            _ = 1 ⊗ₜ[R] (algebraMap R S ry * sx) := by
                  exact fiberTmul_algebraMap_mul (R := R) p ry sx
    have hy' :
        (rx * ry) • y = 1 ⊗ₜ[R] (algebraMap R S rx * sy) := by
      calc
        (rx * ry) • y = rx • (ry • y) := by
          rw [mul_smul]
        _ = rx • (1 ⊗ₜ[R] sy : p.asIdeal.Fiber S) := by
          rw [hsy]
        _ = 1 ⊗ₜ[R] (algebraMap R S rx * sy) := by
          calc
            rx • (1 ⊗ₜ[R] sy : p.asIdeal.Fiber S) =
                (algebraMap R p.asIdeal.ResidueField rx) ⊗ₜ[R] sy := by
                  rw [TensorProduct.smul_tmul']
                  simp [Algebra.smul_def]
            _ = 1 ⊗ₜ[R] (algebraMap R S rx * sy) := by
                  exact fiberTmul_algebraMap_mul (R := R) p rx sy
    rw [smul_add, hx', hy', TensorProduct.tmul_add]

/-- Helper for Chap10 Lemma 10 136 10: a fiber element in the ideal generated by finitely many
image generators can be cleared to a single tensor `1 ⊗ g` with `g` in the original span. -/
private lemma exists_smul_eq_one_tmul_of_mem_span_image
    {S : Type*} [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (s : Finset S) {x : p.asIdeal.Fiber S}
    (hx : x ∈ Ideal.span ((fun a : S ↦ (1 ⊗ₜ[R] a : p.asIdeal.Fiber S)) '' (s : Set S))) :
    ∃ r ∉ p.asIdeal, ∃ g ∈ Ideal.span (s : Set S), r • x = 1 ⊗ₜ[R] g := by
  classical
  -- Induct over the ideal generated by the fiber images and clear denominators in the coefficient
  -- branch using the reusable fiber lemma above.
  refine Submodule.span_induction
    (p := fun x _ ↦
      ∃ r ∉ p.asIdeal, ∃ g ∈ Ideal.span (s : Set S), r • x = 1 ⊗ₜ[R] g)
    ?mem ?zero ?add ?smul hx
  · intro x hxmem
    rcases hxmem with ⟨a, ha, rfl⟩
    refine ⟨1, ?_, a, Ideal.subset_span ha, ?_⟩
    · intro h1
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one p.asIdeal).2 h1)
    · simp
  · refine ⟨1, ?_, 0, Ideal.zero_mem _, ?_⟩
    · intro h1
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one p.asIdeal).2 h1)
    · simp
  · intro x y _hxmem _hymem hxw hyw
    obtain ⟨rx, hrx, gx, hgx, hxEq⟩ := hxw
    obtain ⟨ry, hry, gy, hgy, hyEq⟩ := hyw
    have hprod : rx * ry ∉ p.asIdeal := by
      intro hmem
      rcases p.isPrime.mem_or_mem hmem with hmem | hmem
      · exact hrx hmem
      · exact hry hmem
    refine ⟨rx * ry, hprod,
      algebraMap R S ry * gx + algebraMap R S rx * gy, ?_, ?_⟩
    · exact Ideal.add_mem _
        (Ideal.mul_mem_left _ (algebraMap R S ry) hgx)
        (Ideal.mul_mem_left _ (algebraMap R S rx) hgy)
    · have hx' :
          (rx * ry) • x = 1 ⊗ₜ[R] (algebraMap R S ry * gx) := by
        calc
          (rx * ry) • x = ry • (rx • x) := by
            rw [mul_comm, mul_smul]
          _ = ry • (1 ⊗ₜ[R] gx : p.asIdeal.Fiber S) := by
            rw [hxEq]
          _ = 1 ⊗ₜ[R] (algebraMap R S ry * gx) := by
            calc
              ry • (1 ⊗ₜ[R] gx : p.asIdeal.Fiber S) =
                  (algebraMap R p.asIdeal.ResidueField ry) ⊗ₜ[R] gx := by
                    rw [TensorProduct.smul_tmul']
                    simp [Algebra.smul_def]
              _ = 1 ⊗ₜ[R] (algebraMap R S ry * gx) := by
                    exact fiberTmul_algebraMap_mul (R := R) p ry gx
      have hy' :
          (rx * ry) • y = 1 ⊗ₜ[R] (algebraMap R S rx * gy) := by
        calc
          (rx * ry) • y = rx • (ry • y) := by
            rw [mul_smul]
          _ = rx • (1 ⊗ₜ[R] gy : p.asIdeal.Fiber S) := by
            rw [hyEq]
          _ = 1 ⊗ₜ[R] (algebraMap R S rx * gy) := by
            calc
              rx • (1 ⊗ₜ[R] gy : p.asIdeal.Fiber S) =
                  (algebraMap R p.asIdeal.ResidueField rx) ⊗ₜ[R] gy := by
                    rw [TensorProduct.smul_tmul']
                    simp [Algebra.smul_def]
              _ = 1 ⊗ₜ[R] (algebraMap R S rx * gy) := by
                    exact fiberTmul_algebraMap_mul (R := R) p rx gy
      rw [smul_add, hx', hy', TensorProduct.tmul_add]
  · intro a x _hxmem hxw
    obtain ⟨rx, hrx, gx, hgx, hxEq⟩ := hxw
    obtain ⟨ra, hra, sa, haEq⟩ := fiberElement_clear_denominator (R := R) p a
    have hprod : ra * rx ∉ p.asIdeal := by
      intro hmem
      rcases p.isPrime.mem_or_mem hmem with hmem | hmem
      · exact hra hmem
      · exact hrx hmem
    refine ⟨ra * rx, hprod, sa * gx, Ideal.mul_mem_left _ sa hgx, ?_⟩
    calc
      (ra * rx) • (a * x) =
          (ra • a) * (rx • x) := by
            simp [Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 ⊗ₜ[R] sa : p.asIdeal.Fiber S) * (1 ⊗ₜ[R] gx) := by
            rw [haEq, hxEq]
      _ = 1 ⊗ₜ[R] (sa * gx) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            simp

/-- Helper for Chap10 Lemma 10 136 10: a finite basic-open cover of one exact fiber can be
combined into a single element whose fiber image is a unit and whose basic open remains in the
cover. -/
private lemma exists_span_fiber_unit_of_finite_basicOpen_cover
    {S : Type*} [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) (s : Finset S)
    (hcover :
      {q : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q = p} ⊆
        ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S))) :
    ∃ g : S,
      g ∈ Ideal.span (s : Set S) ∧
        IsUnit (1 ⊗ₜ[R] g : p.asIdeal.Fiber S) ∧
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
            ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S)) := by
  classical
  letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  let sp : Finset (p.asIdeal.Fiber S) := s.image (fun a ↦ (1 ⊗ₜ[R] a : p.asIdeal.Fiber S))
  have hfiber_cover :
      (Set.univ : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ⊆
        ⋃ a ∈ sp, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
    intro qF _hqF
    let q := e.symm qF
    have hq : q.1 ∈ ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum S)) :=
      hcover q.2
    simp only [Set.mem_iUnion] at hq
    rcases hq with ⟨a, ha⟩
    rcases ha with ⟨has, hqa⟩
    have hqF_basic :
        qF ∈ (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) :
          Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
      let qF' : PrimeSpectrum (p.asIdeal.Fiber S) := PrimeSpectrum.preimageEquivFiber R S p q
      have hqF' : qF' = qF := by
        exact (PrimeSpectrum.preimageHomeomorphFiber R S p).toEquiv.apply_symm_apply qF
      have : (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) ∉ qF'.asIdeal := by
        rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]
        simpa [IsScalarTower.algebraMap_apply R S q.1.asIdeal.ResidueField] using
          (PrimeSpectrum.mem_basicOpen a q.1).1 hqa
      exact hqF' ▸ (PrimeSpectrum.mem_basicOpen (1 ⊗ₜ[R] a : p.asIdeal.Fiber S) qF').2 this
    exact Set.mem_iUnion.2
      ⟨1 ⊗ₜ[R] a, Set.mem_iUnion.2 ⟨Finset.mem_image.2 ⟨a, has, rfl⟩, hqF_basic⟩⟩
  obtain ⟨x, hxspan, hxone, _hxbasic⟩ :=
    exists_modEq_one_of_zeroLocus_subset_finite_basicOpen
      (J := (⊥ : Ideal (p.asIdeal.Fiber S))) sp <| by
        simpa using hfiber_cover
  have hxone' : x = 1 := by
    simpa using congrArg (AlgEquiv.quotientBot p.asIdeal.ResidueField (p.asIdeal.Fiber S)) hxone
  obtain ⟨r, hrp, g, hgspan, hgEq⟩ :=
    exists_smul_eq_one_tmul_of_mem_span_image (R := R) p s <| by
      simpa [sp, Ideal.map_span] using hxspan
  refine ⟨g, hgspan, ?_, basicOpen_subset_iUnion_basicOpen_of_mem_span s hgspan⟩
  rw [hxone'] at hgEq
  have hunit_r : IsUnit (algebraMap R (p.asIdeal.Fiber S) r) := by
    have hnonzero : algebraMap R p.asIdeal.ResidueField r ≠ 0 := by
      simpa using hrp
    let hru : IsUnit (algebraMap R p.asIdeal.ResidueField r) := isUnit_iff_ne_zero.mpr hnonzero
    simpa [IsScalarTower.algebraMap_apply R p.asIdeal.ResidueField (p.asIdeal.Fiber S)] using
      hru.map (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))
  have hunit_lhs : IsUnit (r • (1 : p.asIdeal.Fiber S)) := by
    simpa [Algebra.smul_def] using hunit_r
  simpa [hgEq] using hunit_lhs

/-- Helper for Chap10 Lemma 10 136 10: at a prime of the base with the expected fiber dimension,
some element that is a unit on that fiber has relative globally complete intersection
localization. -/
private theorem exists_relativeGCI_localizationAway_unit_fiber_of_fiberDimension
    (p : PrimeSpectrum R)
    (hdim : ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ g : PresentedAlgebra,
      IsUnit (1 ⊗ₜ[R] g : p.asIdeal.Fiber PresentedAlgebra) ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  -- First cover the exact fiber by finitely many basic opens inside the bounded locus.
  obtain ⟨s, hcover, hbounded⟩ :=
    exists_finite_basicOpen_cover_fiber_subset_relativeDimensionAtLELocus (f := f) p hdim
  -- Combine that finite exact-fiber cover into one element that is a unit on the fiber.
  obtain ⟨g, _hgspan, hgunit, hgbasic⟩ :=
    exists_span_fiber_unit_of_finite_basicOpen_cover (R := R) p s hcover
  refine ⟨g, hgunit, ?_⟩
  -- Its principal open is still contained in the bounded locus, so the localized chart is RGCI.
  exact isRelativeGlobalCompleteIntersection_localizationAway_of_basicOpen_subset_relativeDimensionAtLELocus
    (f := f) g (fun q hq ↦ hbounded (hgbasic hq))

/-- Helper for Chap10 Lemma 10 136 10: if the relative dimension at a point has the expected
value, then a principal open neighbourhood of that point has relative globally complete
intersection localization. -/
private theorem exists_relativeGCI_localizationAway_not_mem_of_relativeDimensionAt
    (q : PrimeSpectrum PresentedAlgebra)
    (hdim : relativeDimensionAt R PresentedAlgebra q = (n - c : WithBot ℕ∞)) :
    ∃ g : PresentedAlgebra,
      g ∉ q.asIdeal ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  -- Shrink the relative-dimension equality to a principal open on which every local fiber
  -- dimension is bounded by `n - c`.
  obtain ⟨g, hgq, hbasic_subset⟩ :=
    exists_basicOpen_subset_relativeDimensionAtLELocus_of_relativeDimensionAt_eq
      (f := f) q hdim
  refine ⟨g, hgq, ?_⟩
  -- The principal-open criterion turns the bounded-dimension locus containment into the desired
  -- localized relative global complete-intersection witness.
  exact isRelativeGlobalCompleteIntersection_localizationAway_of_basicOpen_subset_relativeDimensionAtLELocus
    (f := f) g hbasic_subset

-- Proof sketch: apply Lemma `10.125.6` to the quotient map `(R / I) → (S / IS)` to find a basic
-- open neighbourhood of `V (IS)` on which all fibers have dimension at most `n - c`; choose
-- `g` cutting out the complementary closed set so that `g = 1` in `S / IS`, lift `g` to some
-- `h` in the polynomial ring, and use the standard presentation of `S_g` by adjoining an inverse
-- for `h` together with Definition `10.136.5`.
/-- Part (1) of Chap10 Lemma 10 136 10: if all fibers of `Spec (S / IS) → Spec (R / I)` have
dimension `n - c` for `S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the
polynomial ring and its image `g` in `S` such that `g = 1` in `S / IS`, the localization `S_g` is
identified with the explicit quotient obtained by adjoining an inverse for `h`, and that displayed
quotient is a relative global complete intersection over `R`. -/
@[stacks 00ST]
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_fiberDimension_on_closedSet
    (I : Ideal R)
    (hdim : ∀ p : PrimeSpectrum R,
      I ≤ p.asIdeal →
        Nonempty (PrimeSpectrum (p.asIdeal.Fiber PresentedAlgebra)) →
          ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        Ideal.Quotient.mk (Ideal.map (algebraMap R PresentedAlgebra) I) g = 1 ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := by
  -- First choose the principal localization carrying both the closed-set congruence and RGCI.
  obtain ⟨g, hgmod, hgci⟩ :=
    exists_relativeGCI_localizationAway_eq_one_mod_ideal_of_closedSet_fiberDimension
      (f := f) I hdim
  -- Lift the chosen quotient element to the polynomial algebra and use the explicit quotient
  -- model for this localization.
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective (I := PresentedIdeal) g
  obtain ⟨e⟩ := nonempty_localizationAway_presentedAlgebra_algEquiv (f := f) h
  have hdisplay :
      Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) :=
    isRelativeGlobalCompleteIntersection_of_algEquiv hgci e
  -- The lift makes the first equality definitional; the remaining properties are transported
  -- from the chosen localized chart.
  refine ⟨h, Ideal.Quotient.mk PresentedIdeal h, e, ?_, ?_, hdisplay⟩
  · rfl
  · exact hgmod

-- Proof sketch: apply Lemma `10.125.6` to the fiber over `p` to obtain a basic open
-- neighbourhood of `Spec (S ⊗[R] κ(p))` on which all fibers have dimension at most `n - c`;
-- choose `g` whose image in the fiber ring is a unit, lift it to some `h`, and identify `S_g`
-- with the quotient obtained by adjoining an inverse for `h`, which is then a relative global
-- complete intersection by Definition `10.136.5`.
/-- Lemma 10.136.10 (2): if `dim (S ⊗[R] κ(p)) = n - c` for
`S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the polynomial ring and
its image `g` in `S` such that `g` becomes a unit in the fiber over `p`, the localization `S_g`
is identified with the explicit quotient obtained by adjoining an inverse for `h`, and that
displayed quotient is a relative global complete intersection over `R`. -/
@[stacks 00ST]
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_fiberDimension_atPrime
    (p : PrimeSpectrum R)
    (hdim : ringKrullDim (p.asIdeal.Fiber PresentedAlgebra) = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        IsUnit (1 ⊗ₜ[R] g : p.asIdeal.Fiber PresentedAlgebra) ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := by
  -- Choose the principal localization that is already RGCI and remains nonvanishing on the fiber.
  obtain ⟨g, hgunit, hgci⟩ :=
    exists_relativeGCI_localizationAway_unit_fiber_of_fiberDimension (f := f) p hdim
  -- Lift the quotient element and compare the canonical localization with the displayed
  -- inverse-adjoining quotient.
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective (I := PresentedIdeal) g
  obtain ⟨e⟩ := nonempty_localizationAway_presentedAlgebra_algEquiv (f := f) h
  have hdisplay :
      Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) :=
    isRelativeGlobalCompleteIntersection_of_algEquiv hgci e
  -- Assemble the displayed witnesses; after lifting, the side condition is exactly the one chosen.
  refine ⟨h, Ideal.Quotient.mk PresentedIdeal h, e, ?_, ?_, hdisplay⟩
  · rfl
  · exact hgunit

-- Proof sketch: use Lemma `10.125.6` at the prime `q` to find a principal open neighbourhood on
-- which the relative dimension is at most `n - c`; choose a generator `g` of that neighbourhood
-- with `g ∉ q`, lift it to some `h` in the polynomial ring, and then use the standard
-- localization presentation together with Definition `10.136.5`.
/-- Lemma 10.136.10 (3): if `dim_q (S / R) = n - c` for
`S = R[x_1, \ldots, x_n] / (f_1, \ldots, f_c)`, then there exist `h` in the polynomial ring and
its image `g` in `S` with `g ∉ q` such that the localization `S_g` is identified with the
explicit quotient obtained by adjoining an inverse for `h`, and that displayed quotient
presentation is a relative global complete intersection over `R`. -/
@[stacks 00ST]
theorem exists_relativeGlobalCompleteIntersection_localizationAway_of_relativeDimensionAt
    (q : PrimeSpectrum PresentedAlgebra)
    (hdim : relativeDimensionAt R PresentedAlgebra q = (n - c : WithBot ℕ∞)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : PresentedAlgebra)
      (_ : Localization.Away g ≃ₐ[R] LocalizedPresentedAlgebra h),
      Ideal.Quotient.mk PresentedIdeal h = g ∧
        g ∉ q.asIdeal ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) := by
  -- Shrink around `q` to a principal localization that is RGCI.
  obtain ⟨g, hgq, hgci⟩ :=
    exists_relativeGCI_localizationAway_not_mem_of_relativeDimensionAt (f := f) q hdim
  -- Lift the neighbourhood generator through the quotient presentation and identify the
  -- localization with the displayed quotient presentation.
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective (I := PresentedIdeal) g
  obtain ⟨e⟩ := nonempty_localizationAway_presentedAlgebra_algEquiv (f := f) h
  have hdisplay :
      Algebra.IsRelativeGlobalCompleteIntersection R (LocalizedPresentedAlgebra h) :=
    isRelativeGlobalCompleteIntersection_of_algEquiv hgci e
  -- The chosen basic open supplies `g ∉ q`; the quotient lift supplies the displayed equality.
  refine ⟨h, Ideal.Quotient.mk PresentedIdeal h, e, ?_, ?_, hdisplay⟩
  · rfl
  · exact hgq

end

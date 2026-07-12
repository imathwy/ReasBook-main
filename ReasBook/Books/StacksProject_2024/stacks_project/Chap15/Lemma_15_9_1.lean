import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
* primary domain: commutative algebra of away localizations, quotient algebras, and étale
  morphisms;
* sampled owner declarations:
  `Localization.Away`,
  `Ideal.Quotient.mk_surjective`,
  `IsLocalization.atUnit`,
  `Algebra.Etale.of_isLocalizationAway`,
  `IsLocalization.Away.algebraMap_isUnit`;
* best owner abstraction: the lifted element `u : A` together with the canonical owner
  `Localization.Away u`; the primitive quotient datum is the canonical `(A ⧸ I)`-algebra map
  `A ⧸ I →ₐ[A ⧸ I] ((Localization.Away u) ⧸ Ideal.map (algebraMap A (Localization.Away u)) I)`;
  the quotient algebra equivalence is the canonical bridge/view `IsLocalization.atUnit`, while
  bijectivity, étaleness, and invertibility are owner-derived API for `Localization.Away u`;
* layer: clause `(1)` is `source-facing`, while clause `(2)` is the attached `bridge/view`
  exposing only the quotient algebra equivalence;
* primitive data: the lift `u` and the canonical quotient algebra equivalence from
  `IsLocalization.atUnit`;
* derived API from the owner `Localization.Away u`: `Algebra.Etale A (Localization.Away u)` and
  `IsUnit (algebraMap A (Localization.Away u) u)`.
-/

universe u

section

variable {A : Type u} [CommRing A] (I : Ideal A)

open Ideal.Quotient (eq_zero_iff_mem)

local notation:max "AwayQuot(" u ")" =>
  ((Localization.Away u) ⧸ Ideal.map (algebraMap A (Localization.Away u)) I)

private noncomputable def awayLiftToQuotient {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    Localization.Away u →ₐ[A] A ⧸ I :=
  let f : A →+* A ⧸ I := Ideal.Quotient.mk I
  let huLift : IsUnit (f u) := by
    simpa [f, hu] using hu_bar
  { toRingHom := IsLocalization.Away.lift u huLift
    commutes' := by
      intro a
      change IsLocalization.Away.lift u huLift (algebraMap A (Localization.Away u) a) = f a
      simpa [f] using IsLocalization.Away.lift_eq u huLift a }

private theorem awayLiftToQuotient_surjective {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    Function.Surjective (awayLiftToQuotient I hu hu_bar) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨algebraMap A (Localization.Away u) a, ?_⟩
  change awayLiftToQuotient I hu hu_bar (algebraMap A (Localization.Away u) a) = Ideal.Quotient.mk I a
  simp [awayLiftToQuotient]

private theorem awayQuotIdeal_le_ker_awayLiftToQuotient {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    Ideal.map (algebraMap A (Localization.Away u)) I ≤ RingHom.ker (awayLiftToQuotient I hu hu_bar) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker]
  change awayLiftToQuotient I hu hu_bar (algebraMap A (Localization.Away u) a) = 0
  rw [show awayLiftToQuotient I hu hu_bar (algebraMap A (Localization.Away u) a) =
      Ideal.Quotient.mk I a by simp [awayLiftToQuotient]]
  exact eq_zero_iff_mem.mpr ha

private theorem ker_awayLiftToQuotient_eq_awayQuotIdeal {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    RingHom.ker (awayLiftToQuotient I hu hu_bar) =
      Ideal.map (algebraMap A (Localization.Away u)) I := by
  ext z
  constructor
  · intro hz
    have hz0 : awayLiftToQuotient I hu hu_bar z = 0 := by
      exact RingHom.mem_ker.mp hz
    obtain ⟨n, a, hzsurj⟩ := IsLocalization.Away.surj u z
    have hza0 : Ideal.Quotient.mk I a = 0 := by
      have hmap : awayLiftToQuotient I hu hu_bar z * Ideal.Quotient.mk I u ^ n = Ideal.Quotient.mk I a := by
        simpa [awayLiftToQuotient, map_mul, map_pow] using
          congrArg (awayLiftToQuotient I hu hu_bar) hzsurj
      simpa [hz0, hu] using hmap.symm
    have haI : a ∈ I := eq_zero_iff_mem.mp hza0
    have hzmul : z * algebraMap A (Localization.Away u) u ^ n ∈
        Ideal.map (algebraMap A (Localization.Away u)) I := by
      simpa [hzsurj] using Ideal.mem_map_of_mem (algebraMap A (Localization.Away u)) haI
    have huPowUnit : IsUnit (algebraMap A (Localization.Away u) u ^ n) :=
      IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit u)
    rcases huPowUnit with ⟨w, hw⟩
    have hw_inv : algebraMap A (Localization.Away u) u ^ n * ↑w⁻¹ = 1 := by
      simpa [hw] using w.mul_inv
    have hz_eq : z = (z * algebraMap A (Localization.Away u) u ^ n) * ↑w⁻¹ := by
      calc
        z = z * 1 := by simp
        _ = z * (algebraMap A (Localization.Away u) u ^ n * ↑w⁻¹) := by rw [hw_inv]
        _ = (z * algebraMap A (Localization.Away u) u ^ n) * ↑w⁻¹ := by rw [mul_assoc]
    rw [hz_eq]
    exact (Ideal.map (algebraMap A (Localization.Away u)) I).mul_mem_right _ hzmul
  · intro hz
    exact awayQuotIdeal_le_ker_awayLiftToQuotient I hu hu_bar hz

private noncomputable def awayQuotAlgEquivQuotient {u_bar : A ⧸ I} {u : A}
    (hu : Ideal.Quotient.mk I u = u_bar) (hu_bar : IsUnit u_bar) :
    AwayQuot(u) ≃ₐ[A] A ⧸ I :=
  (Ideal.quotientEquivAlgOfEq A (ker_awayLiftToQuotient_eq_awayQuotIdeal I hu hu_bar).symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective (awayLiftToQuotient_surjective I hu hu_bar)

-- Proof sketch: choose a lift `u : A` of `u_bar` using surjectivity of `Ideal.Quotient.mk I`.
-- Because `u_bar` is already a unit in `A ⧸ I`, the canonical localization map
-- `Localization.Away u → A ⧸ I` descends across the quotient by the extended ideal and becomes an
-- equivalence. The bijectivity of the induced quotient algebra map is the source-facing shadow of
-- that owner equivalence. The étaleness of `A → Localization.Away u` and invertibility of the
-- image of `u` are canonical owner consequences handled separately below.
/-- Lemma 15.9.1 (1): if `u_bar : A ⧸ I` is a unit, then there exists a lift `u : A` whose
principal localization makes the canonical quotient algebra map bijective. The étaleness and
invertibility properties needed later are owner-derived consequences of `Localization.Away u`,
not primitive payload of this source-facing clause. -/
theorem exists_localizationAway_lift_of_isUnit_quotient
    {u_bar : A ⧸ I} (hu_bar : IsUnit u_bar) :
    ∃ u : A,
      Ideal.Quotient.mk I u = u_bar ∧
        Function.Bijective (algebraMap (A ⧸ I) AwayQuot(u)) := by
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective u_bar
  let e : AwayQuot(u) ≃ₐ[A] A ⧸ I := awayQuotAlgEquivQuotient I hu hu_bar
  have he : Function.LeftInverse e (algebraMap (A ⧸ I) AwayQuot(u)) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change e (Ideal.Quotient.mk _ (algebraMap A (Localization.Away u) a)) = Ideal.Quotient.mk I a
    simp [e, awayQuotAlgEquivQuotient, awayLiftToQuotient]
  have hinj : Function.Injective (algebraMap (A ⧸ I) AwayQuot(u)) := he.injective
  have hsurj : Function.Surjective (algebraMap (A ⧸ I) AwayQuot(u)) := by
    intro y
    refine ⟨e y, ?_⟩
    apply e.injective
    simpa using he (e y)
  exact ⟨u, hu, ⟨hinj, hsurj⟩⟩

-- Proof sketch: part `(1)` gives bijectivity of the canonical quotient algebra map, and
-- `AlgEquiv.ofBijective` upgrades that canonical owner map to the desired quotient algebra
-- equivalence.
/-- Lemma 15.9.1 (2): if `u_bar : A ⧸ I` is a unit, then some lift `u : A` induces an
`(A ⧸ I)`-algebra isomorphism from `A ⧸ I` to the quotient of `Localization.Away u` by the
extended ideal. This is the bridge/view clause attached to part `(1)`. -/
theorem exists_quotientAlgEquiv_localizationAway_of_isUnit_quotient
    {u_bar : A ⧸ I} (hu_bar : IsUnit u_bar) :
    ∃ (u : A) (_eIso : (A ⧸ I) ≃ₐ[A ⧸ I] AwayQuot(u)),
      Ideal.Quotient.mk I u = u_bar := by
  obtain ⟨u, hu, hbij⟩ := exists_localizationAway_lift_of_isUnit_quotient I hu_bar
  have hbij' : Function.Bijective (Algebra.ofId (A ⧸ I) AwayQuot(u)) := by
    simpa using hbij
  exact ⟨u, AlgEquiv.ofBijective (Algebra.ofId (A ⧸ I) AwayQuot(u)) hbij', hu⟩

-- Proof sketch: every quotient element has a lift by `Ideal.Quotient.mk_surjective`, and every
-- away-localization is étale by `Algebra.Etale.of_isLocalizationAway`, so the unit hypothesis is
-- redundant here.
/-- Lemma 15.9.1 (3): every `u_bar : A ⧸ I` admits a lift `u : A` such that
`A → Localization.Away u` is étale. The unit hypothesis from the source is redundant because
every away-localization is canonically étale. -/
theorem exists_etale_localizationAway_lift_of_quotient
    (u_bar : A ⧸ I) :
    ∃ u : A, Ideal.Quotient.mk I u = u_bar ∧
      Algebra.Etale A (Localization.Away u) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u_bar
  exact ⟨u, rfl, Algebra.Etale.of_isLocalizationAway u⟩

-- Proof sketch: every quotient element lifts, and its lift becomes a unit in the away-localization
-- by `IsLocalization.Away.algebraMap_isUnit`, so the unit hypothesis is redundant here.
/-- Lemma 15.9.1 (4): every `u_bar : A ⧸ I` admits a lift `u : A` whose image is a unit in
`Localization.Away u`. The unit hypothesis from the source is redundant because this is a
canonical property of away-localizations. -/
theorem exists_isUnit_localizationAway_lift_of_quotient
    (u_bar : A ⧸ I) :
    ∃ u : A, Ideal.Quotient.mk I u = u_bar ∧
      IsUnit (algebraMap A (Localization.Away u) u) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u_bar
  exact ⟨u, rfl, IsLocalization.Away.algebraMap_isUnit u⟩

end

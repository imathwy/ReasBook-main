import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-
Domain triage: this file is in the commutative algebra of the `N-1` and `N-2` conditions under a
finite principal-open cover.

Owner abstractions sampled for this item:
- `IsN1Ring` and `IsN2Ring`, the source-facing owners from `Definition_10_161_1`;
- `isN1Ring_of_isLocalization` and `isN2Ring_of_isLocalization`, the localization-stability
  bridge theorems from `Lemma_10_161_3`;
- `Module.Finite.of_localizationSpan_finite`, the canonical finite-module descent theorem over a
  principal-open cover from `Lemma_10_23_2`.

Primitive data are the finite cover `s`, the unit-ideal hypothesis `hs`, and the domain hypotheses
for the chosen localizations. The localized `N-1` / `N-2` conditions are source-facing
assumptions. The finite-normalization statements and localization identifications are derived API
internal to the proofs, so this file should reuse the owners above directly rather than introducing
parallel local wrappers.
-/

/- Lemma 10.161.4, the `N-1` clause, is exactly the owner definition `IsN1Ring`: the forward
direction is `IsN1Ring.integralClosure_finite`, and the reverse direction is `IsN1Ring.mk`. -/
recall IsN1Ring.integralClosure_finite
recall IsN1Ring.mk

/- Lemma 10.161.4, the `N-2` clause, is exactly the owner definition `IsN2Ring`: the forward
direction is `IsN2Ring.integralClosure_finite`, and the reverse direction is `IsN2Ring.mk`. -/
recall IsN2Ring.integralClosure_finite
recall IsN2Ring.mk

variable (s : Finset R)

/-- Helper for Lemma 10.161.4: if the localization `R_f` is a domain, then `f` is nonzero in
`R`. -/
lemma localizationAway_ne_zero
    (f : s) [IsDomain (Localization.Away f.1)] :
    f.1 ≠ 0 := by
  -- A zero element cannot become a unit in a domain localization.
  intro hf
  have hunit : IsUnit (algebraMap R (Localization.Away f.1) f.1) :=
    IsLocalization.map_units (Localization.Away f.1) ⟨f.1, Submonoid.mem_powers _⟩
  have hne : algebraMap R (Localization.Away f.1) f.1 ≠ 0 := hunit.ne_zero
  exact hne <| by simp [hf]

/-- Helper for Lemma 10.161.4: every power of an element with domain localization is a
nonzerodivisor. -/
lemma localizationAway_le_nonZeroDivisors
    (f : s) [IsDomain (Localization.Away f.1)] :
    Submonoid.powers f.1 ≤ nonZeroDivisors R := by
  -- Reduce to the nonvanishing of the generator and then use powers in a domain.
  intro x hx
  rw [mem_nonZeroDivisors_iff_ne_zero]
  rcases (show ∃ n : ℕ, f.1 ^ n = x by simpa [Submonoid.mem_powers_iff] using hx) with ⟨n, rfl⟩
  exact pow_ne_zero n (localizationAway_ne_zero (s := s) f)

/-- Helper for Lemma 10.161.4: integral elements over `R` remain integral after localizing the
base ring away from `f`. -/
lemma integralClosure_le_localizationAway_integralClosure
    {L : Type u} [Field L] [Algebra R L] (f : s)
    [Algebra (Localization.Away f.1) L] [IsScalarTower R (Localization.Away f.1) L] :
    integralClosure R L ≤
      (integralClosure (Localization.Away f.1) L).restrictScalars R := by
  -- The localized base ring receives `R`, so integrality is preserved along the map.
  intro x hx
  change IsIntegral (Localization.Away f.1) x
  exact IsIntegral.map_of_comp_eq (φ := algebraMap R (Localization.Away f.1)) (ψ := RingHom.id _)
    (by
      ext y
      simp [IsScalarTower.algebraMap_apply R (Localization.Away f.1) L]) hx

/-- Helper for Lemma 10.161.4: finiteness of the localized integral closures on a principal-open
cover descends to finiteness of the global integral closure. -/
lemma integralClosure_finite_of_localizationAway_cover
    {L : Type u} [Field L] [Algebra R L]
    [∀ f : s, Algebra (Localization.Away f.1) L]
    [∀ f : s, IsScalarTower R (Localization.Away f.1) L]
    [∀ f : s, IsLocalization.Away (algebraMap R L f.1) L]
    (hs : Ideal.span (s : Set R) = ⊤)
    (hfinite : ∀ f : s, Module.Finite (Localization.Away f.1)
      (integralClosure (Localization.Away f.1) L)) :
    Module.Finite R (integralClosure R L) := by
  -- For each generator, compare the localized global normalization with the local normalization.
  let hle : ∀ f : s, integralClosure R L ≤
      (integralClosure (Localization.Away f.1) L).restrictScalars R := fun f ↦
    integralClosure_le_localizationAway_integralClosure (R := R) (s := s) f
  let fint : ∀ f : s, integralClosure R L →+* integralClosure (Localization.Away f.1) L := fun f ↦
    (Subalgebra.inclusion (hle f)).toRingHom
  letI : ∀ f : s, Algebra (integralClosure R L)
      (integralClosure (Localization.Away f.1) L) := fun f ↦
    (fint f).toAlgebra
  letI : ∀ f : s,
      SMul (integralClosure R L) (integralClosure (Localization.Away f.1) L) := fun f ↦
    (show
        Algebra (integralClosure R L) (integralClosure (Localization.Away f.1) L) from
          inferInstance).toSMul
  letI : ∀ f : s, IsScalarTower R (integralClosure R L)
      (integralClosure (Localization.Away f.1) L) := fun f ↦
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <| by rfl
  letI : ∀ f : s, IsScalarTower (integralClosure R L)
      (integralClosure (Localization.Away f.1) L) L := fun f ↦
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      cases x
      rfl
  letI : ∀ f : s,
      IsLocalization.Away (algebraMap R (integralClosure R L) f.1)
        (integralClosure (Localization.Away f.1) L) := fun f ↦
    IsLocalization.Away.integralClosure (R := R) (S := L) (Rf := Localization.Away f.1)
      (Sf := L) f.1
  let κ : ∀ f : s, integralClosure R L →ₗ[R] integralClosure (Localization.Away f.1) L := fun f ↦
    (IsScalarTower.toAlgHom R (integralClosure R L)
      (integralClosure (Localization.Away f.1) L)).toLinearMap
  letI : ∀ f : s, IsLocalizedModule (Submonoid.powers f.1) (κ f) := fun f ↦ inferInstance
  -- Apply the principal-open descent theorem to the integral closure itself.
  exact Module.Finite.of_localizationSpan_finite' s hs κ hfinite

/-- Helper for Lemma 10.161.4: the local `N-1` hypothesis gives finiteness of the integral
closure in the common fraction field. -/
lemma localizationAway_integralClosure_finite_fractionRing
    (f : s) [IsDomain (Localization.Away f.1)]
    [Algebra (Localization.Away f.1) (FractionRing R)]
    [IsScalarTower R (Localization.Away f.1) (FractionRing R)]
    [IsFractionRing (Localization.Away f.1) (FractionRing R)]
    [IsN1Ring (Localization.Away f.1)] :
    Module.Finite (Localization.Away f.1)
      (integralClosure (Localization.Away f.1) (FractionRing R)) := by
  -- First use `N-1` over the local fraction ring, then transport along the fraction-field
  -- equivalence to the common ambient fraction field of `R`.
  have hfinite_local :
      Module.Finite (Localization.Away f.1)
        (integralClosure (Localization.Away f.1) (FractionRing (Localization.Away f.1))) := by
    exact IsN1Ring.integralClosure_finite (R := Localization.Away f.1)
  exact Module.Finite.equiv
    (FractionRing.algEquiv (Localization.Away f.1) (FractionRing R)).mapIntegralClosure.toLinearEquiv

/-- Helper for Lemma 10.161.4: after transporting the finite extension structure across the local
fraction-field equivalence, the localized `N-2` hypothesis applies. -/
lemma localizationAway_integralClosure_finite_of_isN2Ring
    {L : Type u} [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] (f : s)
    [IsDomain (Localization.Away f.1)]
    [Algebra (Localization.Away f.1) L]
    [IsScalarTower R (Localization.Away f.1) L]
    [Algebra (FractionRing (Localization.Away f.1)) L]
    [IsScalarTower (Localization.Away f.1) (FractionRing (Localization.Away f.1)) L]
    [FiniteDimensional (FractionRing (Localization.Away f.1)) L]
    [IsN2Ring (Localization.Away f.1)] :
    Module.Finite (Localization.Away f.1)
      (integralClosure (Localization.Away f.1) L) := by
  -- Once `L` is viewed as a finite extension of the local fraction field, the `N-2` owner closes
  -- the local integral-closure finiteness goal immediately.
  exact IsN2Ring.integralClosure_finite_of_finiteDimensional
    (R := Localization.Away f.1) (L := L)

-- Proof sketch: use the local `N-1` assumptions together with `isN1Ring_of_isLocalization` to
-- place the canonical normalization owner on each principal localization, transport that
-- finiteness statement across `IsLocalization.integralClosure`, and descend finiteness of the
-- global normalization via `Module.Finite.of_localizationSpan_finite`.
/-- Lemma 10.161.4 (1): if the elements of `s` generate the unit ideal and each localization
`R_f` is `N-1`, then `R` is `N-1`. -/
@[stacks 032H]
theorem isN1Ring_of_isN1Ring_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, let _ : IsDomain (Localization.Away f.1) := hdom f
      IsN1Ring (Localization.Away f.1)) :
    IsN1Ring R := by
  -- Follow the source proof: descend finiteness of the global normalization from the principal
  -- open cover in the common fraction field.
  refine IsN1Ring.mk ?_
  letI : ∀ f : s, IsDomain (Localization.Away f.1) := hdom
  let hpow : ∀ f : s, Submonoid.powers f.1 ≤ nonZeroDivisors R := fun f ↦
    localizationAway_le_nonZeroDivisors (R := R) (s := s) f
  letI : ∀ f : s, Algebra (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.Away f.1) (FractionRing R) (Submonoid.powers f.1) (nonZeroDivisors R)
      (hpow f)
  letI : ∀ f : s, IsScalarTower R (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.Away f.1) (FractionRing R) (Submonoid.powers f.1) (nonZeroDivisors R)
      (hpow f)
  letI : ∀ f : s, IsFractionRing (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f.1)
      (Localization.Away f.1) (FractionRing R)
  letI : ∀ f : s, IsN1Ring (Localization.Away f.1) := fun f ↦ h f
  letI : ∀ f : s, IsLocalization.Away (algebraMap R (FractionRing R) f.1) (FractionRing R) :=
    fun f ↦
      IsLocalization.self <| by
        rintro x hx
        rcases (show ∃ n : ℕ, (algebraMap R (FractionRing R) f.1) ^ n = x by
          simpa [Submonoid.mem_powers_iff] using hx) with ⟨n, rfl⟩
        have hne : algebraMap R (FractionRing R) f.1 ≠ 0 := by
          intro hf0
          exact localizationAway_ne_zero (R := R) (s := s) f <|
            (IsFractionRing.injective R (FractionRing R)) <| by simpa using hf0
        exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hne)
  -- Each localized normalization is finite by the local `N-1` hypothesis transported to the
  -- common fraction field.
  exact integralClosure_finite_of_localizationAway_cover (R := R) (s := s) hs fun f ↦
    localizationAway_integralClosure_finite_fractionRing (R := R) (s := s) f

-- Proof sketch: for a finite extension `L / FractionRing R`, apply the localized owner theorem
-- `isN2Ring_of_isLocalization` to each principal localization, identify the localization of
-- `integralClosure R L` with the local integral closure via `IsLocalization.integralClosure`, and
-- descend finiteness back to `R` using `Module.Finite.of_localizationSpan_finite`.
/-- Lemma 10.161.4 (2): if the elements of `s` generate the unit ideal and each localization
`R_f` is `N-2`, then `R` is `N-2`. -/
@[stacks 032H]
theorem isN2Ring_of_isN2Ring_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, let _ : IsDomain (Localization.Away f.1) := hdom f
      IsN2Ring (Localization.Away f.1)) :
    IsN2Ring R := by
  -- Follow the source proof literally for an arbitrary finite extension of the fraction field.
  refine IsN2Ring.mk fun L => ?_
  intro _ _ _ _ _
  letI : ∀ f : s, IsDomain (Localization.Away f.1) := hdom
  let hpow : ∀ f : s, Submonoid.powers f.1 ≤ nonZeroDivisors R := fun f ↦
    localizationAway_le_nonZeroDivisors (R := R) (s := s) f
  letI : ∀ f : s, Algebra (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.Away f.1) (FractionRing R) (Submonoid.powers f.1) (nonZeroDivisors R)
      (hpow f)
  letI : ∀ f : s, IsScalarTower R (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.Away f.1) (FractionRing R) (Submonoid.powers f.1) (nonZeroDivisors R)
      (hpow f)
  letI : ∀ f : s, IsFractionRing (Localization.Away f.1) (FractionRing R) := fun f ↦
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f.1)
      (Localization.Away f.1) (FractionRing R)
  letI : ∀ f : s, Algebra (Localization.Away f.1) L := fun f ↦
    (RingHom.comp (algebraMap (FractionRing R) L)
      (algebraMap (Localization.Away f.1) (FractionRing R))).toAlgebra
  letI : ∀ f : s, IsScalarTower (Localization.Away f.1) (FractionRing R) L := fun f ↦ by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    rfl
  letI : ∀ f : s, IsScalarTower R (Localization.Away f.1) L := fun f ↦ by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    change (algebraMap R L) x =
      (algebraMap (FractionRing R) L)
        ((algebraMap (Localization.Away f.1) (FractionRing R)) ((algebraMap R (Localization.Away f.1)) x))
    rw [← IsScalarTower.algebraMap_apply R (Localization.Away f.1) (FractionRing R) x]
    exact IsScalarTower.algebraMap_apply R (FractionRing R) L x
  letI : ∀ f : s, IsN2Ring (Localization.Away f.1) := fun f ↦ h f
  let e : ∀ f : s, FractionRing (Localization.Away f.1) ≃ₐ[Localization.Away f.1] FractionRing R :=
    fun f ↦ FractionRing.algEquiv (Localization.Away f.1) (FractionRing R)
  let fL : ∀ f : s, FractionRing (Localization.Away f.1) →ₐ[Localization.Away f.1] L := fun f ↦
    (IsScalarTower.toAlgHom (Localization.Away f.1) (FractionRing R) L).comp (e f)
  letI : ∀ f : s, Algebra (FractionRing (Localization.Away f.1)) L := fun f ↦
    (fL f).toRingHom.toAlgebra
  letI : ∀ f : s, IsScalarTower (Localization.Away f.1)
      (FractionRing (Localization.Away f.1)) L := fun f ↦ by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    calc
      algebraMap (Localization.Away f.1) L x =
          algebraMap (FractionRing R) L
            (algebraMap (Localization.Away f.1) (FractionRing R) x) := by
        exact IsScalarTower.algebraMap_apply (Localization.Away f.1) (FractionRing R) L x
      _ =
          algebraMap (FractionRing (Localization.Away f.1)) L
            (algebraMap (Localization.Away f.1) (FractionRing (Localization.Away f.1)) x) := by
        simpa using
          (IsFractionRing.algEquiv_commutes (e f)
            (show L ≃ₐ[FractionRing (Localization.Away f.1)] L from AlgEquiv.refl)
            (algebraMap (Localization.Away f.1) (FractionRing (Localization.Away f.1)) x))
  letI : ∀ f : s, Module.Finite (FractionRing (Localization.Away f.1)) L := fun f ↦ by
    letI : Module.Finite (FractionRing R) L := inferInstance
    have hcompat :
        RingHom.comp (algebraMap (FractionRing (Localization.Away f.1)) L)
            ↑((e f).symm.toRingEquiv) =
          RingHom.comp (RingEquiv.refl L) (algebraMap (FractionRing R) L) := by
      ext x
      simpa using
        (IsFractionRing.algEquiv_commutes (e f).symm
          (show L ≃ₐ[FractionRing (Localization.Away f.1)] L from AlgEquiv.refl) x)
    exact Module.Finite.of_equiv_equiv ((e f).symm.toRingEquiv) (RingEquiv.refl L) hcompat
  letI : ∀ f : s, FiniteDimensional (FractionRing (Localization.Away f.1)) L := fun f ↦ by
    infer_instance
  letI : ∀ f : s, IsLocalization.Away (algebraMap R L f.1) L := fun f ↦
    IsLocalization.self <| by
      rintro x hx
      rcases (show ∃ n : ℕ, (algebraMap R L f.1) ^ n = x by
        simpa [Submonoid.mem_powers_iff] using hx) with ⟨n, rfl⟩
      have hne : algebraMap R L f.1 ≠ 0 := by
        intro hf0
        exact localizationAway_ne_zero (R := R) (s := s) f <|
          (algebraMap_injective_of_field_isFractionRing R L (FractionRing R) L) <| by
            simpa using hf0
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero n hne)
  -- The localized integral closures are finite over each principal open by the local `N-2`
  -- hypotheses, and then finiteness descends along the cover.
  exact integralClosure_finite_of_localizationAway_cover (R := R) (s := s) hs fun f ↦
    localizationAway_integralClosure_finite_of_isN2Ring (R := R) (s := s) (L := L) f

end

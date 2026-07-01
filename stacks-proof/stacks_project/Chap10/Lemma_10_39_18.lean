import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open scoped TensorProduct
open LocalizedModule TensorProduct
open TensorProduct.AlgebraTensorModule

section LocalizationFlatness

variable {R : Type u} [CommRing R]
variable (S : Submonoid R) {Rₛ : Type v} [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]

/- Canonical recall: for a multiplicative subset `S` of a ring `R`, the localization `S⁻¹R`
is flat as an `R`-algebra. This is exactly the canonical theorem `IsLocalization.flat`. -/
recall IsLocalization.flat

variable {N : Type w} [AddCommMonoid N] [Module R N] [Module Rₛ N] [IsScalarTower R Rₛ N]

/- Canonical recall: if `M` is a module over a localization `S⁻¹R`, then `M` is flat over `R`
if and only if it is flat over `S⁻¹R`. This is exactly the canonical theorem
`Module.flat_iff_of_isLocalization`. -/
recall Module.flat_iff_of_isLocalization

variable {M : Type v} [AddCommMonoid M] [Module R M]

-- Proof sketch: one direction is preserved by localization at a prime, and the converse follows
-- by reducing to the maximal-local criterion after localizing further at maximal ideals over each
-- prime.
/-- Lemma 10.39.18 (1): an `R`-module `M` is flat if and only if each localization `Mₚ` is flat
over `Rₚ` for every prime ideal `p` of `R`. -/
theorem flat_iff_flat_localizedModule_atPrime
    : Module.Flat R M ↔
        ∀ p : PrimeSpectrum R,
          Module.Flat (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  constructor
  · intro hM p
    -- Localizing a flat module at a prime remains flat over the localized ring.
    letI : Module.Flat R M := hM
    simpa [LocalizedModule.AtPrime] using
      (Module.Flat.localizedModule (M := M) p.asIdeal.primeCompl)
  · intro h
    -- The prime-local hypothesis in particular gives the maximal-local one.
    apply Module.flat_of_localized_maximal
    intro P hP
    exact
      (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl
        (M := LocalizedModule.AtPrime P M)).mp <|
        by simpa [LocalizedModule.AtPrime] using h ⟨P, inferInstance⟩

-- Proof sketch: use the canonical maximal-local criterion in mathlib for one direction and
-- localization of flat modules for the reverse implication.
/-- Lemma 10.39.18 (2): an `R`-module `M` is flat if and only if each localization `Mₘ` is flat
over `Rₘ` for every maximal ideal `m` of `R`. -/
theorem flat_iff_flat_localizedModule_atMaximal
    : Module.Flat R M ↔
        ∀ m : MaximalSpectrum R,
          Module.Flat (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal M) := by
  constructor
  · intro hM m
    -- Localizing a flat module at a maximal ideal remains flat over the localized ring.
    letI : Module.Flat R M := hM
    simpa [LocalizedModule.AtPrime] using
      (Module.Flat.localizedModule (M := M) m.asIdeal.primeCompl)
  · intro h
    -- This is exactly the canonical maximal-local criterion for flatness.
    apply Module.flat_of_localized_maximal
    intro P hP
    exact
      (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl
        (M := LocalizedModule.AtPrime P M)).mp <|
        by simpa [LocalizedModule.AtPrime] using h ⟨P, hP⟩

end LocalizationFlatness

section RelativeLocalizationFlatness

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

noncomputable section

/- The localization of an `A`-module at a prime `Q` of `A` is canonically a module over the
localization of `R` at the inverse-image prime `Q ∩ R`, via the local ring map
`R_(Q ∩ R) → A_Q`. -/
noncomputable instance (Q : Ideal A) [Q.IsPrime] :
    Module (Localization.AtPrime (Q.under R)) (LocalizedModule.AtPrime Q M) :=
  Module.compHom (LocalizedModule.AtPrime Q M)
    (Localization.localRingHom (Q.under R) Q (algebraMap R A) rfl)

noncomputable instance (Q : Ideal A) [Q.IsPrime] :
    IsScalarTower (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)
      (LocalizedModule.AtPrime Q M) := by
  letI : Module (Localization.AtPrime (Q.under R)) (LocalizedModule.AtPrime Q M) :=
    Module.compHom (LocalizedModule.AtPrime Q M)
      (Localization.localRingHom (Q.under R) Q (algebraMap R A) rfl)
  simpa using
    (IsScalarTower.restrictScalars (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)
      (LocalizedModule.AtPrime Q M))

variable {N : Type x} [AddCommMonoid N] [Module R N]

/-- Helper for Lemma 10.39.18: localizing `X ⊗[R] Q` at a multiplicative subset of `A` agrees
with tensoring the localized `A`-module `X` over `R` with `Q`. -/
noncomputable def localized_tensor_right_equiv
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] (Q : Type*) [AddCommMonoid Q] [Module R Q] :
    LocalizedModule T X ⊗[R] Q ≃ₗ[A] LocalizedModule T (X ⊗[R] Q) :=
  IsLocalizedModule.linearEquiv T
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
    (LocalizedModule.mkLinearMap T (X ⊗[R] Q))

/-- Helper for Lemma 10.39.18: the `R_(q ∩ R)`-action on `M_q` is compatible with the original
`R`-action. -/
noncomputable instance (Q : Ideal A) [Q.IsPrime] :
    IsScalarTower R (Localization.AtPrime (Q.under R)) (LocalizedModule.AtPrime Q M) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change
      (Localization.localRingHom (Q.under R) Q (algebraMap R A) rfl
        (algebraMap R (Localization.AtPrime (Q.under R)) r)) • x = r • x
    rw [Localization.localRingHom_to_map]
    simp

/-- Helper for Lemma 10.39.18: the canonical localized tensor map is exactly tensoring on the
localized module. -/
lemma localized_lTensor_map_eq
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    IsLocalizedModule.map T
        (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
        (AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
        (AlgebraTensorModule.lTensor A X f) =
      AlgebraTensorModule.lTensor A (LocalizedModule T X) f := by
  -- Freeze `map_lTensor` at the concrete localization model so later rewrites do not leave any
  -- localized codomain implicit.
  simpa using
    (IsLocalizedModule.map_lTensor (S := T) (R := R) (A := A) (M := X)
      (M' := LocalizedModule T X) (N := Q) (P := Q')
      (f := f) (g := LocalizedModule.mkLinearMap T X))

/-- Helper for Lemma 10.39.18: after the canonical localization-tensor identification, localizing
`X ⊗[R] f` agrees with tensoring `f` against the localized module `X_T`. -/
lemma localized_lTensor_intertwines
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    ((LocalizedModule.map T (AlgebraTensorModule.lTensor A X f)).restrictScalars A).comp
        (localized_tensor_right_equiv (R := R) (A := A) T Q).toLinearMap =
      (localized_tensor_right_equiv (R := R) (A := A) T Q').toLinearMap.comp
        (AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
  -- Route correction: replace the old pure-tensor extensional proof by the canonical owner
  -- transport identity `restrictScalars_map_eq`, then rewrite the middle map by `map_lTensor`.
  let eQ := localized_tensor_right_equiv (R := R) (A := A) (X := X) T Q
  let eQ' := localized_tensor_right_equiv (R := R) (A := A) (X := X) T Q'
  have hlocalized :
      IsLocalizedModule.map T
          (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
          (AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
          (AlgebraTensorModule.lTensor A X f) =
        AlgebraTensorModule.lTensor A (LocalizedModule T X) f :=
    localized_lTensor_map_eq (R := R) (A := A) (T := T) (X := X) f
  have hmap :
      (LocalizedModule.map T (AlgebraTensorModule.lTensor A X f)).restrictScalars A =
        (eQ'.toLinearMap.comp
          (AlgebraTensorModule.lTensor A (LocalizedModule T X) f)).comp
          eQ.symm.toLinearMap := by
    -- The canonical tensor-localization equivalence is the localized-module `iso`, so the owner
    -- theorem becomes exactly the desired conjugation formula.
    rw [LocalizedModule.restrictScalars_map_eq (R := A) (S := T)
      (g₁ := AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
      (g₂ := AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
      (l := AlgebraTensorModule.lTensor A X f)]
    rw [hlocalized]
    simpa [eQ, eQ', localized_tensor_right_equiv, IsLocalizedModule.linearEquiv,
      IsLocalizedModule.iso_localizedModule_eq_refl, LinearMap.comp_assoc]
  -- Postcompose the conjugation formula by `eQ` so the inverse comparison map cancels.
  calc
    ((LocalizedModule.map T (AlgebraTensorModule.lTensor A X f)).restrictScalars A).comp eQ.toLinearMap
        = (((eQ'.toLinearMap.comp
            (AlgebraTensorModule.lTensor A (LocalizedModule T X) f)).comp
              eQ.symm.toLinearMap).comp eQ.toLinearMap) := by
            rw [hmap]
    _ = eQ'.toLinearMap.comp (AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
      ext z
      simp [LinearMap.comp_assoc]

/-- Helper for Lemma 10.39.18: injectivity of the localization of `X ⊗[R] f` is equivalent to
injectivity of tensoring `f` against the localized module `X_T`. -/
lemma localized_lTensor_injective_iff
    (T : Submonoid A) {X : Type*} [AddCommMonoid X] [Module R X] [Module A X]
    [IsScalarTower R A X] {Q Q' : Type*} [AddCommMonoid Q] [AddCommMonoid Q']
    [Module R Q] [Module R Q'] (f : Q →ₗ[R] Q') :
    Function.Injective (LocalizedModule.map T (AlgebraTensorModule.lTensor A X f)) ↔
      Function.Injective (AlgebraTensorModule.lTensor A (LocalizedModule T X) f) := by
  -- The owner injectivity criterion already compares the localized map with the corresponding
  -- map between arbitrary localized-module models, and the explicit adapter identifies it with
  -- tensoring on the localized module.
  have hiff :=
    (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective
      (S := T)
      (g₁ := AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap T X))
      (g₂ := AlgebraTensorModule.rTensor R Q' (LocalizedModule.mkLinearMap T X))
      (l := AlgebraTensorModule.lTensor A X f)).symm
  rw [localized_lTensor_map_eq (R := R) (A := A) (T := T) (X := X) (f := f)] at hiff
  exact hiff

/-- Helper for Lemma 10.39.18: localizing an `A`-module preserves flatness over the base ring
`R`. -/
lemma flat_localizedModule_of_flat (T : Submonoid A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule T M) := by
  -- Use the submodule version of the flatness criterion so only additive-monoid structure is
  -- needed on the localized module.
  rw [Module.Flat.iff_lTensor_injectiveₛ] at hM ⊢
  intro Q _ _ N
  have hTensor : Function.Injective (N.subtype.lTensor M) := hM N
  have hTensorA : Function.Injective (AlgebraTensorModule.lTensor A M N.subtype) := by
    simpa [AlgebraTensorModule.coe_lTensor] using hTensor
  have hLocalized :
      Function.Injective (LocalizedModule.map T (AlgebraTensorModule.lTensor A M N.subtype)) :=
    LocalizedModule.map_injective T (AlgebraTensorModule.lTensor A M N.subtype) hTensorA
  have hLocalizedTensor :=
    (localized_lTensor_injective_iff (R := R) (A := A) T (X := M) N.subtype).mp hLocalized
  simpa [AlgebraTensorModule.coe_lTensor] using hLocalizedTensor

/-- Helper for Lemma 10.39.18: if `M` is flat over `R`, then its localization at a prime of `A`
is flat over the corresponding localized base ring `R_(q ∩ R)`. -/
lemma flat_localizedModule_atPrime_over_under_of_flat (hM : Module.Flat R M)
    (q : PrimeSpectrum A) :
    Module.Flat (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal M) := by
  -- First view `M_q` as an `R`-flat module, then convert to flatness over `R_(q ∩ R)`.
  letI : Module (Localization.AtPrime (q.asIdeal.under R)) (LocalizedModule.AtPrime q.asIdeal M) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal M)
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl)
  letI :
      IsScalarTower R (Localization.AtPrime (q.asIdeal.under R))
        (LocalizedModule.AtPrime q.asIdeal M) :=
      inferInstance
  have hLocalizedR : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) :=
    flat_localizedModule_of_flat (R := R) (A := A) q.asIdeal.primeCompl hM
  exact
    (Module.flat_iff_of_isLocalization
      (Localization.AtPrime (q.asIdeal.under R)) (q.asIdeal.under R).primeCompl
      (M := LocalizedModule.AtPrime q.asIdeal M)).mpr hLocalizedR

/-- Helper for Lemma 10.39.18: flatness over `R` descends from the maximal localizations over the
under-rings `R_(m ∩ R)`. -/
lemma flat_of_flat_localizedModule_atMaximal_over_under
    (h :
      ∀ m : MaximalSpectrum A,
        Module.Flat (Localization.AtPrime (m.asIdeal.under R))
          (LocalizedModule.AtPrime m.asIdeal M)) :
    Module.Flat R M := by
  -- Convert each maximal-local hypothesis to an `R`-flat localized module and apply the owner
  -- theorem `Module.flat_of_isLocalized_maximal`.
  apply Module.flat_of_isLocalized_maximal
    (R := R) (S := A) (M := M)
    (Mₚ := fun P _ ↦ LocalizedModule.AtPrime P M)
    (f := fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M)
  intro P hP
  letI : Module (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) :=
    Module.compHom (LocalizedModule.AtPrime P M)
      (Localization.localRingHom (P.under R) P (algebraMap R A) rfl)
  letI :
      IsScalarTower R (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) :=
      inferInstance
  have hPflat :
      Module.Flat (Localization.AtPrime (P.under R)) (LocalizedModule.AtPrime P M) :=
    h ⟨P, hP⟩
  exact
    (Module.flat_iff_of_isLocalization
      (Localization.AtPrime (P.under R)) (P.under R).primeCompl
      (M := LocalizedModule.AtPrime P M)).mp hPflat

/-- Helper for Lemma 10.39.18: localizing away from an element of `A` preserves flatness over
the base ring `R`. -/
lemma flat_localizedModule_away_of_flat (a : A) (hM : Module.Flat R M) :
    Module.Flat R (LocalizedModule.Away a M) := by
  -- This is the previous localization-preservation lemma specialized to a principal submonoid.
  simpa [LocalizedModule.Away] using
    flat_localizedModule_of_flat (R := R) (A := A) (Submonoid.powers a) hM

-- Proof sketch: if `M` is flat over `R`, then every localization away from a generator remains
-- flat; conversely, use the localization-away spanning criterion for flatness over the target ring.
/-- Lemma 10.39.18 (3): if `g₁, …, gₘ` generate the unit ideal of an `R`-algebra `A`, then an
`A`-module `M` is flat over `R` if and only if every localization `M[1 / gᵢ]` is flat over `R`. -/
theorem flat_iff_flat_localizedModule_away_of_span_eq_top
    {n : ℕ} (g : Fin n → A) (hg : Ideal.span (Set.range g) = ⊤) :
    Module.Flat R M ↔ ∀ i : Fin n, Module.Flat R (LocalizedModule.Away (g i) M) := by
  constructor
  · intro hM i
    -- Each localization away from a generator is still flat over `R`.
    exact flat_localizedModule_away_of_flat (R := R) (A := A) (g i) hM
  · intro hAway
    -- The local flatness data match the canonical owner `Module.flat_of_isLocalized_span`.
    apply Module.flat_of_isLocalized_span
      (R := R) (S := A) (M := M) (s := Set.range g) hg
      (Mₛ := fun a ↦ LocalizedModule.Away a.1 M)
      (g := fun a ↦ LocalizedModule.mkLinearMap (Submonoid.powers a.1) M)
    rintro ⟨a, ⟨i, rfl⟩⟩
    exact hAway i

-- Proof sketch: localize a flat `R`-module `M` at each prime of `A` for one implication; for the
-- converse, descend flatness from all prime localizations lying over `R`.
/-- Lemma 10.39.18 (4): for an `R`-algebra `A` and an `A`-module `M`, `M` is flat over `R` if and
only if for every prime ideal `q` of `A`, the localization `M_q` is flat over
`R_{q ∩ R}`. -/
theorem flat_iff_flat_localizedModule_atPrime_over_under
    : Module.Flat R M ↔
        ∀ q : PrimeSpectrum A,
          Module.Flat (Localization.AtPrime (q.asIdeal.under R))
            (LocalizedModule.AtPrime q.asIdeal M) := by
  constructor
  · intro hM q
    -- Relative prime local flatness is localization-preservation plus the localized-ring criterion.
    exact flat_localizedModule_atPrime_over_under_of_flat (R := R) (A := A) hM q
  · intro hPrime
    -- The prime-local hypotheses in particular give the maximal-local ones.
    exact flat_of_flat_localizedModule_atMaximal_over_under (R := R) (A := A)
      (M := M) fun m ↦ by
        simpa using hPrime m.toPrimeSpectrum

-- Proof sketch: the forward implication follows by localization at maximal ideals of `A`; the
-- converse is obtained from the prime-local criterion by restricting to maximal ideals.
/-- Lemma 10.39.18 (5): for an `R`-algebra `A` and an `A`-module `M`, `M` is flat over `R` if and
only if for every maximal ideal `m` of `A`, the localization `Mₘ` is flat over
`R_{m ∩ R}`. -/
theorem flat_iff_flat_localizedModule_atMaximal_over_under
    : Module.Flat R M ↔
        ∀ m : MaximalSpectrum A,
          Module.Flat (Localization.AtPrime (m.asIdeal.under R))
            (LocalizedModule.AtPrime m.asIdeal M) := by
  constructor
  · intro hM m
    -- The maximal-local statement is the prime-local statement specialized to a maximal ideal.
    simpa using
      flat_localizedModule_atPrime_over_under_of_flat (R := R) (A := A) hM m.toPrimeSpectrum
  · intro hMax
    -- This is exactly the maximal-local descent helper proved above.
    exact flat_of_flat_localizedModule_atMaximal_over_under (R := R) (A := A) (M := M) hMax

end

end RelativeLocalizationFlatness

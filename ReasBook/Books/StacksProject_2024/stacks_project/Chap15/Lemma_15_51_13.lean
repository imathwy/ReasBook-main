import Mathlib
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_43_8
import StacksProject_2024.Chap10.Lemma_10_45_3
import StacksProject_2024.Chap10.Lemma_10_163_5
import StacksProject_2024.Chap10.Lemma_10_163_10
import StacksProject_2024.Chap10.Lemma_10_164_6
import StacksProject_2024.Chap10.Lemma_10_166_4
import StacksProject_2024.Chap10.Lemma_10_158_10
import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap15.Lemma_15_41_3_Regular_maps_and_base_change
import StacksProject_2024.Chap15.Lemma_15_51_11

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open IsLocalRing
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

namespace Algebra

/-- The finite-field-extension form of Serre's condition `(R_n)`, viewed as a Chapter 15
`FieldAlgebraProperty`. -/
abbrev FiniteFieldExtensionSerreConditionRProperty (n : ℕ) : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦
    ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
      SerreConditionR (K ⊗[k] A) n

end Algebra

section

variable {n : ℕ}

/-- Helper for Lemma 15.51.13: evaluating the finite-field-extension property at a chosen finite
extension just unfolds the defining quantifier. -/
theorem finiteFieldExtensionSerreConditionRProperty_apply
    {k : Type u} {A : Type u} {K : Type u}
    [Field k] [CommRing A] [Algebra k A]
    [Field K] [Algebra k K] [FiniteDimensional k K]
    (hA : @Algebra.FiniteFieldExtensionSerreConditionRProperty.{u} n k A
      inferInstance inferInstance inferInstance) :
    SerreConditionR (K ⊗[k] A) n := by
  -- Within the owner universe of `FieldAlgebraProperty`, evaluation is just the defining
  -- quantifier of the abbreviation.
  exact hA K

/-- Helper for Lemma 15.51.13: Serre's condition `(R_n)` ascends along a regular ring map. -/
theorem serreConditionR_of_regularRingHom
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    [f.IsRegularRingMap] [IsNoetherianRing S] [SerreConditionR R n] :
    SerreConditionR S n := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  exact
    serreConditionR_of_flat_of_fiber (R := R) (S := S) (k := n) fun p ↦ by
      let _ : IsRegularRing (p.asIdeal.Fiber S) := hRS.isRegularRing_fiber p
      exact IsRegularRing.serreConditionR n

/-- Helper for Lemma 15.51.13: Serre's condition `(R_n)` is invariant under ring equivalence. -/
theorem serreConditionR_iff_of_ringEquiv
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    SerreConditionR R n ↔ SerreConditionR S n := by
  constructor
  · intro hR
    letI : SerreConditionR R n := hR
    exact
      serreConditionR_of_faithfullyFlat e.symm.toRingHom
        (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)
  · intro hS
    letI : SerreConditionR S n := hS
    exact
      serreConditionR_of_faithfullyFlat e.toRingHom
        (RingHom.FaithfullyFlat.of_bijective e.bijective)

/-- Helper for Lemma 15.51.13: swapping the factors of a tensor product preserves Serre's
condition `(R_n)` because the two tensor products are ring-equivalent. -/
theorem serreConditionR_of_tensorProduct_comm
    {k : Type u} {A : Type u} {K : Type u}
    [Field k] [CommRing A] [Field K] [Algebra k A] [Algebra k K]
    (h : SerreConditionR (A ⊗[k] K) n) :
    SerreConditionR (K ⊗[k] A) n := by
  -- Proof comment: the tensor commutor is a ring equivalence, so `(R_n)` transports across it.
  exact
    (serreConditionR_iff_of_ringEquiv (n := n)
      (Algebra.TensorProduct.comm k A K).toRingEquiv).1 h

/-- Helper for Lemma 15.51.13: smooth ring maps are regular ring maps. -/
theorem regularRingMap_of_smooth
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] :
    (algebraMap R S).IsRegularRingMap := by
  refine
    { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
      isGeometricallyRegular_fiber := fun p ↦ ?_ }
  -- Each fiber stays smooth over the residue field after base change, hence geometrically regular.
  letI : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  letI : Algebra.IsGeometricallyRegular p.asIdeal.ResidueField p.asIdeal.ResidueField :=
    inferInstance
  infer_instance

/-- Helper for Lemma 15.51.13: Serre's condition `(R_n)` is preserved by localization. -/
theorem serreConditionR_of_isLocalization
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [SerreConditionR R n] :
    SerreConditionR S n := by
  let _ : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_localizationAtPrime := ?_ }
  intro q hq
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal := by
    -- Localizing the localization `S` at `q` gives the same ring as localizing `R` at `q ∩ R`.
    simpa [p] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
        (Localization.AtPrime q.asIdeal) q.asIdeal)
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime q.asIdeal :=
    IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
  have hqdim : ringKrullDim (Localization.AtPrime q.asIdeal) ≤ n := by
    -- Route correction: rewrite the height bound at `q` into the localized Krull-dimension bound
    -- expected by the iterated-localization comparison.
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal) = ↑q.asIdeal.height := by
        exact IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
          (Localization.AtPrime q.asIdeal)
      _ ≤ n := by
        rw [Ideal.height_eq_primeHeight]
        exact_mod_cast hq
  have hpdim : ringKrullDim (Localization.AtPrime p.asIdeal) ≤ n := by
    -- Transport the dimension bound across the iterated-localization equivalence.
    rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    exact hqdim
  have hp : (p.asIdeal.primeHeight : ENat) ≤ n := by
    -- Rewrite the transported localization bound back into the prime-height form used by `(R_n)`.
    have hp' : ((p.asIdeal.primeHeight : ENat) : WithBot ℕ∞) ≤ n := by
      calc
        ((p.asIdeal.primeHeight : ENat) : WithBot ℕ∞)
            = ringKrullDim (Localization.AtPrime p.asIdeal) := by
              symm
              simpa [Ideal.height_eq_primeHeight] using
                (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
                  (Localization.AtPrime p.asIdeal))
        _ ≤ n := hpdim
    exact_mod_cast hp'
  have hregp : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    SerreConditionR.isRegularLocalRing_localizationAtPrime p hp
  let _ : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hregp
  -- The target localization is regular because it is ring-equivalent to the source localization.
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

/-- Helper for Lemma 15.51.13: passing from a smooth `k'`-model to its fraction field preserves
Serre's condition `(R_n)` on the tensor product. -/
theorem serreConditionR_of_fractionRing_tensor_model
    {k' : Type u} {K' : Type u} {S0 : Type u} {B : Type u}
    [Field k'] [Field K'] [CommRing S0] [CommRing B]
    [Algebra k' S0] [Algebra k' B] [Algebra k' K'] [Algebra B K'] [IsScalarTower k' B K']
    [IsFractionRing B K'] [SerreConditionR (B ⊗[k'] S0) n] :
    SerreConditionR (K' ⊗[k'] S0) n := by
  -- TODO: prove this by keeping the proof on the explicit tensor model `S0 ⊗[k'] B`,
  -- localizing along `B → K'`, and only then cancelling the middle base change to
  -- reach `K' ⊗[k'] S0`. The current blocker is the base-ring alignment for
  -- `cancelBaseChangeAlg` on the localization model.
  sorry

/-- Helper for Lemma 15.51.13: if `K / k` is essentially of finite type and every finite field
extension of `k` gives `(R_n)` after tensoring with `A`, then `K ⊗[k] A` has `(R_n)`. -/
theorem serreConditionR_tensorProduct_of_essFiniteType_fieldExtension
    {k : Type u} {K : Type u} {A : Type u}
    [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A] [Algebra.EssFiniteType k K]
    (hA : FiniteFieldExtensionSerreConditionRProperty n k A) :
    SerreConditionR (K ⊗[k] A) n := by
  -- TODO: follow the textbook route `k → k' → B → K'`. The existing source-faithful plan is:
  -- evaluate the property on `S0 := k' ⊗[k] A`, ascend along the smooth base change to
  -- `B ⊗[k'] S0`, pass to `K'` by the fraction-ring localization helper above, and then descend
  -- from `K'` back to `K` by faithfully flat tensor descent. The current blocker is the
  -- smooth-model/fraction-ring interface from the previous theorem.
  sorry

/-- Lemma 15.51.13 (1): the finite-field-extension form of Serre's condition `(R_n)` is preserved
after base change along a finitely generated extension of the ground field. -/
theorem finiteFieldExtensionSerreConditionR_baseChange_of_finitelyGeneratedFieldExtension
    {k : Type u} {K : Type u} {A : Type u}
    [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A] [Algebra.EssFiniteType k K]
    (hA : FiniteFieldExtensionSerreConditionRProperty n k A) :
    FiniteFieldExtensionSerreConditionRProperty n K (K ⊗[k] A) := by
  -- TODO: after the essentially-finite-type tensor theorem above is repaired, apply it to the
  -- composite finitely generated extension `L / k` and cancel the middle `K`-base change.
  sorry

/-- Helper for Lemma 15.51.13: a finite extension of the ground field preserves the same-ring
finite-field-extension form of Serre's condition `(R_n)`. -/
theorem finiteFieldExtensionSerreConditionR_of_finite_baseFieldExtension
    {k : Type u} {k' : Type u} {A : Type u}
    [Field k] [Field k'] [CommRing A]
    [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
    [FiniteDimensional k k']
    (hA : FiniteFieldExtensionSerreConditionRProperty n k A) :
    FiniteFieldExtensionSerreConditionRProperty n k' A := by
  -- TODO: prove this by combining the finitely-generated base-change theorem with the canonical
  -- algebra equivalence `k' ⊗[k] A ≃ₐ[k'] A`. The remaining blocker is packaging the tensor-unit
  -- comparison in the Chapter 15 universe discipline used by `FieldAlgebraProperty`.
  sorry

/-- Helper for Lemma 15.51.13: for a Noetherian ring, Serre's condition `(R_n)` can be checked on
all prime localizations. -/
theorem serreConditionR_iff_localizationAtPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    SerreConditionR R n ↔
      ∀ p : PrimeSpectrum R, SerreConditionR (Localization.AtPrime p.asIdeal) n := by
  constructor
  · intro hR p
    letI : SerreConditionR R n := hR
    -- The forward implication is exactly localization stability for `(R_n)`.
    exact serreConditionR_of_isLocalization (n := n) p.asIdeal.primeCompl
  · intro hlocal
    refine
      { toIsNoetherian := inferInstance
        isRegularLocalRing_localizationAtPrime := ?_ }
    intro p hp
    let A := Localization.AtPrime p.asIdeal
    letI : SerreConditionR A n := hlocal p
    have hdim : ringKrullDim A ≤ n := by
      -- Rewrite the source height bound at `p` into the Krull-dimension bound on `A = R_p`.
      calc
        ringKrullDim A = ↑p.asIdeal.height := by
          exact IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A
        _ ≤ n := by
          rw [Ideal.height_eq_primeHeight]
          exact_mod_cast hp
    let e : Localization.AtPrime (closedPoint A).asIdeal ≃ₐ[A] A :=
      localizationAtClosedPoint_algEquiv_self A
    have hclosed : ((closedPoint A).asIdeal.primeHeight : ENat) ≤ n := by
      -- Transport the local Krull-dimension bound to the closed-point localization and rewrite
      -- once back to the prime-height criterion required by `SerreConditionR`.
      have hclosed' : (((closedPoint A).asIdeal.primeHeight : ENat) : WithBot ℕ∞) ≤ n := by
        calc
          (((closedPoint A).asIdeal.primeHeight : ENat) : WithBot ℕ∞)
              = ringKrullDim (Localization.AtPrime (closedPoint A).asIdeal) := by
                symm
                simpa [Ideal.height_eq_primeHeight] using
                  (IsLocalization.AtPrime.ringKrullDim_eq_height (closedPoint A).asIdeal
                    (Localization.AtPrime (closedPoint A).asIdeal))
          _ = ringKrullDim A := by
            simpa using ringKrullDim_eq_of_ringEquiv e.toRingEquiv
          _ ≤ n := hdim
      exact_mod_cast hclosed'
    have hregClosed : IsRegularLocalRing (Localization.AtPrime (closedPoint A).asIdeal) :=
      SerreConditionR.isRegularLocalRing_localizationAtPrime
        (R := A) (k := n) (p := closedPoint A) hclosed
    let _ : IsRegularLocalRing (Localization.AtPrime (closedPoint A).asIdeal) := hregClosed
    -- Regularity at the closed point of `A` is exactly regularity of `A` itself.
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

section

variable {k : Type u} {A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- Lemma 15.51.13 (2): for a Noetherian `k`-algebra `A`, the finite-field-extension form of
Serre's condition `(R_n)` can be checked on the localizations `A_𝔭`. -/
theorem finiteFieldExtensionSerreConditionR_iff_localizationAtPrime [IsNoetherianRing A] :
    FiniteFieldExtensionSerreConditionRProperty n k A ↔
      ∀ p : PrimeSpectrum A,
        FiniteFieldExtensionSerreConditionRProperty n k (Localization.AtPrime p.asIdeal) := by
  -- TODO: restore the explicit localization model
  -- `D := (K ⊗[k] A) ⊗[A] A_p`, prove that it is a localization of `K ⊗[k] A`,
  -- and use the prime-comparison argument already outlined here. The remaining blocker is the
  -- Noetherian/localization elaboration around the reverse implication.
  sorry

end

section

variable {κ : Type u} {R : Type u} {S : Type u}
variable [Field κ] [CommRing R] [CommRing S]
variable [Algebra κ R] [Algebra κ S] [Algebra R S]
variable [Module.FaithfullyFlat R S]

/-- Helper for Lemma 15.51.13: after tensoring a faithfully flat `κ`-algebra map by `K`,
Serre's condition `(R_n)` descends from `K ⊗[κ] S` to `K ⊗[κ] R`. -/
theorem tensor_product_serreConditionR_of_faithfullyFlat
    (hcomm : ∀ x : κ, algebraMap κ S x = (algebraMap R S) ((algebraMap κ R) x))
    (K : Type u) [Field K] [Algebra κ K]
    [SerreConditionR (K ⊗[κ] S) n] :
    SerreConditionR (K ⊗[κ] R) n := by
  letI : IsScalarTower κ R S := IsScalarTower.of_algebraMap_eq hcomm
  letI : Algebra R (K ⊗[κ] R) := Algebra.TensorProduct.rightAlgebra
  let D := (K ⊗[κ] R) ⊗[R] S
  letI : CommRing D := inferInstance
  letI : Algebra (K ⊗[κ] R) D := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S D := Algebra.TensorProduct.rightAlgebra
  let f : (K ⊗[κ] R) →+* D := algebraMap (K ⊗[κ] R) D
  have hf : f.FaithfullyFlat := by
    -- Base change preserves faithful flatness for the tensor square.
    letI : Module.FaithfullyFlat (K ⊗[κ] R) D := inferInstance
    simpa [f] using
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f.FaithfullyFlat)
  let e : D ≃ₐ[K] (K ⊗[κ] S) :=
    Algebra.IsPushout.cancelBaseChangeAlg κ K R (K ⊗[κ] R) S
  have hD : SerreConditionR D n := by
    -- The explicit tensor square is the pushout model of `K ⊗[κ] S`.
    exact (serreConditionR_iff_of_ringEquiv (n := n) e.toRingEquiv).2 inferInstance
  letI : SerreConditionR D n := hD
  -- Descend `(R_n)` along the faithfully flat tensor extension.
  exact serreConditionR_of_faithfullyFlat f hf

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]

/-- Lemma 15.51.13 (3): if `A → B → C` are maps of Noetherian rings, `A → B` is flat, every fiber
of `A → B` satisfies the finite-field-extension form of `(R_n)`, and `B → C` is regular, then
every fiber of `A → C` satisfies the same property. -/
theorem fiber_finiteFieldExtensionSerreConditionR_of_regularRingMap [Module.Flat A B]
    [(algebraMap B C).IsRegularRingMap]
    (hfiber :
      ∀ p : PrimeSpectrum A,
        FiniteFieldExtensionSerreConditionRProperty n p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    ∀ p : PrimeSpectrum A,
      FiniteFieldExtensionSerreConditionRProperty n p.asIdeal.ResidueField (p.asIdeal.Fiber C) :=
    by
  -- TODO: follow the stable Chapter 15 fiber pattern: identify `S0 := B ⊗[A] κ(p)` with the
  -- actual fiber by ring equivalence, tensor with `K / κ(p)`, ascend along the regular map after
  -- the two base changes, and finally transport back to `K ⊗[κ(p)] Fiber C`. The current blocker
  -- is the universe-stable regular-base-change step on the `U0 := S0 ⊗[κ] K` model.
  sorry

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
  [IsLocalRing B] [IsLocalRing C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] in
/-- Helper for Lemma 15.51.13: after tensoring the closed fiber with a finite extension of the
residue field, Serre's condition `(R_n)` descends along the induced faithfully flat map. -/
theorem serreConditionR_closedFiber_tensor_of_faithfullyFlat
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (K : Type v) [Field K] [Algebra (ResidueField A) K]
    [FiniteDimensional (ResidueField A) K]
    [SerreConditionR (K ⊗[ResidueField A] ((maximalIdeal A).Fiber C)) n] :
    SerreConditionR (K ⊗[ResidueField A] ((maximalIdeal A).Fiber B)) n := by
  -- TODO: descend faithful flatness from `B → C` to the closed fibers, identify the explicit
  -- tensor model of the closed fiber of `C`, and then apply the generic tensor faithfully-flat
  -- descent theorem. The current blocker is the explicit tensor/pushout bookkeeping on the closed
  -- fiber comparison map.
  sorry

omit [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
  [IsLocalRing B] [IsLocalRing C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] in
/-- Lemma 15.51.13 (4): under a faithfully flat local extension on closed fibers, the
finite-field-extension form of Serre's condition `(R_n)` descends from the closed fiber over `C`
to the closed fiber over `B`. -/
theorem closedFiber_finiteFieldExtensionSerreConditionR_of_faithfullyFlat
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (hC :
      FiniteFieldExtensionSerreConditionRProperty n (ResidueField A) ((maximalIdeal A).Fiber C)) :
    FiniteFieldExtensionSerreConditionRProperty n (ResidueField A) ((maximalIdeal A).Fiber B) :=
    by
  -- TODO: once the owner-universe mismatch for `FiniteFieldExtensionSerreConditionRProperty`
  -- evaluation is repaired, evaluate `hC` at the chosen finite residue-field extension `K` and
  -- descend `(R_n)` through `serreConditionR_closedFiber_tensor_of_faithfullyFlat`.
  sorry

end

end

namespace Algebra

section

variable {n : ℕ}

/-- Helper for Lemma 15.51.13: once the descended tensor comparison is expressed as a ring
equivalence, Serre's condition `(R_n)` transports across it. -/
theorem serreConditionR_of_descended_tensor_ringEquiv
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (hS : SerreConditionR S n) :
    SerreConditionR R n := by
  -- Proof comment: `(R_n)` is a ring-theoretic property, so a chosen ring equivalence lets us
  -- move it back from the descended tensor model to the original tensor product.
  exact (serreConditionR_iff_of_ringEquiv (n := n) e).2 hS

/-- Lemma 15.51.13 (5), owner-form: the Chapter 15 field-algebra property
`P(k → R) := ∀ K / k` finite, `SerreConditionR (K ⊗[k] R) n` has property `(E)`. -/
theorem finiteFieldExtensionSerreConditionR_hasPropertyE :
    (FiniteFieldExtensionSerreConditionRProperty n).HasPropertyE := by
  refine { separableBaseChange := ?_ }
  intro k k' A _ _ _ _ _ _ _ _ hA
  intro L _ _ _
  -- Route correction: the owner proof now follows the textbook decomposition explicitly. For the
  -- finite test extension `L / k'`, first descend it to a finite stage `m' / m / k`; then apply
  -- the already-proved finite-field-extension package over the finite subextension `m / k`; and
  -- finally transport `(R_n)` back to `L ⊗[k'] A`.
  -- TODO: prove the finite-stage descent lemma producing finite fields `m / k` and `m' / m`
  -- together with a tensor comparison `L ⊗[k'] A ≃+* m' ⊗[m] A`, and combine it with the finite
  -- separable same-ring step over `m / k`.
  sorry

/-- Helper for Lemma 15.51.13: the finite-field-extension form of Serre's condition `(R_n)` has
property `(C)` in the Chapter 15 owner package. -/
instance finiteFieldExtensionSerreConditionR_hasPropertyC :
    FieldAlgebraProperty.HasPropertyC (FiniteFieldExtensionSerreConditionRProperty n) where
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hfiber
    exact fiber_finiteFieldExtensionSerreConditionR_of_regularRingMap (n := n) hfiber

/-- Helper for Lemma 15.51.13: the finite-field-extension form of Serre's condition `(R_n)` has
property `(D)` in the Chapter 15 owner package. -/
instance finiteFieldExtensionSerreConditionR_hasPropertyD :
    FieldAlgebraProperty.HasPropertyD (FiniteFieldExtensionSerreConditionRProperty n) where
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    exact closedFiber_finiteFieldExtensionSerreConditionR_of_faithfullyFlat (n := n) hBC hC

/-- Lemma 15.51.13 packages the finite-field-extension form of Serre's condition `(R_n)` into the
canonical owner for field-algebra properties satisfying `(A)` through `(E)`. -/
instance finiteFieldExtensionSerreConditionR_hasPropertiesABCDE :
    (FiniteFieldExtensionSerreConditionRProperty n).HasPropertiesABCDE where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hA
    exact finiteFieldExtensionSerreConditionR_baseChange_of_finitelyGeneratedFieldExtension hA
  localizationCriterion := by
    intro k A _ _ _ _
    exact finiteFieldExtensionSerreConditionR_iff_localizationAtPrime
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hfiber
    exact fiber_finiteFieldExtensionSerreConditionR_of_regularRingMap (n := n) hfiber
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    exact closedFiber_finiteFieldExtensionSerreConditionR_of_faithfullyFlat (n := n) hBC hC
  separableBaseChange := by
    simpa using finiteFieldExtensionSerreConditionR_hasPropertyE.separableBaseChange

end

end Algebra

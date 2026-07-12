import Mathlib
import StacksProject_2024.Chap15.Lemma_15_9_1
import StacksProject_2024.Chap15.Lemma_15_9_5

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 15.9.6: constant polynomials attached to a unit and its inverse multiply to
`1`. -/
lemma constant_unit_mul_constant_inv_eq_one
    {R : Type*} [CommRing R] (u : Units R) :
    C (↑u : R) * C (↑u⁻¹ : R) = (1 : R[X]) := by
  -- Compare coefficients: only the constant term survives, and it is `u * u⁻¹ = 1`.
  ext i
  cases i with
  | zero =>
      simp
  | succ n =>
      simpa [Polynomial.coeff_one]

-- Proof sketch: lift the unit leading coefficient of `gbar` to a unit after an étale localization
-- using Lemma `15.9.1`, rescale `gbar` and `hbar` so that both become monic modulo `I`, and then
-- apply the monic lifting statement of Lemma `15.9.5`. Finally rescale the lifted factors back by
-- the lifted unit to recover a lift of the original factorization.
/-- Lemma 15.9.6: if a monic polynomial `f` factors modulo `I` as `gbar * hbar`, with invertible
leading coefficient for `gbar` and with `gbar`, `hbar` generating the unit ideal in
`(A ⧸ I)[X]`, then after an étale base change `A → A'` inducing an isomorphism
`A ⧸ I ≃ A' ⧸ IA'`, the polynomial `f` admits a factorization `g' * h'` lifting the given
factorization over `A ⧸ I`. -/
@[stacks 07M1]
theorem exists_etale_factorization_lift_of_isUnit_leadingCoeff
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hunit : IsUnit gbar.leadingCoeff) (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
        f.map (algebraMap A A') = g' * h' ∧
          gbar.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
          hbar.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) :=
  by
    -- First make the leading coefficient invertible on the nose by localizing away from a lift.
    obtain ⟨u, q1, hu⟩ :=
      exists_quotientAlgEquiv_localizationAway_of_isUnit_quotient
        (A := A) (I := I) (u_bar := gbar.leadingCoeff) hunit
    let A1 : Type u := Localization.Away u
    let I1 : Ideal A1 := Ideal.map (algebraMap A A1) I
    let g1 : (A1 ⧸ I1)[X] := gbar.map q1.toRingHom
    let h1 : (A1 ⧸ I1)[X] := hbar.map q1.toRingHom
    let u1 : Units A1 := IsUnit.unit (IsLocalization.Away.algebraMap_isUnit u)
    let u1bar : Units (A1 ⧸ I1) := u1.map (Ideal.Quotient.mk I1)
    let g0 : (A1 ⧸ I1)[X] := C (↑u1bar⁻¹ : A1 ⧸ I1) * g1
    let h0 : (A1 ⧸ I1)[X] := C (↑u1bar : A1 ⧸ I1) * h1
    have hmap_comp :
        (Ideal.Quotient.mk I1).comp (algebraMap A A1) =
          q1.toRingHom.comp (Ideal.Quotient.mk I) := by
      -- The quotient equivalence `q1` is an `(A / I)`-algebra map, so it agrees with the
      -- canonical quotient map on coefficients from `A`.
      ext a
      simpa [I1, RingHom.comp_apply] using (q1.commutes (Ideal.Quotient.mk I a)).symm
    have hfactor1 :
        (f.map (algebraMap A A1)).map (Ideal.Quotient.mk I1) = g1 * h1 := by
      -- Transport the original residue factorization along the quotient equivalence `q1`.
      calc
        (f.map (algebraMap A A1)).map (Ideal.Quotient.mk I1)
            = f.map (q1.toRingHom.comp (Ideal.Quotient.mk I)) := by
                rw [Polynomial.map_map, hmap_comp]
        _ = (f.map (Ideal.Quotient.mk I)).map q1.toRingHom := by
              rw [Polynomial.map_map]
        _ = (gbar * hbar).map q1.toRingHom := by rw [hfactor]
        _ = g1 * h1 := by
              simp [g1, h1, Polynomial.map_mul]
    have hu1bar_apply : q1 (Ideal.Quotient.mk I u) = (↑u1bar : A1 ⧸ I1) := by
      -- The localized lift of `u` reduces to the same quotient unit as `q1` sends `ū` to.
      simpa [u1bar, u1, I1] using (q1.commutes (Ideal.Quotient.mk I u))
    have hg1_leading :
        g1.leadingCoeff = (↑u1bar : A1 ⧸ I1) := by
      -- The leading coefficient of the transported factor is exactly the chosen quotient unit.
      calc
        g1.leadingCoeff = q1.toRingHom gbar.leadingCoeff := by
          simpa [g1] using
            (Polynomial.leadingCoeff_map_of_injective (f := q1.toRingHom) q1.injective gbar)
        _ = q1.toRingHom (Ideal.Quotient.mk I u) := by
              rw [hu]
        _ = (↑u1bar : A1 ⧸ I1) := hu1bar_apply
    have hg0 : g0.Monic := by
      -- Normalize the first factor by dividing by its unit leading coefficient.
      have hunit1 : IsUnit g1.leadingCoeff := ⟨u1bar, hg1_leading.symm⟩
      have hunit1_eq : hunit1.unit = u1bar := by
        apply Units.ext
        simpa [hunit1, hg1_leading]
      have hmonic : (hunit1.unit⁻¹ • g1).Monic :=
        monic_of_isUnit_leadingCoeff_inv_smul hunit1
      simpa [g0, Units.smul_def, Polynomial.smul_eq_C_mul, hunit1_eq] using hmonic
    have hconst_cancel :
        C (↑u1bar⁻¹ : A1 ⧸ I1) * C (↑u1bar : A1 ⧸ I1) = (1 : (A1 ⧸ I1)[X]) := by
      -- The normalization constants cancel because they come from a unit and its inverse.
      ext i
      cases i with
      | zero =>
          simp
      | succ n =>
          simpa [Polynomial.coeff_one]
    have hconst_cancel' :
        C (↑u1bar : A1 ⧸ I1) * C (↑u1bar⁻¹ : A1 ⧸ I1) = (1 : (A1 ⧸ I1)[X]) := by
      -- The same cancellation holds in the opposite order by commutativity.
      calc
        C (↑u1bar : A1 ⧸ I1) * C (↑u1bar⁻¹ : A1 ⧸ I1)
            = C (↑u1bar⁻¹ : A1 ⧸ I1) * C (↑u1bar : A1 ⧸ I1) := by
                rw [mul_comm]
        _ = (1 : (A1 ⧸ I1)[X]) := hconst_cancel
    have hscale0 : g0 * h0 = g1 * h1 := by
      -- The inverse unit scalars cancel when the normalized factors are multiplied back together.
      calc
        g0 * h0
            = (C (↑u1bar⁻¹ : A1 ⧸ I1) * g1) * (C (↑u1bar : A1 ⧸ I1) * h1) := by
                rfl
        _ = (C (↑u1bar⁻¹ : A1 ⧸ I1) * C (↑u1bar : A1 ⧸ I1)) * (g1 * h1) := by
              ac_rfl
        _ = (1 : (A1 ⧸ I1)[X]) * (g1 * h1) := by rw [hconst_cancel]
        _ = g1 * h1 := by simp
    have hfactor0 :
        (f.map (algebraMap A A1)).map (Ideal.Quotient.mk I1) = g0 * h0 := by
      -- The two normalizing scalars cancel in the product, so the residue factorization is
      -- unchanged after normalization.
      calc
        (f.map (algebraMap A A1)).map (Ideal.Quotient.mk I1) = g1 * h1 := hfactor1
        _ = g0 * h0 := hscale0.symm
    have hprod_monic : (g0 * h0).Monic := by
      -- The normalized product is still the reduction of the monic polynomial `f`.
      have hm :
          ((f.map (algebraMap A A1)).map (Ideal.Quotient.mk I1)).Monic := by
        simpa using (hf.map (algebraMap A A1)).map (Ideal.Quotient.mk I1)
      simpa [hfactor0] using hm
    have hh0 : h0.Monic := by
      -- Once the left normalized factor is monic, the monicity of the total product forces the
      -- right normalized factor to be monic as well.
      exact hg0.of_mul_monic_left hprod_monic
    have hcoprime1 : IsCoprime g1 h1 := by
      -- Transport the Bézout relation defining coprimeness along `q1`.
      rcases hcoprime with ⟨a, b, hab⟩
      refine ⟨a.map q1.toRingHom, b.map q1.toRingHom, ?_⟩
      simpa [g1, h1, Polynomial.map_add, Polynomial.map_mul] using
        congrArg (Polynomial.map q1.toRingHom) hab
    have hcoprime0 : IsCoprime g0 h0 := by
      -- Scaling the two factors by inverse units preserves the Bézout identity.
      rcases hcoprime1 with ⟨a, b, hab⟩
      refine ⟨C (↑u1bar : A1 ⧸ I1) * a, C (↑u1bar⁻¹ : A1 ⧸ I1) * b, ?_⟩
      calc
        (C (↑u1bar : A1 ⧸ I1) * a) * g0 + (C (↑u1bar⁻¹ : A1 ⧸ I1) * b) * h0
            = (C (↑u1bar : A1 ⧸ I1) * C (↑u1bar⁻¹ : A1 ⧸ I1)) * (a * g1) +
                (C (↑u1bar⁻¹ : A1 ⧸ I1) * C (↑u1bar : A1 ⧸ I1)) * (b * h1) := by
                  simp [g0, h0]
                  ac_rfl
        _ = (1 : (A1 ⧸ I1)[X]) * (a * g1) + (1 : (A1 ⧸ I1)[X]) * (b * h1) := by
              rw [hconst_cancel', hconst_cancel]
        _ = a * g1 + b * h1 := by simp
        _ = 1 := hab
    -- Apply the monic lifting theorem over the localized base ring `A1`.
    obtain ⟨A2, _, _, _, q2, G, H, hGmonic, hHmonic, hGH, hGred, hHred⟩ :=
      exists_etale_lift_factorization_of_monic_mod_ideal
        (A := A1) I1 (f.map (algebraMap A A1)) g0 h0
        (hf.map (algebraMap A A1)) hg0 hh0 hfactor0 hcoprime0
    letI : Algebra A A1 := inferInstance
    letI : Algebra A A2 :=
      ((algebraMap A1 A2).comp (algebraMap A A1)).toAlgebra
    letI : IsScalarTower A A1 A2 :=
      IsScalarTower.of_algebraMap_eq' <|
        RingHom.ext fun a ↦ rfl
    have hEtaleA2 : Etale A A2 := by
      -- Étaleness is stable under composition with the initial away-localization.
      letI : Etale A A1 := Algebra.Etale.of_isLocalizationAway u
      exact (Algebra.Etale.comp (R := A) (A := A1) (B := A2) : Etale A A2)
    let K1 : Ideal A2 := Ideal.map (algebraMap A1 A2) I1
    let K : Ideal A2 := Ideal.map (algebraMap A A2) I
    have hI2 :
        K1 = K := by
      -- The iterated ideal extension `I A1 A2` agrees with the direct extension `I A2`.
      simpa [I1, K] using
        (localized_extended_ideal_eq (A := A) (B := A1) (A' := A2) I)
    -- Route correction: freeze the quotient transport `K1 = K` once and reuse that packaged
    -- comparison instead of coercing `q2` through definitional equality at each rewrite.
    let qTransport : (A2 ⧸ K1) ≃+* (A2 ⧸ K) :=
      (Ideal.quotientEquivAlgOfEq A2 hI2).toRingEquiv
    let q2K : (A1 ⧸ I1) ≃+* (A2 ⧸ K) :=
      q2.toRingEquiv.trans qTransport
    let qTotal : (A ⧸ I) ≃+* (A2 ⧸ K) :=
      q1.toRingEquiv.trans q2K
    let v : Units A2 := u1.map (algebraMap A1 A2)
    let vbar : Units (A2 ⧸ K) := v.map (Ideal.Quotient.mk K)
    let g' : A2[X] := C (↑v : A2) * G
    let h' : A2[X] := C (↑v⁻¹ : A2) * H
    have hq2K_mk (a : A1) :
        q2K (Ideal.Quotient.mk I1 a) = Ideal.Quotient.mk K (algebraMap A1 A2 a) := by
      -- The transported quotient comparison still sends coefficient classes to coefficient
      -- classes after rewriting the target ideal from `K1` to `K`.
      calc
        q2K (Ideal.Quotient.mk I1 a)
            = qTransport (q2 (Ideal.Quotient.mk I1 a)) := by
                rfl
        _ = qTransport
              (Ideal.Quotient.mk K1 (algebraMap A1 A2 a)) := by
                simpa [K1, I1] using (q2.commutes (Ideal.Quotient.mk I1 a))
        _ = Ideal.Quotient.mk K (algebraMap A1 A2 a) := by
              change (Ideal.quotientEquivAlgOfEq A2 hI2)
                  (Ideal.Quotient.mk K1 (algebraMap A1 A2 a)) =
                Ideal.Quotient.mk K (algebraMap A1 A2 a)
              rw [Ideal.quotientEquivAlgOfEq_mk]
    have hq2K_u1bar :
        q2K (↑u1bar : A1 ⧸ I1) = (↑vbar : A2 ⧸ K) := by
      -- Apply the quotient-class formula to the chosen lift `u1`.
      simpa [u1bar, vbar, v] using hq2K_mk (a := (↑u1 : A1))
    have hq2K_u1bar_inv :
        q2K (↑u1bar⁻¹ : A1 ⧸ I1) = (↑vbar⁻¹ : A2 ⧸ K) := by
      -- The same quotient-class formula handles the inverse unit.
      simpa [u1bar, vbar, v] using hq2K_mk (a := (↑u1⁻¹ : A1))
    have hqTransport_comp :
        qTransport.toRingHom.comp (Ideal.Quotient.mk K1) = Ideal.Quotient.mk K := by
      -- On coefficient classes from `A2`, the transported quotient map is just the canonical
      -- quotient map modulo `K`.
      ext a
      simpa [qTransport] using
        (Ideal.quotientEquivAlgOfEq_mk (R₁ := A2) (h := hI2) (x := a))
    have hqTotal_commutes (x : A ⧸ I) :
        qTotal x = algebraMap (A ⧸ I) (A2 ⧸ K) x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      -- Evaluate the total comparison on a representative from `A`.
      calc
        qTotal (Ideal.Quotient.mk I a)
            = q2K (q1 (Ideal.Quotient.mk I a)) := by
                rfl
        _ = q2K (Ideal.Quotient.mk I1 (algebraMap A A1 a)) := by
              simpa [I1] using (q1.commutes (Ideal.Quotient.mk I a))
        _ = Ideal.Quotient.mk K (algebraMap A1 A2 (algebraMap A A1 a)) := by
              exact hq2K_mk (a := algebraMap A A1 a)
        _ = algebraMap (A ⧸ I) (A2 ⧸ K) (Ideal.Quotient.mk I a) := by
              simp [K, IsScalarTower.algebraMap_eq A A1 A2]
    let quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] (A2 ⧸ K) :=
      { toRingEquiv := qTotal
        commutes' := hqTotal_commutes }
    have hGredK :
        g0.map q2K.toRingHom = G.map (Ideal.Quotient.mk K) := by
      -- Rewrite the reduction of `G` across the identified target ideals `K1 = K`.
      calc
        g0.map q2K.toRingHom
            = (g0.map q2.toRingHom).map
                qTransport.toRingHom := by
                  simp [q2K, Polynomial.map_map]
        _ = (G.map (Ideal.Quotient.mk K1)).map
              qTransport.toRingHom := by
                rw [hGred]
        _ = G.map
              (qTransport.toRingHom.comp (Ideal.Quotient.mk K1)) := by
                  rw [Polynomial.map_map]
        _ = G.map (Ideal.Quotient.mk K) := by
              rw [hqTransport_comp]
    have hHredK :
        h0.map q2K.toRingHom = H.map (Ideal.Quotient.mk K) := by
      -- The same transport step rewrites the reduction of `H` from `K1` to `K`.
      calc
        h0.map q2K.toRingHom
            = (h0.map q2.toRingHom).map
                qTransport.toRingHom := by
                  simp [q2K, Polynomial.map_map]
        _ = (H.map (Ideal.Quotient.mk K1)).map
              qTransport.toRingHom := by
                rw [hHred]
        _ = H.map
              (qTransport.toRingHom.comp (Ideal.Quotient.mk K1)) := by
                  rw [Polynomial.map_map]
        _ = H.map (Ideal.Quotient.mk K) := by
              rw [hqTransport_comp]
    have hg0_map :
        g0.map q2K.toRingHom =
          C (↑vbar⁻¹ : A2 ⧸ K) * g1.map q2K.toRingHom := by
      -- Mapping the normalized left factor records exactly one inverse unit scalar.
      calc
        g0.map q2K.toRingHom
            = (C (↑u1bar⁻¹ : A1 ⧸ I1) * g1).map q2K.toRingHom := by
                rfl
        _ = C (q2K (↑u1bar⁻¹ : A1 ⧸ I1)) * g1.map q2K.toRingHom := by
              simp [Polynomial.map_mul, Polynomial.map_C]
        _ = C (↑vbar⁻¹ : A2 ⧸ K) * g1.map q2K.toRingHom := by
              rw [hq2K_u1bar_inv]
    have hh0_map :
        h0.map q2K.toRingHom =
          C (↑vbar : A2 ⧸ K) * h1.map q2K.toRingHom := by
      -- Mapping the normalized right factor records the complementary unit scalar.
      calc
        h0.map q2K.toRingHom
            = (C (↑u1bar : A1 ⧸ I1) * h1).map q2K.toRingHom := by
                rfl
        _ = C (q2K (↑u1bar : A1 ⧸ I1)) * h1.map q2K.toRingHom := by
              simp [Polynomial.map_mul, Polynomial.map_C]
        _ = C (↑vbar : A2 ⧸ K) * h1.map q2K.toRingHom := by
              rw [hq2K_u1bar]
    have hconst_vbar :
        C (↑vbar : A2 ⧸ K) * C (↑vbar⁻¹ : A2 ⧸ K) = (1 : (A2 ⧸ K)[X]) := by
      -- The transported unit and its inverse still cancel as constant polynomials.
      simpa using constant_unit_mul_constant_inv_eq_one vbar
    have hconst_vbar' :
        C (↑vbar⁻¹ : A2 ⧸ K) * C (↑vbar : A2 ⧸ K) = (1 : (A2 ⧸ K)[X]) := by
      -- We also need the same cancellation in the opposite order for the right factor.
      simpa using constant_unit_mul_constant_inv_eq_one (vbar⁻¹)
    have hg1red :
        g1.map q2K.toRingHom = g'.map (Ideal.Quotient.mk K) := by
      -- Multiply the normalized reduction by the transported unit to recover the original left
      -- factor modulo `K`.
      calc
        g1.map q2K.toRingHom
            = (1 : (A2 ⧸ K)[X]) * g1.map q2K.toRingHom := by simp
        _ = (C (↑vbar : A2 ⧸ K) * C (↑vbar⁻¹ : A2 ⧸ K)) * g1.map q2K.toRingHom := by
              rw [hconst_vbar]
        _ = C (↑vbar : A2 ⧸ K) * (C (↑vbar⁻¹ : A2 ⧸ K) * g1.map q2K.toRingHom) := by
              ac_rfl
        _ = C (↑vbar : A2 ⧸ K) * g0.map q2K.toRingHom := by
              rw [← hg0_map]
        _ = C (↑vbar : A2 ⧸ K) * G.map (Ideal.Quotient.mk K) := by
              rw [hGredK]
        _ = g'.map (Ideal.Quotient.mk K) := by
              simp [g', vbar, v, Polynomial.map_mul, Polynomial.map_C]
    have hh1red :
        h1.map q2K.toRingHom = h'.map (Ideal.Quotient.mk K) := by
      -- Multiply by the inverse transported unit to undo the normalization on the right factor.
      calc
        h1.map q2K.toRingHom
            = (1 : (A2 ⧸ K)[X]) * h1.map q2K.toRingHom := by simp
        _ = (C (↑vbar⁻¹ : A2 ⧸ K) * C (↑vbar : A2 ⧸ K)) * h1.map q2K.toRingHom := by
              rw [hconst_vbar']
        _ = C (↑vbar⁻¹ : A2 ⧸ K) * (C (↑vbar : A2 ⧸ K) * h1.map q2K.toRingHom) := by
              ac_rfl
        _ = C (↑vbar⁻¹ : A2 ⧸ K) * h0.map q2K.toRingHom := by
              rw [← hh0_map]
        _ = C (↑vbar⁻¹ : A2 ⧸ K) * H.map (Ideal.Quotient.mk K) := by
              rw [hHredK]
        _ = h'.map (Ideal.Quotient.mk K) := by
              simp [h', vbar, v, Polynomial.map_mul, Polynomial.map_C]
    have hfactorA2 :
        f.map (algebraMap A A2) = g' * h' := by
      -- After base change to `A2`, the normalized factorization is rescaled back by inverse units.
      calc
        f.map (algebraMap A A2) = G * H := by
          simpa [Polynomial.map_map, IsScalarTower.algebraMap_eq A A1 A2] using hGH
        _ = (1 : A2[X]) * (G * H) := by simp
        _ = (C (↑v : A2) * C (↑v⁻¹ : A2)) * (G * H) := by
              rw [constant_unit_mul_constant_inv_eq_one v]
        _ = (C (↑v : A2) * G) * (C (↑v⁻¹ : A2) * H) := by
              ac_rfl
        _ = g' * h' := by
              simp [g', h']
    have hquotientAlgEquiv_toRingHom :
        quotientAlgEquiv.toRingHom = qTotal.toRingHom := by
      rfl
    have hgbar_red :
        gbar.map quotientAlgEquiv.toRingHom = g'.map (Ideal.Quotient.mk K) := by
      -- Compose the residue comparison `q1` with the transported target comparison `q2K`.
      calc
        gbar.map quotientAlgEquiv.toRingHom = gbar.map qTotal.toRingHom := by
          rw [hquotientAlgEquiv_toRingHom]
        _ = g1.map q2K.toRingHom := by
              simpa [g1, qTotal, Polynomial.map_map]
        _ = g'.map (Ideal.Quotient.mk K) := hg1red
    have hhbar_red :
        hbar.map quotientAlgEquiv.toRingHom = h'.map (Ideal.Quotient.mk K) := by
      -- The same composition rewrites the right factor to the rescaled lift.
      calc
        hbar.map quotientAlgEquiv.toRingHom = hbar.map qTotal.toRingHom := by
          rw [hquotientAlgEquiv_toRingHom]
        _ = h1.map q2K.toRingHom := by
              simpa [h1, qTotal, Polynomial.map_map]
        _ = h'.map (Ideal.Quotient.mk K) := hh1red
    exact ⟨A2, inferInstance, inferInstance, hEtaleA2,
      by simpa [K] using quotientAlgEquiv,
      g', h', hfactorA2,
      by simpa [K] using hgbar_red,
      by simpa [K] using hhbar_red⟩

end

end Algebra

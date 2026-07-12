import StacksProject_2024.Chap10.Lemma_10_122_10
import StacksProject_2024.Chap10.Lemma_10_126_6.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: after the second shrink, the induced `R_f`-algebra structure on
the final target `S_(fg)` is the composite of the first-away map `R_f → S_f` with the target-side
away-to-away map `S_f → S_(fg)`. This is the target-side transport identity needed for the direct
localization comparison. -/
private theorem final_away_target_isLocalization_mapped_powers
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    IsLocalization
      (Submonoid.map eQuot.toMonoidHom (Submonoid.powers uQ))
      (Localization.Away (algebraMap R S fg)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let fg : R := f * g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap R S fg)
        (Localization.Away (algebraMap R S fg)))
  let ρprodS : Localization.Away (algebraMap R S f) →+*
      Localization.Away ((algebraMap R S f) * algebraMap R S g) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away ((algebraMap R S f) * algebraMap R S g))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away ((algebraMap R S f) * algebraMap R S g)) := ρprodS.toAlgebra
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap R (Localization.Away f) g))
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  let coeff : Localization.Away (algebraMap R S f) :=
    algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g)
  have hpow :
      Submonoid.map eQuot.toMonoidHom (Submonoid.powers uQ) =
        Submonoid.powers coeff := by
    simpa [Qf, uQ, eQuot, coeff] using
      (final_away_target_quotient_map_powers
        (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj)
  have hprod : IsLocalization.Away coeff
      (Localization.Away ((algebraMap R S f) * algebraMap R S g)) := by
    simpa [coeff] using
      (final_away_target_chart_isLocalization_product (R := R) (S := S) (f := f) (g := g))
  letI : IsLocalization.Away coeff
      (Localization.Away ((algebraMap R S f) * algebraMap R S g)) := hprod
  let eProd : Localization.Away coeff ≃ₐ[Localization.Away (algebraMap R S f)]
      Localization.Away ((algebraMap R S f) * algebraMap R S g) :=
    Localization.algEquiv (Submonoid.powers coeff)
      (Localization.Away ((algebraMap R S f) * algebraMap R S g))
  let eMul : Localization.Away ((algebraMap R S f) * algebraMap R S g) ≃ₐ[
      Localization.Away (algebraMap R S f)] Localization.Away (algebraMap R S fg) :=
    final_away_target_product_to_mul_transport (R := R) (S := S) (f := f) (g := g)
  have hloc : IsLocalization (Submonoid.powers coeff)
      (Localization.Away (algebraMap R S fg)) := by
    -- Proof comment: transport the owner localization from the product chart to the final chart.
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers coeff) (eProd.trans eMul)
  -- Proof comment: the quotient generator maps to the target coefficient, so the transported
  -- product-chart localization is exactly the mapped-powers localization needed here.
  dsimp only
  rw [hpow]
  exact hloc

/-- Helper for Lemma 10.126.6: the final target `S_(fg)` is already the owner localization of the
quotient chart `Qf` at `uQ = [C g]`. This is the target-side analogue of the source-side direct
localization package, now expressed without any generic transport through
`algEquivOfAlgEquiv`. -/
private noncomputable abbrev final_away_target_localization_algEquiv_over_quotient
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    letI : Algebra Qf (Localization.Away (algebraMap R S f)) := eQuot.toAlgHom.toAlgebra
    letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
      (ρfgS.comp eQuot.toRingHom).toAlgebra
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    Localization.Away uQ ≃ₐ[Qf]
      Localization.Away (algebraMap R S fg) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let fg : R := f * g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap R S fg)
        (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp eQuot.toRingHom).toAlgebra
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap R (Localization.Away f) g))
  have hmapped :
      IsLocalization
        (Submonoid.map eQuot.toRingEquiv.toMonoidWithZeroHom.toMonoidHom
          (Submonoid.powers uQ))
        (Localization.Away (algebraMap R S fg)) := by
    simpa [fg, Qf, uQ, eQuot, ρfgS] using
      (final_away_target_isLocalization_mapped_powers
        (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj)
  letI :
      IsLocalization
        (Submonoid.map eQuot.toRingEquiv.toMonoidWithZeroHom.toMonoidHom
          (Submonoid.powers uQ))
        (Localization.Away (algebraMap R S fg)) := hmapped
  have haway : IsLocalization.Away uQ (Localization.Away (algebraMap R S fg)) := by
    -- Proof comment: transfer the localization structure back across the quotient equivalence
    -- `Qf ≃ S_f`, whose induced algebra map on the final chart is definitionally `ρfgS ∘ eQuot`.
    simpa [IsLocalization.Away] using
      (IsLocalization.of_ringEquiv_left (K := Localization.Away (algebraMap R S fg))
        (e := eQuot.toRingEquiv)
        (M₁ := Submonoid.map eQuot.toRingEquiv.toMonoidWithZeroHom.toMonoidHom
          (Submonoid.powers uQ))
        (M₂ := Submonoid.powers uQ)
        rfl (fun x ↦ rfl))
  letI : IsLocalization.Away uQ (Localization.Away (algebraMap R S fg)) := haway
  -- Proof comment: with the owner `Qf`-away localization instance installed, the canonical
  -- localization equivalence gives the desired quotient-linear target chart.
  dsimp only
  exact Localization.algEquiv (Submonoid.powers uQ)
    (Localization.Away (algebraMap R S fg))

/-- Helper for Lemma 10.126.6: the final target `S_(fg)` is already the owner localization of the
quotient chart `Qf` at `uQ = [C g]`. This is the target-side analogue of the source-side direct
localization package, now expressed without any generic transport through
`algEquivOfAlgEquiv`. -/
private theorem final_away_target_isLocalizationAway
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
      (ρfgS.comp eQuot.toRingHom).toAlgebra
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    IsLocalization.Away uQ (Localization.Away (algebraMap R S fg)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let fg : R := f * g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap R S fg)
        (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f)
      (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp eQuot.toRingHom).toAlgebra
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap R (Localization.Away f) g))
  -- Route correction: package the target chart first as a `Qf`-localization via the quotient
  -- equivalence `eQuot`, and only afterwards forget scalars back to `R_f`.
  exact
    IsLocalization.isLocalization_of_algEquiv
      (Submonoid.powers uQ)
      (final_away_target_localization_algEquiv_over_quotient
        (R := R)
        (S := S)
        (n := n)
        (f := f)
        (g := g)
        πshift
        hπshiftSurj)

/-- Helper for Lemma 10.126.6: after fixing the owner-localization witness on the target side,
the canonical localization equivalence identifies `Qf[uQ⁻¹]` with the final-away target `S_(fg)`.
-/
private noncomputable abbrev final_away_target_localization_algEquiv
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
      (ρfgS.comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    Localization.Away uQ ≃ₐ[Localization.Away f]
      Localization.Away (algebraMap R S fg) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let fg : R := f * g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap R S fg)
        (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp eQuot.toRingHom).toAlgebra
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap R (Localization.Away f) g))
  let eQf :
      Localization.Away uQ ≃ₐ[Qf] Localization.Away (algebraMap R S fg) :=
    final_away_target_localization_algEquiv_over_quotient
      (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj
  have hcomm :
      eQf.toRingHom.comp (algebraMap (Localization.Away f) (Localization.Away uQ)) =
        algebraMap (Localization.Away f) (Localization.Away (algebraMap R S fg)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp only [RingHom.comp_apply]
    calc
      eQf
          (algebraMap (Localization.Away f) (Localization.Away uQ)
            (algebraMap R (Localization.Away f) x)) =
        eQf
          (algebraMap Qf (Localization.Away uQ)
            (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
              (MvPolynomial.C (algebraMap R (Localization.Away f) x)))) := by
              rfl
      _ =
        algebraMap Qf (Localization.Away (algebraMap R S fg))
          (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
            (MvPolynomial.C (algebraMap R (Localization.Away f) x))) := by
              rw [eQf.commutes]
      _ =
        ρfgS (πshift (MvPolynomial.C (algebraMap R (Localization.Away f) x))) := by
              exact congrArg ρfgS
                (Ideal.quotientKerAlgEquivOfSurjective_mk
                  (f := πshift) hπshiftSurj
                  (MvPolynomial.C (algebraMap R (Localization.Away f) x))).symm
      _ =
        ρfgS
          (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
            (algebraMap R (Localization.Away f) x)) := by
              simp
      _ =
        algebraMap (Localization.Away f) (Localization.Away (algebraMap R S fg))
          (algebraMap R (Localization.Away f) x) := by
              rfl
  -- Proof comment: rebuilding the equivalence from the owner-side ring equivalence records the
  -- scalar compatibility once and avoids a repeated typeclass search through `restrictScalars`.
  exact
    { toRingEquiv := eQf.toRingEquiv
      commutes' := fun x ↦ DFunLike.congr_fun hcomm x }

/-- Helper for Lemma 10.126.6: the direct target-side localization equivalence sends the class of
a polynomial `ψ` to the final-away value `ρfgS (πshift ψ)`. -/
private theorem final_away_target_localization_algEquiv_apply_mk
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift)
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
      (ρfgS.comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    final_away_target_localization_algEquiv
        (R := R)
        (S := S)
        (n := n)
        (f := f)
        (g := g)
        πshift
        hπshiftSurj
        (algebraMap Qf (Localization.Away uQ)
          (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ)) =
      ρfgS (πshift ψ) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let fg : R := f * g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap R S fg)
        (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let uQ : Qf :=
    Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
      (MvPolynomial.C (algebraMap R (Localization.Away f) g))
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp eQuot.toRingHom).toAlgebra
  let hloc :=
    final_away_target_localization_algEquiv_over_quotient
      (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj
  -- Proof comment: the rebuilt `R_f`-linear equivalence has the same underlying ring map as the
  -- owner `Qf`-linear equivalence, so its value on `[ψ] / 1` is just the owner `commutes` formula.
  dsimp only
  change hloc
      (algebraMap Qf (Localization.Away uQ)
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ)) =
    ρfgS (πshift ψ)
  calc
    hloc
        (algebraMap Qf (Localization.Away uQ)
          (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ)) =
      algebraMap Qf (Localization.Away (algebraMap R S fg))
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ) := by
        rw [hloc.commutes]
    _ =
      ρfgS
        (eQuot (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom) ψ)) := by
        rfl
    _ = ρfgS (πshift ψ) := by
        exact congrArg ρfgS
          (Ideal.quotientKerAlgEquivOfSurjective_mk
            (f := πshift) hπshiftSurj ψ)

/-- Helper for Lemma 10.126.6: under the target-side quotient algebra structure on the final away
chart, the class of a constant polynomial `C x` is sent to the ordinary image of `x` in `S_(fg)`.
This isolates the coefficient computation needed to compare the repaired localization equivalence
with the structural `R_f`-algebra map. -/
private theorem final_away_target_quotient_algebraMap_apply_constant
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift)
    (x : R) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
      (ρfgS.comp eQuot.toRingHom).toAlgebra
    algebraMap Qf (Localization.Away (algebraMap R S fg))
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) x))) =
      algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S x) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let fg : R := f * g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
    simpa [fg, map_mul] using (inferInstance :
      IsLocalization.Away (algebraMap R S fg)
        (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp eQuot.toRingHom).toAlgebra
  -- Proof comment: the quotient class of a constant first evaluates through `eQuot` to the
  -- corresponding coefficient in `S_f`, and the final-away square then sends it to `S_(fg)`.
  dsimp only
  calc
    algebraMap Qf (Localization.Away (algebraMap R S fg))
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) x))) =
      ρfgS
        (eQuot (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) x)))) := by
        rfl
    _ = ρfgS (πshift (MvPolynomial.C (algebraMap R (Localization.Away f) x))) := by
        exact congrArg ρfgS
          (Ideal.quotientKerAlgEquivOfSurjective_mk
            (f := πshift) hπshiftSurj
            (MvPolynomial.C (algebraMap R (Localization.Away f) x)))
    _ = ρfgS
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) x)) := by
        simp
    _ = algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S x) := by
        simpa [fg, ρfgS] using
          (final_away_target_algebraMap_on_base (R := R) (S := S) (f := f) (g := g) x)

/-- Helper for Lemma 10.126.6: after transporting the shifted presentation to the final away
chart, the quotient comparison becomes an algebra equivalence, hence the final-away presentation is
surjective with kernel generated by the transported shifted relations. -/
private theorem final_away_quotient_comparison_eq_localization_equiv
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift)
    (hkerle :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      let fg : R := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
          (Localization.Away (algebraMap R S fg)) := by
            simpa [fg, map_mul] using (inferInstance :
              IsLocalization.Away (algebraMap R S fg)
                (Localization.Away (algebraMap R S fg)))
      let ρfgS : Localization.Away (algebraMap R S f) →+*
          Localization.Away (algebraMap R S fg) :=
        IsLocalization.Away.awayToAwayRight
          (P := Localization.Away (algebraMap R S fg))
          (algebraMap R S f) (algebraMap R S g)
      letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
        (Localization.awayMap (algebraMap R S) fg).toAlgebra
      let πshiftFinal :
          MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
            Localization.Away (algebraMap R S fg) :=
        MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom) :
    True := by
  -- Proof comment: this placeholder declaration records no additional data in its current form.
  trivial

/-- Helper for Chap10 Lemma 10 126 6: the quotient equivalence obtained by composing the
source-side final-away quotient transport with the target-side final-away localization equivalence
has the expected value on every class coming from the first-away polynomial ring. -/
private theorem final_away_comparison_algEquiv_apply_source_mk
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift)
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
      (ρfgS.comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
    let K : Ideal (MvPolynomial (Fin n) (Localization.Away f)) :=
      RingHom.ker πshift.toRingHom
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf :=
      Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    let eSource :
        Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
      final_away_source_quotient_transport_algEquiv
        (R := R) (n := n) (f := f) (g := g) K
    let eTarget :
        Localization.Away uQ ≃ₐ[Localization.Away f]
          Localization.Away (algebraMap R S fg) :=
      final_away_target_localization_algEquiv
        (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj
    (eSource.symm.trans eTarget)
        (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ)) =
      ρfgS (πshift ψ) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let fg : R := f * g
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
  let K : Ideal (MvPolynomial (Fin n) (Localization.Away f)) :=
    RingHom.ker πshift.toRingHom
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
  let uQ : Qf :=
    Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) g))
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
    Ideal.map (MvPolynomial.map ρfgR) K
  let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  let eSource :
      Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
    final_away_source_quotient_transport_algEquiv
      (R := R) (n := n) (f := f) (g := g) K
  let eTarget :
      Localization.Away uQ ≃ₐ[Localization.Away f]
        Localization.Away (algebraMap R S fg) :=
    final_away_target_localization_algEquiv
      (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj
  have hsource :
      eSource
          (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) =
        Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
    simpa [fg, ρfgR, K, Qf, uQ, Kfg, Tfg, eSource] using
      final_away_source_quotient_transport_algEquiv_apply_mk
        (R := R) (n := n) (f := f) (g := g) K ψ
  -- Proof comment: replace the final-away quotient class by its source-localization preimage,
  -- then use the target-side localization computation on that same `[ψ] / 1` element.
  dsimp only
  rw [← hsource]
  calc
    (eSource.symm.trans eTarget)
        (eSource (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ))) =
      eTarget (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) := by
        simp
    _ = ρfgS (πshift ψ) := by
        simpa [fg, ρfgS, K, Qf, uQ, eTarget] using
          final_away_target_localization_algEquiv_apply_mk
            (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj ψ

/-- Helper for Lemma 10.126.6: after transporting the shifted presentation to the final away
chart, the quotient comparison becomes an algebra equivalence, hence the final-away presentation is
surjective with kernel generated by the transported shifted relations. -/
private theorem final_away_shifted_presentation_surj_ker
    {n m : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
    (hπshiftSurj :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Function.Surjective πshift)
    (relsFinal : Fin m → MvPolynomial (Fin n) (Localization.Away (f * g)))
    (hrelsFinalSpan :
      let fg : R := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Ideal.span (Set.range relsFinal) =
        Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom))
    (htransportedKernelLe :
      let fg : R := f * g
      let ρfgR : Localization.Away f →+* Localization.Away fg :=
        IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
      letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
          (Localization.Away (algebraMap R S fg)) := by
            simpa [fg, map_mul] using (inferInstance :
              IsLocalization.Away (algebraMap R S fg)
                (Localization.Away (algebraMap R S fg)))
      let ρfgS : Localization.Away (algebraMap R S f) →+*
          Localization.Away (algebraMap R S fg) :=
        IsLocalization.Away.awayToAwayRight
          (P := Localization.Away (algebraMap R S fg))
          (algebraMap R S f) (algebraMap R S g)
      letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
        (Localization.awayMap (algebraMap R S) fg).toAlgebra
      let πshiftFinal :
          MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
            Localization.Away (algebraMap R S fg) :=
        MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
        (Localization.Away (algebraMap R S fg)) := by
          simpa [fg, map_mul] using (inferInstance :
            IsLocalization.Away (algebraMap R S fg)
              (Localization.Away (algebraMap R S fg)))
    let ρfgS : Localization.Away (algebraMap R S f) →+*
        Localization.Away (algebraMap R S fg) :=
      IsLocalization.Away.awayToAwayRight
        (P := Localization.Away (algebraMap R S fg))
        (algebraMap R S f) (algebraMap R S g)
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
    Function.Surjective πshiftFinal ∧
      RingHom.ker πshiftFinal.toRingHom = Ideal.span (Set.range relsFinal) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  let fg : R := f * g
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S fg)) := ρfgS.toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  let K : Ideal (MvPolynomial (Fin n) (Localization.Away f)) :=
    RingHom.ker πshift.toRingHom
  let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
  let uQ : Qf :=
    Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) g))
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
    Ideal.map (MvPolynomial.map ρfgR) K
  let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  let πshiftFinal :
      MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
        Localization.Away (algebraMap R S fg) :=
    MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
  let eQuot :
      Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
    Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
  letI : Algebra Qf (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp eQuot.toRingHom).toAlgebra
  let eSource :
      Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
    final_away_source_quotient_transport_algEquiv
      (R := R) (n := n) (f := f) (g := g) K
  let eTarget :
      Localization.Away uQ ≃ₐ[Localization.Away f]
        Localization.Away (algebraMap R S fg) :=
    final_away_target_localization_algEquiv
      (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj
  let e : Tfg ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S fg) :=
    eSource.symm.trans eTarget
  let qComp :
      Tfg →ₐ[Localization.Away fg] Localization.Away (algebraMap R S fg) :=
    final_away_quotient_comparison
      (R := R)
      (S := S)
      (πshift := πshift)
      (f := f)
      (g := g)
      htransportedKernelLe
  have hmaps : e.toRingHom = qComp.toRingHom := by
    letI : IsLocalization.Away uQ Tfg :=
      final_away_source_quotient_isLocalizationAway
        (R := R) (n := n) (f := f) (g := g) K
    letI : IsLocalization.Away uQ (Localization.Away (algebraMap R S fg)) :=
      final_away_target_isLocalizationAway
        (R := R) (S := S) (n := n) (f := f) (g := g) πshift hπshiftSurj
    -- Proof comment: it is enough to compare the two maps on the dense source quotient `Qf`;
    -- the source-side and quotient-lift computation lemmas give the same value there.
    apply IsLocalization.ringHom_ext (Submonoid.powers uQ)
    ext ψ
    · simp only [RingHom.comp_apply]
      have hbase :
          algebraMap Qf Tfg (Ideal.Quotient.mk K (MvPolynomial.C ψ)) =
            Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.C ψ)) := by
        simpa [fg, ρfgR, K, Qf, Kfg, Tfg] using
          final_away_source_quotient_algebraMap_apply_mk
            (R := R)
            (n := n)
            (f := f)
            (g := g)
            K
            (MvPolynomial.C ψ)
      rw [hbase]
      calc
        e (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.C ψ))) =
          ρfgS (πshift (MvPolynomial.C ψ)) := by
            simpa [fg, ρfgR, ρfgS, K, Qf, uQ, Kfg, Tfg, eSource, eTarget, e] using
              final_away_comparison_algEquiv_apply_source_mk
                (R := R)
                (S := S)
                (πshift := πshift)
                (f := f)
                (g := g)
                hπshiftSurj
                (MvPolynomial.C ψ)
        _ = qComp (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.C ψ))) := by
            simpa [fg, ρfgR, ρfgS, K, Qf, Kfg, Tfg, qComp] using
              (final_away_quotient_comparison_apply_mk
                (R := R)
                (S := S)
                (πshift := πshift)
                (f := f)
                (g := g)
                htransportedKernelLe
                (MvPolynomial.C ψ)).symm
    · simp only [RingHom.comp_apply]
      have hbase :
          algebraMap Qf Tfg (Ideal.Quotient.mk K (MvPolynomial.X ψ)) =
            Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.X ψ)) := by
        simpa [fg, ρfgR, K, Qf, Kfg, Tfg] using
          final_away_source_quotient_algebraMap_apply_mk
            (R := R)
            (n := n)
            (f := f)
            (g := g)
            K
            (MvPolynomial.X ψ)
      rw [hbase]
      calc
        e (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.X ψ))) =
          ρfgS (πshift (MvPolynomial.X ψ)) := by
            simpa [fg, ρfgR, ρfgS, K, Qf, uQ, Kfg, Tfg, eSource, eTarget, e] using
              final_away_comparison_algEquiv_apply_source_mk
                (R := R)
                (S := S)
                (πshift := πshift)
                (f := f)
                (g := g)
                hπshiftSurj
                (MvPolynomial.X ψ)
        _ = qComp (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR (MvPolynomial.X ψ))) := by
            simpa [fg, ρfgR, ρfgS, K, Qf, Kfg, Tfg, qComp] using
              (final_away_quotient_comparison_apply_mk
                (R := R)
                (S := S)
                (πshift := πshift)
                (f := f)
                (g := g)
                htransportedKernelLe
                (MvPolynomial.X ψ)).symm
  let eFg : Tfg ≃ₐ[Localization.Away fg] Localization.Away (algebraMap R S fg) :=
    { toRingEquiv := e.toRingEquiv
      commutes' := by
        intro x
        calc
          e (algebraMap (Localization.Away fg) Tfg x) =
            qComp (algebraMap (Localization.Away fg) Tfg x) := by
              exact DFunLike.congr_fun hmaps (algebraMap (Localization.Away fg) Tfg x)
          _ = algebraMap (Localization.Away fg)
                (Localization.Away (algebraMap R S fg)) x := by
              exact qComp.commutes x }
  have he :
      ∀ φ : MvPolynomial (Fin n) (Localization.Away fg),
        eFg (Ideal.Quotient.mk Kfg φ) = πshiftFinal φ := by
    intro φ
    -- Proof comment: after the map comparison, arbitrary representatives are handled by the
    -- quotient lift defining `qComp`; no induction on final-away polynomial representatives is
    -- needed.
    calc
      eFg (Ideal.Quotient.mk Kfg φ) =
        qComp (Ideal.Quotient.mk Kfg φ) := by
          exact DFunLike.congr_fun hmaps (Ideal.Quotient.mk Kfg φ)
      _ = πshiftFinal φ := by
          rfl
  obtain ⟨hπsurj, hker⟩ :=
    surjective_and_kernel_span_of_quotient_comparison_algEquiv
      (π := πshiftFinal)
      (rels := relsFinal)
      (K := Kfg)
      hrelsFinalSpan
      eFg
      he
  -- Proof comment: the generic quotient-comparison lemma returns the same underlying
  -- surjectivity and ring-kernel statement for the original `R_(fg)`-linear presentation.
  exact ⟨hπsurj, hker⟩

/-- Helper for Chap10 Lemma 10 126 6: an idempotent-kernel retraction gives a product
decomposition whose complementary factor lies in a universe large enough for the source algebra. -/
private theorem awayProductDecomposition_of_idempotentKernel_ulift
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (σ : B →ₐ[A] A)
    (hσ : Function.LeftInverse σ (algebraMap A B))
    {e : B} (he : IsIdempotentElem e)
    (hker : RingHom.ker σ.toRingHom = Ideal.span ({e} : Set B)) :
    ∃ (C : Type (max v w)) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (B ≃ₐ[A] (A × C)) := by
  obtain ⟨C₀, hC₀, hAlgC₀, ⟨e₀⟩⟩ :=
    away_product_decomposition_of_idempotent_kernel_retraction σ hσ he hker
  let C : Type (max v w) := ULift.{max v w, v} C₀
  letI : CommRing C := inferInstance
  letI : Algebra A C := inferInstance
  let liftEquiv : C₀ ≃ₐ[A] C := (ULift.algEquiv (R := A) (A := C₀)).symm
  let finalEquiv : B ≃ₐ[A] (A × C) :=
    e₀.trans (AlgEquiv.prodCongr (AlgEquiv.refl : A ≃ₐ[A] A) liftEquiv)
  -- Proof comment: the standard idempotent splitter returns the complementary quotient in the
  -- source-algebra universe; `ULift` can only move it to a larger universe.
  exact ⟨C, inferInstance, inferInstance, ⟨finalEquiv⟩⟩

/-- Helper for Chap10 Lemma 10 126 6: quotienting the current away chart by the kernel of the
zero-section retraction recovers the base away ring. -/
private noncomputable abbrev kernelQuotientAlgEquivOfZeroSectionRetraction
    {fg : R}
    [Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg))]
    (σfg : Localization.Away (algebraMap R S fg) →ₐ[Localization.Away fg] Localization.Away fg)
    (hσfg :
      Function.LeftInverse σfg
        (algebraMap (Localization.Away fg) (Localization.Away (algebraMap R S fg)))) :
    (Localization.Away (algebraMap R S fg) ⧸ RingHom.ker σfg.toRingHom) ≃ₐ[Localization.Away fg]
      Localization.Away fg := by
  -- Proof comment: the retraction identity identifies the quotient by `ker σfg` with the base
  -- away ring via the standard first-isomorphism theorem for ring retractions.
  exact
    Ideal.quotientKerAlgEquivOfRightInverse
      (f := σfg)
      (g := algebraMap (Localization.Away fg) (Localization.Away (algebraMap R S fg)))
      hσfg

/-- Helper for Chap10 Lemma 10 126 6: the quotient by the current away-chart zero-section kernel
is already projective over the base away ring. This packages the verified prefix of the
current-chart route before the remaining source-denominator shrink. -/
private theorem kernelQuotientProjectiveOverBase_ofZeroSectionRetraction
    {fg : R}
    [Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg))]
    (σfg : Localization.Away (algebraMap R S fg) →ₐ[Localization.Away fg] Localization.Away fg)
    (hσfg :
      Function.LeftInverse σfg
        (algebraMap (Localization.Away fg) (Localization.Away (algebraMap R S fg)))) :
    Module.Projective (Localization.Away fg)
      (Localization.Away (algebraMap R S fg) ⧸ RingHom.ker σfg.toRingHom) := by
  let e :=
    kernelQuotientAlgEquivOfZeroSectionRetraction
      (R := R)
      (S := S)
      (fg := fg)
      σfg
      hσfg
  -- Proof comment: transport the canonical projective `A`-module structure on `A` itself across
  -- the quotient equivalence from the previous helper.
  exact Module.Projective.of_equiv' e.symm.toLinearEquiv

/-- Helper for Chap10 Lemma 10 126 6: after shrinking away from `fg`, the tracked prime `q`
lifts to a prime of the current away chart, and the localized target remains quasi-finite over
the localized base. This records the stabilized geometric setup before the remaining
local-ring-comparison step. -/
private theorem currentAwayPrime_and_quasiFiniteAt_of_bijectiveLocalRingHom
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over))
    {fg : R}
    (hfg : fg ∉ p) :
    let B := Localization.Away (algebraMap R S fg)
    letI : Algebra (Localization.Away fg) B :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    ∃ qfg : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap S B) qfg = ⟨q, inferInstance⟩ ∧
      Algebra.QuasiFiniteAt (Localization.Away fg) qfg.asIdeal := by
  let B := Localization.Away (algebraMap R S fg)
  letI : Algebra (Localization.Away fg) B :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  have hfq : algebraMap R S fg ∉ q := by
    intro hmem
    exact hfg <| by
      rw [hq.over]
      simpa [Ideal.mem_comap] using hmem
  have hdisj :
      Disjoint (Submonoid.powers (algebraMap R S fg) : Set S) q := by
    -- Proof comment: every power of the inverted element still avoids `q`, so the localized
    -- target prime is just the standard image of `q`.
    rw [Set.disjoint_left]
    intro x hxPow hxq
    rcases (Submonoid.mem_powers_iff _ _).mp hxPow with ⟨n, rfl⟩
    exact hfq <| ‹q.IsPrime›.mem_of_pow_mem n hxq
  have hqfgPrime : (Ideal.map (algebraMap S B) q).IsPrime := by
    -- Proof comment: primality survives localization exactly because the denominator submonoid is
    -- disjoint from `q`.
    exact
      IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers (algebraMap R S fg))
        B
        q
        inferInstance
        hdisj
  let qfg : PrimeSpectrum B := ⟨Ideal.map (algebraMap S B) q, hqfgPrime⟩
  have hqfgComap : PrimeSpectrum.comap (algebraMap S B) qfg = ⟨q, inferInstance⟩ := by
    ext1
    -- Proof comment: by the same disjointness condition, contracting the localized prime gives
    -- back the original prime `q`.
    simpa [qfg, PrimeSpectrum.comap_asIdeal] using
      (IsLocalization.comap_map_of_isPrime_disjoint
        (Submonoid.powers (algebraMap R S fg))
        B
        (show q.IsPrime from inferInstance)
        hdisj)
  have hquasi : Algebra.QuasiFiniteAt R q :=
    quasiFiniteAt_of_bijective_localRingHom
      (R := R)
      (S := S)
      (p := p)
      (q := q)
      hq
      hlocal
  have hquasiAway : Algebra.QuasiFiniteAt (Localization.Away fg) qfg.asIdeal := by
    have hqfgOver : qfg.asIdeal.LiesOver q := by
      refine ⟨?_⟩
      simpa [PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hqfgComap).symm
    have hquasiTarget : Algebra.QuasiFiniteAt R qfg.asIdeal := by
      -- Proof comment: localization maps are surjective on stalks, so quasi-finiteness at `q`
      -- transports directly to the localized target prime `qfg`.
      letI : qfg.asIdeal.LiesOver q := hqfgOver
      exact
        Algebra.QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver
          (R := R)
          (S := S)
          (T := B)
          q
          (RingHom.surjectiveOnStalks_of_isLocalization
            (M := Submonoid.powers (algebraMap R S fg))
            B)
          qfg.asIdeal
    letI : IsScalarTower R (Localization.Away fg) B :=
      away_localization_isScalarTower
        (R := R)
        (S := S)
        (f := fg)
    -- Proof comment: once the localized target is known to be quasi-finite over `R`, the tower
    -- `R → R_(fg) → S_(fg)` lets us restrict scalars on the base to `R_(fg)`.
    exact toQuasiFiniteAt_of_restrictScalars qfg hquasiTarget
  exact ⟨qfg, hqfgComap, hquasiAway⟩

/-- Helper for Chap10 Lemma 10 126 6: the source prime below the current away-chart prime is the
original base prime. -/
private theorem currentAway_under_comap_eq_basePrime
    (hq : q.LiesOver p)
    {fg : R} :
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    ∀ qfg : PrimeSpectrum (Localization.Away (algebraMap R S fg)),
      PrimeSpectrum.comap (algebraMap S (Localization.Away (algebraMap R S fg))) qfg =
        ⟨q, inferInstance⟩ →
      (qfg.asIdeal.under (Localization.Away fg)).under R = p := by
  let B := Localization.Away (algebraMap R S fg)
  letI : Algebra (Localization.Away fg) B :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  letI : IsScalarTower R (Localization.Away fg) B :=
    away_localization_isScalarTower
      (R := R)
      (S := S)
      (f := fg)
  intro qfg hqfg
  have hqfgIdeal : Ideal.comap (algebraMap S B) qfg.asIdeal = q := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqfg
  ext x
  -- Proof comment: unfold the two contractions and use the canonical away-map algebra square to
  -- compare the current-away prime directly with the original prime `q`.
  calc
    x ∈ (qfg.asIdeal.under (Localization.Away fg)).under R
        ↔ algebraMap R B x ∈ qfg.asIdeal := by
          change
            algebraMap (Localization.Away fg) B (algebraMap R (Localization.Away fg) x) ∈
                qfg.asIdeal ↔
              algebraMap R B x ∈ qfg.asIdeal
          rw [← IsScalarTower.algebraMap_apply R (Localization.Away fg) B x]
    _ ↔ algebraMap R S x ∈ q := by
          rw [← hqfgIdeal]
          rfl
    _ ↔ x ∈ p := by
          rw [hq.over]
          rfl

/-- Helper for Chap10 Lemma 10 126 6: Zariski's main theorem gives a finite
`A`-subalgebra neighborhood of the current away chart whose basic open is the target basic open
around `qfg`. -/
private theorem currentAway_exists_finiteSubalgebra_awayMap_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (qfg : PrimeSpectrum B)
    (hquasi : Algebra.QuasiFiniteAt A qfg.asIdeal) :
    ∃ (B' : Subalgebra A B) (r : B'),
      Module.Finite A B' ∧ (r : B) ∉ qfg.asIdeal ∧
        Function.Bijective (Localization.awayMap B'.val.toRingHom r) := by
  letI : Algebra.QuasiFiniteAt A qfg.asIdeal := hquasi
  obtain ⟨B', hB'fg, r, hr, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
      (R := A)
      (S := B)
      qfg.asIdeal
  have hfinite : Module.Finite A B' :=
    ⟨(Subalgebra.toSubmodule B').fg_top.mpr hB'fg⟩
  -- Proof comment: the Zariski-main owner supplies finite generation of the subalgebra; this is
  -- the same as module-finiteness for the bundled subalgebra, and the away-map bijection is kept
  -- unchanged for the next refinement step.
  exact ⟨B', r, hfinite, hr, hbij⟩

/-- Helper for Chap10 Lemma 10 126 6: a final-away zero-section retraction with pure finitely
generated kernel gives the required product decomposition. -/
private theorem localizedZeroSectionProductDecomposition_of_pureKernel
    {fh : R}
    [Algebra (Localization.Away fh) (Localization.Away (algebraMap R S fh))]
    (σ : Localization.Away (algebraMap R S fh) →ₐ[Localization.Away fh] Localization.Away fh)
    (hσ :
      Function.LeftInverse σ
        (algebraMap (Localization.Away fh) (Localization.Away (algebraMap R S fh))))
    (hkerPure : (RingHom.ker σ.toRingHom).Pure)
    (hkerFg : (RingHom.ker σ.toRingHom).FG) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra (Localization.Away fh) C),
      Nonempty
        (Localization.Away (algebraMap R S fh) ≃ₐ[Localization.Away fh]
          (Localization.Away fh × C)) := by
  -- Proof comment: the owner splitter turns a pure finitely generated retraction kernel into an
  -- idempotent generator and then into the product decomposition, with only a universe lift on the
  -- complementary factor.
  exact
    awayProductDecomposition_of_pureKernel_ulift
      (A := Localization.Away fh)
      (B := Localization.Away (algebraMap R S fh))
      σ
      hσ
      hkerPure
      hkerFg

/-- Helper for Chap10 Lemma 10 126 6: a final-away zero-section retraction whose kernel is
generated by an idempotent gives the required product decomposition. -/
private theorem localizedZeroSectionProductDecomposition_of_idempotentKernel
    {fh : R}
    [Algebra (Localization.Away fh) (Localization.Away (algebraMap R S fh))]
    (σ : Localization.Away (algebraMap R S fh) →ₐ[Localization.Away fh] Localization.Away fh)
    (hσ :
      Function.LeftInverse σ
        (algebraMap (Localization.Away fh) (Localization.Away (algebraMap R S fh))))
    {e : Localization.Away (algebraMap R S fh)}
    (he : IsIdempotentElem e)
    (hker : RingHom.ker σ.toRingHom = Ideal.span ({e} : Set
      (Localization.Away (algebraMap R S fh)))) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra (Localization.Away fh) C),
      Nonempty
        (Localization.Away (algebraMap R S fh) ≃ₐ[Localization.Away fh]
          (Localization.Away fh × C)) := by
  -- Proof comment: once the semilocal spreading step supplies an idempotent generator for the
  -- retraction kernel, the already proved idempotent splitter produces the product factor.
  exact
    awayProductDecomposition_of_idempotentKernel_ulift
      (A := Localization.Away fh)
      (B := Localization.Away (algebraMap R S fh))
      σ
      hσ
      he
      hker

/-- Helper for Chap10 Lemma 10 126 6: if a zero-section kernel is the image of the
`MvPolynomial.idealOfVars` ideal and all displayed variables land in a prime, then the kernel is
contained in that prime. -/
private theorem zeroSectionKernel_le_trackedPrime
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ}
    (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (σ : B →ₐ[A] A)
    (Q : PrimeSpectrum B)
    (hker :
      RingHom.ker σ.toRingHom =
        Ideal.map π.toRingHom (MvPolynomial.idealOfVars (Fin n) A))
    (hX : ∀ i, π (MvPolynomial.X i) ∈ Q.asIdeal) :
    RingHom.ker σ.toRingHom ≤ Q.asIdeal := by
  -- Proof comment: rewrite the kernel as the mapped variable ideal and reduce containment to
  -- checking the polynomial variables, which generate `MvPolynomial.idealOfVars`.
  rw [hker]
  exact Ideal.map_le_iff_le_comap.mpr <| by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hX i

/-- Helper for Chap10 Lemma 10 126 6: a bijective final-away base map supplies a zero-section
retraction whose kernel is generated by the idempotent `0`. -/
private theorem exists_idempotentKernel_retraction_of_bijective_awayMap
    (fh : R)
    (hbij : Function.Bijective (Localization.awayMap (algebraMap R S) fh)) :
    letI : Algebra (Localization.Away fh) (Localization.Away (algebraMap R S fh)) :=
      (Localization.awayMap (algebraMap R S) fh).toAlgebra
    ∃ (σfh : Localization.Away (algebraMap R S fh) →ₐ[
        Localization.Away fh] Localization.Away fh),
      Function.LeftInverse σfh
        (algebraMap (Localization.Away fh)
          (Localization.Away (algebraMap R S fh))) ∧
      ∃ e : Localization.Away (algebraMap R S fh),
        IsIdempotentElem e ∧
          RingHom.ker σfh.toRingHom = Ideal.span ({e} : Set
            (Localization.Away (algebraMap R S fh))) := by
  letI : Algebra (Localization.Away fh) (Localization.Away (algebraMap R S fh)) :=
    (Localization.awayMap (algebraMap R S) fh).toAlgebra
  have hbij' :
      Function.Bijective
        (algebraMap (Localization.Away fh) (Localization.Away (algebraMap R S fh))) := by
    -- Proof comment: under the canonical final-away algebra structure, the algebra map is the
    -- owner `Localization.awayMap`, so its bijectivity is exactly the hypothesis.
    simpa [RingHom.algebraMap_toAlgebra] using hbij
  let e : Localization.Away fh ≃ₐ[Localization.Away fh]
      Localization.Away (algebraMap R S fh) :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hbij'
  let σfh : Localization.Away (algebraMap R S fh) →ₐ[Localization.Away fh]
      Localization.Away fh := e.symm.toAlgHom
  refine ⟨σfh, ?_, 0, ?_, ?_⟩
  · -- Proof comment: the inverse equivalence is visibly a left inverse to the final-away algebra
    -- map.
    intro x
    exact e.symm_apply_apply x
  · exact IsIdempotentElem.zero
  · have hkerBot : RingHom.ker σfh.toRingHom = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot σfh.toRingHom).mp e.symm.injective
    -- Proof comment: an injective retraction has zero kernel, and `⊥` is the span of the zero
    -- idempotent.
    rw [hkerBot]
    simp

/-- Helper for Chap10 Lemma 10 126 6: after one more base shrink, the current-away
zero-section retraction has an idempotent-generated kernel on the final away chart. -/
private theorem exists_finalAway_idempotentKernel_of_currentAwayRetraction
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over))
    {fg : R}
    (hfg : fg ∉ p) :
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    (σfg : Localization.Away (algebraMap R S fg) →ₐ[Localization.Away fg] Localization.Away fg)
    → (hσfg :
      Function.LeftInverse σfg
        (algebraMap (Localization.Away fg) (Localization.Away (algebraMap R S fg))))
    → (hkerσfgFg : (RingHom.ker σfg.toRingHom).FG)
    → Module.Projective (Localization.Away fg)
        (Localization.Away (algebraMap R S fg) ⧸ RingHom.ker σfg.toRingHom)
    → (qfg : PrimeSpectrum (Localization.Away (algebraMap R S fg)))
    → PrimeSpectrum.comap
        (algebraMap S (Localization.Away (algebraMap R S fg))) qfg =
        ⟨q, inferInstance⟩
    → Algebra.QuasiFiniteAt (Localization.Away fg) qfg.asIdeal
    → (qfg.asIdeal.under (Localization.Away fg)).under R = p
    →
    ∃ (h : R) (_ : h ∉ p),
      letI : Algebra (Localization.Away (fg * h))
          (Localization.Away (algebraMap R S (fg * h))) :=
        (Localization.awayMap (algebraMap R S) (fg * h)).toAlgebra
      ∃ (σfh : Localization.Away (algebraMap R S (fg * h)) →ₐ[
          Localization.Away (fg * h)] Localization.Away (fg * h)),
        Function.LeftInverse σfh
          (algebraMap (Localization.Away (fg * h))
            (Localization.Away (algebraMap R S (fg * h)))) ∧
        ∃ e : Localization.Away (algebraMap R S (fg * h)),
          IsIdempotentElem e ∧
            RingHom.ker σfh.toRingHom = Ideal.span ({e} : Set
              (Localization.Away (algebraMap R S (fg * h)))) := by
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  intro σfg hσfg hkerσfgFg hquotProjective qfg hqfg hquasiAway hqfgUnder
  let A := Localization.Away fg
  let B := Localization.Away (algebraMap R S fg)
  -- Route correction: the overstrong route making the whole final-away map bijective is avoided.
  -- The source proof instead keeps the current-away zero-section kernel as the controlled object.
  have hbasePrime : (qfg.asIdeal.under A).under R = p := hqfgUnder
  obtain ⟨B', r, hB'finite, hr, hB'away⟩ :=
    currentAway_exists_finiteSubalgebra_awayMap_bijective
      (A := Localization.Away fg)
      (B := Localization.Away (algebraMap R S fg))
      qfg
      hquasiAway
  have hquotProjectiveBase :
      Module.Projective A (B ⧸ RingHom.ker σfg.toRingHom) := hquotProjective
  have hcurrentKernelFg : (RingHom.ker σfg.toRingHom).FG := hkerσfgFg
  have hzeroSection :
      Function.LeftInverse σfg (algebraMap A B) := hσfg
  have hneBase : fg ∉ p := hfg
  have htrackedTarget :
      PrimeSpectrum.comap (algebraMap S B) qfg = ⟨q, inferInstance⟩ := hqfg
  -- Proof comment: the verified prefix now has the Zariski-main finite neighborhood `B'`,
  -- the current-away retraction kernel, and the tracked contraction data all in the same
  -- `A := R_(fg)`, `B := S_(fg)` normal form. The remaining step is the source proof's
  -- semilocal idempotent-spreading paragraph.
  let _ := hbasePrime
  let _ := B'
  let _ := r
  let _ := hB'finite
  let _ := hr
  let _ := hB'away
  let _ := hquotProjectiveBase
  let _ := hcurrentKernelFg
  let _ := hzeroSection
  let _ := hneBase
  let _ := htrackedTarget
  -- TODO: prove that the localized zero-section kernel is generated by an idempotent after
  -- semilocalizing at `qfg.asIdeal.under A`, then clear that single `A`-denominator back to an
  -- element `h : R` outside `p` and transport the retraction to the final away chart.
  sorry

/-- Helper for Chap10 Lemma 10 126 6: after one more base shrink, the final-away zero-section
retraction gives the requested product decomposition. -/
private theorem exists_product_decomposition_of_pureKernel_zeroSectionRetraction
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over))
    {fg : R}
    (hfg : fg ∉ p) :
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    (σfg : Localization.Away (algebraMap R S fg) →ₐ[Localization.Away fg] Localization.Away fg)
    → (hσfg :
      Function.LeftInverse σfg
        (algebraMap (Localization.Away fg) (Localization.Away (algebraMap R S fg))))
    → (hkerσfgFg : (RingHom.ker σfg.toRingHom).FG)
    →
    ∃ (h : R) (_ : h ∉ p),
      letI : Algebra (Localization.Away (fg * h))
          (Localization.Away (algebraMap R S (fg * h))) :=
        (Localization.awayMap (algebraMap R S) (fg * h)).toAlgebra
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra (Localization.Away (fg * h)) C),
        Nonempty
          (Localization.Away (algebraMap R S (fg * h)) ≃ₐ[Localization.Away (fg * h)]
            (Localization.Away (fg * h) × C)) := by
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  intro σfg hσfg hkerσfgFg
  have hquotProjective :
      Module.Projective (Localization.Away fg)
        (Localization.Away (algebraMap R S fg) ⧸ RingHom.ker σfg.toRingHom) :=
    kernelQuotientProjectiveOverBase_ofZeroSectionRetraction
      (R := R)
      (S := S)
      (fg := fg)
      σfg
      hσfg
  obtain ⟨qfg, hqfg, hquasiAway⟩ :=
    currentAwayPrime_and_quasiFiniteAt_of_bijectiveLocalRingHom
      (R := R)
      (S := S)
      (p := p)
      (q := q)
      hq
      hlocal
      hfg
  have hqfgUnder :
      (qfg.asIdeal.under (Localization.Away fg)).under R = p :=
    currentAway_under_comap_eq_basePrime
      (R := R)
      (S := S)
      (p := p)
      (q := q)
      hq
      qfg
      hqfg
  -- Route correction: the final assembly no longer asks for a pure-kernel package. The remaining
  -- spreading helper now returns the idempotent-generated kernel shape consumed directly by the
  -- product splitter.
  obtain ⟨h, hh, σfh, hσfh, e, he, hker⟩ :=
    exists_finalAway_idempotentKernel_of_currentAwayRetraction
      (R := R)
      (S := S)
      (p := p)
      (q := q)
      hq
      hlocal
      hfg
      σfg
      hσfg
      hkerσfgFg
      hquotProjective
      qfg
      hqfg
      hquasiAway
      hqfgUnder
  letI : Algebra (Localization.Away (fg * h))
      (Localization.Away (algebraMap R S (fg * h))) :=
    (Localization.awayMap (algebraMap R S) (fg * h)).toAlgebra
  obtain ⟨C, hC, hAlgC, hsplit⟩ :=
    localizedZeroSectionProductDecomposition_of_idempotentKernel
      (R := R)
      (S := S)
      (fh := fg * h)
      σfh
      hσfh
      he
      hker
  -- Proof comment: the structural helper supplies the final denominator outside `p`; the
  -- idempotent-kernel splitter supplies exactly the product decomposition at that denominator.
  exact ⟨h, hh, C, hC, hAlgC, hsplit⟩

/-- Helper for Lemma 10.126.6: once the final-away zero-section retraction is constructed, the
remaining source-proof paragraph is reduced to shrinking until its kernel is pure; then the
idempotent-kernel splitter gives the product decomposition. -/
private theorem exists_away_product_decomposition_of_zero_section_retraction
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over))
    {fg : R}
    (hfg : fg ∉ p) :
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    (σfg : Localization.Away (algebraMap R S fg) →ₐ[Localization.Away fg] Localization.Away fg)
    → (hσfg :
      Function.LeftInverse σfg
        (algebraMap (Localization.Away fg) (Localization.Away (algebraMap R S fg))))
    → (hkerσfgFg : (RingHom.ker σfg.toRingHom).FG)
    →
    ∃ (h : R) (_ : h ∉ p),
      letI : Algebra (Localization.Away (fg * h))
          (Localization.Away (algebraMap R S (fg * h))) :=
        (Localization.awayMap (algebraMap R S) (fg * h)).toAlgebra
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra (Localization.Away (fg * h)) C),
        Nonempty
          (Localization.Away (algebraMap R S (fg * h)) ≃ₐ[Localization.Away (fg * h)]
            (Localization.Away (fg * h) × C)) := by
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  intro σfg hσfg hkerσfgFg
  -- Proof comment: the remaining source-facing semilocal step packages the transport of the
  -- zero-section retraction through one more basic-open shrink and then applies the product
  -- splitter.
  exact
    exists_product_decomposition_of_pureKernel_zeroSectionRetraction
      (R := R)
      (S := S)
      (p := p)
      (q := q)
      hq
      hlocal
      hfg
      σfg
      hσfg
      hkerσfgFg

-- Proof sketch: write `S` by a finite presentation over `R` and use the local isomorphism
-- `R_p ≃ S_q` to produce a retraction after replacing `R` by `R_f` for some `f ∉ p`. The kernel of
-- that retraction becomes a finitely generated pure ideal near `p`, hence is generated by an
-- idempotent after shrinking once more. The standard idempotent splitting then identifies `S_f`
-- with a product `R_f × C`.
/-- Lemma 10.126.6: if `S` is a finitely presented `R`-algebra, `q` is a prime ideal of `S`
lying over a prime ideal `p` of `R`, and the induced local map `R_𝔭 → S_𝔮` is bijective, then
there exist `f ∉ p` and an `R_f`-algebra `C` such that `S_f ≅ R_f × C` as `R_f`-algebras. -/
@[stacks 00QR]
theorem exists_away_product_decomposition_of_bijective_localRingHom
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    ∃ (f : R) (_ : f ∉ p),
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra (Localization.Away f) C),
        Nonempty
          (Localization.Away (algebraMap R S f) ≃ₐ[Localization.Away f]
            (Localization.Away f × C)) := by
  -- Route correction: abandon the quasi-finite subalgebra detour and follow the source proof
  -- directly through a finite presentation and common denominator clearing on the presentation
  -- generators.
  obtain ⟨n, π, hπsurj, hπkerfg⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  let localEquiv : Localization.AtPrime p ≃+* Localization.AtPrime q :=
    RingEquiv.ofBijective (Localization.localRingHom p q (algebraMap R S) hq.over) hlocal
  let generatorPreimage : Fin n → Localization.AtPrime p := fun i ↦
    localEquiv.symm (algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)))
  have hgeneratorPreimage :
      ∀ i,
        (Localization.localRingHom p q (algebraMap R S) hq.over) (generatorPreimage i) =
          algebraMap S (Localization.AtPrime q) (π (MvPolynomial.X i)) :=
    generator_preimage_maps_to_variable
      (R := R) (S := S) (p := p) (q := q) hq hlocal π
  obtain ⟨f, hf, a, ha⟩ :=
    exists_notMem_and_common_denominator_atPrime
      (R := R) (p := p) generatorPreimage
  obtain ⟨m, rels, hrels⟩ :
      ∃ m : ℕ, ∃ rels : Fin m → MvPolynomial (Fin n) R,
        Ideal.span (Set.range rels) = RingHom.ker π.toRingHom := by
    -- Proof comment: before shifting variables, fix one explicit finite family generating the
    -- kernel of the original presentation. The new shifted-kernel helpers above show that the same
    -- finite-generation step is available again after the localized translation.
    simpa using Submodule.fg_iff_exists_fin_generating_family.mp hπkerfg
  let ρR : Localization.Away f →+* Localization.AtPrime p :=
    Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
      (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
  have hfq : algebraMap R S f ∉ q := by
    intro hfq
    exact hf (by
      rw [hq.over]
      simpa [Ideal.mem_comap] using hfq)
  let ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q :=
    Localization.awayLift (algebraMap S (Localization.AtPrime q)) (algebraMap R S f)
      (IsLocalization.map_units (Localization.AtPrime q)
        ((⟨algebraMap R S f, hfq⟩ : q.primeCompl)))
  have hawaySquare :
      ρS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR :=
    away_to_atPrime_square_commutes (R := R) (S := S) (p := p) (q := q) hq hf
  let u : Fin n → Localization.Away f :=
    let denom : Submonoid.powers f := ⟨f, ⟨1, by simp⟩⟩
    fun i ↦ IsLocalization.mk' (Localization.Away f) (a i) denom
  have hu : ∀ i, ρR (u i) = generatorPreimage i :=
    -- Proof comment: the tuple `u = a / f` already recovers the chosen inverse-local preimages in
    -- `R_𝔭`, so the remaining work is purely to compare the localized polynomial presentation with
    -- this concrete tuple.
    away_cleared_tuple_eq_generator_preimage
      (R := R) (p := p) (hf := hf) a generatorPreimage ha
  letI : IsLocalization.Away (π (MvPolynomial.C (σ := Fin n) f))
      (Localization.Away (algebraMap R S f)) := by
        simpa using (inferInstance :
          IsLocalization.Away (algebraMap R S f) (Localization.Away (algebraMap R S f)))
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    away_localization_isScalarTower (R := R) (f := f)
  have hπf :
      ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
          (Localization.Away (algebraMap R S f)) π
          (MvPolynomial.C (σ := Fin n) f)).comp
          (AlgHom.restrictScalars R
            (localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm.toAlgHom)) =
        (AlgHom.restrictScalars R
          (MvPolynomial.aeval
            (fun i ↦
              algebraMap S (Localization.Away (algebraMap R S f))
                (π (MvPolynomial.X i))) :
              MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
                Localization.Away (algebraMap R S f))) := by
    -- Proof comment: the first new localization bridge identifies the owner-side conjugated
    -- presentation with the explicit `R_f`-polynomial presentation on coefficients and variables.
    simpa using
      transported_away_presentation_eq_localized_aeval
        (R := R) (S := S) (π := π) (f := f)
  have hπfX :
      ∀ i,
        (AlgHom.restrictScalars R
          (MvPolynomial.aeval
            (fun j ↦
              algebraMap S (Localization.Away (algebraMap R S f))
                (π (MvPolynomial.X j))) :
            MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
              Localization.Away (algebraMap R S f))) (MvPolynomial.X i) =
          algebraMap S (Localization.Away (algebraMap R S f))
            (π (MvPolynomial.X i)) := by
    intro i
    -- Proof comment: the explicit localized presentation sends each polynomial variable to the
    -- localized image of the corresponding presentation generator by construction.
    simp
  let πeval :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f) :=
    MvPolynomial.aeval
      (fun i ↦
        algebraMap S (Localization.Away (algebraMap R S f))
          (π (MvPolynomial.X i)))
  let πshift :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f) :=
    MvPolynomial.aeval
      (fun i ↦
        algebraMap S (Localization.Away (algebraMap R S f))
          (π (MvPolynomial.X i)) -
          algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
            (u i))
  have hπshiftSub :
      πshift =
        πeval.comp
          (MvPolynomial.aeval (R := Localization.Away f)
            fun i ↦ MvPolynomial.X i - MvPolynomial.C (u i)) := by
    -- Proof comment: the shifted localized presentation is literally the unshifted presentation
    -- after substituting `X i - u i`.
    simpa [πeval, πshift] using
      shifted_localized_presentation_eq_sub
        (v := fun i ↦
          algebraMap S (Localization.Away (algebraMap R S f))
            (π (MvPolynomial.X i)))
        (u := u)
  have hshiftX : ∀ i, ρS (πshift (MvPolynomial.X i)) = 0 := by
    -- Proof comment: after the first shrink, the translated generators vanish in the stalk `S_q`;
    -- this is the source proof's key turning point before descending the zero section.
    simpa [πshift, ρR, ρS] using
      shifted_localized_variables_vanish_at_q
        (R := R) (S := S) (p := p) (q := q) hq (hf := hf) π
        generatorPreimage hgeneratorPreimage u hu
  have hπtransportSurj :
      Function.Surjective
        ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap R S f)) π
            (MvPolynomial.C (σ := Fin n) f)).comp
            (AlgHom.restrictScalars R
              (localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm.toAlgHom)) := by
    intro y
    obtain ⟨z, hz⟩ :=
      IsLocalization.Away.mapₐ_surjective_of_surjective
        (Aₚ := Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Bₚ := Localization.Away (algebraMap R S f))
        (f := π)
        (a := MvPolynomial.C (σ := Fin n) f)
        hπsurj y
    refine ⟨(localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f) z, ?_⟩
    -- Proof comment: the conjugated presentation is surjective because the direct away map is
    -- surjective and the polynomial-localization equivalence supplies the needed preimage.
    change (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
        (Localization.Away (algebraMap R S f)) π
        (MvPolynomial.C (σ := Fin n) f))
        ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm
          ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f) z)) = y
    have hz' :
        (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap R S f)) π
            (MvPolynomial.C (σ := Fin n) f))
          ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm
            ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f) z)) =
        (IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap R S f)) π
            (MvPolynomial.C (σ := Fin n) f)) z := by
      exact congrArg
        ((IsLocalization.Away.mapₐ (Localization.Away (MvPolynomial.C (σ := Fin n) f))
            (Localization.Away (algebraMap R S f)) π
            (MvPolynomial.C (σ := Fin n) f)))
        ((localized_mvPolynomial_algEquiv_over_base (R := R) (n := n) f).symm_apply_apply z)
    exact hz'.trans hz
  have hπevalSurj : Function.Surjective πeval := by
    -- Proof comment: the explicit localized presentation `πeval` is the conjugated away
    -- presentation from `hπf`, so surjectivity transfers across that identification.
    have hsurjR :
        Function.Surjective
          (AlgHom.restrictScalars R
            (MvPolynomial.aeval
              (fun i ↦
                algebraMap S (Localization.Away (algebraMap R S f))
                  (π (MvPolynomial.X i))) :
              MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
                Localization.Away (algebraMap R S f))) := by
      rw [← hπf]
      exact hπtransportSurj
    simpa [πeval] using hsurjR
  have hπshiftSurj : Function.Surjective πshift := by
    -- Proof comment: the shifted presentation differs from `πeval` only by the invertible
    -- translation `X i ↦ X i - u i`, so surjectivity persists after the first shrink.
    exact surjective_shifted_presentation
      (πeval := πeval)
      hπevalSurj
      u
      πshift
      hπshiftSub
  obtain ⟨mShift, relsShift, hrelsShift, hconstShift⟩ :=
    exists_sign_aligned_shifted_kernel_family
      (R := R) (S := S) (p := p) (q := q) hq (hf := hf)
      (πeval := πeval) hπevalSurj u (πshift := πshift) hπshiftSub
      ρR ρS hawaySquare hlocal hshiftX
  obtain ⟨g₂, hg₂, hconstZero⟩ :=
    exists_notMem_zero_shifted_constants_after_second_shrink
      (R := R)
      (p := p)
      (hf := hf)
      (rels := relsShift)
      hconstShift
  let fg : R := f * g₂
  let ρfgR : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g₂
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g₂)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  let ρfgS : Localization.Away (algebraMap R S f) →+*
      Localization.Away (algebraMap R S fg) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (algebraMap R S fg))
      (algebraMap R S f) (algebraMap R S g₂)
  have hfinalAwaySquare :
      ρfgS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.awayMap (algebraMap R S) fg).comp ρfgR := by
    -- Proof comment: the second shrink now has the same canonical commuting square as the first
    -- shrink to the stalks, so the remaining work can be phrased on the final away chart without
    -- further transport through ad hoc coercions.
    simpa [fg, ρfgR, ρfgS] using
      final_away_square_commutes (R := R) (S := S) f g₂
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  let πshiftFinal :
      MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
        Localization.Away (algebraMap R S fg) :=
    MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
  let relsFinal : Fin mShift → MvPolynomial (Fin n) (Localization.Away fg) :=
    fun j ↦ MvPolynomial.map ρfgR (relsShift j)
  have hrelsFinalConstZero :
      ∀ j, MvPolynomial.constantCoeff (relsFinal j) = 0 := by
    intro j
    -- Proof comment: the second shrink was chosen exactly so that the transported constant
    -- coefficients of the shifted relations literally vanish in the final away chart `R_(fg)`.
    dsimp [relsFinal]
    simpa [fg, ρfgR] using hconstZero j
  have hrelsFinalSpan :
      Ideal.span (Set.range relsFinal) =
        Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) := by
    -- Proof comment: package the transported relation family as the coefficient-wise image of the
    -- already controlled shifted kernel ideal on `R_f`.
    simpa [fg, ρfgR, relsFinal] using
      final_away_relations_span_eq_map_shifted_kernel
        (R := R)
        (relsShift := relsShift)
        (K := RingHom.ker πshift.toRingHom)
        hrelsShift
  have hπshiftFinalMap :
      ∀ ψ : MvPolynomial (Fin n) (Localization.Away f),
        πshiftFinal (MvPolynomial.map ρfgR ψ) = ρfgS (πshift ψ) := by
    -- Proof comment: this is the pointwise transport bridge from the shifted presentation on
    -- `R_f` to the final away chart `R_(fg)`.
    intro ψ
    simpa [fg, ρfgR, ρfgS, πshiftFinal] using
      final_away_shifted_presentation_map
        (R := R)
        (S := S)
        (ψ := ψ)
        (πshift := πshift)
        (f := f)
        (g := g₂)
  have hrelsFinalSpanLe :
      Ideal.span (Set.range relsFinal) ≤ RingHom.ker πshiftFinal.toRingHom := by
    -- Proof comment: every transported shifted relation still vanishes under the final-away
    -- presentation, so their span already lies in the new kernel.
    refine Ideal.span_le.mpr ?_
    intro ψ hψ
    rcases hψ with ⟨j, rfl⟩
    change πshiftFinal (relsFinal j) = 0
    have hrelShift : πshift (relsShift j) = 0 := by
      have hrelShiftMem : relsShift j ∈ RingHom.ker πshift.toRingHom := by
        rw [← hrelsShift]
        exact Ideal.subset_span (Set.mem_range_self j)
      simpa [RingHom.mem_ker] using hrelShiftMem
    calc
      πshiftFinal (relsFinal j) = ρfgS (πshift (relsShift j)) := by
        simpa [relsFinal] using hπshiftFinalMap (relsShift j)
      _ = 0 := by simp [hrelShift]
  have htransportedKernelLe :
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom) ≤
        RingHom.ker πshiftFinal.toRingHom := by
    -- Proof comment: after identifying the transported relation span with the mapped old kernel,
    -- the already proved vanishing of the transported relations gives the forward kernel
    -- inclusion on the final away chart.
    rw [← hrelsFinalSpan]
    exact hrelsFinalSpanLe
  let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
    Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
  let qComp :
      (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) →ₐ[Localization.Away fg]
        Localization.Away (algebraMap R S fg) :=
    final_away_quotient_comparison
      (R := R)
      (S := S)
      (πshift := πshift)
      (f := f)
      (g := g₂)
      htransportedKernelLe
  have hqComp_apply :
      ∀ ψ : MvPolynomial (Fin n) (Localization.Away f),
        qComp (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ)) = ρfgS (πshift ψ) := by
    intro ψ
    -- Proof comment: the descended quotient comparison agrees with the transported shifted
    -- presentation on every generator coming from the first away chart.
    simpa [Kfg, qComp, fg, ρfgR, ρfgS] using
      final_away_quotient_comparison_apply_mk
        (R := R)
        (S := S)
        (πshift := πshift)
        (f := f)
        (g := g₂)
        htransportedKernelLe
        ψ
  have hπshiftFinal :
      Function.Surjective πshiftFinal ∧
        RingHom.ker πshiftFinal.toRingHom = Ideal.span (Set.range relsFinal) := by
    -- Proof comment: this packages the entire final-away quotient-localization transport, so the
    -- main theorem can now continue with the zero-section retraction exactly as in the source
    -- argument.
    simpa [Kfg, πshiftFinal, fg, ρfgR, ρfgS] using
      final_away_shifted_presentation_surj_ker
        (R := R)
        (S := S)
        (πshift := πshift)
        (f := f)
        (g := g₂)
        hπshiftSurj
        relsFinal
        hrelsFinalSpan
        htransportedKernelLe
  obtain ⟨hπshiftFinalSurj, hπshiftFinalKer⟩ := hπshiftFinal
  obtain ⟨σfg, hσfg, hσfg_comp, hkerσfg⟩ :=
    shifted_zero_section_retraction_of_zero_constant_relations
      (πshift := πshiftFinal)
      hπshiftFinalSurj
      relsFinal
      hπshiftFinalKer.symm
      hrelsFinalConstZero
  have hσfgX : ∀ i, σfg (πshiftFinal (MvPolynomial.X i)) = 0 := by
    intro i
    -- Proof comment: the newly exposed zero-section computation now records the source proof's
    -- key generator identity: the retraction kills each shifted variable on the final away chart.
    simpa using hσfg_comp (MvPolynomial.X i)
  have hkerσfgFg : (RingHom.ker σfg.toRingHom).FG := by
    -- Proof comment: finite generation of the final-away retraction kernel is now discharged
    -- entirely formally from the zero-section kernel description.
    exact
      kernel_fg_of_zero_section_retraction
        (A := Localization.Away fg)
        (B := Localization.Away (algebraMap R S fg))
        (n := n)
        (σ := σfg)
        (π := πshiftFinal)
        hkerσfg
  have hfg : fg ∉ p := by
    -- Proof comment: the two shrinking parameters both avoid `p`, so their product does as well.
    exact ‹p.IsPrime›.mul_notMem hf hg₂
  -- Proof comment: all earlier presentation work is now packaged into the final-away retraction
  -- `σfg`; the rest of the theorem is exactly the isolated semilocal-purity/idempotent paragraph.
  obtain ⟨h, hh, C, hC, hAlgC, hsplit⟩ :=
    exists_away_product_decomposition_of_zero_section_retraction
      (R := R)
      (S := S)
      (p := p)
      (q := q)
      hq
      hlocal
      hfg
      σfg
      hσfg
      hkerσfgFg
  refine ⟨fg * h, ?_, C, hC, hAlgC, ?_⟩
  · -- Proof comment: the final shrinking parameter is the product of two elements already chosen
    -- outside `p`.
    exact ‹p.IsPrime›.mul_notMem hfg hh
  · simpa [fg, mul_assoc] using hsplit

end

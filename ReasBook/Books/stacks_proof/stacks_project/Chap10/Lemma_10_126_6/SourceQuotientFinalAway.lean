import StacksProject_2024.Chap10.Lemma_10_126_6.SourceQuotientCoeffChart

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: under the quotient equivalence attached to the surjective
shifted presentation on `R_f`, the quotient class of the coefficient polynomial `C g` is sent to
the localized coefficient `g / 1` in `S_f`. -/
theorem final_away_source_quotient_isLocalizationAway
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    IsLocalization.Away uQ Tfg := by
  intro fg c Qf uQ ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  letI : IsLocalization.Away c (Localization.Away fg) :=
    final_away_coeff_isLocalizationAway
      (R := R)
      (f := f)
      (g := g)
  letI : IsLocalization.Away (MvPolynomial.C (σ := Fin n) c)
      (MvPolynomial (Fin n) (Localization.Away fg)) := by
        simpa [IsLocalization.Away, Submonoid.map_powers] using
          (MvPolynomial.isLocalization
            (σ := Fin n)
            (M := Submonoid.powers c)
            (S := Localization.Away fg))
  intro Kfg Tfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  have hloc :
      IsLocalization
        (Algebra.algebraMapSubmonoid
          (R := MvPolynomial (Fin n) (Localization.Away f))
          (S := Qf)
          (Submonoid.powers (MvPolynomial.C c)))
        Tfg := by
      simpa [Algebra.algebraMapSubmonoid] using
        (IsLocalization.of_surjective
          (M := Submonoid.powers (MvPolynomial.C c))
          (S := MvPolynomial (Fin n) (Localization.Away fg))
          (Ideal.Quotient.mk K)
          Ideal.Quotient.mk_surjective
          (Ideal.Quotient.mk Kfg)
          Ideal.Quotient.mk_surjective
          rfl
          (by
            simpa [Kfg, RingHom.algebraMap_toAlgebra] using
              (le_rfl :
                Ideal.map (MvPolynomial.map ρfgR) K ≤
                  Ideal.map (MvPolynomial.map ρfgR) K)) :
          IsLocalization
            ((Submonoid.powers (MvPolynomial.C c)).map (Ideal.Quotient.mk K))
            Tfg)
  -- Proof comment: quotienting the polynomial localization on the final-away coefficient chart
  -- gives the owner localization of `Qf` at `uQ = [C g]`, exactly as on the source chart.
  simpa [IsLocalization.Away, uQ,
    final_away_source_quotient_powers_eq
      (R := R)
      (n := n)
      (f := f)
      (g := g)
      K] using hloc

/-- Helper for Lemma 10.126.6: the quotient-localization equivalence from the first-away source
quotient to the final-away polynomial quotient sends a quotient generator to its transported
final-away class. -/
noncomputable abbrev final_away_source_quotient_localization_algEquiv
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    Localization.Away uQ ≃ₐ[Localization.Away f] Tfg := by
  intro fg c Qf uQ ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  intro Kfg Tfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  letI : IsLocalization.Away uQ Tfg :=
    final_away_source_quotient_isLocalizationAway
      (R := R)
      (n := n)
      (f := f)
      (g := g)
      K
  let eQf : Localization.Away uQ ≃ₐ[Qf] Tfg :=
    Localization.algEquiv (Submonoid.powers uQ) Tfg
  have hcomm :
      eQf.toRingHom.comp (algebraMap (Localization.Away f) (Localization.Away uQ)) =
        algebraMap (Localization.Away f) Tfg := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp only [RingHom.comp_apply]
    calc
      eQf
          (algebraMap (Localization.Away f) (Localization.Away uQ)
            (algebraMap R (Localization.Away f) x)) =
        eQf
          (algebraMap Qf (Localization.Away uQ)
            (Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) x)))) := by
              rfl
      _ =
        algebraMap Qf Tfg
          (Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) x))) := by
              rw [eQf.commutes]
      _ =
        Ideal.Quotient.mk Kfg
          (MvPolynomial.C
            (ρfgR (algebraMap R (Localization.Away f) x))) := by
              simpa using
                final_away_source_quotient_algebraMap_apply_mk
                  (R := R)
                  (n := n)
                  (f := f)
                  (g := g)
                  K
                  (MvPolynomial.C (algebraMap R (Localization.Away f) x))
      _ = algebraMap (Localization.Away f) Tfg (algebraMap R (Localization.Away f) x) := by
              rfl
  let e : Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
    { toRingEquiv := eQf.toRingEquiv
      commutes' := fun x ↦ DFunLike.congr_fun hcomm x }
  -- Proof comment: the new main route localizes `Qf` directly on the final-away chart `Tfg`,
  -- bypassing the old coefficient-chart transport from the critical path.
  exact e

/-- Helper for Lemma 10.126.6: the source-side quotient-localization equivalence carries the class
of a polynomial `ψ` to the class of its coefficient-wise transport to the final away chart. -/
theorem final_away_source_quotient_localization_algEquiv_apply_mk
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    final_away_source_quotient_localization_algEquiv
        (n := n) (f := f) (g := g) K
        (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) =
      Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
  intro fg c Qf uQ ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  intro Kfg Tfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  letI : IsLocalization.Away uQ Tfg :=
    final_away_source_quotient_isLocalizationAway
      (R := R)
      (n := n)
      (f := f)
      (g := g)
      K
  let eQf : Localization.Away uQ ≃ₐ[Qf] Tfg :=
    Localization.algEquiv (Submonoid.powers uQ) Tfg
  have hcomm :
      eQf.toRingHom.comp (algebraMap (Localization.Away f) (Localization.Away uQ)) =
        algebraMap (Localization.Away f) Tfg := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp only [RingHom.comp_apply]
    calc
      eQf
          (algebraMap (Localization.Away f) (Localization.Away uQ)
            (algebraMap R (Localization.Away f) x)) =
        eQf
          (algebraMap Qf (Localization.Away uQ)
            (Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) x)))) := by
              rfl
      _ =
        algebraMap Qf Tfg
          (Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) x))) := by
              rw [eQf.commutes]
      _ =
        Ideal.Quotient.mk Kfg
          (MvPolynomial.C
            (ρfgR (algebraMap R (Localization.Away f) x))) := by
              simpa using
                final_away_source_quotient_algebraMap_apply_mk
                  (R := R)
                  (n := n)
                  (f := f)
                  (g := g)
                  K
                  (MvPolynomial.C (algebraMap R (Localization.Away f) x))
      _ = algebraMap (Localization.Away f) Tfg (algebraMap R (Localization.Away f) x) := by
              rfl
  let e : Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
    { toRingEquiv := eQf.toRingEquiv
      commutes' := fun x ↦ DFunLike.congr_fun hcomm x }
  -- Proof comment: on the direct source-side localization, the class of `ψ` is again `ψ / 1`,
  -- so the calculation is the canonical `Localization.algEquiv_mk'` formula followed by the
  -- quotient-map computation to the final-away chart.
  change e (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) = _
  rw [← IsLocalization.mk'_one
      (M := Submonoid.powers uQ)
      (S := Localization.Away uQ)
      (Ideal.Quotient.mk K ψ)]
  change eQf
      (IsLocalization.mk' (Localization.Away uQ) (Ideal.Quotient.mk K ψ) 1) = _
  rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
  simpa using
    final_away_source_quotient_algebraMap_apply_mk
      (R := R)
      (n := n)
      (f := f)
      (g := g)
      K
      ψ

/-- Helper for Lemma 10.126.6: under the quotient equivalence attached to the surjective
shifted presentation on `R_f`, the quotient class of the coefficient polynomial `C g` is sent to
the localized coefficient `g / 1` in `S_f`. -/
theorem final_away_source_quotient_away_generator_image
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
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    eQuot
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))) =
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
        (algebraMap R (Localization.Away f) g) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro Qf eQuot
  -- Proof comment: this is just the quotient comparison on one explicit presentation
  -- generator, namely the coefficient polynomial `C g`.
  change
    (Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj)
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))) =
      algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
        (algebraMap R (Localization.Away f) g)
  calc
    (Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj)
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))) =
      πshift (MvPolynomial.C (algebraMap R (Localization.Away f) g)) := by
        exact Ideal.quotientKerAlgEquivOfSurjective_mk
          (f := πshift)
          hπshiftSurj
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    _ = algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g) := by
            simp

/-- Helper for Lemma 10.126.6: localizing the source quotient equivalence at the distinguished
class `uQ = [C g]` sends the powers of `uQ` to the powers of the localized coefficient `g / 1`. -/
theorem final_away_source_quotient_map_powers
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
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ RingHom.ker πshift.toRingHom
    let uQ : Qf :=
      Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
        (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    let eQuot :
        Qf ≃ₐ[Localization.Away f] Localization.Away (algebraMap R S f) :=
      Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj
    Submonoid.map eQuot.toMonoidHom (Submonoid.powers uQ) =
      Submonoid.powers
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro Qf uQ eQuot
  -- Proof comment: `Submonoid.map_powers` reduces the claim to the image of the one generator,
  -- and that image is exactly the computation from `final_away_source_quotient_away_generator_image`.
  simpa [uQ] using
    (Submonoid.map_powers
      (f := eQuot.toMonoidHom)
      uQ).trans <| by
        congr 1
        simpa [Qf] using
          final_away_source_quotient_away_generator_image
            (R := R)
            (S := S)
            (n := n)
            (f := f)
            (g := g)
            πshift
            hπshiftSurj

end

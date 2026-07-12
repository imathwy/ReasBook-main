import StacksProject_2024.Chap10.Lemma_10_126_6.SourceQuotientBasic

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: under the quotient equivalence attached to the surjective
shifted presentation on `R_f`, the quotient class of the coefficient polynomial `C g` is sent to
the localized coefficient `g / 1` in `S_f`. -/
theorem coeff_chart_mvPolynomial_isLocalizationAway
    {n : ℕ} {f g : R} :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    IsLocalization.Away (MvPolynomial.C (σ := Fin n) c)
      (MvPolynomial (Fin n) (Localization.Away c)) := by
  intro c
  -- Proof comment: localizing coefficients from `R_f` to `R_f[g⁻¹]` localizes the whole
  -- multivariable polynomial ring at the coefficient polynomial `C (g / 1)`.
  simpa [IsLocalization.Away] using
    (inferInstance :
      IsLocalization
        ((Submonoid.powers c).map (MvPolynomial.C (σ := Fin n)))
        (MvPolynomial (Fin n) (Localization.Away c)))

/-- Helper for Lemma 10.126.6: under the quotient equivalence attached to the surjective
shifted presentation on `R_f`, the quotient class of the coefficient polynomial `C g` is sent to
the localized coefficient `g / 1` in `S_f`. -/
theorem source_quotient_coeff_chart_isLocalizationAway
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let Kc : Ideal (MvPolynomial (Fin n) (Localization.Away c)) :=
      Ideal.map (MvPolynomial.map (algebraMap (Localization.Away f) (Localization.Away c))) K
    let Qc := MvPolynomial (Fin n) (Localization.Away c) ⧸ Kc
    letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
    IsLocalization.Away uQ Qc := by
  intro c Qf uQ Kc Qc
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away c)) :=
    (MvPolynomial.map
      (algebraMap (Localization.Away f) (Localization.Away c))).toAlgebra
  letI : IsLocalization.Away (MvPolynomial.C (σ := Fin n) c)
      (MvPolynomial (Fin n) (Localization.Away c)) :=
    coeff_chart_mvPolynomial_isLocalizationAway
      (R := R)
      (n := n)
      (f := f)
      (g := g)
  letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
  have hloc :
      IsLocalization
        (Algebra.algebraMapSubmonoid
          (R := MvPolynomial (Fin n) (Localization.Away f))
          (S := Qf)
          (Submonoid.powers (MvPolynomial.C c)))
        Qc := by
      simpa [Algebra.algebraMapSubmonoid] using
        (IsLocalization.of_surjective
          (M := Submonoid.powers (MvPolynomial.C c))
          (S := MvPolynomial (Fin n) (Localization.Away c))
          (Ideal.Quotient.mk K)
          Ideal.Quotient.mk_surjective
          (Ideal.Quotient.mk Kc)
          Ideal.Quotient.mk_surjective
          rfl
          (by
            simpa [Kc, RingHom.algebraMap_toAlgebra] using
              (le_rfl :
                Ideal.map
                    (MvPolynomial.map
                      (algebraMap (Localization.Away f) (Localization.Away c))) K ≤
                  Ideal.map
                    (MvPolynomial.map
                      (algebraMap (Localization.Away f) (Localization.Away c))) K)) :
          IsLocalization
            ((Submonoid.powers (MvPolynomial.C c)).map (Ideal.Quotient.mk K))
            Qc)
  -- Proof comment: quotienting the polynomial localization on the coefficient chart gives the
  -- owner localization of `Qf` at the image of `C c`; the image submonoid is exactly the powers
  -- of `uQ = [C c]`.
  simpa [IsLocalization.Away, uQ,
    final_away_source_quotient_powers_eq
      (R := R)
      (n := n)
      (f := f)
      (g := g)
      K] using hloc

/-- Helper for Lemma 10.126.6: the owner localization `Q_f[[C g]⁻¹]` is exactly the quotient on
the coefficient chart `Q_c`. -/
noncomputable abbrev source_quotient_localization_on_coeff_chart
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let Kc : Ideal (MvPolynomial (Fin n) (Localization.Away c)) :=
      Ideal.map (MvPolynomial.map (algebraMap (Localization.Away f) (Localization.Away c))) K
    let Qc := MvPolynomial (Fin n) (Localization.Away c) ⧸ Kc
    letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
    Localization.Away uQ ≃ₐ[Localization.Away f] Qc := by
  intro c Qf uQ Kc Qc
  letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
  letI : IsLocalization.Away uQ Qc :=
    source_quotient_coeff_chart_isLocalizationAway
      (R := R)
      (n := n)
      (f := f)
      (g := g)
      K
  let eQf : Localization.Away uQ ≃ₐ[Qf] Qc :=
    Localization.algEquiv (Submonoid.powers uQ) Qc
  have hcomm :
      eQf.toRingHom.comp (algebraMap (Localization.Away f) (Localization.Away uQ)) =
        algebraMap (Localization.Away f) Qc := by
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
        algebraMap Qf Qc
          (Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) x))) := by
              rw [eQf.commutes]
      _ =
        Ideal.Quotient.mk Kc
          (MvPolynomial.C
            (algebraMap (Localization.Away f) (Localization.Away c)
              (algebraMap R (Localization.Away f) x))) := by
              simpa [Kc] using
                (Ideal.Quotient.algebraMap_quotient_map_quotient
                  (R := MvPolynomial (Fin n) (Localization.Away f))
                  (S := MvPolynomial (Fin n) (Localization.Away c))
                  (p := K)
                  (x := MvPolynomial.C (algebraMap R (Localization.Away f) x)))
      _ =
        algebraMap (Localization.Away f) Qc (algebraMap R (Localization.Away f) x) := by
              rfl
  let e : Localization.Away uQ ≃ₐ[Localization.Away f] Qc :=
    { toRingEquiv := eQf.toRingEquiv
      commutes' := fun x ↦ DFunLike.congr_fun hcomm x }
  -- Proof comment: once `Qc` is known to be the owner localization of `Qf` at `uQ`, the desired
  -- `R_f`-algebra equivalence is just the canonical localization equivalence restricted along the
  -- scalar tower `R_f → Qf`.
  exact e

/-- Helper for Lemma 10.126.6: the source quotient localization chart sends the class of a
polynomial `ψ` to the class of its coefficient-wise image on the coefficient chart. -/
theorem source_quotient_localization_on_coeff_chart_apply_mk
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let Kc : Ideal (MvPolynomial (Fin n) (Localization.Away c)) :=
      Ideal.map (MvPolynomial.map (algebraMap (Localization.Away f) (Localization.Away c))) K
    let Qc := MvPolynomial (Fin n) (Localization.Away c) ⧸ Kc
    letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
    source_quotient_localization_on_coeff_chart
        (R := R) (n := n) (f := f) (g := g) K
        (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) =
      Ideal.Quotient.mk Kc
        (MvPolynomial.map
          (algebraMap (Localization.Away f) (Localization.Away c)) ψ) := by
  intro c Qf uQ Kc Qc
  letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
  letI : IsLocalization.Away uQ Qc :=
    source_quotient_coeff_chart_isLocalizationAway
      (R := R)
      (n := n)
      (f := f)
      (g := g)
      K
  let eQf : Localization.Away uQ ≃ₐ[Qf] Qc :=
    Localization.algEquiv (Submonoid.powers uQ) Qc
  have hcomm :
      eQf.toRingHom.comp (algebraMap (Localization.Away f) (Localization.Away uQ)) =
        algebraMap (Localization.Away f) Qc := by
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
        algebraMap Qf Qc
          (Ideal.Quotient.mk K (MvPolynomial.C (algebraMap R (Localization.Away f) x))) := by
              rw [eQf.commutes]
      _ =
        Ideal.Quotient.mk Kc
          (MvPolynomial.C
            (algebraMap (Localization.Away f) (Localization.Away c)
              (algebraMap R (Localization.Away f) x))) := by
              simpa [Kc] using
                (Ideal.Quotient.algebraMap_quotient_map_quotient
                  (R := MvPolynomial (Fin n) (Localization.Away f))
                  (S := MvPolynomial (Fin n) (Localization.Away c))
                  (p := K)
                  (x := MvPolynomial.C (algebraMap R (Localization.Away f) x)))
      _ =
        algebraMap (Localization.Away f) Qc (algebraMap R (Localization.Away f) x) := by
              rfl
  let e : Localization.Away uQ ≃ₐ[Localization.Away f] Qc :=
    { toRingEquiv := eQf.toRingEquiv
      commutes' := fun x ↦ DFunLike.congr_fun hcomm x }
  -- Proof comment: rewrite the quotient generator as the localization class `ψ / 1`, evaluate
  -- the canonical localization equivalence on that class, and then use the explicit quotient-map
  -- formula on the coefficient chart.
  change e (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) = _
  rw [← IsLocalization.mk'_one
      (M := Submonoid.powers uQ)
      (S := Localization.Away uQ)
      (Ideal.Quotient.mk K ψ)]
  change eQf
      (IsLocalization.mk' (Localization.Away uQ) (Ideal.Quotient.mk K ψ) 1) = _
  rw [Localization.algEquiv_mk', IsLocalization.mk'_one]
  rfl

/-- Helper for Lemma 10.126.6: the canonical quotient map from the first-away source quotient to
the coefficient-chart quotient sends the class of `ψ` to the class of its coefficient-wise image.
-/
theorem source_quotient_coeff_chart_algebraMap_apply_mk
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away c)) :=
      (MvPolynomial.map
        (algebraMap (Localization.Away f) (Localization.Away c))).toAlgebra
    let Kc : Ideal (MvPolynomial (Fin n) (Localization.Away c)) :=
      Ideal.map
        (MvPolynomial.map (algebraMap (Localization.Away f) (Localization.Away c))) K
    letI : Algebra
        (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
        (MvPolynomial (Fin n) (Localization.Away c) ⧸ Kc) :=
      Ideal.Quotient.algebraQuotientMapQuotient
    algebraMap
        (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
        (MvPolynomial (Fin n) (Localization.Away c) ⧸ Kc)
        (Ideal.Quotient.mk K ψ) =
      Ideal.Quotient.mk Kc
        (MvPolynomial.map
          (algebraMap (Localization.Away f) (Localization.Away c)) ψ) := by
  intro c
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away c)) :=
    (MvPolynomial.map
      (algebraMap (Localization.Away f) (Localization.Away c))).toAlgebra
  intro Kc
  letI : Algebra
      (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
      (MvPolynomial (Fin n) (Localization.Away c) ⧸ Kc) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  -- Proof comment: this is exactly the quotient-map computation for the coefficient base-change
  -- homomorphism from `R_f` to the coefficient chart `R_f[g⁻¹]`.
  rfl

/-- Helper for Lemma 10.126.6: the quotient map to the coefficient-chart quotient has kernel equal
to the mapped ideal. -/
theorem source_quotient_coeff_chart_quotient_ker_eq
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Kc : Ideal (MvPolynomial (Fin n) (Localization.Away c)) :=
      Ideal.map (MvPolynomial.map (algebraMap (Localization.Away f) (Localization.Away c))) K
    RingHom.ker (Ideal.Quotient.mk Kc) = Kc := by
  intro c Kc
  -- Proof comment: the quotient map by an ideal always has that ideal as its kernel.
  rw [Ideal.mk_ker]

/-- Helper for Lemma 10.126.6: the coefficient-chart equivalence induces the expected equality on
polynomial coefficient maps before quotienting. -/
theorem final_away_source_quotient_transport_map_eq
    {n : ℕ} {f g : R} :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    let e :
        Localization.Away c ≃ₐ[Localization.Away f] Localization.Away fg :=
      final_away_coeff_chart_algEquiv (R := R) f g
    (MvPolynomial.map (σ := Fin n) e.toRingHom).comp
        (MvPolynomial.map (σ := Fin n)
          (algebraMap (Localization.Away f) (Localization.Away c))) =
      MvPolynomial.map (σ := Fin n) ρfgR := by
  intro fg c ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  intro e
  -- Proof comment: `MvPolynomial.ringHom_ext` reduces the transported polynomial map to the
  -- coefficient action and the variables, and `e.commutes` identifies the coefficient action.
  apply MvPolynomial.ringHom_ext
  · intro a
    -- Proof comment: on coefficients this is exactly `e.commutes`, rewritten through `C`.
    simpa [RingHom.comp_apply, RingHom.algebraMap_toAlgebra] using
      congrArg (MvPolynomial.C (σ := Fin n)) (e.commutes a)
  · intro i
    simp

/-- Helper for Lemma 10.126.6: after transporting coefficients across the chart equivalence, the
mapped source ideal on the coefficient chart is exactly the final-away mapped ideal. -/
theorem final_away_source_quotient_transport_ideal_map_eq
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    let e :
        Localization.Away c ≃ₐ[Localization.Away f] Localization.Away fg :=
      final_away_coeff_chart_algEquiv (R := R) f g
    let Kc : Ideal (MvPolynomial (Fin n) (Localization.Away c)) :=
      Ideal.map
        (MvPolynomial.map (σ := Fin n)
          (algebraMap (Localization.Away f) (Localization.Away c))) K
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map (σ := Fin n) ρfgR) K
    Ideal.map (MvPolynomial.map (σ := Fin n) e.toRingHom) Kc = Kfg := by
  intro fg c ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  intro e
  -- Proof comment: after rewriting the transported polynomial map, the target ideal equality is
  -- just the canonical `Ideal.map_map` formula.
  change
    Ideal.map (MvPolynomial.map (σ := Fin n) e.toRingHom)
        (Ideal.map
          (MvPolynomial.map (σ := Fin n)
            (algebraMap (Localization.Away f) (Localization.Away c))) K) =
      Ideal.map (MvPolynomial.map (σ := Fin n) ρfgR) K
  rw [Ideal.map_map]
  congr 1
  exact
    final_away_source_quotient_transport_map_eq
      (R := R)
      (n := n)
      (f := f)
      (g := g)

/-- Helper for Lemma 10.126.6: first localize the source quotient at `[C g]`, then transport the
resulting quotient along the coefficient-chart equivalence to reach the final-away quotient. -/
noncomputable abbrev final_away_source_quotient_transport_algEquiv
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let Kc : Ideal (MvPolynomial (Fin n) (Localization.Away c)) :=
      Ideal.map (MvPolynomial.map (algebraMap (Localization.Away f) (Localization.Away c))) K
    let Qc := MvPolynomial (Fin n) (Localization.Away c) ⧸ Kc
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    Localization.Away uQ ≃ₐ[Localization.Away f] Tfg := by
  intro fg c Qf uQ Kc Qc ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
  intro Kfg Tfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  let eCoeff :
      MvPolynomial (Fin n) (Localization.Away c) ≃ₐ[Localization.Away f]
        MvPolynomial (Fin n) (Localization.Away fg) :=
    MvPolynomial.mapAlgEquiv (Fin n) (final_away_coeff_chart_algEquiv (R := R) f g)
  let eQuot : Qc ≃ₐ[Localization.Away f] Tfg :=
    Ideal.quotientEquivAlg Kc Kfg eCoeff
      ((final_away_source_quotient_transport_ideal_map_eq
        (R := R)
        (n := n)
        (f := f)
        (g := g)
        K).symm)
  -- Proof comment: after the owner localization `Qf[uQ⁻¹] ≃ Qc` is fixed, the remaining step is
  -- the single quotient transport induced by the coefficient-chart algebra equivalence.
  exact
    (source_quotient_localization_on_coeff_chart
      (R := R)
      (n := n)
      (f := f)
      (g := g)
      K).trans eQuot

/-- Helper for Chap10 Lemma 10 126 6: the source-side final-away quotient transport sends the
localization class of a first-away polynomial to the quotient class of its final-away coefficient
transport. This is the computation bridge needed before comparing with the target-side
localization equivalence. -/
theorem final_away_source_quotient_transport_algEquiv_apply_mk
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let Kc : Ideal (MvPolynomial (Fin n) (Localization.Away c)) :=
      Ideal.map (MvPolynomial.map (algebraMap (Localization.Away f) (Localization.Away c))) K
    let Qc := MvPolynomial (Fin n) (Localization.Away c) ⧸ Kc
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    let Tfg := MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    final_away_source_quotient_transport_algEquiv
        (R := R) (n := n) (f := f) (g := g) K
        (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) =
      Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
  intro fg c Qf uQ Kc Qc ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : Algebra Qf Qc := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Qc := Ideal.Quotient.algebra _
  intro Kfg Tfg
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  let eCoeff :
      MvPolynomial (Fin n) (Localization.Away c) ≃ₐ[Localization.Away f]
        MvPolynomial (Fin n) (Localization.Away fg) :=
    MvPolynomial.mapAlgEquiv (Fin n) (final_away_coeff_chart_algEquiv (R := R) f g)
  let eQuot : Qc ≃ₐ[Localization.Away f] Tfg :=
    Ideal.quotientEquivAlg Kc Kfg eCoeff
      ((final_away_source_quotient_transport_ideal_map_eq
        (R := R)
        (n := n)
        (f := f)
        (g := g)
        K).symm)
  -- Proof comment: evaluate the first localization chart on `[ψ] / 1`, then push the resulting
  -- coefficient-chart quotient class through the quotient equivalence induced by the final-away
  -- coefficient transport.
  calc
    final_away_source_quotient_transport_algEquiv
        (R := R) (n := n) (f := f) (g := g) K
        (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ)) =
      eQuot
        (source_quotient_localization_on_coeff_chart
          (R := R) (n := n) (f := f) (g := g) K
          (algebraMap Qf (Localization.Away uQ) (Ideal.Quotient.mk K ψ))) := by
        rfl
    _ =
      eQuot
        (Ideal.Quotient.mk Kc
          (MvPolynomial.map
            (algebraMap (Localization.Away f) (Localization.Away c)) ψ)) := by
        rw [source_quotient_localization_on_coeff_chart_apply_mk
          (R := R) (n := n) (f := f) (g := g) K ψ]
    _ = Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
        have hpoly :
            eCoeff
                (MvPolynomial.map
                  (algebraMap (Localization.Away f) (Localization.Away c)) ψ) =
              MvPolynomial.map ρfgR ψ := by
          simpa [RingHom.comp_apply, eCoeff] using
            DFunLike.congr_fun
              (final_away_source_quotient_transport_map_eq
                (R := R)
                (n := n)
                (f := f)
                (g := g))
              ψ
        calc
          eQuot
              (Ideal.Quotient.mk Kc
                (MvPolynomial.map
                  (algebraMap (Localization.Away f) (Localization.Away c)) ψ)) =
            Ideal.Quotient.mk Kfg
              (eCoeff
                (MvPolynomial.map
                  (algebraMap (Localization.Away f) (Localization.Away c)) ψ)) := by
              change
                (Kc.quotientEquivAlg Kfg eCoeff
                    ((final_away_source_quotient_transport_ideal_map_eq
                      (R := R)
                      (n := n)
                      (f := f)
                      (g := g)
                      K).symm))
                  (Ideal.Quotient.mk Kc
                    (MvPolynomial.map
                      (algebraMap (Localization.Away f) (Localization.Away c)) ψ)) =
                  Ideal.Quotient.mk Kfg
                    (eCoeff
                      (MvPolynomial.map
                        (algebraMap (Localization.Away f) (Localization.Away c)) ψ))
              exact
                Ideal.quotientEquivAlg_mk
                  (I := Kc)
                  Kfg
                  (f := eCoeff)
                  ((final_away_source_quotient_transport_ideal_map_eq
                    (R := R)
                    (n := n)
                    (f := f)
                    (g := g)
                    K).symm)
                  (MvPolynomial.map
                    (algebraMap (Localization.Away f) (Localization.Away c)) ψ)
          _ = Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
              rw [hpoly]

end

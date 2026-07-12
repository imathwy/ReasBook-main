import StacksProject_2024.Chap10.Lemma_10_126_6.PolynomialLocalization

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: after shrinking at `f`, the canonical maps from the away
localizations to the prime localizations commute with the original local ring map. -/
theorem away_to_atPrime_square_commutes
    (hq : q.LiesOver p) {f : R} (hf : f ∉ p) :
    let ρR : Localization.Away f →+* Localization.AtPrime p :=
      Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
        (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
    let ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q :=
      Localization.awayLift (algebraMap S (Localization.AtPrime q)) (algebraMap R S f)
        (IsLocalization.map_units (Localization.AtPrime q)
          (⟨algebraMap R S f, by
            intro hfq
            exact hf (by
              rw [hq.over]
              simpa [Ideal.mem_comap] using hfq)⟩ : q.primeCompl))
    ρS.comp (Localization.awayMap (algebraMap R S) f) =
      (Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR := by
  let ρR : Localization.Away f →+* Localization.AtPrime p :=
    Localization.awayLift (algebraMap R (Localization.AtPrime p)) f
      (IsLocalization.map_units (Localization.AtPrime p) (⟨f, hf⟩ : p.primeCompl))
  let ρS : Localization.Away (algebraMap R S f) →+* Localization.AtPrime q :=
    Localization.awayLift (algebraMap S (Localization.AtPrime q)) (algebraMap R S f)
      (IsLocalization.map_units (Localization.AtPrime q)
        (⟨algebraMap R S f, by
          intro hfq
          exact hf (by
            rw [hq.over]
            simpa [Ideal.mem_comap] using hfq)⟩ : q.primeCompl))
  -- Proof comment: both maps out of `R_f` are localization lifts, so equality is controlled by
  -- their values on the image of `R`.
  suffices
      ρS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR by
    simpa [ρR, ρS]
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  -- Proof comment: the left side is the direct away-then-stalk map, while the right side is the
  -- stalk map `R_p → S_q` after the canonical map `R_f → R_p`; both send `r` to the same image
  -- in `S_q`.
  have haway :
      (Localization.awayMap (algebraMap R S) f) (algebraMap R (Localization.Away f) r) =
        algebraMap R (Localization.Away (algebraMap R S f)) r := by
    simpa [RingHom.algebraMap_toAlgebra] using
      (Localization.awayMapₐ (Algebra.ofId R S) f).commutes r
  have hρR :
      ρR (algebraMap R (Localization.Away f) r) =
        algebraMap R (Localization.AtPrime p) r := by
    simp [ρR, Localization.awayLift]
  calc
    (ρS.comp (Localization.awayMap (algebraMap R S) f)) (algebraMap R (Localization.Away f) r)
        = ρS (algebraMap R (Localization.Away (algebraMap R S f)) r) := by
            rw [RingHom.comp_apply, haway]
    _ = algebraMap S (Localization.AtPrime q) (algebraMap R S r) := by
          rw [IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) r]
          simp [ρS, Localization.awayLift]
    _ = (Localization.localRingHom p q (algebraMap R S) hq.over)
          (algebraMap R (Localization.AtPrime p) r) := by
          symm
          exact Localization.localRingHom_to_map p q (algebraMap R S) hq.over r
    _ = ((Localization.localRingHom p q (algebraMap R S) hq.over).comp ρR)
          (algebraMap R (Localization.Away f) r) := by
          rw [RingHom.comp_apply, hρR]

/-- Helper for Lemma 10.126.6: after the second shrink from `R_f` to `R_(f * g)`, the matching
second shrink from `S_f` to `S_(f * g)` fits into the expected commuting away square. -/
theorem final_away_square_commutes
    (f g : R) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
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
    ρfgS.comp (Localization.awayMap (algebraMap R S) f) =
      (Localization.awayMap (algebraMap R S) fg).comp ρfgR := by
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
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  have haway_f :
      ∀ r : R,
        (Localization.awayMap (algebraMap R S) f) (algebraMap R (Localization.Away f) r) =
          algebraMap R (Localization.Away (algebraMap R S f)) r := by
    intro r
    -- Proof comment: the first away map is exactly the installed `R_f`-algebra map on `S_f`.
    simpa [RingHom.algebraMap_toAlgebra] using
      (Localization.awayMapₐ (Algebra.ofId R S) f).commutes r
  have haway_fg :
      ∀ r : R,
        (Localization.awayMap (algebraMap R S) fg) (algebraMap R (Localization.Away fg) r) =
          algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S r) := by
    intro r
    -- Proof comment: the final away map is likewise the scalar map of the `R_(fg)`-algebra
    -- structure on `S_(fg)`.
    simpa [RingHom.algebraMap_toAlgebra] using
      (Localization.awayMapₐ (Algebra.ofId R S) fg).commutes r
  have hρfgR :
      ∀ r : R,
        ρfgR (algebraMap R (Localization.Away f) r) =
          algebraMap R (Localization.Away fg) r := by
    intro r
    -- Proof comment: the source-side second shrink sends the class of `r / 1` to the same class
    -- in `R_(fg)`.
    simpa [ρfgR, fg] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away f) (P := Localization.Away fg)
        (x := f) (y := g) (a := r))
  have hρfgS :
      ∀ r : R,
        ρfgS (algebraMap R (Localization.Away (algebraMap R S f)) r) =
          algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S r) := by
    intro r
    -- Proof comment: on the target side, the second shrink is again the canonical away-to-away
    -- map, now applied to the image of `r` inside `S_f`.
    rw [show algebraMap R (Localization.Away (algebraMap R S f)) r =
        algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S r) by
          simpa using
            (DFunLike.congr_fun
              (IsScalarTower.algebraMap_eq R S
                (Localization.Away (algebraMap R S f))) r).symm]
    simpa [ρfgS, fg] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away (algebraMap R S f))
        (P := Localization.Away (algebraMap R S fg))
        (x := algebraMap R S f) (y := algebraMap R S g)
        (a := algebraMap R S r))
  -- Proof comment: as in the first away-to-stalk square, localization uniqueness reduces the
  -- comparison to the image of the original ring `R`.
  suffices
      ρfgS.comp (Localization.awayMap (algebraMap R S) f) =
        (Localization.awayMap (algebraMap R S) fg).comp ρfgR by
    simpa [fg, ρfgR, ρfgS]
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  calc
    (ρfgS.comp (Localization.awayMap (algebraMap R S) f))
        (algebraMap R (Localization.Away f) r)
        = ρfgS (algebraMap R (Localization.Away (algebraMap R S f)) r) := by
            rw [RingHom.comp_apply, haway_f r]
    _ = algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S r) := by
          exact hρfgS r
    _ = (Localization.awayMap (algebraMap R S) fg)
          (algebraMap R (Localization.Away fg) r) := by
          symm
          exact haway_fg r
    _ = ((Localization.awayMap (algebraMap R S) fg).comp ρfgR)
          (algebraMap R (Localization.Away f) r) := by
          rw [RingHom.comp_apply, hρfgR r]

/-- Helper for Lemma 10.126.6: the shifted presentation on `R_f` transports pointwise to the final
away chart `R_(f * g)` by applying `MvPolynomial.map` to the coefficients and the canonical
away-to-away map to the target values of the shifted variables. -/
theorem final_away_shifted_presentation_map
    {n : ℕ} {f g : R}
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    ∀ (πshift :
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f)),
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
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
      (ρfgS.comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
    πshiftFinal (MvPolynomial.map ρfgR ψ) = ρfgS (πshift ψ) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro πshift
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
  have hcoeff :
      (algebraMap (Localization.Away fg) (Localization.Away (algebraMap R S fg))).comp ρfgR =
        ρfgS.comp (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))) := by
    -- Proof comment: the coefficient comparison is exactly the canonical final-away square once
    -- both away maps are rewritten as the installed algebra maps on the localized targets.
    rw [← awayMap_algebraMap_eq_algebraMap (R := R) (S := S) fg]
    rw [← awayMap_algebraMap_eq_algebraMap (R := R) (S := S) f]
    symm
    simpa [fg, ρfgR, ρfgS] using
      final_away_square_commutes (R := R) (S := S) f g
  have hπshift_aeval :
      MvPolynomial.aeval (fun i ↦ πshift (MvPolynomial.X i)) = πshift := by
    -- Proof comment: an algebra map out of a multivariable polynomial ring is determined by its
    -- values on the variables, so the displayed `aeval` is just `πshift` itself.
    apply MvPolynomial.algHom_ext
    intro i
    simp
  calc
    πshiftFinal (MvPolynomial.map ρfgR ψ)
        = MvPolynomial.eval₂Hom
            ((algebraMap (Localization.Away fg)
              (Localization.Away (algebraMap R S fg))).comp ρfgR)
            (fun i ↦ ρfgS (πshift (MvPolynomial.X i))) ψ := by
              -- Proof comment: rewrite the final-away presentation as an explicit `eval₂Hom` and
              -- transport the coefficient map through `MvPolynomial.map`.
              simp [πshiftFinal, MvPolynomial.aeval_eq_eval₂Hom]
    _ = MvPolynomial.eval₂Hom
          (ρfgS.comp
            (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))))
          (fun i ↦ ρfgS (πshift (MvPolynomial.X i))) ψ := by
            rw [hcoeff]
    _ = ρfgS ((MvPolynomial.aeval fun i ↦ πshift (MvPolynomial.X i)) ψ) := by
          -- Proof comment: after the coefficient maps match, the target side is exactly the image
          -- of evaluating the old shifted presentation and then applying the away-to-away map.
          symm
          simpa [MvPolynomial.aeval_eq_eval₂Hom] using
            (MvPolynomial.map_aeval
              (R := Localization.Away f)
              (σ := Fin n)
              (S₁ := Localization.Away (algebraMap R S f))
              (B := Localization.Away (algebraMap R S fg))
              (g := fun i ↦ πshift (MvPolynomial.X i))
              (φ := ρfgS)
              (p := ψ))
    _ = ρfgS (πshift ψ) := by
          rw [hπshift_aeval]

/-- Helper for Lemma 10.126.6: after the second shrink, the transported relation family
`relsFinal` spans exactly the image of the old shifted kernel ideal under coefficient base change.
-/
theorem final_away_relations_span_eq_map_shifted_kernel
    {n m : ℕ} {f g : R}
    (relsShift : Fin m → MvPolynomial (Fin n) (Localization.Away f))
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (hK : Ideal.span (Set.range relsShift) = K) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    let relsFinal : Fin m → MvPolynomial (Fin n) (Localization.Away fg) :=
      fun j ↦ MvPolynomial.map ρfgR (relsShift j)
    Ideal.span (Set.range relsFinal) = Ideal.map (MvPolynomial.map ρfgR) K := by
  intro fg ρfgR relsFinal
  -- Proof comment: this is the source-proof transport step in pure ideal language:
  -- the new final-away relations are just the old relations with coefficients mapped along
  -- `R_f → R_(fg)`, so their span is the image ideal of the old shifted kernel.
  rw [← hK, Ideal.map_span]
  refine congrArg Ideal.span ?_
  ext ψ
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨relsShift j, Set.mem_range_self j, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    rcases hφ with ⟨j, rfl⟩
    exact Set.mem_range_self j

/-- Helper for Lemma 10.126.6: the forward transported-kernel inclusion on the final away chart
descends the final shifted presentation to the quotient by the mapped old kernel. -/
noncomputable def final_away_quotient_comparison
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
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
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
      (ρfgS.comp
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
    (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) →ₐ[Localization.Away fg]
      Localization.Away (algebraMap R S fg) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro fg ρfgR
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  intro ρfgS
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  intro Kfg πshiftFinal
  -- Proof comment: the forward kernel inclusion is exactly the datum needed to descend
  -- `πshiftFinal` across the quotient by the transported old kernel.
  exact Ideal.Quotient.liftₐ Kfg πshiftFinal hkerle

/-- Helper for Lemma 10.126.6: the quotient comparison map just defined sends each transported
polynomial class to the final-away image of the old shifted presentation. -/
theorem final_away_quotient_comparison_apply_mk
    {n : ℕ} {f g : R}
    (πshift :
      letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
        (Localization.awayMap (algebraMap R S) f).toAlgebra
      MvPolynomial (Fin n) (Localization.Away f) →ₐ[Localization.Away f]
        Localization.Away (algebraMap R S f))
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
        RingHom.ker πshiftFinal.toRingHom)
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
    letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
      (Localization.awayMap (algebraMap R S) fg).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) (RingHom.ker πshift.toRingHom)
    let πshiftFinal :
        MvPolynomial (Fin n) (Localization.Away fg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      MvPolynomial.aeval (fun i ↦ ρfgS (πshift (MvPolynomial.X i)))
    let qComp :
        (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) →ₐ[Localization.Away fg]
          Localization.Away (algebraMap R S fg) :=
      final_away_quotient_comparison (R := R) (S := S) (πshift := πshift) (f := f) (g := g) hkerle
    qComp (Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ)) = ρfgS (πshift ψ) := by
  intro fg ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : IsLocalization.Away ((algebraMap R S f) * algebraMap R S g)
      (Localization.Away (algebraMap R S fg)) := by
        simpa [fg, map_mul] using (inferInstance :
          IsLocalization.Away (algebraMap R S fg)
            (Localization.Away (algebraMap R S fg)))
  intro ρfgS
  letI : Algebra (Localization.Away fg) (Localization.Away (algebraMap R S fg)) :=
    (Localization.awayMap (algebraMap R S) fg).toAlgebra
  intro Kfg πshiftFinal qComp
  -- Proof comment: after descending `πshiftFinal`, the quotient computation reduces immediately
  -- to the already established pointwise final-away transport formula.
  change πshiftFinal (MvPolynomial.map ρfgR ψ) = ρfgS (πshift ψ)
  simpa [πshiftFinal] using
    final_away_shifted_presentation_map
      (R := R)
      (S := S)
      (ψ := ψ)
      (πshift := πshift)
      (f := f)
      (g := g)

/-- Helper for Lemma 10.126.6: once the quotient comparison map is upgraded to an algebra
equivalence, surjectivity of the presentation and the exact kernel formula become formal
consequences of that equivalence. -/
theorem surjective_and_ker_of_quotient_comparison_algEquiv
    {A : Type*} [CommRing A]
    {P : Type*} [CommRing P] [Algebra A P]
    {B : Type*} [CommRing B] [Algebra A B]
    (π : P →ₐ[A] B)
    (K : Ideal P)
    (e : (P ⧸ K) ≃ₐ[A] B)
    (he : ∀ x : P, e (Ideal.Quotient.mk K x) = π x) :
    Function.Surjective π ∧ RingHom.ker π.toRingHom = K := by
  constructor
  · intro b
    obtain ⟨q, rfl⟩ := e.surjective b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    -- Proof comment: every quotient class has a polynomial representative, and the comparison
    -- formula `he` turns that representative into a preimage for `π`.
    exact ⟨x, (he x).symm⟩
  · ext x
    constructor
    · intro hx
      -- Proof comment: if `π x = 0`, then the quotient class of `x` maps to zero under the
      -- equivalence `e`, hence the class itself is zero and `x` lies in `K`.
      have hq : e (Ideal.Quotient.mk K x) = e 0 := by
        simpa [he x, RingHom.mem_ker] using hx
      have hmk : Ideal.Quotient.mk K x = 0 := e.injective hq
      exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
    · intro hx
      -- Proof comment: an element of `K` has zero quotient class, so the comparison identity
      -- immediately forces its image under `π` to vanish.
      have hmk : Ideal.Quotient.mk K x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
      have hq : e (Ideal.Quotient.mk K x) = 0 := by
        simpa using congrArg e hmk
      simpa [RingHom.mem_ker, he x] using hq

/-- Helper for Lemma 10.126.6: if the quotient comparison algebra equivalence is already expressed
over a spanning family of relations, the kernel formula can be rewritten directly in that
relation-span form. -/
theorem surjective_and_kernel_span_of_quotient_comparison_algEquiv
    {A : Type*} [CommRing A]
    {P : Type*} [CommRing P] [Algebra A P]
    {B : Type*} [CommRing B] [Algebra A B]
    {ι : Type*}
    (π : P →ₐ[A] B)
    (rels : ι → P)
    (K : Ideal P)
    (hspan : Ideal.span (Set.range rels) = K)
    (e : (P ⧸ K) ≃ₐ[A] B)
    (he : ∀ x : P, e (Ideal.Quotient.mk K x) = π x) :
    Function.Surjective π ∧
      RingHom.ker π.toRingHom = Ideal.span (Set.range rels) := by
  obtain ⟨hπsurj, hker⟩ :=
    surjective_and_ker_of_quotient_comparison_algEquiv
      (π := π) (K := K) e he
  refine ⟨hπsurj, ?_⟩
  calc
    RingHom.ker π.toRingHom = K := hker
    _ = Ideal.span (Set.range rels) := hspan.symm

end

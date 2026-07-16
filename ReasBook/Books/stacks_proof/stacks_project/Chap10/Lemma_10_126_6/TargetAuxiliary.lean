import stacks_proof.stacks_project.Chap10.Lemma_10_126_6.TargetChartTransport

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: after identifying the quotient chart `Qf` with the first-away
target through `eQuot`, the image of the distinguished powers submonoid is exactly the powers of
the transported generator `eQuotQ uQ`. -/
theorem final_away_target_map_powers_eq_powers
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
    letI : Algebra Qf (Localization.Away (algebraMap R S f)) := eQuot.toAlgHom.toAlgebra
    let eQuotQ : Qf ≃ₐ[Qf] Localization.Away (algebraMap R S f) :=
      AlgEquiv.ofRingEquiv (f := eQuot.toRingEquiv) fun x ↦ rfl
    Submonoid.map eQuotQ.toMonoidHom (Submonoid.powers uQ) =
      Submonoid.powers (eQuotQ uQ) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro Qf uQ eQuot
  letI : Algebra Qf (Localization.Away (algebraMap R S f)) := eQuot.toAlgHom.toAlgebra
  intro eQuotQ
  -- Proof comment: this is the owner-side `Submonoid.map_powers` identity, stated once so later
  -- localization transport does not have to rediscover it through large `simp` searches.
  simpa [Submonoid.map_powers]


/-- Helper for Lemma 10.126.6: after the second shrink, the induced `R_f`-algebra structure on
the final target `S_(fg)` is the composite of the first-away map `R_f → S_f` with the target-side
away-to-away map `S_f → S_(fg)`. This is the target-side transport identity needed for the direct
localization comparison. -/
theorem final_away_target_algebraMap_on_base
    {f g : R} (x : R) :
    let fg : R := f * g
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    letI : IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      away_localization_isScalarTower (R := R) (S := S) f
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
    algebraMap (Localization.Away f) (Localization.Away (algebraMap R S fg))
        (algebraMap R (Localization.Away f) x) =
      algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S x) := by
  let fg : R := f * g
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  letI : IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    away_localization_isScalarTower (R := R) (S := S) f
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
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S fg)) :=
    (ρfgS.comp
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f)))).toAlgebra
  -- Proof comment: the final-away `R_f`-algebra map is the composite of the first-away structural
  -- map with `ρfgS`, so the claim reduces to the corresponding `S_f`-to-`S_(fg)` computation.
  calc
    algebraMap (Localization.Away f) (Localization.Away (algebraMap R S fg))
        (algebraMap R (Localization.Away f) x) =
      ρfgS
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) x)) := by
            rfl
    _ =
      ρfgS
        (algebraMap S (Localization.Away (algebraMap R S f))
          (algebraMap R S x)) := by
            rw [final_away_target_chart_generator_eq (R := R) (S := S) (f := f) (g := x)]
    _ = algebraMap S (Localization.Away (algebraMap R S fg)) (algebraMap R S x) := by
          simpa [ρfgS, fg] using
            (IsLocalization.Away.awayToAwayRight_eq
              (S := Localization.Away (algebraMap R S f))
              (P := Localization.Away (algebraMap R S fg))
              (x := algebraMap R S f)
              (y := algebraMap R S g)
              (a := algebraMap R S x))


/-- Helper for Lemma 10.126.6: under the quotient equivalence attached to the shifted
presentation on `R_f`, the distinguished class `uQ = [C g]` already maps to the usual target
coefficient `g / 1` in `S_f`. This records the pre-localization generator computation used by the
target-side powers comparison. -/
theorem final_away_target_quotient_generator_image
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
    eQuot uQ =
      algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro Qf uQ eQuot
  -- Proof comment: this is the quotient comparison on the specific coefficient polynomial `C g`;
  -- after evaluating `eQuot`, the remaining identification is the standard first-away generator
  -- formula.
  change
    (Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj)
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))) =
      algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g)
  calc
    (Ideal.quotientKerAlgEquivOfSurjective hπshiftSurj)
        (Ideal.Quotient.mk (RingHom.ker πshift.toRingHom)
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))) =
      πshift (MvPolynomial.C (algebraMap R (Localization.Away f) g)) := by
        exact Ideal.quotientKerAlgEquivOfSurjective_mk
          (f := πshift)
          hπshiftSurj
          (MvPolynomial.C (algebraMap R (Localization.Away f) g))
    _ = algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g) := by
          simpa [final_away_target_chart_generator_eq (R := R) (S := S) (f := f) (g := g)]

end

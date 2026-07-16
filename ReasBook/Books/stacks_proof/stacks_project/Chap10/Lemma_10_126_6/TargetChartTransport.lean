import stacks_proof.stacks_project.Chap10.Lemma_10_126_6.SourceQuotientFinalAway

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: after the second shrink, the induced `R_f`-algebra structure on
the final target `S_(fg)` is the composite of the first-away map `R_f → S_f` with the target-side
away-to-away map `S_f → S_(fg)`. This is the target-side transport identity needed for the direct
localization comparison. -/
theorem final_away_target_chart_generator_eq
    {f g : R} :
    letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
      (Localization.awayMap (algebraMap R S) f).toAlgebra
    algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
        (algebraMap R (Localization.Away f) g) =
      algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  -- Proof comment: the first away map `R_f → S_f` is exactly the structural algebra map, so the
  -- coefficient `g / 1` has the same description from the `R_f` and `S` viewpoints.
  calc
    algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
        (algebraMap R (Localization.Away f) g) =
      (Localization.awayMap (algebraMap R S) f)
        (algebraMap R (Localization.Away f) g) := by
          rw [← awayMap_algebraMap_eq_algebraMap (R := R) (S := S) f]
    _ = algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g) := by
          simpa [RingHom.algebraMap_toAlgebra] using
            (Localization.awayMapₐ (Algebra.ofId R S) f).commutes g

/-- Helper for Lemma 10.126.6: before transporting across the final-away chart identification,
the genuine target-side iterated localization `S_f[(g / 1)⁻¹]` is the away localization at the
product denominator `(f * g) / 1` inside `S`. -/
theorem final_away_target_chart_isLocalization_product
    {f g : R} :
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away ((algebraMap R S f) * algebraMap R S g)) :=
      (IsLocalization.Away.awayToAwayRight
        (P := Localization.Away ((algebraMap R S f) * algebraMap R S g))
        (algebraMap R S f)
        (algebraMap R S g)).toAlgebra
    IsLocalization.Away
      (algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g))
      (Localization.Away ((algebraMap R S f) * algebraMap R S g)) := by
  let ρprodS : Localization.Away (algebraMap R S f) →+*
      Localization.Away ((algebraMap R S f) * algebraMap R S g) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away ((algebraMap R S f) * algebraMap R S g))
      (algebraMap R S f)
      (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away ((algebraMap R S f) * algebraMap R S g)) := ρprodS.toAlgebra
  let eTargetChart :
      Localization.Away
          (algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g)) ≃ₐ[
            Localization.Away (algebraMap R S f)]
        Localization.Away ((algebraMap R S f) * algebraMap R S g) :=
    final_away_coeff_chart_algEquiv
      (R := S)
      (f := algebraMap R S f)
      (g := algebraMap R S g)
  -- Proof comment: transport the owner localization witness along the explicit coefficient-chart
  -- equivalence `S_f[(g / 1)⁻¹] ≃ S[(fg)⁻¹]`.
  exact
    IsLocalization.isLocalization_of_algEquiv
      (Submonoid.powers
        (algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g)))
      eTargetChart

/-- Helper for Lemma 10.126.6: the product-side target chart `S[((f)(g))⁻¹]` and the pipeline
target `S[(fg)⁻¹]` are canonically equivalent as `S_f`-algebras. This isolates the `map_mul`
transport that was previously hidden inside large `simpa` terms. -/
noncomputable def final_away_target_product_to_mul_transport
    {f g : R} :
    let fg : R := f * g
    letI : Algebra (Localization.Away (algebraMap R S f))
        (Localization.Away ((algebraMap R S f) * algebraMap R S g)) :=
      (IsLocalization.Away.awayToAwayRight
        (P := Localization.Away ((algebraMap R S f) * algebraMap R S g))
        (algebraMap R S f)
        (algebraMap R S g)).toAlgebra
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
    Localization.Away ((algebraMap R S f) * algebraMap R S g) ≃ₐ[
      Localization.Away (algebraMap R S f)]
      Localization.Away (algebraMap R S fg) := by
  intro fg
  let ρprodS : Localization.Away (algebraMap R S f) →+*
      Localization.Away ((algebraMap R S f) * algebraMap R S g) :=
    IsLocalization.Away.awayToAwayRight
      (P := Localization.Away ((algebraMap R S f) * algebraMap R S g))
      (algebraMap R S f)
      (algebraMap R S g)
  letI : Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away ((algebraMap R S f) * algebraMap R S g)) := ρprodS.toAlgebra
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
  let eS :
      Localization.Away ((algebraMap R S f) * algebraMap R S g) ≃ₐ[S]
        Localization.Away (algebraMap R S fg) :=
    Localization.algEquiv
      (Submonoid.powers ((algebraMap R S f) * algebraMap R S g))
      (Localization.Away (algebraMap R S fg))
  -- Proof comment: first compare the two final-away charts as `S`-localizations of the same
  -- denominator, then restrict scalars along `S_f → S[(fg)⁻¹]` by checking the two maps agree on
  -- the image of `S`.
  refine AlgEquiv.ofRingEquiv (f := eS.toRingEquiv) ?_
  intro a
  have hbase :
      eS.toRingHom.comp
          (algebraMap (Localization.Away (algebraMap R S f))
            (Localization.Away ((algebraMap R S f) * algebraMap R S g))) =
        ρfgS := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R S f))
    ext s
    calc
      eS.toRingHom
          (algebraMap (Localization.Away (algebraMap R S f))
            (Localization.Away ((algebraMap R S f) * algebraMap R S g))
            (algebraMap S (Localization.Away (algebraMap R S f)) s)) =
        eS.toRingHom (algebraMap S
          (Localization.Away ((algebraMap R S f) * algebraMap R S g)) s) := by
            rw [show
              algebraMap (Localization.Away (algebraMap R S f))
                  (Localization.Away ((algebraMap R S f) * algebraMap R S g))
                  (algebraMap S (Localization.Away (algebraMap R S f)) s) =
                algebraMap S
                  (Localization.Away ((algebraMap R S f) * algebraMap R S g)) s by
              simpa [ρprodS] using
                (IsLocalization.Away.awayToAwayRight_eq
                  (S := Localization.Away (algebraMap R S f))
                  (P := Localization.Away ((algebraMap R S f) * algebraMap R S g))
                  (x := algebraMap R S f)
                  (y := algebraMap R S g)
                  (a := s))]
      _ = algebraMap S (Localization.Away (algebraMap R S fg)) s := by
            simpa using eS.commutes s
      _ = ρfgS (algebraMap S (Localization.Away (algebraMap R S f)) s) := by
            symm
            simpa [ρfgS, fg] using
              (IsLocalization.Away.awayToAwayRight_eq
                (S := Localization.Away (algebraMap R S f))
                (P := Localization.Away (algebraMap R S fg))
                (x := algebraMap R S f)
                (y := algebraMap R S g)
                (a := s))
  simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hbase a

/-- Helper for Lemma 10.126.6: after the second shrink, the induced `R_f`-algebra structure on
the final target `S_(fg)` is the composite of the first-away map `R_f → S_f` with the target-side
away-to-away map `S_f → S_(fg)`. This is the target-side transport identity needed for the direct
localization comparison. -/
theorem final_away_target_quotient_map_powers
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
        (algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
    (Localization.awayMap (algebraMap R S) f).toAlgebra
  intro Qf uQ eQuot
  -- Proof comment: first identify the image of `uQ = [C g]` under the quotient equivalence with
  -- the coefficient `g / 1` seen from `R_f`, then rewrite that coefficient from the `R_f` and `S`
  -- viewpoints using the installed first-away algebra structure.
  calc
    Submonoid.map eQuot.toMonoidHom (Submonoid.powers uQ) =
        Submonoid.powers
          (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
            (algebraMap R (Localization.Away f) g)) := by
          simpa [Qf, uQ, eQuot] using
            final_away_source_quotient_map_powers
              (R := R)
              (S := S)
              (n := n)
              (f := f)
              (g := g)
              πshift
              hπshiftSurj
    _ =
      Submonoid.powers
        (algebraMap S (Localization.Away (algebraMap R S f)) (algebraMap R S g)) := by
          rw [final_away_target_chart_generator_eq (R := R) (S := S) (f := f) (g := g)]

end

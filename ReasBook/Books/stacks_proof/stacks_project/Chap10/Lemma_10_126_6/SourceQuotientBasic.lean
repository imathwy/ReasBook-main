import stacks_proof.stacks_project.Chap10.Lemma_10_126_6.ZeroSection

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FinitePresentation R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.126.6: in the quotient of a multivariable polynomial ring, the image of
the powers of a coefficient polynomial `C c` is exactly the powers of its quotient class. -/
theorem quotient_mvPolynomial_algebraMapSubmonoid_powers_eq
    {A : Type*} [CommRing A] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) A)) (c : A) :
    Algebra.algebraMapSubmonoid
      (R := MvPolynomial (Fin n) A)
      (S := MvPolynomial (Fin n) A ⧸ I)
      (Submonoid.powers (MvPolynomial.C c)) =
        Submonoid.powers
          (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A ⧸ I)
            (MvPolynomial.C c)) := by
  -- Proof comment: quotienting preserves the coefficient embedding `C`, so the image of the
  -- powers submonoid remains the powers of the quotient class of the same coefficient polynomial.
  simpa using
    (Algebra.algebraMapSubmonoid_powers
      (R := MvPolynomial (Fin n) A)
      (S := MvPolynomial (Fin n) A ⧸ I)
      (MvPolynomial.C c))

/-- Helper for Lemma 10.126.6: in the first-away source quotient, the image of the powers of
`C g` is exactly the powers of the quotient class of that coefficient polynomial. -/
theorem final_away_source_quotient_powers_eq
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f))) :
    let Qf := MvPolynomial (Fin n) (Localization.Away f) ⧸ K
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    Algebra.algebraMapSubmonoid
      (R := MvPolynomial (Fin n) (Localization.Away f))
      (S := Qf)
      (Submonoid.powers (MvPolynomial.C c)) =
        Submonoid.powers (Ideal.Quotient.mk K (MvPolynomial.C c)) := by
  intro Qf c
  -- Proof comment: after quotienting, the image of `C g` is definitionally the quotient class
  -- `Ideal.Quotient.mk K (C g)`, so this is exactly the generic quotient-powers lemma.
  change Algebra.algebraMapSubmonoid
      (R := MvPolynomial (Fin n) (Localization.Away f))
      (S := MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
      (Submonoid.powers (MvPolynomial.C c)) =
    Submonoid.powers
      (algebraMap (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
        (MvPolynomial.C c))
  simpa using
    quotient_mvPolynomial_algebraMapSubmonoid_powers_eq
      (A := Localization.Away f)
      (n := n)
      (I := K)
      c

/-- Helper for Lemma 10.126.6: the canonical quotient map from the first-away polynomial quotient
to the final-away polynomial quotient sends the class of `ψ` to the class of
`MvPolynomial.map ρfgR ψ`. -/
theorem final_away_source_quotient_algebraMap_apply_mk
    {n : ℕ} {f g : R}
    (K : Ideal (MvPolynomial (Fin n) (Localization.Away f)))
    (ψ : MvPolynomial (Fin n) (Localization.Away f)) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
        (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
    let Kfg : Ideal (MvPolynomial (Fin n) (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfgR) K
    letI : Algebra
        (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
        (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) :=
      Ideal.Quotient.algebraQuotientMapQuotient
    algebraMap
        (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
        (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg)
        (Ideal.Quotient.mk K ψ) =
      Ideal.Quotient.mk Kfg (MvPolynomial.map ρfgR ψ) := by
  intro fg ρfgR
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (MvPolynomial (Fin n) (Localization.Away fg)) := (MvPolynomial.map ρfgR).toAlgebra
  intro Kfg
  letI : Algebra
      (MvPolynomial (Fin n) (Localization.Away f) ⧸ K)
      (MvPolynomial (Fin n) (Localization.Away fg) ⧸ Kfg) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  -- Proof comment: this is exactly the quotient-map computation for the coefficient base-change
  -- homomorphism `MvPolynomial.map ρfgR`, so the quotient representative is unchanged by
  -- normalization.
  rfl

/-- Helper for Lemma 10.126.6: the second basic-open map `R_f → R_(fg)` is compatible with the
original `R`-algebra structures, so `R_(fg)` lies in the expected scalar tower over `R_f`. -/
theorem final_away_right_isScalarTower (f g : R) :
    let fg : R := f * g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    IsScalarTower R (Localization.Away f) (Localization.Away fg) := by
  intro fg ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  -- Proof comment: the away-to-away map still sends `r / 1` to `r / 1`, so the induced
  -- `Localization.Away f`-algebra structure agrees with the original `R`-algebra map.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro r
  symm
  simpa [ρfgR, fg] using
    (IsLocalization.Away.awayToAwayRight_eq
      (S := Localization.Away f)
      (P := Localization.Away fg)
      (x := f)
      (y := g)
      (a := r))

/-- Helper for Lemma 10.126.6: viewing `R_(fg)` from the `R_g` side gives the analogous scalar
tower used by the commutation argument for iterated away localizations. -/
theorem final_away_left_isScalarTower (f g : R) :
    let fg : R := f * g
    let ρgfR : Localization.Away g →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayLeft (P := Localization.Away fg) g f
    letI : Algebra (Localization.Away g) (Localization.Away fg) := ρgfR.toAlgebra
    IsScalarTower R (Localization.Away g) (Localization.Away fg) := by
  intro fg ρgfR
  letI : Algebra (Localization.Away g) (Localization.Away fg) := ρgfR.toAlgebra
  -- Proof comment: this is the left-handed version of the same compatibility statement, now
  -- computed through `awayToAwayLeft`.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro r
  symm
  simpa [ρgfR, fg, mul_comm] using
    (IsLocalization.Away.awayToAwayLeft_eq
      (S := Localization.Away g)
      (P := Localization.Away fg)
      (x := g)
      (y := f)
      (a := r))

/-- Helper for Lemma 10.126.6: the defining denominator `f / 1` is a unit in the first away
chart `R_f`. This is the coefficient-level unit used to compare `g / 1` with `(fg) / 1`. -/
theorem final_away_base_denominator_isUnit (f : R) :
    IsUnit (algebraMap R (Localization.Away f) f) := by
  -- Proof comment: away-localizing at `f` makes the image of `f` invertible by definition.
  exact
    IsLocalization.Away.algebraMap_isUnit
      (R := R)
      (S := Localization.Away f)
      (x := f)

/-- Helper for Lemma 10.126.6: in `R_f`, the product denominator `(fg) / 1` differs from `g / 1`
by the unit `f / 1`, so these two elements are associated. -/
theorem final_away_coeff_product_associated (f g : R) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    Associated (algebraMap R (Localization.Away f) (f * g)) c := by
  intro c
  -- Proof comment: rewrite `(fg) / 1` as `(f / 1) * (g / 1)` and cancel the unit `f / 1`.
  rw [map_mul]
  simpa [c, mul_comm] using
    (associated_mul_unit_left
      (algebraMap R (Localization.Away f) g)
      (algebraMap R (Localization.Away f) f)
      (final_away_base_denominator_isUnit (R := R) f))

/-- Helper for Lemma 10.126.6: the genuine coefficient chart `(R_f)_(g / 1)` is already an
away-localization of `R` at `fg`. This is the source-side chart before transporting back to the
final away ring `R_(fg)`. -/
theorem final_away_coeff_chart_isLocalizationAway_product
    (f g : R) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    IsLocalization.Away (f * g) (Localization.Away c) := by
  intro c
  letI : IsScalarTower R (Localization.Away f) (Localization.Away c) := inferInstance
  -- Proof comment: localizing `R_f` once more at `g / 1` is exactly the iterated-away situation
  -- covered by `IsLocalization.Away.mul'`.
  exact IsLocalization.Away.mul' (Localization.Away f) (Localization.Away c) f g

/-- Helper for Lemma 10.126.6: the genuine coefficient chart `(R_f)_(g / 1)` and the final chart
`R_(fg)` are canonically isomorphic as `R`-algebras because both localize `R` away from `fg`. -/
noncomputable def final_away_coeff_chart_algEquiv_over_R
    (f g : R) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    Localization.Away (f * g) ≃ₐ[R] Localization.Away c := by
  intro c
  letI : IsLocalization.Away (f * g) (Localization.Away c) :=
    final_away_coeff_chart_isLocalizationAway_product (R := R) f g
  -- Proof comment: once both rings are registered as away-localizations of the same element,
  -- the universal localization comparison gives the canonical algebra equivalence.
  exact Localization.algEquiv (Submonoid.powers (f * g)) (Localization.Away c)

/-- Helper for Lemma 10.126.6: the composed `R`-algebra structure on the genuine coefficient chart
`(R_f)_(g / 1)` agrees with the scalar tower through `R_f`. -/
theorem final_away_coeff_chart_isScalarTower (f g : R) :
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    IsScalarTower R (Localization.Away f) (Localization.Away c) := by
  intro c
  -- Proof comment: this is the textbook coefficient chart, so the `R`-structure is literally the
  -- composite `R → R_f → (R_f)_(g / 1)` through the canonical localization instances.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro r
  rfl

/-- Helper for Lemma 10.126.6: after fixing the scalar-tower data on the coefficient chart, the
canonical comparison with `R_(fg)` restricts from `R` to an `R_f`-algebra equivalence. -/
noncomputable def final_away_coeff_chart_algEquiv
    (f g : R) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    Localization.Away c ≃ₐ[Localization.Away f] Localization.Away fg := by
  intro fg c ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : IsScalarTower R (Localization.Away f) (Localization.Away fg) :=
    final_away_right_isScalarTower (R := R) f g
  letI : IsScalarTower R (Localization.Away f) (Localization.Away c) :=
    final_away_coeff_chart_isScalarTower (R := R) f g
  let eR : Localization.Away c ≃ₐ[R] Localization.Away fg :=
    (final_away_coeff_chart_algEquiv_over_R (R := R) f g).symm
  -- Proof comment: the already constructed `R`-algebra equivalence now lives over `R_f` because
  -- both coefficient charts send every element of `R_f` to the same image in `R_(fg)`.
  refine AlgEquiv.ofRingEquiv (f := eR.toRingEquiv) ?_
  intro a
  have hbase :
      eR.toRingHom.comp (algebraMap (Localization.Away f) (Localization.Away c)) = ρfgR := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    -- Proof comment: both comparison maps agree on `R`, so localization extensionality promotes
    -- that equality to a map equality on `R_f`.
    have hcompc :
        algebraMap (Localization.Away f) (Localization.Away c)
            (algebraMap R (Localization.Away f) r) =
          algebraMap R (Localization.Away c) r := by
      simpa using
        DFunLike.congr_fun
          (IsScalarTower.algebraMap_eq R (Localization.Away f) (Localization.Away c))
          r
    calc
      eR.toRingHom
          (algebraMap (Localization.Away f) (Localization.Away c)
            (algebraMap R (Localization.Away f) r)) =
        eR (algebraMap R (Localization.Away c) r) := by
          rw [hcompc]
          rfl
      _ = algebraMap R (Localization.Away fg) r := by
            simpa [eR] using eR.commutes r
      _ = ρfgR (algebraMap R (Localization.Away f) r) := by
            symm
            simpa [ρfgR, fg] using
              (IsLocalization.Away.awayToAwayRight_eq
                (S := Localization.Away f)
                (P := Localization.Away fg)
                (x := f)
                (y := g)
                (a := r))
  simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hbase a

/-- Helper for Lemma 10.126.6: under the quotient equivalence attached to the surjective
shifted presentation on `R_f`, the quotient class of the coefficient polynomial `C g` is sent to
the localized coefficient `g / 1` in `S_f`. -/
theorem final_away_coeff_isLocalizationAway
    {f g : R} :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let ρfgR : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
    IsLocalization.Away c (Localization.Away fg) := by
  -- Route correction: the genuine source chart `(R_f)_(g / 1)` is now isolated in
  -- `final_away_coeff_chart_isLocalizationAway_product` and compared with `R_(fg)` over `R` in
  -- `final_away_coeff_chart_algEquiv_over_R`. The remaining blocker is upgrading that comparison
  -- to an `R_f`-algebra equivalence so `IsLocalization.isLocalization_of_algEquiv` can transport
  -- the away witness from the source chart back to `R_(fg)` without reopening the old `whnf`
  -- path on the quotient transport.
  intro fg c ρfgR
  letI : Algebra (Localization.Away f) (Localization.Away fg) := ρfgR.toAlgebra
  letI : IsScalarTower R (Localization.Away f) (Localization.Away fg) :=
    final_away_right_isScalarTower (R := R) f g
  letI : IsScalarTower R (Localization.Away f) (Localization.Away c) :=
    final_away_coeff_chart_isScalarTower (R := R) f g
  let e :
      Localization.Away c ≃ₐ[Localization.Away f] Localization.Away fg :=
    final_away_coeff_chart_algEquiv (R := R) f g
  -- Proof comment: `Localization.Away c` is the owner localization of `R_f` away from `c`, and
  -- the restricted-scalars equivalence `e` transports that witness directly to the final chart.
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers c) e

end

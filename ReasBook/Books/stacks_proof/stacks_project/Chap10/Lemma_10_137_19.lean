import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {R : Type u} {Sbar : Type v} [CommRing R] (I : Ideal R)
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar] [Smooth (R ⧸ I) Sbar]

/- Domain-style sampling:
* primary domain: smooth commutative algebras over quotient rings and their local standard-smooth
  presentations;
* sampled declarations:
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`,
  `Algebra.IsStandardSmooth`,
  `jacobian_inverted_quotient_isStandardSmooth`,
  `exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic`;
* best owner abstraction: on each lifted chart, the target structure should be expressed directly
  by the canonical owner `Algebra.IsStandardSmooth R S`, not by a parallel presentation wrapper;
* primitive vs. derived:
  the primitive source data are the quotient ideal `I`, the quotient algebra `Sbar`, and the
  ambient owner `[Smooth (R ⧸ I) Sbar]`;
  the cover, the lifted chart algebra `S`, its standard-smooth owner, and the quotient comparison
  `Localization.Away g ≃ₐ[R ⧸ I] S ⧸ Ideal.map (algebraMap R S) I` are derived existence data.

Source/core/bridge triage:
* `source-facing`: the existence of a standard-open cover of `Spec Sbar` by charts that lift to
  standard smooth `R`-algebras;
* `core/canonical`: `Algebra.IsStandardSmooth`;
* `bridge/view`: the quotient comparison equivalence identifying each chart
  `Localization.Away g` with the reduction modulo `I` of its lift.

The weaker Chapter 10 theorem
`exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic` has the same local
quotient-lift shape, but its owner conclusion is only the relative-global-complete-intersection
structure. This file keeps the stronger source-facing standard-smooth conclusion rather than
introducing any intermediate wrapper.
-/

omit [Smooth (R ⧸ I) Sbar] in
/-- Helper for Chap10 Lemma 10 137 19: every coefficient in a submersive presentation over
`R ⧸ I` lifts along the surjection `R → R ⧸ I`. -/
lemma submersivePresentationHasCoeffsOfQuotient {T : Type v} [CommRing T] [Algebra (R ⧸ I) T]
    [Algebra R T] [IsScalarTower R (R ⧸ I) T] {ι : Type*} {σ : Type*} [Finite σ]
    (P : Algebra.SubmersivePresentation (R ⧸ I) T ι σ) :
    P.HasCoeffs R := by
  -- Every coefficient in `R ⧸ I` has a preimage in `R`, so the whole coefficient package lifts.
  refine ⟨?_⟩
  intro x _hx
  simpa using (Ideal.Quotient.mk_surjective x : ∃ y : R, Ideal.Quotient.mk I y = x)

omit [Smooth (R ⧸ I) Sbar] in
/-- Helper for Chap10 Lemma 10 137 19: the descended presentation over `R` reduces back to the
original `(R ⧸ I)`-presentation. -/
noncomputable def reducedPresentationQuotientEquiv {T : Type v} [CommRing T] [Algebra (R ⧸ I) T]
    [Algebra R T] [IsScalarTower R (R ⧸ I) T] {ι : Type*} {σ : Type*}
    (P : Algebra.Presentation (R ⧸ I) T ι σ) [P.HasCoeffs R] :
    (P.ModelOfHasCoeffs R ⧸ Ideal.map (algebraMap R (P.ModelOfHasCoeffs R)) I) ≃ₐ[R ⧸ I] T :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (P.ModelOfHasCoeffs R) I).trans
    (P.tensorModelOfHasCoeffsEquiv R)

omit [Smooth (R ⧸ I) Sbar] in
/-- Helper for Chap10 Lemma 10 137 19: mapping an ideal into a localization can be computed
through the intermediate presentation ring. -/
lemma localizationIdealMapEq {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] (K : Ideal A) :
    Ideal.map (algebraMap A C) K = Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) K) := by
  -- Rewrite the algebra map through the intermediate ring before using `Ideal.map_map`.
  calc
    Ideal.map (algebraMap A C) K
        = Ideal.map (((algebraMap B C) : B →+* C).comp (algebraMap A B)) K := by
            rw [IsScalarTower.algebraMap_eq A B C]
    _ = Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) K) := by
          rw [Ideal.map_map]

omit [Smooth (R ⧸ I) Sbar] in
/-- Helper for Chap10 Lemma 10 137 19: if an `A`-algebra structure on `C` is defined by composing
the maps `A → B → C`, then its algebra map is exactly that composite. -/
lemma algebraMapEqCompOfToAlgebra {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] :
    let _ : Algebra A C := RingHom.toAlgebra (((algebraMap B C) : B →+* C).comp (algebraMap A B))
    ∀ a : A, algebraMap A C a = algebraMap B C (algebraMap A B a) := by
  -- Read the chosen `RingHom.toAlgebra` structure back as its defining composite ring map.
  dsimp
  intro a
  simp [RingHom.algebraMap_toAlgebra]

omit [Smooth (R ⧸ I) Sbar] in
/-- Helper for Chap10 Lemma 10 137 19: under the reduction equivalence, the lifted Jacobian class
maps to the original Jacobian unit. -/
lemma reducedLiftedJacobianImage {T : Type v} [CommRing T] [Algebra (R ⧸ I) T]
    [Algebra R T] [IsScalarTower R (R ⧸ I) T] {ι : Type*} {σ : Type*} [Finite σ]
    (P : Algebra.SubmersivePresentation (R ⧸ I) T ι σ)
    [P.HasCoeffs R] :
    let Ppres : Algebra.Presentation (R ⧸ I) T ι σ := P.toPresentation
    let S0 := Ppres.ModelOfHasCoeffs R
    let J : Ideal S0 := Ideal.map (algebraMap R S0) I
    let Δ0 : S0 := (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian
    reducedPresentationQuotientEquiv (R := R) (I := I) Ppres (Ideal.Quotient.mk J Δ0) =
      P.jacobian := by
  -- Route correction: send the lifted Jacobian class to the tensor model first, then evaluate the
  -- descended Jacobian polynomial back at the original submersive presentation.
  dsimp [reducedPresentationQuotientEquiv]
  have hΔ0 :
      (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian =
        Ideal.Quotient.mk
          (Ideal.span (Set.range (P.toPresentation.relationOfHasCoeffs R)))
          (P.jacobianOfHasCoeffs R) := by
    classical
    letI : Fintype σ := Fintype.ofFinite σ
    letI : DecidableEq σ := Classical.decEq σ
    have hdet :
        (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobiMatrix.det = P.jacobianOfHasCoeffs R := by
      rw [Algebra.SubmersivePresentation.jacobianOfHasCoeffs]
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    rw [show
      (algebraMap (P.toPreSubmersivePresentation.ofHasCoeffs R).Ring
          (P.toPresentation.ModelOfHasCoeffs R)) =
        Ideal.Quotient.mk (Ideal.span (Set.range (P.toPresentation.relationOfHasCoeffs R))) by
          rfl]
    exact congrArg
      (Ideal.Quotient.mk (Ideal.span (Set.range (P.toPresentation.relationOfHasCoeffs R)))) hdet
  rw [hΔ0]
  simpa using
    (P.toPresentation.tensorModelOfHasCoeffsEquiv_tmul (R₀ := R) (x := (1 : R ⧸ I))
      (y := P.jacobianOfHasCoeffs R)).trans P.aeval_jacobianOfHasCoeffs R

omit [Smooth (R ⧸ I) Sbar] in
/-- Helper for Chap10 Lemma 10 137 19: the reduced lifted Jacobian is already a unit before
localizing, so the reduced localization later collapses by `IsLocalization.atUnit`. -/
lemma reducedLiftedJacobianIsUnit {T : Type v} [CommRing T] [Algebra (R ⧸ I) T]
    [Algebra R T] [IsScalarTower R (R ⧸ I) T] {ι : Type*} {σ : Type*} [Finite σ]
    (P : Algebra.SubmersivePresentation (R ⧸ I) T ι σ)
    [P.HasCoeffs R] :
    let Ppres : Algebra.Presentation (R ⧸ I) T ι σ := P.toPresentation
    let S0 := Ppres.ModelOfHasCoeffs R
    let J : Ideal S0 := Ideal.map (algebraMap R S0) I
    let Δ0 : S0 := (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian
    IsUnit (Ideal.Quotient.mk J Δ0) := by
  -- Transport the original Jacobian unit across the reduced-presentation equivalence.
  dsimp
  let e0 := reducedPresentationQuotientEquiv (R := R) (I := I) P.toPresentation
  have hunit :
      IsUnit
        (e0.symm P.jacobian) := by
    exact
      IsUnit.map
        (e0.symm :
          T →+* (P.toPresentation.ModelOfHasCoeffs R ⧸
            Ideal.map (algebraMap R (P.toPresentation.ModelOfHasCoeffs R)) I))
        P.jacobian_isUnit
  have hsymm :
      e0.symm P.jacobian =
        Ideal.Quotient.mk
          (Ideal.map (algebraMap R (P.toPresentation.ModelOfHasCoeffs R)) I)
          ((P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian) := by
    apply e0.injective
    simpa using (reducedLiftedJacobianImage (R := R) (I := I) P).symm
  simpa [hsymm] using hunit

omit [Smooth (R ⧸ I) Sbar] in
/-- Helper for Chap10 Lemma 10 137 19: every standard smooth `(R ⧸ I)`-algebra is the reduction
modulo `I` of a standard smooth `R`-algebra. -/
theorem existsStandardSmoothLiftOfQuotientStandardSmooth {T : Type v} [CommRing T]
    [Algebra (R ⧸ I) T] [IsStandardSmooth (R ⧸ I) T] [Algebra R T]
    [IsScalarTower R (R ⧸ I) T] :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : IsStandardSmooth R S),
      Nonempty (T ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := by
  classical
  obtain ⟨ι, σ, hσ, hι, hP⟩ := Algebra.IsStandardSmooth.out (R := R ⧸ I) (S := T)
  letI : Finite σ := hσ
  letI : Finite ι := hι
  letI : DecidableEq σ := Classical.decEq σ
  obtain ⟨P⟩ := hP
  letI : P.HasCoeffs R := submersivePresentationHasCoeffsOfQuotient (R := R) (I := I) P
  let Ppres : Algebra.Presentation (R ⧸ I) T ι σ := P.toPresentation
  letI : Ppres.HasCoeffs R := inferInstance
  let S0 := Ppres.ModelOfHasCoeffs R
  letI : CommRing S0 := inferInstance
  letI : Algebra R S0 := inferInstance
  let P0 : Algebra.PreSubmersivePresentation R S0 ι σ :=
    P.toPreSubmersivePresentation.ofHasCoeffs R
  let Δ0 : S0 := P0.jacobian
  let S := Localization.Away Δ0
  letI : CommRing S := inferInstance
  letI : Algebra S0 S := inferInstance
  letI : Algebra R S := inferInstance
  letI : Module S0 S0 := Semiring.toModule
  letI : DistribMulAction S0 S0 := { (Semiring.toModule : Module S0 S0) with }
  let Q : Algebra.SubmersivePresentation S0 S Unit Unit :=
    Algebra.SubmersivePresentation.localizationAway S Δ0
  let Ploc : Algebra.SubmersivePresentation R S (Unit ⊕ ι) (Unit ⊕ σ) :=
    { toPreSubmersivePresentation := Q.toPreSubmersivePresentation.comp P0
      jacobian_isUnit := by
        -- After adjoining an inverse to `Δ0`, the composite Jacobian is a product of units.
        have hΔ : IsUnit (algebraMap S0 S P0.jacobian) :=
          IsLocalization.Away.algebraMap_isUnit P0.jacobian
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        exact hΔ.mul Q.jacobian_isUnit }
  have hStd : IsStandardSmooth R S := by
    -- The localized descended presentation is submersive, hence standard smooth.
    exact Ploc.isStandardSmooth
  have hquot : Nonempty (T ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := by
    let J : Ideal S0 := Ideal.map (algebraMap R S0) I
    let e0 : (S0 ⧸ J) ≃ₐ[R ⧸ I] T :=
      reducedPresentationQuotientEquiv (R := R) (I := I) Ppres
    have hunitΔbar : IsUnit (Ideal.Quotient.mk J Δ0) := by
      -- The lifted Jacobian becomes the original Jacobian unit after reducing modulo `I`.
      simpa [Ppres, S0, J, P0, Δ0] using
        reducedLiftedJacobianIsUnit (R := R) (I := I) P
    have hmapJS : Ideal.map (algebraMap R S) I = Ideal.map (algebraMap S0 S) J := by
      -- Re-express the quotient ideal in the localization over the intermediate ring `S0`.
      simpa [J] using localizationIdealMapEq (A := R) (B := S0) (C := S) I
    letI : Algebra (S0 ⧸ J) (S ⊗[S0] (S0 ⧸ J)) :=
      Algebra.TensorProduct.rightAlgebra (R := S0) (A := S) (B := S0 ⧸ J)
    let eQuotTensor :
        (S ⧸ Ideal.map (algebraMap S0 S) J) ≃ₐ[S0 ⧸ J] ((S0 ⧸ J) ⊗[S0] S) :=
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor S J
    let eTensorComm :
        ((S0 ⧸ J) ⊗[S0] S) ≃ₐ[S0 ⧸ J] (S ⊗[S0] (S0 ⧸ J)) :=
      { __ := Algebra.TensorProduct.comm S0 (S0 ⧸ J) S
        commutes' := fun _ ↦ rfl }
    let eTensorAway :
        (S ⊗[S0] (S0 ⧸ J)) ≃ₐ[S0 ⧸ J] Localization.Away (Ideal.Quotient.mk J Δ0) :=
      IsLocalization.Away.tensorRightEquiv (R := S0) (S := S0 ⧸ J) (A := S) (r := Δ0)
    let eAwayCollapse :
        Localization.Away (Ideal.Quotient.mk J Δ0) ≃ₐ[S0 ⧸ J] (S0 ⧸ J) :=
      (IsLocalization.atUnit (S0 ⧸ J) (Localization.Away (Ideal.Quotient.mk J Δ0))
        (Ideal.Quotient.mk J Δ0) hunitΔbar).symm
    let eReduced :
        (S ⧸ Ideal.map (algebraMap S0 S) J) ≃ₐ[S0 ⧸ J] (S0 ⧸ J) :=
      eQuotTensor.trans (eTensorComm.trans (eTensorAway.trans eAwayCollapse))
    letI : Algebra (R ⧸ I) (S ⧸ Ideal.map (algebraMap S0 S) J) :=
      RingHom.toAlgebra
        (((algebraMap (S0 ⧸ J) (S ⧸ Ideal.map (algebraMap S0 S) J)) :
            (S0 ⧸ J) →+* (S ⧸ Ideal.map (algebraMap S0 S) J)).comp
          (algebraMap (R ⧸ I) (S0 ⧸ J)))
    let eReducedRbar :
        (S ⧸ Ideal.map (algebraMap S0 S) J) ≃ₐ[R ⧸ I] (S0 ⧸ J) :=
      { __ := eReduced.toRingEquiv
        commutes' := by
          intro r
          rw [algebraMapEqCompOfToAlgebra (A := R ⧸ I) (B := S0 ⧸ J)
            (C := S ⧸ Ideal.map (algebraMap S0 S) J) r]
          simpa using eReduced.commutes ((algebraMap (R ⧸ I) (S0 ⧸ J)) r) }
    let eQuotientToT :
        (S ⧸ Ideal.map (algebraMap S0 S) J) ≃ₐ[R ⧸ I] T :=
      eReducedRbar.trans e0
    let eMapEq :
        (S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap S0 S) J) :=
      { __ := Ideal.quotientEquiv _ _ (RingEquiv.refl S) (by simpa using hmapJS.symm)
        commutes' := by
          rintro ⟨r⟩
          rfl }
    -- Compose the reduction comparison with the quotient-ideal rewrite.
    exact ⟨(eMapEq.trans eQuotientToT).symm⟩
  obtain ⟨eT⟩ := hquot
  let U : Type (max u v) := ULift.{v} S
  letI : CommRing U := inferInstance
  letI : Algebra R U := inferInstance
  let fUL : S →ₐ[R] U :=
    { toRingHom :=
        { toFun := ULift.up
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      commutes' := fun _ ↦ rfl }
  have hfUL : Function.Bijective fUL := by
    constructor
    · intro x y hxy
      exact congrArg ULift.down hxy
    · intro y
      refine ⟨y.down, ?_⟩
      cases y
      rfl
  let eUL : S ≃ₐ[R] U := AlgEquiv.ofBijective fUL hfUL
  have hStdU : IsStandardSmooth R U := by
    letI : IsStandardSmooth R S := hStd
    exact Algebra.IsStandardSmooth.of_algEquiv eUL
  have hULmap :
      Ideal.map (algebraMap R S) I =
        (Ideal.map (algebraMap R U) I).map (eUL.symm : U →+* S) := by
    -- The `ULift` algebra equivalence is inverse to the canonical lift `S → ULift S`.
    calc
      Ideal.map (algebraMap R S) I
          = Ideal.map (((eUL.symm : U →+* S).comp (algebraMap R U))) I := by
              congr 1
              ext r
              simpa using eUL.symm.commutes r
      _ = (Ideal.map (algebraMap R U) I).map (eUL.symm : U →+* S) := by
            rw [Ideal.map_map]
  let eULquotR :
      (U ⧸ Ideal.map (algebraMap R U) I) ≃ₐ[R] (S ⧸ Ideal.map (algebraMap R S) I) :=
    Ideal.quotientEquivAlg _ _ eUL.symm hULmap
  let eULquot :
      (U ⧸ Ideal.map (algebraMap R U) I) ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I) :=
    { __ := eULquotR
      commutes' := by
        rintro ⟨r⟩
        change Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) (eUL.symm (algebraMap R U r)) =
          Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) (algebraMap R S r)
        exact congrArg (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (eUL.symm.commutes r) }
  exact ⟨U, inferInstance, inferInstance, hStdU, ⟨eT.trans eULquot.symm⟩⟩

-- Proof sketch: apply `Algebra.Smooth.exists_span_eq_top_isStandardSmooth` to the smooth map
-- `R ⧸ I → Sbar` to obtain a unit-ideal cover by basic opens on which `Sbar` is standard smooth
-- over `R ⧸ I`. For each chart, extract a submersive presentation from the owner
-- `Algebra.IsStandardSmooth`, lift the defining equations and Jacobian determinant to `R`, and
-- use Example `10.137.7` to produce a standard smooth `R`-algebra whose reduction modulo `I`
-- identifies with the given localization.
/-- Chap10 Lemma 10 137 19: a smooth `(R ⧸ I)`-algebra admits a standard-open cover by
localizations which are reductions modulo `I` of standard smooth `R`-algebras. -/
@[stacks 04B1]
theorem exists_standardSmooth_lift_cover_of_quotient_smooth :
    ∃ s : Set Sbar, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
        (_ : IsStandardSmooth R S),
          Nonempty ((Localization.Away g) ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := by
  classical
  obtain ⟨s, hs, hstd⟩ :=
    Algebra.Smooth.exists_span_eq_top_isStandardSmooth (R := R ⧸ I) (S := Sbar)
  refine ⟨s, hs, ?_⟩
  intro g hg
  let T := Localization.Away g
  letI : Algebra R T :=
    RingHom.toAlgebra (((algebraMap (R ⧸ I) T) : (R ⧸ I) →+* T).comp (Ideal.Quotient.mk I))
  letI : IsScalarTower R (R ⧸ I) T :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsStandardSmooth (R ⧸ I) T := hstd g hg
  -- Each standard-smooth chart over `R ⧸ I` lifts independently to a standard-smooth `R`-chart.
  simpa [T] using
    existsStandardSmoothLiftOfQuotientStandardSmooth (R := R) (I := I) (T := T)

end

end Algebra

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {R : Type u} {Sbar : Type v} [CommRing R] (I : Ideal R)
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar] [Etale (R ⧸ I) Sbar]

omit [Etale (R ⧸ I) Sbar] in
/-- Helper for Lemma 10.143.10: every coefficient of a presentation over `R ⧸ I` lifts along the
surjection `R → R ⧸ I`. -/
lemma presentation_hasCoeffs_of_quotient {ι : Type*} {σ : Type*}
    [Algebra R Sbar] [IsScalarTower R (R ⧸ I) Sbar]
    (P : Algebra.Presentation (R ⧸ I) Sbar ι σ) :
    P.HasCoeffs R := by
  -- Every coefficient in `R ⧸ I` has a preimage in `R`, so the presentation coefficients lift.
  refine ⟨?_⟩
  intro x _hx
  simpa using (Ideal.Quotient.mk_surjective x : ∃ y : R, Ideal.Quotient.mk I y = x)

omit [Etale (R ⧸ I) Sbar] in
/-- Helper for Lemma 10.143.10: the full submersive coefficient package over `R ⧸ I` also lifts
along `R → R ⧸ I`. -/
lemma submersivePresentation_hasCoeffs_of_quotient {ι : Type*} {σ : Type*}
    [Algebra R Sbar] [IsScalarTower R (R ⧸ I) Sbar]
    [Finite σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation (R ⧸ I) Sbar ι σ) :
    P.HasCoeffs R := by
  -- Every coefficient appearing in the submersive data lives in `R ⧸ I`, so surjectivity of the
  -- quotient map lifts the whole coefficient package at once.
  refine ⟨?_⟩
  intro x _hx
  simpa using (Ideal.Quotient.mk_surjective x : ∃ y : R, Ideal.Quotient.mk I y = x)

/-- Helper for Lemma 10.143.10: the descended presentation over `R` reduces back to the original
`(R ⧸ I)`-presentation. -/
noncomputable def reduced_presentation_quotient_equiv {ι : Type*} {σ : Type*}
    [Algebra R Sbar] [IsScalarTower R (R ⧸ I) Sbar]
    (P : Algebra.Presentation (R ⧸ I) Sbar ι σ) [P.HasCoeffs R] :
    (P.ModelOfHasCoeffs R ⧸ Ideal.map (algebraMap R (P.ModelOfHasCoeffs R)) I) ≃ₐ[R ⧸ I] Sbar :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (P.ModelOfHasCoeffs R) I).trans
    (P.tensorModelOfHasCoeffsEquiv R)

/-- Helper for Lemma 10.143.10: mapping an ideal to the localization can be computed through the
intermediate presentation ring. -/
lemma localization_ideal_map_eq {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] (K : Ideal A) :
    Ideal.map (algebraMap A C) K = Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) K) := by
  -- Route correction: rewrite the quotient ideal over the intermediate ring first, so the later
  -- localization comparison only sees the canonical `B → C` algebra structure.
  calc
    Ideal.map (algebraMap A C) K
        = Ideal.map (((algebraMap B C) : B →+* C).comp (algebraMap A B)) K := by
            rw [IsScalarTower.algebraMap_eq A B C]
    _ = Ideal.map (algebraMap B C) (Ideal.map (algebraMap A B) K) := by
          rw [Ideal.map_map]

/-- Helper for Lemma 10.143.10: if the `R`-algebra structure on `B` is defined by
`RingHom.toAlgebra (g.comp f)`, then its algebra map is exactly the composite `g.comp f`. -/
lemma algebraMap_eq_comp_of_toAlgebra {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] :
    let _ : Algebra A C := RingHom.toAlgebra (((algebraMap B C) : B →+* C).comp (algebraMap A B))
    ∀ a : A, algebraMap A C a = algebraMap B C (algebraMap A B a) := by
  dsimp
  intro a
  -- Read the chosen `RingHom.toAlgebra` structure back as its defining composite map.
  simp [RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.143.10: under the reduction equivalence, the lifted Jacobian determinant
descends to the original Jacobian unit. -/
lemma reduced_lifted_jacobian_image {ι : Type*} {σ : Type*}
    [Algebra R Sbar] [IsScalarTower R (R ⧸ I) Sbar]
    [Finite σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation (R ⧸ I) Sbar ι σ)
    [P.HasCoeffs R] :
    let Ppres : Algebra.Presentation (R ⧸ I) Sbar ι σ := P.toPresentation
    let S0 := Ppres.ModelOfHasCoeffs R
    let J : Ideal S0 := Ideal.map (algebraMap R S0) I
    let Δ0 : S0 := (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian
    reduced_presentation_quotient_equiv (R := R) (I := I) (Sbar := Sbar) Ppres
      (Ideal.Quotient.mk J Δ0) = P.jacobian := by
  -- Route correction: push the quotient class to the canonical tensor generator first, then the
  -- tensor-model equivalence evaluates the descended Jacobian polynomial back to `P.jacobian`.
  dsimp [reduced_presentation_quotient_equiv]
  -- The descended Jacobian is the quotient class of the smaller-ring Jacobian determinant.
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
    exact congrArg (Ideal.Quotient.mk (Ideal.span (Set.range (P.toPresentation.relationOfHasCoeffs R)))) hdet
  rw [hΔ0]
  -- Evaluate that descended polynomial through the canonical tensor-model equivalence.
  simpa using
    (P.toPresentation.tensorModelOfHasCoeffsEquiv_tmul (R₀ := R) (x := (1 : R ⧸ I))
      (y := P.jacobianOfHasCoeffs R)).trans P.aeval_jacobianOfHasCoeffs R

/-- Helper for Lemma 10.143.10: the reduced lifted Jacobian is already a unit before localizing,
so the quotient localization later collapses by `IsLocalization.Away.atUnit`. -/
lemma reduced_lifted_jacobian_isUnit {ι : Type*} {σ : Type*}
    [Algebra R Sbar] [IsScalarTower R (R ⧸ I) Sbar]
    [Finite σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation (R ⧸ I) Sbar ι σ)
    [P.HasCoeffs R] :
    let Ppres : Algebra.Presentation (R ⧸ I) Sbar ι σ := P.toPresentation
    let S0 := Ppres.ModelOfHasCoeffs R
    let J : Ideal S0 := Ideal.map (algebraMap R S0) I
    let Δ0 : S0 := (P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian
    IsUnit (Ideal.Quotient.mk J Δ0) := by
  -- The source proof uses the Jacobian criterion exactly here: after reduction, the lifted
  -- determinant becomes the original Jacobian, which is a unit because `P` is submersive.
  dsimp
  let e0 :=
    reduced_presentation_quotient_equiv (R := R) (I := I) (Sbar := Sbar) P.toPresentation
  have hunit : IsUnit (e0.symm P.jacobian) :=
    IsUnit.map (e0.symm : Sbar →+* (P.toPresentation.ModelOfHasCoeffs R ⧸
      Ideal.map (algebraMap R (P.toPresentation.ModelOfHasCoeffs R)) I)) P.jacobian_isUnit
  have hsymm :
      e0.symm P.jacobian =
        Ideal.Quotient.mk
          (Ideal.map (algebraMap R (P.toPresentation.ModelOfHasCoeffs R)) I)
          ((P.toPreSubmersivePresentation.ofHasCoeffs R).jacobian) := by
    apply e0.injective
    simpa using (reduced_lifted_jacobian_image (R := R) (I := I) (Sbar := Sbar) P).symm
  simpa [hsymm] using hunit

/- Domain-style sampling:
* primary domain: étale commutative algebras over quotient rings and their lifting to the base
  ring;
* sampled declarations:
  `Algebra.Etale`,
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`,
  `exists_standardSmooth_lift_cover_of_quotient_smooth`,
  `exists_etale_lift_to_quotient_of_smooth`;
* best owner abstraction: the primitive owner data are the ambient étale structures on the
  quotient algebra `Sbar` and on the lifted algebra `S`; the reduction isomorphism is derived
  comparison data and should be exposed on the canonical quotient-identification surface
  `Nonempty ((S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I] Sbar)`.

Source/core/bridge triage:
* `source-facing`: the existence of an étale `R`-algebra lifting the given étale
  `(R ⧸ I)`-algebra;
* `core/canonical`: the owner predicate `Algebra.Etale` together with the quotient algebra
  `S ⧸ Ideal.map (algebraMap R S) I`;
* `bridge/view`: the quotient comparison equivalence identifying that reduction with `Sbar`.

Primitive-vs-derived split:
* primitive data: only the lifted algebra `S` with its `R`-algebra and étale structures;
* derived API: the comparison equivalence between its reduction modulo `I` and `Sbar`.

This item is not a pure recall: it adds genuine source-facing existence content. The refinement is
therefore to keep the theorem and remove only the non-canonical `AlgHom`-plus-bijectivity
packaging of the comparison isomorphism.
-/

-- Proof sketch: by Lemma 10.143.2, present the étale `(R ⧸ I)`-algebra `Sbar` as standard smooth
-- of relative dimension `0`, with as many generators as relations and invertible Jacobian
-- determinant. Lift the defining polynomials to `R`, adjoin an inverse to the lifted determinant,
-- and use the standard étale criterion to obtain an étale `R`-algebra `S`. Reducing modulo `I`
-- recovers the original presentation, giving the required quotient algebra equivalence.
/-- Lemma 10.143.10: every étale algebra over the quotient ring `R ⧸ I` lifts to an étale
`R`-algebra whose reduction modulo `I` is isomorphic to the given quotient algebra. -/
@[stacks 04D1]
theorem exists_etale_lift_of_quotient :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : Etale R S),
      Nonempty ((S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I] Sbar) := by
  let Rbar : Type u := R ⧸ I
  letI : Algebra R Sbar :=
    RingHom.toAlgebra ((algebraMap Rbar Sbar).comp (Ideal.Quotient.mk I))
  letI : IsScalarTower R Rbar Sbar :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hstd : Algebra.IsStandardSmoothOfRelativeDimension 0 Rbar Sbar :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance)
  -- Extract the zero-dimensional submersive presentation that drives the source proof.
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (R := Rbar) (S := Sbar) (n := 0)
  letI : Finite σ := hσ
  letI : Finite ι := hι
  letI : DecidableEq σ := Classical.decEq σ
  letI : P.HasCoeffs R := submersivePresentation_hasCoeffs_of_quotient (R := R) (I := I) P
  let Ppres : Algebra.Presentation Rbar Sbar ι σ := P.toPresentation
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
  have hQdim : Q.dimension = 0 := by
    -- The localization-away presentation has one generator and one relation.
    simpa [Q, Algebra.Presentation.dimension]
  have hPloc : Ploc.dimension = 0 := by
    -- The lifted quotient has the same relative dimension as the original presentation.
    rw [show Ploc.dimension = (Q.toPreSubmersivePresentation.comp P0).dimension by rfl]
    rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
    simpa [P0, hP, hQdim]
  have hEt : Algebra.Etale R S := by
    -- Zero-dimensional standard smooth algebras are exactly the étale ones.
    rw [Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero]
    exact Ploc.isStandardSmoothOfRelativeDimension hPloc
  let T : Type (max u v) := ULift.{v} S
  letI : CommRing T := inferInstance
  letI : Algebra R T := inferInstance
  let fUL : S →ₐ[R] T :=
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
  let eUL : S ≃ₐ[R] T := AlgEquiv.ofBijective fUL hfUL
  have hEtT : Algebra.Etale R T := by
    letI : Algebra.Etale R S := hEt
    exact Algebra.Etale.of_equiv eUL
  have hquot : Nonempty ((T ⧸ Ideal.map (algebraMap R T) I) ≃ₐ[Rbar] Sbar) := by
    classical
    let J : Ideal S0 := Ideal.map (algebraMap R S0) I
    let e0 : (S0 ⧸ J) ≃ₐ[Rbar] Sbar :=
      reduced_presentation_quotient_equiv (R := R) (I := I) (Sbar := Sbar) Ppres
    have hΔbar : e0 (Ideal.Quotient.mk J Δ0) = P.jacobian := by
      -- Route correction: the Jacobian transport is now packaged separately, so the remaining
      -- quotient-localization step can work purely over `S0 ⧸ J`.
      simpa [Ppres, S0, J, P0, Δ0] using
        reduced_lifted_jacobian_image (R := R) (I := I) (Sbar := Sbar) P
    have hunitΔbar : IsUnit (Ideal.Quotient.mk J Δ0) := by
      -- The source proof needs exactly this unit to collapse the reduced localization.
      simpa [Ppres, S0, J, P0, Δ0] using
        reduced_lifted_jacobian_isUnit (R := R) (I := I) (Sbar := Sbar) P
    have hmapJS :
        Ideal.map (algebraMap R S) I = Ideal.map (algebraMap S0 S) J := by
      -- Re-express the ideal in the localization over the intermediate presentation ring `S0`.
      simpa [J] using localization_ideal_map_eq (A := R) (B := S0) (C := S) I
    letI : Algebra (S0 ⧸ J) (S ⊗[S0] (S0 ⧸ J)) :=
      Algebra.TensorProduct.rightAlgebra (R := S0) (A := S) (B := S0 ⧸ J)
    -- Route correction: keep the quotient/localization comparison entirely over `S0 ⧸ J` before
    -- restricting scalars back to `R ⧸ I`.
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
    -- Compose the three structural steps from the source proof, then remove the localization
    -- using that the reduced Jacobian is already a unit.
    let eReduced :
        (S ⧸ Ideal.map (algebraMap S0 S) J) ≃ₐ[S0 ⧸ J] (S0 ⧸ J) :=
      eQuotTensor.trans (eTensorComm.trans (eTensorAway.trans eAwayCollapse))
    letI : Algebra Rbar (S ⧸ Ideal.map (algebraMap S0 S) J) :=
      RingHom.toAlgebra
        (((algebraMap (S0 ⧸ J) (S ⧸ Ideal.map (algebraMap S0 S) J)) : (S0 ⧸ J) →+*
            (S ⧸ Ideal.map (algebraMap S0 S) J)).comp (algebraMap Rbar (S0 ⧸ J)))
    let eReducedRbar :
        (S ⧸ Ideal.map (algebraMap S0 S) J) ≃ₐ[Rbar] (S0 ⧸ J) :=
      { __ := eReduced.toRingEquiv
        commutes' := by
          intro r
          -- Rewrite the explicit quotient algebra map through `S0 ⧸ J`, then use that the
          -- reduced comparison is already an algebra equivalence over `S0 ⧸ J`.
          rw [algebraMap_eq_comp_of_toAlgebra (A := Rbar) (B := S0 ⧸ J)
            (C := S ⧸ Ideal.map (algebraMap S0 S) J) r]
          simpa using eReduced.commutes ((algebraMap Rbar (S0 ⧸ J)) r) }
    let eSbar' :
        (S ⧸ Ideal.map (algebraMap S0 S) J) ≃ₐ[Rbar] Sbar :=
      -- Compose the reduced-side comparison with the presentation reduction equivalence.
      eReducedRbar.trans e0
    let eMapEq :
        (S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[Rbar] (S ⧸ Ideal.map (algebraMap S0 S) J) :=
      { __ := Ideal.quotientEquiv _ _ (RingEquiv.refl S) (by simpa using hmapJS.symm)
        commutes' := by
          rintro ⟨r⟩
          rfl }
    let eSbar :
        (S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[Rbar] Sbar :=
      eMapEq.trans eSbar'
    have hULmap :
        Ideal.map (algebraMap R S) I =
          (Ideal.map (algebraMap R T) I).map (eUL.symm : T →+* S) := by
      -- The `ULift` algebra equivalence is inverse to the canonical lift `S → ULift S`.
      calc
        Ideal.map (algebraMap R S) I
            = Ideal.map (((eUL.symm : T →+* S).comp (algebraMap R T))) I := by
                congr 1
                ext r
                simpa using eUL.symm.commutes r
        _ = (Ideal.map (algebraMap R T) I).map (eUL.symm : T →+* S) := by
              rw [Ideal.map_map]
    let eULquotR :
        (T ⧸ Ideal.map (algebraMap R T) I) ≃ₐ[R] (S ⧸ Ideal.map (algebraMap R S) I) :=
      Ideal.quotientEquivAlg _ _ eUL.symm hULmap
    let eULquot :
        (T ⧸ Ideal.map (algebraMap R T) I) ≃ₐ[Rbar] (S ⧸ Ideal.map (algebraMap R S) I) :=
      { __ := eULquotR
        commutes' := by
          rintro ⟨r⟩
          change Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) (eUL.symm (algebraMap R T r)) =
            Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) (algebraMap R S r)
          exact congrArg (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)) (eUL.symm.commutes r) }
    exact ⟨eULquot.trans eSbar⟩
  exact ⟨T, inferInstance, inferInstance, hEtT, hquot⟩

end

end Algebra

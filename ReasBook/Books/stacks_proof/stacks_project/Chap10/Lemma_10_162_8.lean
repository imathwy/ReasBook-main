import Mathlib
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Lemma_10_31_2
import StacksProject_2024.Chap10.Lemma_10_160_11
import StacksProject_2024.Chap10.Lemma_10_161_5
import StacksProject_2024.Chap10.Lemma_10_161_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Finset Finsupp
open IsLocalRing AdicCompletion
open scoped BigOperators PowerSeries TensorProduct

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: commutative algebra of Nagata rings and the complete-local criterion for the
  `N-2` condition on prime quotients;
- sampled owner declarations of the same kind:
  `IsCompleteLocalRing`,
  `NagataRing`,
  `quotient_isCompleteLocalRing`,
  `IsN2Ring`;
- best owner abstraction: `NagataRing` is the source-facing owner for this item, with complete
  locality and Noetherianity as primitive hypotheses and the prime-quotient `N-2` conditions as
  derived owner data;
- primitive data vs. derived API:
  the primitive inputs are only `[IsCompleteLocalRing R]` and `[IsNoetherianRing R]`,
  while the quotient-by-prime `IsN2Ring` instances belong to the `NagataRing` owner API.

Source/core/bridge triage:
- `source-facing`: the complete-local criterion proving `NagataRing R`;
- `core/canonical`: the owner class `NagataRing` together with its quotient field
  `quotient_isN2Ring`;
- `bridge/view`: the quotient stability theorem `quotient_isCompleteLocalRing`, which supplies the
  canonical complete-local input on each prime quotient.
-/
-- Proof sketch: for each prime ideal `p`, the quotient `R ⧸ p` is again complete local by
-- `quotient_isCompleteLocalRing`, and it is Noetherian by the canonical quotient instance. Hence
-- it remains to show that a
-- Noetherian complete local domain is `N-2`; reduce by the Cohen structure theorem and the finite
-- extension reduction to formal power series rings over a field or a Cohen ring, then apply the
-- power-series and Tate lemmas to reduce to the field case.

/-- Helper for Chap10 Lemma 10 162 8: zero formal variables recover the coefficient ring. -/
private theorem mvPowerSeries_fin_zero_ringEquiv
    (A : Type u) [CommSemiring A] :
    Nonempty (MvPowerSeries (Fin 0) A ≃+* A) := by
  refine ⟨?_⟩
  refine
    { toFun := MvPowerSeries.constantCoeff
      invFun := MvPowerSeries.C
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }
  · -- Coefficientwise equality reduces every `Fin 0` exponent vector to `0`.
    intro f
    ext d
    have hd : d = 0 := Subsingleton.elim _ _
    simp [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · -- Constant coefficient is a left inverse to the constant-series embedding.
    intro r
    simp
  · -- The constant-coefficient map is multiplicative.
    intro f g
    simp
  · -- The constant-coefficient map is additive.
    intro f g
    simp

/-- Helper for Chap10 Lemma 10 162 8: splitting variables indexed by `σ ⊕ τ` identifies
`MvPowerSeries (σ ⊕ τ) A` with `MvPowerSeries σ (MvPowerSeries τ A)`. -/
private theorem mvPowerSeries_sum_ringEquiv
    (A : Type u) [CommSemiring A] (σ τ : Type*) :
    Nonempty (MvPowerSeries (σ ⊕ τ) A ≃+* MvPowerSeries σ (MvPowerSeries τ A)) := by
  refine ⟨?_⟩
  refine
    { toFun := fun f d e ↦ f (sumElim d e)
      invFun := fun f d ↦
        f
          (comapDomain Sum.inl d Sum.inl_injective.injOn)
          (comapDomain Sum.inr d Sum.inr_injective.injOn)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_
      map_add' := ?_ }
  · -- Splitting and recombining a multi-index leaves it unchanged.
    intro f
    funext d
    simp [Finsupp.comapDomain_sumElim_comapDomain]
  · -- Recombining the two split parts recovers both nested coefficient indices.
    intro f
    funext d
    funext e
    simp
  · -- Multiplication is checked by decomposing the antidiagonal sum over split exponents.
    intro f g
    classical
    funext d
    funext e
    let F : MvPowerSeries σ (MvPowerSeries τ A) := fun d e ↦ f (sumElim d e)
    let G : MvPowerSeries σ (MvPowerSeries τ A) := fun d e ↦ g (sumElim d e)
    have h :
        Finset.sum (antidiagonal (sumElim d e))
          (fun p : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) ↦ f p.1 * g p.2) =
        Finset.sum (antidiagonal d)
          (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦
            Finset.sum (antidiagonal e)
              (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦
                f (sumElim p.1 q.1) * g (sumElim p.2 q.2))) := by
      let split : ((σ →₀ ℕ) × (σ →₀ ℕ)) × ((τ →₀ ℕ) × (τ →₀ ℕ)) →
          (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) :=
        fun x ↦ (sumElim x.1.1 x.2.1, sumElim x.1.2 x.2.2)
      let unsplit : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) →
          ((σ →₀ ℕ) × (σ →₀ ℕ)) × ((τ →₀ ℕ) × (τ →₀ ℕ)) :=
        fun x ↦
          (( comapDomain Sum.inl x.1 Sum.inl_injective.injOn
           , comapDomain Sum.inl x.2 Sum.inl_injective.injOn)
          , ( comapDomain Sum.inr x.1 Sum.inr_injective.injOn
            , comapDomain Sum.inr x.2 Sum.inr_injective.injOn))
      have hleft : Function.LeftInverse unsplit split := by
        intro x
        rcases x with ⟨⟨x1, x2⟩, x3, x4⟩
        simp [split, unsplit, Finsupp.comapDomain_inl_sumElim,
          Finsupp.comapDomain_inr_sumElim]
      rw [← Finsupp.image_sumElim_product_antidiagonal]
      rw [Finset.sum_image hleft.injective.injOn]
      rw [Finset.sum_product]
    calc
      (f * g) (sumElim d e)
          = Finset.sum (antidiagonal (sumElim d e))
              (fun p : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) ↦ f p.1 * g p.2) := by
                simpa using MvPowerSeries.coeff_mul (sumElim d e) f g
      _ = Finset.sum (antidiagonal d)
            (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦
              Finset.sum (antidiagonal e)
                (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦
                  f (sumElim p.1 q.1) * g (sumElim p.2 q.2))) := h
      _ = (F * G) d e := by
            calc
              Finset.sum (antidiagonal d)
                  (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦
                    Finset.sum (antidiagonal e)
                      (fun q : (τ →₀ ℕ) × (τ →₀ ℕ) ↦
                        f (sumElim p.1 q.1) * g (sumElim p.2 q.2)))
                  = Finset.sum (antidiagonal d) (fun p ↦ (F p.1 * G p.2) e) := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      simpa [F, G] using MvPowerSeries.coeff_mul e (F p.1) (G p.2)
              _ = (Finset.sum (antidiagonal d) (fun p ↦ F p.1 * G p.2)) e := by
                    exact
                      (Finset.sum_apply e (antidiagonal d) fun p ↦
                        F p.1 * G p.2).symm
              _ = (F * G) d e := by
                    simpa using congrArg (fun s : MvPowerSeries τ A ↦ s e)
                      (MvPowerSeries.coeff_mul d F G)
  · -- Addition is coefficientwise under the split-variable identification.
    intro f g
    rfl

/-- Helper for Chap10 Lemma 10 162 8: the distinguished `Option.none` variable is isolated as a
unit-indexed summand. -/
private noncomputable def mvPowerSeries_optionToUnitSum (σ : Type*) : Option σ ≃ Unit ⊕ σ :=
  (Equiv.optionEquivSumPUnit σ).trans (Equiv.sumComm _ _)

/-- Helper for Chap10 Lemma 10 162 8: one distinguished variable gives a univariate power series
ring over the remaining multivariable power series ring. -/
private theorem optionMvPowerSeries_ringEquiv
    (A : Type u) [CommSemiring A] (σ : Type*) :
    Nonempty (MvPowerSeries (Option σ) A ≃+* PowerSeries (MvPowerSeries σ A)) := by
  -- First split `Option σ` as `Unit ⊕ σ`, then read the unit component as the univariate index.
  rcases mvPowerSeries_sum_ringEquiv A Unit σ with ⟨e⟩
  exact ⟨(MvPowerSeries.renameEquiv A (mvPowerSeries_optionToUnitSum σ)).toRingEquiv.trans e⟩

/-- Helper for Chap10 Lemma 10 162 8: adjoining one `Fin` variable is a univariate
power-series extension of the previous finite-variable ring. -/
private theorem mvPowerSeries_fin_succ_ringEquiv
    (A : Type u) [CommSemiring A] (d : ℕ) :
    Nonempty (MvPowerSeries (Fin (d + 1)) A ≃+* PowerSeries (MvPowerSeries (Fin d) A)) := by
  -- Reindex `Fin (d + 1)` as `Option (Fin d)` and use the distinguished-variable equivalence.
  rcases optionMvPowerSeries_ringEquiv A (Fin d) with ⟨e⟩
  exact ⟨(MvPowerSeries.renameEquiv A (_root_.finSuccEquiv d)).toRingEquiv.trans e⟩

/-- Helper for Chap10 Lemma 10 162 8: finite-variable formal power series over a domain form a
domain. -/
private instance mvPowerSeries_fin_isDomain
    (A : Type u) [CommRing A] [IsDomain A] (d : ℕ) :
    IsDomain (MvPowerSeries (Fin d) A) :=
  NoZeroDivisors.to_isDomain _

/-- Helper for Chap10 Lemma 10 162 8: one-variable formal power series over a domain form a
domain. -/
private instance powerSeries_isDomain
    (A : Type u) [CommRing A] [IsDomain A] :
    IsDomain (PowerSeries A) :=
  NoZeroDivisors.to_isDomain _

/-- Helper for Chap10 Lemma 10 162 8: finite-variable formal power series over a Noetherian
`N-2` domain are again `N-2`. -/
private lemma mvPowerSeries_fin_isN2Ring
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsN2Ring A] (d : ℕ) :
    IsN2Ring (MvPowerSeries (Fin d) A) := by
  induction d with
  | zero =>
      -- The zero-variable case is transported from the coefficient ring.
      rcases mvPowerSeries_fin_zero_ringEquiv A with ⟨e⟩
      exact isN2Ring_of_ringEquiv e.symm
  | succ d ih =>
      -- The successor case is one-variable power-series permanence followed by reindexing.
      rcases mvPowerSeries_fin_succ_ringEquiv A d with ⟨e⟩
      letI : IsN2Ring (MvPowerSeries (Fin d) A) := ih
      letI : IsN2Ring (PowerSeries (MvPowerSeries (Fin d) A)) :=
        isN2Ring_powerSeries (MvPowerSeries (Fin d) A)
      exact isN2Ring_of_ringEquiv e.symm

/-- Helper for Chap10 Lemma 10 162 8: a module-finite algebra is finite type and quasi-finite. -/
private lemma moduleFinite_finiteTypeQuasiFinite
    {A : Type u} {B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] :
    Algebra.FiniteType.QuasiFinite A B := by
  -- A finite algebra map is finite type and quasi-finite in the canonical ring-hom sense.
  letI : Algebra.FiniteType A B := Module.Finite.finiteType B
  have hFinite : (algebraMap A B).Finite := by
    rw [RingHom.finite_algebraMap]
    infer_instance
  have hQuasiFinite : Algebra.QuasiFinite A B := by
    rw [← RingHom.quasiFinite_algebraMap]
    exact RingHom.QuasiFinite.of_finite hFinite
  exact Algebra.FiniteType.QuasiFinite.of_quasiFinite hQuasiFinite

/-- Helper for Chap10 Lemma 10 162 8: a proper quotient of a complete local ring is local. -/
private lemma quotientCompleteLocal_isLocalRing (I : Ideal R) (hI : I ≠ ⊤) :
    IsLocalRing (R ⧸ I) := by
  -- A proper quotient is nontrivial, and locality descends along the quotient map.
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Lemma 10 162 8: the maximal ideal of a local quotient is the image of the
source maximal ideal. -/
private lemma quotientCompleteLocal_maximalIdeal_eq_map (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) := by
  -- Surjectivity of the quotient map identifies the target maximal ideal with the mapped source
  -- maximal ideal.
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Chap10 Lemma 10 162 8: the `maximalIdeal R`-adic completion of `R ⧸ I`, as an
`R`-module, is canonically the quotient itself. -/
private noncomputable def quotientCompleteLocal_completionLinearEquiv (I : Ideal R) :
    AdicCompletion (maximalIdeal R) (R ⧸ I) ≃ₗ[R] R ⧸ I :=
  let eCompletion :
      AdicCompletion (maximalIdeal R) (R ⧸ I) ≃ₗ[R]
        AdicCompletion (maximalIdeal R) R ⊗[R] (R ⧸ I) :=
    (LinearEquiv.restrictScalars R
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) (R ⧸ I))).symm
  let eTensor :
      (R ⧸ I) ≃ₐ[R] AdicCompletion (maximalIdeal R) R ⊗[R] (R ⧸ I) :=
    (Algebra.TensorProduct.lid R (R ⧸ I)).symm.trans
      (Algebra.TensorProduct.congr
        (AdicCompletion.ofAlgEquiv (maximalIdeal R))
        (AlgEquiv.refl : (R ⧸ I) ≃ₐ[R] (R ⧸ I)))
  eCompletion.trans eTensor.symm.toLinearEquiv

/-- Helper for Chap10 Lemma 10 162 8: the quotient-completion equivalence evaluates the
completion class of `x` to `x`. -/
private lemma quotientCompleteLocal_completionLinearEquiv_of (I : Ideal R) (x : R ⧸ I) :
    quotientCompleteLocal_completionLinearEquiv (R := R) I
        (AdicCompletion.of (maximalIdeal R) (R ⧸ I) x) = x := by
  -- Both canonical comparison equivalences send a quotient class to its tensor with `1`, so the
  -- composite evaluates back to the original quotient class.
  simp [quotientCompleteLocal_completionLinearEquiv]

/-- Helper for Chap10 Lemma 10 162 8: a quotient of a complete local ring is complete for the
source maximal-ideal topology. -/
private lemma quotientCompleteLocal_isAdicComplete_maximalIdeal (I : Ideal R) :
    IsAdicComplete (maximalIdeal R) (R ⧸ I) := by
  have hof_eq :
      (AdicCompletion.of (maximalIdeal R) (R ⧸ I) :
          (R ⧸ I) →ₗ[R] AdicCompletion (maximalIdeal R) (R ⧸ I)) =
        (quotientCompleteLocal_completionLinearEquiv (R := R) I).symm.toLinearMap := by
    -- Identify the completion map by applying the quotient-completion equivalence pointwise.
    apply LinearMap.ext
    intro x
    apply (quotientCompleteLocal_completionLinearEquiv (R := R) I).injective
    simp [quotientCompleteLocal_completionLinearEquiv_of]
  -- Once the completion map is the inverse equivalence, it is bijective.
  exact (AdicCompletion.of_bijective_iff).mp <| by
    simpa [hof_eq] using
      (quotientCompleteLocal_completionLinearEquiv (R := R) I).symm.bijective

/-- Helper for Chap10 Lemma 10 162 8: a quotient of a complete local ring is complete for the
image of the source maximal ideal. -/
private lemma quotientCompleteLocal_isAdicComplete_mappedMaximalIdeal
    (I : Ideal R) (_hI : I ≠ ⊤) :
    IsAdicComplete (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) (R ⧸ I) := by
  -- Transport source-maximal-ideal completeness across the quotient algebra map.
  exact
    (IsAdicComplete.map_algebraMap_iff
      (R := R) (S := R ⧸ I) (I := maximalIdeal R) (M := R ⧸ I)).2 <|
      quotientCompleteLocal_isAdicComplete_maximalIdeal (R := R) I

/-- Helper for Chap10 Lemma 10 162 8: a proper quotient of a Noetherian complete local ring is
again a complete local ring. -/
private theorem quotientCompleteLocal_isCompleteLocalRing (I : Ideal R) (hI : I ≠ ⊤) :
    IsCompleteLocalRing (R ⧸ I) := by
  letI : IsLocalRing (R ⧸ I) := quotientCompleteLocal_isLocalRing (R := R) I hI
  have hcomplete : IsAdicComplete (maximalIdeal (R ⧸ I)) (R ⧸ I) := by
    -- Rewrite the quotient maximal ideal as the mapped source maximal ideal and apply the
    -- transported completeness lemma.
    rw [← quotientCompleteLocal_maximalIdeal_eq_map (R := R) I]
    exact quotientCompleteLocal_isAdicComplete_mappedMaximalIdeal (R := R) I hI
  -- Package locality and maximal-ideal adic completeness into the chapter owner.
  exact
    { toIsLocalRing := quotientCompleteLocal_isLocalRing (R := R) I hI
      toIsAdicComplete := hcomplete }

/-- Helper for Chap10 Lemma 10 162 8: a Cohen ring is `N-2`. -/
private lemma cohenRing_isN2Ring
    (Λ : Type u) [CommRing Λ] [IsCohenRing Λ] : IsN2Ring Λ := by
  let x : Λ := ringChar (ResidueField Λ)
  have hdom : IsDomain (Λ ⧸ Ideal.span ({x} : Set Λ)) := by
    -- The Cohen-ring defining quotient is the residue field, hence a domain.
    let e := IsCohenRing.quotientSpanResidueCharRingEquiv (R := Λ)
    exact e.toMulEquiv.isDomain (ResidueField Λ)
  letI : IsDomain (Λ ⧸ Ideal.span ({x} : Set Λ)) := hdom
  have hN2 : IsN2Ring (Λ ⧸ Ideal.span ({x} : Set Λ)) := by
    -- The same quotient identification transports the field `N-2` instance.
    let e := IsCohenRing.quotientSpanResidueCharRingEquiv (R := Λ)
    simpa [x] using isN2Ring_of_ringEquiv e.symm
  letI : IsN2Ring (Λ ⧸ Ideal.span ({x} : Set Λ)) := hN2
  have hcomplete : IsAdicComplete (Ideal.span ({x} : Set Λ)) Λ := by
    -- The generator `x` spans the maximal ideal, so complete-locality is exactly `x`-adic
    -- completeness.
    rw [← IsCohenRing.maximalIdeal_eq_span_residueChar]
    infer_instance
  letI : IsAdicComplete (Ideal.span ({x} : Set Λ)) Λ := hcomplete
  -- Tate's criterion upgrades the principal quotient from `N-2` to the Cohen ring itself.
  exact isN2Ring_of_normal_of_adicComplete_of_principal_quotient_isN2Ring (R := Λ) x

/-- Helper for Chap10 Lemma 10 162 8: a Noetherian complete local domain is `N-2`. -/
private lemma isN2Ring_of_noetherian_completeLocalDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsCompleteLocalRing A] :
    IsN2Ring A := by
  -- Choose the finite regular complete-local subring supplied by the Cohen-structure package.
  rcases exists_finite_regular_completeLocalSubring (R := A) with
    ⟨R₀, hcomplete, hregular, hlocal, hresidue, hfinite, d, hmodel⟩
  letI : IsCompleteLocalRing R₀ := hcomplete
  letI : IsRegularLocalRing R₀ := hregular
  letI : Module.Finite R₀ A := hfinite
  have hR₀N2 : IsN2Ring R₀ := by
    -- The source subring is modeled either over its residue field or over a Cohen ring.
    rcases hmodel with hfield | hcohen
    · rcases hfield with ⟨e⟩
      have hsrc : IsN2Ring (MvPowerSeries (Fin d) (ResidueField R₀)) :=
        mvPowerSeries_fin_isN2Ring (ResidueField R₀) d
      letI : IsN2Ring (MvPowerSeries (Fin d) (ResidueField R₀)) := hsrc
      exact isN2Ring_of_ringEquiv e
    · rcases hcohen with ⟨Λ, hΛRing, hΛCohen, ⟨e⟩⟩
      letI : CommRing Λ := hΛRing
      letI : IsCohenRing Λ := hΛCohen
      have hΛN2 : IsN2Ring Λ := cohenRing_isN2Ring Λ
      letI : IsN2Ring Λ := hΛN2
      have hsrc : IsN2Ring (MvPowerSeries (Fin d) Λ) :=
        mvPowerSeries_fin_isN2Ring Λ d
      letI : IsN2Ring (MvPowerSeries (Fin d) Λ) := hsrc
      exact isN2Ring_of_ringEquiv e
  letI : IsN2Ring R₀ := hR₀N2
  have hqf : Algebra.FiniteType.QuasiFinite R₀ A := moduleFinite_finiteTypeQuasiFinite
  have hinj : Function.Injective (algebraMap R₀ A) := by
    -- The algebra map from a subring is the inclusion, so equality is detected in `A`.
    intro x y hxy
    exact Subtype.ext hxy
  -- Quasi-finite permanence carries `N-2` from the finite source subring to `A`.
  exact isN2Ring_of_quasiFinite_extension (R := R₀) (S := A) hqf hinj

/-- Chap10 Lemma 10 162 8: a Noetherian complete local ring is a Nagata ring. -/
@[stacks 032W]
instance nagataRing_of_noetherian_completeLocalRing : NagataRing R := by
  -- A Nagata ring is Noetherian and has `N-2` prime quotients; Noetherianity is already an
  -- ambient instance, so it remains to prove the quotient condition.
  refine NagataRing.mk ?_
  intro p hp
  letI : p.IsPrime := hp
  letI : IsCompleteLocalRing (R ⧸ p) := quotientCompleteLocal_isCompleteLocalRing (R := R) p hp.ne_top
  -- Prime quotients are domains, and the complete-local domain helper supplies `N-2`.
  exact isN2Ring_of_noetherian_completeLocalDomain (R ⧸ p)

end

end

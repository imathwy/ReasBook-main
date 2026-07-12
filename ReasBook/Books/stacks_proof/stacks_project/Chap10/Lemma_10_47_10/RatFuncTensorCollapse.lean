import Mathlib
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Definition_10_47_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped RatFunc TensorProduct
open Algebra.TensorProduct

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

attribute [local instance] Polynomial.algebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.47.10: the one-variable polynomial ring over `K` is the tensor product
`K ⊗[k] k[X]`. -/
noncomputable def one_variable_polynomial_tensor_ringEquiv :
    K ⊗[k] Polynomial k ≃+* Polynomial K :=
  let e₁ : K ⊗[k] Polynomial k ≃ₐ[k] K ⊗[k] MvPolynomial PUnit.{1} k :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K ≃ₐ[k] K)
      (MvPolynomial.pUnitAlgEquiv.{u, 0} k).symm).restrictScalars k
  let e₂ : K ⊗[k] MvPolynomial PUnit.{1} k ≃ₐ[k] MvPolynomial PUnit.{1} K :=
    (MvPolynomial.algebraTensorAlgEquiv (σ := PUnit.{1}) k K).restrictScalars k
  let e₃ : MvPolynomial PUnit.{1} K ≃ₐ[k] Polynomial K :=
    (MvPolynomial.pUnitAlgEquiv.{u, 0} K).restrictScalars k
  ((e₁.trans e₂).trans e₃).toRingEquiv

/-- Helper for Lemma 10.47.10: iterated base change along `R → R'` rewrites
`(K ⊗[R] R') ⊗[R'] B` as `K ⊗[R] B`. -/
noncomputable def tensor_base_change_assoc_ringEquiv
    {R R' K' B : Type u} [CommRing R] [Field R'] [CommRing K'] [CommRing B]
    [Algebra R R'] [Algebra R K'] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B] :
    let _ : Algebra R' (K' ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    (K' ⊗[R] R') ⊗[R'] B ≃+* K' ⊗[R] B :=
  -- Proof comment: follow the standard `comm + commRight + cancelBaseChange + comm` route, so
  -- the duplicated base `R'` is canceled before returning to the source tensor order.
  let _ : Algebra R' (K' ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  (((Algebra.TensorProduct.comm R' (K' ⊗[R] R') B).trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : B ≃ₐ[R'] B)
        ((Algebra.TensorProduct.commRight R R' K').symm))).trans
      (Algebra.TensorProduct.cancelBaseChange R R' R' B K')).toRingEquiv.trans
    (Algebra.TensorProduct.comm R B K').toRingEquiv

/-- Helper for Lemma 10.47.10: the canonical map from `k(X)` to the fraction ring of `k[X]`
fits into the expected scalar tower over `k[X]`. -/
theorem ratFunc_base_fractionRing_isScalarTower :
    letI : Algebra k⟮X⟯ (FractionRing (Polynomial k)) :=
      ((RatFunc.toFractionRingAlgEquiv k (Polynomial k)).toAlgHom).toAlgebra
    IsScalarTower (Polynomial k) k⟮X⟯ (FractionRing (Polynomial k)) := by
  let e : k⟮X⟯ ≃ₐ[Polynomial k] FractionRing (Polynomial k) :=
    RatFunc.toFractionRingAlgEquiv k (Polynomial k)
  letI : Algebra k⟮X⟯ (FractionRing (Polynomial k)) := e.toAlgHom.toAlgebra
  -- Proof comment: the transported `k(X)`-algebra is chosen so that its structure map is exactly
  -- the rational-function-to-fraction-ring comparison, so the tower identity is exactly the
  -- `comp_algebraMap` compatibility of that algebra equivalence.
  exact IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm

/-- Helper for Lemma 10.47.10: nonzero polynomials from `k[X]` become units in `K(X)`. -/
theorem ratFunc_polynomial_denominators_are_units :
    Algebra.algebraMapSubmonoid K⟮X⟯ (nonZeroDivisors (Polynomial k)) ≤
      IsUnit.submonoid K⟮X⟯ := by
  rintro _ ⟨q, hq, rfl⟩
  -- Proof comment: `K(X)` is a field, so it suffices to check that the image of a nonzero
  -- denominator does not vanish.
  change IsUnit ((algebraMap (Polynomial k) K⟮X⟯) q)
  rw [isUnit_iff_ne_zero]
  intro hq_zero
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hq)
    ((FaithfulSMul.algebraMap_injective (Polynomial k) K⟮X⟯) (by simpa using hq_zero))

/-- Helper for Lemma 10.47.10: after tensoring the localization `K[X] → K(X)` with a
`k[X]`-algebra `Ω`, the same denominator set still presents the tensor product as a localization.
-/
theorem ratFunc_tensor_over_polynomial_isLocalization
    {Ω : Type u} [Field Ω] [Algebra (Polynomial k) Ω] :
    letI : Algebra Ω (Polynomial K ⊗[Polynomial k] Ω) :=
      Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := Polynomial K) (B := Ω)
    letI : Algebra Ω (K⟮X⟯ ⊗[Polynomial k] Ω) :=
      Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := K⟮X⟯) (B := Ω)
    let tensorQS : Algebra (Polynomial K ⊗[Polynomial k] Ω) (K⟮X⟯ ⊗[Polynomial k] Ω) :=
      (tensor_right_map (R := Polynomial k) (S := K⟮X⟯) (Q := Polynomial K) (T := Ω)).toAlgebra
    letI : Algebra (Polynomial K ⊗[Polynomial k] Ω) (K⟮X⟯ ⊗[Polynomial k] Ω) := tensorQS
    IsLocalization
      (Algebra.algebraMapSubmonoid (Polynomial K ⊗[Polynomial k] Ω)
        (nonZeroDivisors (Polynomial K)))
      (K⟮X⟯ ⊗[Polynomial k] Ω) := by
  let rightQ : Algebra Ω (Polynomial K ⊗[Polynomial k] Ω) :=
    Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := Polynomial K) (B := Ω)
  letI : Algebra Ω (Polynomial K ⊗[Polynomial k] Ω) := rightQ
  let rightS : Algebra Ω (K⟮X⟯ ⊗[Polynomial k] Ω) :=
    Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := K⟮X⟯) (B := Ω)
  letI : Algebra Ω (K⟮X⟯ ⊗[Polynomial k] Ω) := rightS
  let leftQ : Algebra (Polynomial K) (Polynomial K ⊗[Polynomial k] Ω) :=
    Algebra.TensorProduct.leftAlgebra (R := Polynomial k) (A := Polynomial K) (B := Ω)
  let leftS : Algebra (Polynomial K) (K⟮X⟯ ⊗[Polynomial k] Ω) :=
    Algebra.TensorProduct.leftAlgebra (R := Polynomial k) (A := K⟮X⟯) (B := Ω)
  let tensorQS : Algebra (Polynomial K ⊗[Polynomial k] Ω) (K⟮X⟯ ⊗[Polynomial k] Ω) :=
    (tensor_right_map (R := Polynomial k) (S := K⟮X⟯) (Q := Polynomial K) (T := Ω)).toAlgebra
  letI : Algebra (Polynomial K ⊗[Polynomial k] Ω) (K⟮X⟯ ⊗[Polynomial k] Ω) := tensorQS
  have hQtower :
      (algebraMap (Polynomial K ⊗[Polynomial k] Ω) (K⟮X⟯ ⊗[Polynomial k] Ω)).comp
          (algebraMap (Polynomial K) (Polynomial K ⊗[Polynomial k] Ω)) =
        algebraMap (Polynomial K) (K⟮X⟯ ⊗[Polynomial k] Ω) := by
    letI : Algebra (Polynomial K) (Polynomial K ⊗[Polynomial k] Ω) := leftQ
    letI : Algebra (Polynomial K) (K⟮X⟯ ⊗[Polynomial k] Ω) := leftS
    -- Proof comment: this is the compatibility statement built into `tensor_right_map`.
    exact tensor_right_map_q_tower
      (R := Polynomial k) (S := K⟮X⟯) (Q := Polynomial K) (T := Ω)
  let hQtowerInst :=
    @IsScalarTower.of_algebraMap_eq' (Polynomial K) (Polynomial K ⊗[Polynomial k] Ω)
      (K⟮X⟯ ⊗[Polynomial k] Ω) inferInstance inferInstance inferInstance leftQ tensorQS leftS
      hQtower
  have hcompat :
      (algebraMap (Polynomial K ⊗[Polynomial k] Ω) (K⟮X⟯ ⊗[Polynomial k] Ω)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    -- Proof comment: the tensor-right localization theorem also needs the right inclusion to be
    -- fixed by the induced algebra map.
    exact tensor_right_map_includeRight_comp
      (R := Polynomial k) (S := K⟮X⟯) (Q := Polynomial K) (T := Ω)
  -- Proof comment: now apply the chapter-local tensor-right localization bridge verbatim.
  exact
    @isLocalization_tensor_right_of_isLocalization (Polynomial k) K⟮X⟯ inferInstance
      inferInstance inferInstance (Polynomial K) inferInstance inferInstance inferInstance
      inferInstance (nonZeroDivisors (Polynomial K)) Ω inferInstance inferInstance rightQ rightS
      tensorQS hQtowerInst inferInstance hcompat

/-- Helper for Lemma 10.47.10: `k(X)` is the literal localization of `k[X]` at the nonzero
polynomials. -/
noncomputable def ratFunc_to_polynomial_localization_algEquiv :
    let M := nonZeroDivisors (Polynomial k)
    let L := Localization M
    k⟮X⟯ ≃ₐ[Polynomial k] L := by
  let M := nonZeroDivisors (Polynomial k)
  let L := Localization M
  let eFrac : k⟮X⟯ ≃ₐ[Polynomial k] FractionRing (Polynomial k) :=
    RatFunc.toFractionRingAlgEquiv k (Polynomial k)
  let eLoc : L ≃ₐ[Polynomial k] FractionRing (Polynomial k) :=
    Localization.algEquiv M (FractionRing (Polynomial k))
  -- Proof comment: both sides are the same localization owner of `k[X]`, so we compare them
  -- through the common fraction-ring model and keep the result at the polynomial base.
  exact eFrac.trans eLoc.symm

/-- Helper for Lemma 10.47.10: localizing the right tensor factor from `k[X]` to `k(X)` rewrites
`K(X) ⊗[k[X]] k(X)` as `K(X)`. -/
noncomputable def ratFunc_tensor_ratFuncBase_ringEquiv :
    K⟮X⟯ ⊗[Polynomial k] k⟮X⟯ ≃+* K⟮X⟯ := by
  let M := nonZeroDivisors (Polynomial k)
  let L := Localization M
  let eBase : k⟮X⟯ ≃ₐ[Polynomial k] L :=
    ratFunc_to_polynomial_localization_algEquiv (k := k)
  let eRewrite : K⟮X⟯ ⊗[Polynomial k] k⟮X⟯ ≃+* K⟮X⟯ ⊗[Polynomial k] L :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K⟮X⟯ ≃ₐ[K⟮X⟯] K⟮X⟯)
      eBase).toRingEquiv
  letI : Algebra K⟮X⟯ (L ⊗[Polynomial k] K⟮X⟯) := Algebra.TensorProduct.rightAlgebra
  let eSwap : K⟮X⟯ ⊗[Polynomial k] L ≃+* L ⊗[Polynomial k] K⟮X⟯ :=
    (Algebra.TensorProduct.commRight (Polynomial k) K⟮X⟯ L).toRingEquiv
  let eLocalize : L ⊗[Polynomial k] K⟮X⟯ ≃+*
      Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) :=
    (Localization.tensorRightAlgEquiv M K⟮X⟯).toRingEquiv
  letI : IsLocalization (Algebra.algebraMapSubmonoid K⟮X⟯ M) K⟮X⟯ :=
    IsLocalization.self (ratFunc_polynomial_denominators_are_units (k := k) (K := K))
  let eCollapseAlg : Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) ≃ₐ[K⟮X⟯] K⟮X⟯ :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid K⟮X⟯ M)
      (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) K⟮X⟯
  let eCollapse : Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) ≃+* K⟮X⟯ :=
    eCollapseAlg.toRingEquiv
  -- Proof comment: this follows the source route exactly: rewrite the right factor to the literal
  -- `k[X]`-localization owner, swap tensor factors, use the tensor-right localization theorem, and
  -- finally collapse the self-localization of `K(X)` because the polynomial denominators are units.
  exact eRewrite.trans <| eSwap.trans <| eLocalize.trans eCollapse

/-- Helper for Lemma 10.47.10: the localization-owner map appearing in the collapse
`K(X) ⊗[k[X]] k(X) -> K(X)` is exactly the canonical map obtained from the fixed
identification `k(X) ≃ Localization (nonZeroDivisors (Polynomial k))`. -/
theorem ratFunc_localization_owner_map_eq :
    let M := nonZeroDivisors (Polynomial k)
    let L := Localization M
    let eBase : k⟮X⟯ ≃ₐ[Polynomial k] L :=
      ratFunc_to_polynomial_localization_algEquiv (k := k)
    letI : IsLocalization (Algebra.algebraMapSubmonoid K⟮X⟯ M) K⟮X⟯ :=
      IsLocalization.self (ratFunc_polynomial_denominators_are_units (k := k) (K := K))
    let eCollapse : Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) ≃ₐ[K⟮X⟯] K⟮X⟯ :=
      IsLocalization.algEquiv (Algebra.algebraMapSubmonoid K⟮X⟯ M)
        (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) K⟮X⟯
    (eCollapse.toRingHom).comp
        (algebraMap L (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M))) =
      (algebraMap k⟮X⟯ K⟮X⟯).comp eBase.symm.toRingHom := by
  let M := nonZeroDivisors (Polynomial k)
  let L := Localization M
  let eBase : k⟮X⟯ ≃ₐ[Polynomial k] L :=
    ratFunc_to_polynomial_localization_algEquiv (k := k)
  letI : IsLocalization (Algebra.algebraMapSubmonoid K⟮X⟯ M) K⟮X⟯ :=
    IsLocalization.self (ratFunc_polynomial_denominators_are_units (k := k) (K := K))
  let eCollapse : Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) ≃ₐ[K⟮X⟯] K⟮X⟯ :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid K⟮X⟯ M)
      (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) K⟮X⟯
  -- Proof comment: both maps leave `k[X]` unchanged, so localization extensionality reduces the
  -- comparison to the image of a polynomial before we collapse the self-localization.
  apply IsLocalization.ringHom_ext M
  refine RingHom.ext fun q => ?_
  calc
    eCollapse (algebraMap L (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M))
        (algebraMap (Polynomial k) L q)) =
      eCollapse (algebraMap (Polynomial k)
        (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) q) := by
          rw [← IsScalarTower.algebraMap_apply (Polynomial k) L
            (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) q]
    _ = algebraMap (Polynomial k) K⟮X⟯ q := by
      have hcollapse :
          eCollapse
              (algebraMap K⟮X⟯ (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M))
                ((algebraMap (Polynomial k) K⟮X⟯) q)) =
            algebraMap (Polynomial k) K⟮X⟯ q := by
        simpa using eCollapse.commutes ((algebraMap (Polynomial k) K⟮X⟯) q)
      change eCollapse
          (algebraMap K⟮X⟯ (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M))
            ((algebraMap (Polynomial k) K⟮X⟯) q)) =
        algebraMap (Polynomial k) K⟮X⟯ q
      exact hcollapse
    _ = ((algebraMap k⟮X⟯ K⟮X⟯).comp eBase.symm.toRingHom)
        (algebraMap (Polynomial k) L q) := by
      -- Proof comment: compare the fixed polynomial image in `k(X)` via `eBase.symm`, then map it
      -- forward to `K(X)` using the canonical inclusion of rational function fields.
      rw [RingHom.comp_apply]
      have hbase :
          algebraMap k⟮X⟯ K⟮X⟯ (eBase.symm ((algebraMap (Polynomial k) L) q)) =
            algebraMap (Polynomial k) K⟮X⟯ q := by
        rw [eBase.symm.commutes q]
        exact (IsScalarTower.algebraMap_apply (Polynomial k) k⟮X⟯ K⟮X⟯ q).symm
      exact hbase.symm

/-- Helper for Lemma 10.47.10: the collapse `K(X) ⊗[k[X]] k(X) ≃ K(X)` respects the right
`k(X)`-scalar action. -/
theorem ratFunc_tensor_ratFuncBase_ringEquiv_commutes (x : k⟮X⟯) :
    letI : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := Algebra.TensorProduct.rightAlgebra
    ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K)
      (algebraMap k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) x) =
        algebraMap k⟮X⟯ K⟮X⟯ x := by
  let M := nonZeroDivisors (Polynomial k)
  let L := Localization M
  let eBase : k⟮X⟯ ≃ₐ[Polynomial k] L :=
    ratFunc_to_polynomial_localization_algEquiv (k := k)
  let eRewrite : K⟮X⟯ ⊗[Polynomial k] k⟮X⟯ ≃+* K⟮X⟯ ⊗[Polynomial k] L :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K⟮X⟯ ≃ₐ[K⟮X⟯] K⟮X⟯)
      eBase).toRingEquiv
  letI : Algebra K⟮X⟯ (L ⊗[Polynomial k] K⟮X⟯) := Algebra.TensorProduct.rightAlgebra
  let eSwap : K⟮X⟯ ⊗[Polynomial k] L ≃+* L ⊗[Polynomial k] K⟮X⟯ :=
    (Algebra.TensorProduct.commRight (Polynomial k) K⟮X⟯ L).toRingEquiv
  let eLocalize : L ⊗[Polynomial k] K⟮X⟯ ≃+*
      Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) :=
    (Localization.tensorRightAlgEquiv M K⟮X⟯).toRingEquiv
  letI : IsLocalization (Algebra.algebraMapSubmonoid K⟮X⟯ M) K⟮X⟯ :=
    IsLocalization.self (ratFunc_polynomial_denominators_are_units (k := k) (K := K))
  let eCollapse : Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) ≃+* K⟮X⟯ :=
    (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid K⟮X⟯ M)
      (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) K⟮X⟯).toRingEquiv
  -- Route correction: rewrite the source scalar as the right pure tensor `1 ⊗ₜ x`, transport it
  -- through the staged comparison, and finish with the already-proved localization-owner formula.
  have hEquiv :
      ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K) =
        (eRewrite.trans <| eSwap.trans <| eLocalize.trans eCollapse) := by
    rfl
  rw [hEquiv]
  rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
  calc
    (eRewrite.trans <| eSwap.trans <| eLocalize.trans eCollapse)
        ((Algebra.TensorProduct.includeRight (R := Polynomial k) (A := K⟮X⟯) (B := k⟮X⟯)) x) =
        eCollapse (eLocalize (eSwap (eRewrite (1 ⊗ₜ[Polynomial k] x)))) := by
          simp [Algebra.TensorProduct.includeRight_apply]
    _ =
        eCollapse (eLocalize (eSwap (1 ⊗ₜ[Polynomial k] eBase x))) := by
          simp [eRewrite]
    _ = eCollapse (eLocalize (eBase x ⊗ₜ[Polynomial k] (1 : K⟮X⟯))) := by
          simp [eSwap]
    _ = eCollapse
          (algebraMap L (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) (eBase x)) := by
          -- Proof comment: the localization stage sends `eBase x ⊗ₜ 1` to the canonical image of
          -- `eBase x` in the localized owner.
          simpa [eLocalize, L] using
            congrArg eCollapse <|
              Localization.tensorRightAlgEquiv_apply_tmul_one
                (M := M) (S := K⟮X⟯) (x := eBase x)
    _ = algebraMap k⟮X⟯ K⟮X⟯ x := by
          -- Proof comment: the final collapse is exactly the fixed owner-map comparison.
          have hOwner :=
            congrArg (fun f => f (eBase x))
              (ratFunc_localization_owner_map_eq (k := k) (K := K))
          calc
            eCollapse ((algebraMap L (Localization (algebraMapSubmonoid K⟮X⟯ M))) (eBase x)) =
                algebraMap k⟮X⟯ K⟮X⟯ (eBase.symm (eBase x)) := by
                  change
                    ((eCollapse.toRingHom.comp
                        (algebraMap L (Localization (algebraMapSubmonoid K⟮X⟯ M))))
                      (eBase x)) =
                    (((algebraMap k⟮X⟯ K⟮X⟯).comp eBase.symm.toRingHom) (eBase x))
                  simpa [RingHom.comp_apply] using hOwner
            _ = algebraMap k⟮X⟯ K⟮X⟯ x := by
                  rw [eBase.symm_apply_apply]

/-- Helper for Lemma 10.47.10: the ring-level collapse of `K(X) ⊗[k[X]] k(X)` is already
`k(X)`-linear. -/
noncomputable def ratFunc_tensor_ratFuncBase_algEquiv :
    let _ : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := Algebra.TensorProduct.rightAlgebra
    K⟮X⟯ ⊗[Polynomial k] k⟮X⟯ ≃ₐ[k⟮X⟯] K⟮X⟯ :=
  let _ : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := Algebra.TensorProduct.rightAlgebra
  AlgEquiv.ofRingEquiv (f := ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K))
    (ratFunc_tensor_ratFuncBase_ringEquiv_commutes (k := k) (K := K))

/-- Helper for Lemma 10.47.10: if two `R`-algebra structures on the same ring agree, then the
corresponding tensor products over `R` are canonically the same ring. -/
noncomputable def tensor_ringEquiv_of_algebra_eq
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R B]
    (alg₁ alg₂ : Algebra R A) (halg : alg₁ = alg₂) :
    (letI := alg₁; A ⊗[R] B) ≃+* (letI := alg₂; A ⊗[R] B) := by
  subst halg
  exact RingEquiv.refl _

/-- Helper for Lemma 10.47.10: the collapse `K(X) ⊗[k[X]] k(X) ≃ K(X)` also respects the
default left `k(X)`-algebra structure on the tensor product. -/
theorem ratFunc_tensor_ratFuncBase_ringEquiv_commutes_left (x : k⟮X⟯) :
    ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K)
      (algebraMap k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) x) =
        algebraMap k⟮X⟯ K⟮X⟯ x := by
  let M := nonZeroDivisors (Polynomial k)
  let L := Localization M
  let eBase : k⟮X⟯ ≃ₐ[Polynomial k] L :=
    ratFunc_to_polynomial_localization_algEquiv (k := k)
  let eRewrite : K⟮X⟯ ⊗[Polynomial k] k⟮X⟯ ≃+* K⟮X⟯ ⊗[Polynomial k] L :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : K⟮X⟯ ≃ₐ[K⟮X⟯] K⟮X⟯)
      eBase).toRingEquiv
  letI : Algebra K⟮X⟯ (L ⊗[Polynomial k] K⟮X⟯) := Algebra.TensorProduct.rightAlgebra
  let eSwap : K⟮X⟯ ⊗[Polynomial k] L ≃+* L ⊗[Polynomial k] K⟮X⟯ :=
    (Algebra.TensorProduct.commRight (Polynomial k) K⟮X⟯ L).toRingEquiv
  let eLocalize : L ⊗[Polynomial k] K⟮X⟯ ≃+*
      Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) :=
    (Localization.tensorRightAlgEquiv M K⟮X⟯).toRingEquiv
  letI : IsLocalization (Algebra.algebraMapSubmonoid K⟮X⟯ M) K⟮X⟯ :=
    IsLocalization.self (ratFunc_polynomial_denominators_are_units (k := k) (K := K))
  let eCollapse : Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M) ≃+* K⟮X⟯ :=
    (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid K⟮X⟯ M)
      (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) K⟮X⟯).toRingEquiv
  have hEquiv :
      ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K) =
        (eRewrite.trans <| eSwap.trans <| eLocalize.trans eCollapse) := by
    rfl
  rw [hEquiv]
  rw [Algebra.TensorProduct.algebraMap_apply]
  calc
    (eRewrite.trans <| eSwap.trans <| eLocalize.trans eCollapse)
        (((algebraMap k⟮X⟯ K⟮X⟯) x) ⊗ₜ[Polynomial k] (1 : k⟮X⟯)) =
        eCollapse (eLocalize (eSwap (eRewrite
          (((algebraMap k⟮X⟯ K⟮X⟯) x) ⊗ₜ[Polynomial k] (1 : k⟮X⟯))))) := by
          rfl
    _ =
        eCollapse (eLocalize (eSwap
          (((algebraMap k⟮X⟯ K⟮X⟯) x) ⊗ₜ[Polynomial k] (1 : L)))) := by
          simp [eRewrite]
    _ = eCollapse (eLocalize ((1 : L) ⊗ₜ[Polynomial k] (algebraMap k⟮X⟯ K⟮X⟯ x))) := by
          simp [eSwap]
    _ = eCollapse
          (algebraMap K⟮X⟯ (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M))
            (algebraMap k⟮X⟯ K⟮X⟯ x)) := by
          exact congrArg eCollapse <|
            (Localization.tensorRightAlgEquiv_apply_one_tmul
              (M := M) (S := K⟮X⟯) (x := algebraMap k⟮X⟯ K⟮X⟯ x))
    _ = algebraMap k⟮X⟯ K⟮X⟯ x := by
          change
            (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid K⟮X⟯ M)
              (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) K⟮X⟯)
              (algebraMap K⟮X⟯ (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M))
                (algebraMap k⟮X⟯ K⟮X⟯ x)) =
              algebraMap k⟮X⟯ K⟮X⟯ x
          simpa using
            (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid K⟮X⟯ M)
              (Localization (Algebra.algebraMapSubmonoid K⟮X⟯ M)) K⟮X⟯).commutes
                (algebraMap k⟮X⟯ K⟮X⟯ x)

/-- Helper for Lemma 10.47.10: the default left and explicit right `k(X)`-algebra structures on
`K(X) ⊗[k[X]] k(X)` coincide after collapsing the tensor product to `K(X)`. -/
theorem ratFunc_tensor_self_algebra_eq :
    (inferInstance : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯)) =
      Algebra.TensorProduct.rightAlgebra := by
  let algLeft : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := inferInstance
  let algRight : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := Algebra.TensorProduct.rightAlgebra
  apply Algebra.algebra_ext
  intro x
  change @algebraMap k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) _ _ algLeft x =
    @algebraMap k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) _ _ algRight x
  apply (ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K)).injective
  calc
    ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K)
        (@algebraMap k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) _ _ algLeft x) =
      algebraMap k⟮X⟯ K⟮X⟯ x := by
        simpa [algLeft] using
          ratFunc_tensor_ratFuncBase_ringEquiv_commutes_left (k := k) (K := K) x
    _ =
      ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K)
        (@algebraMap k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) _ _ algRight x) := by
        symm
        letI : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := algRight
        simpa [algRight] using
          ratFunc_tensor_ratFuncBase_ringEquiv_commutes (k := k) (K := K) x

/-- Helper for Lemma 10.47.10: on `K(X) ⊗[k[X]] k(X)`, the right `k(X)`-algebra structure is the
canonical right tensor inclusion. -/
theorem ratFunc_tensor_self_rightAlgebra_eq_includeRight :
    letI : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := Algebra.TensorProduct.rightAlgebra
    algebraMap k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) =
      Algebra.TensorProduct.includeRight.toRingHom := by
  letI : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := Algebra.TensorProduct.rightAlgebra
  -- Proof comment: for the right tensor algebra, the structure map is definitionally the right
  -- inclusion `x ↦ 1 ⊗ₜ x`.
  simpa using
    (Algebra.TensorProduct.algebraMap_eq_includeRight
      (R := Polynomial k) (A := K⟮X⟯) (B := k⟮X⟯))
end

end Algebra

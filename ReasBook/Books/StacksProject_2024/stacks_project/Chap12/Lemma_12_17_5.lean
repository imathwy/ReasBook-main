import Mathlib
import StacksProject_2024.stacks_project.Chap12.Example_12_17_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GradedObject
open CategoryTheory.GradedObject.Monoidal
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory

variable {F : Type u} [Field F]

/-
Source/core/bridge triage for Lemma 12.17.5:
- source-facing statement: a left-dualizable graded `F`-vector space has finite total dimension,
  and the evaluation map induces nondegenerate degreewise pairings
- core/canonical owner: `ExactPairing W V` for a chosen left dual `W` of `V`, together with the
  signed graded braiding `GradedObject.Monoidal.koszulBraiding` from Example 12.17.4 and the
  canonical support owner `GradedObject.finrankSupport`
- bridge/view: the degreewise bilinear pairing obtained by restricting the owner evaluation map to
  the summand of total degree `0` and transporting it to the `W^{-n} ⊗ V^n` order used by the
  textbook pairing through the Koszul-signed braiding
-/

/-- A graded `F`-vector space has finite total dimension if only finitely many graded pieces are
nonzero and each graded piece is finite dimensional. We record this using the canonical graded
support `GradedObject.finrankSupport`. -/
abbrev hasFiniteTotalDimension (V : GradedObject ℤ (ModuleCat F)) : Prop :=
  Set.Finite (GradedObject.finrankSupport V) ∧ ∀ n : ℤ, FiniteDimensional F (V n)

/-- For a finite-dimensional graded piece of a graded `F`-vector space, belonging to the
canonical finite-rank support is equivalent to being nonzero. -/
private theorem mem_finrankSupport_iff_not_isZero
    (V : GradedObject ℤ (ModuleCat F)) (n : ℤ) [FiniteDimensional F (V n)] :
    n ∈ GradedObject.finrankSupport V ↔ ¬ IsZero (V n) := by
  have hzero : Module.finrank F (V n) = 0 ↔ IsZero (V n) := by
    rw [Module.finrank_eq_zero_iff_of_free F (V n), ModuleCat.isZero_iff_subsingleton]
  rw [GradedObject.finrankSupport, Function.mem_support]
  exact not_congr hzero

private theorem finrankSupport_eq_nonzero_degrees
    (V : GradedObject ℤ (ModuleCat F)) (hfd : ∀ n : ℤ, FiniteDimensional F (V n)) :
    GradedObject.finrankSupport V = {n : ℤ | ¬ IsZero (V n)} := by
  ext n
  letI := hfd n
  simpa using mem_finrankSupport_iff_not_isZero V n

/-- Textbook reformulation of `hasFiniteTotalDimension`: only finitely many graded pieces are
nonzero, and every graded piece is finite dimensional. -/
theorem hasFiniteTotalDimension_iff
    (V : GradedObject ℤ (ModuleCat F)) :
    hasFiniteTotalDimension V ↔
      Set.Finite {n : ℤ | ¬ IsZero (V n)} ∧ ∀ n : ℤ, FiniteDimensional F (V n) := by
  constructor
  · rintro ⟨hfin, hfd⟩
    rw [finrankSupport_eq_nonzero_degrees V hfd] at hfin
    exact ⟨hfin, hfd⟩
  · rintro ⟨hfin, hfd⟩
    exact ⟨(finrankSupport_eq_nonzero_degrees V hfd).symm ▸ hfin, hfd⟩

variable {V W : GradedObject ℤ (ModuleCat F)} [ExactPairing W V]

/-- Helper for Lemma 12.17.5: the tensor summand indexed by `(p, q)` in a graded tensor product. -/
omit [ExactPairing W V] in
private abbrev tensorSummand
    (V W : GradedObject ℤ (ModuleCat F)) (p q : ℤ) : ModuleCat F :=
  V p ⊗ W q

/-- Helper for Lemma 12.17.5: postcomposing a descended graded tensor map can be checked on each
`(p, q)` summand. -/
@[reassoc]
omit [ExactPairing W V] in
private theorem iTensorObj_tensorObjDesc_assoc
    {A B : ModuleCat F} {n : ℤ}
    (f : ∀ p q (h : p + q = n), tensorSummand V W p q ⟶ A)
    (u : A ⟶ B) (p q : ℤ) (h : p + q = n) :
    ιTensorObj V W p q n h ≫ tensorObjDesc f ≫ u = f p q h ≫ u := by
  -- Evaluate the descended tensor map on the chosen summand before postcomposing.
  simpa using congrArg (fun t ↦ t ≫ u) (ι_tensorObjDesc (f := f) p q h)

/-- Helper for Lemma 12.17.5: projection from the degree-`0` tensor term onto the diagonal
summand `(n, -n)`. -/
omit [ExactPairing W V] in
private noncomputable def degreewiseTensorProjection
    (V W : GradedObject ℤ (ModuleCat F)) (n : ℤ) :
    (V ⊗ W) 0 ⟶ tensorSummand V W n (-n) :=
  tensorObjDesc fun p q _ ↦
    if hp : p = n then
      if hq : q = -n then
        show tensorSummand V W p q ⟶ tensorSummand V W n (-n) from
          eqToHom (by subst p; subst q; rfl)
      else
        show tensorSummand V W p q ⟶ tensorSummand V W n (-n) from
          0
    else
      show tensorSummand V W p q ⟶ tensorSummand V W n (-n) from
        0

/-- Helper for Lemma 12.17.5: the degreewise projection is the identity on the diagonal summand
`(n, -n)`. -/
@[reassoc]
omit [ExactPairing W V] in
private theorem degreewiseTensorProjection_diag
    (V W : GradedObject ℤ (ModuleCat F)) (n : ℤ) :
    ιTensorObj V W n (-n) 0 (add_neg_cancel n) ≫ degreewiseTensorProjection V W n =
      𝟙 (tensorSummand V W n (-n)) := by
  -- On the chosen diagonal branch, the descended projection keeps exactly that summand.
  simpa using
    (iTensorObj_tensorObjDesc_assoc
      (V := V) (W := W)
      (f := fun p q _ ↦
        if hp : p = n then
          if hq : q = -n then
            show tensorSummand V W p q ⟶ tensorSummand V W n (-n) from
              eqToHom (by subst p; subst q; rfl)
          else
            show tensorSummand V W p q ⟶ tensorSummand V W n (-n) from
              0
        else
          show tensorSummand V W p q ⟶ tensorSummand V W n (-n) from
            0)
      (u := 𝟙 _)
      (p := n) (q := -n) (h := add_neg_cancel n))

/-- Helper for Lemma 12.17.5: away from the diagonal summand `(n, -n)`, the degreewise projection
vanishes. -/
@[reassoc]
omit [ExactPairing W V] in
private theorem degreewiseTensorProjection_off_diagonal
    (V W : GradedObject ℤ (ModuleCat F)) (n p q : ℤ) (h : p + q = 0)
    (hdiag : p ≠ n ∨ q ≠ -n) :
    ιTensorObj V W p q 0 h ≫ degreewiseTensorProjection V W n = 0 := by
  -- Once the summand is not the diagonal one, the relevant branch of the defining family is zero.
  rcases hdiag with hp | hq
  · simpa [degreewiseTensorProjection, hp] using
      (iTensorObj_tensorObjDesc_assoc
        (V := V) (W := W)
        (f := fun p' q' _ ↦
          if hp' : p' = n then
            if hq' : q' = -n then
              show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
                eqToHom (by subst p'; subst q'; rfl)
            else
              show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
                0
          else
            show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
              0)
        (u := 𝟙 _)
        (p := p) (q := q) (h := h))
  · by_cases hp : p = n
    · subst hp
      simpa [degreewiseTensorProjection, hq] using
        (iTensorObj_tensorObjDesc_assoc
          (V := V) (W := W)
          (f := fun p' q' _ ↦
            if hp' : p' = n then
              if hq' : q' = -n then
                show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
                  eqToHom (by subst p'; subst q'; rfl)
              else
                show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
                  0
            else
              show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
                0)
          (u := 𝟙 _)
          (p := n) (q := q) (h := by simpa using h))
    · simpa [degreewiseTensorProjection, hp] using
        (iTensorObj_tensorObjDesc_assoc
          (V := V) (W := W)
          (f := fun p' q' _ ↦
            if hp' : p' = n then
              if hq' : q' = -n then
                show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
                  eqToHom (by subst p'; subst q'; rfl)
              else
                show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
                  0
            else
              show tensorSummand V W p' q' ⟶ tensorSummand V W n (-n) from
                0)
          (u := 𝟙 _)
          (p := p) (q := q) (h := h))

/-- Helper for Lemma 12.17.5: the diagonal coevaluation component extracted from the global
coevaluation of the chosen exact pairing. -/
private noncomputable def degreewiseCoevaluationHom
    (V W : GradedObject ℤ (ModuleCat F)) [ExactPairing W V] (n : ℤ) :
    𝟙_ (ModuleCat F) ⟶ tensorSummand W V (-n) (-(-n)) :=
  tensorUnit₀.inv ≫ (η_ W V) 0 ≫ degreewiseTensorProjection W V (-n)

/-- Helper for Lemma 12.17.5: the unbraided degreewise evaluation map in the exact-pairing order
`V^n ⊗ W^{-n} → F`. -/
private abbrev degreewiseRawEvaluationHom
    (V W : GradedObject ℤ (ModuleCat F)) [ExactPairing W V] (n : ℤ) :
    V n ⊗ W (-n) ⟶ 𝟙_ (ModuleCat F) :=
  ιTensorObj V W n (-n) 0 (by simpa [add_comm] using add_neg_cancel n) ≫
    ε_ W V 0 ≫ tensorUnit₀.hom

/-- The degree-`0` component of the exact-pairing evaluation, restricted to the `(-n,n)` tensor
summand and written in textbook order via the Koszul-signed braiding from Example 12.17.4. -/
private abbrev degreewiseEvaluationHom
    (V W : GradedObject ℤ (ModuleCat F)) [ExactPairing W V] (n : ℤ) :
    W (-n) ⊗ V n ⟶ 𝟙_ (ModuleCat F) :=
  ιTensorObj W V (-n) n 0 (neg_add_cancel n) ≫ (koszulBraiding W V).hom 0 ≫
    ε_ W V 0 ≫ tensorUnit₀.hom

/-- The degreewise bilinear pairing induced from the evaluation of a chosen left dual `W` of `V`,
written in the textbook order `W^{-n} × V^n → F`. -/
noncomputable abbrev degreewiseEvaluation
    (V W : GradedObject ℤ (ModuleCat F)) [ExactPairing W V] (n : ℤ) :
    W (-n) →ₗ[F] V n →ₗ[F] F :=
  TensorProduct.curry (degreewiseEvaluationHom V W n).hom

/-- Helper for Lemma 12.17.5: over a field, an exact pairing `N ⊣ M` produces a finite
generating family of `M` from the coevaluation element `η(1)`, so `M` is finite dimensional. -/
private theorem module_exactPairing_target_finiteDimensional
    {M N : Type u} [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [ExactPairing (ModuleCat.of F N) (ModuleCat.of F M)] :
    FiniteDimensional F M := by
  -- Expand the controlling coevaluation element `η(1)` as a finite sum of pure tensors.
  let z : N ⊗[F] M := (η_ (ModuleCat.of F N) (ModuleCat.of F M)) 1
  obtain ⟨k, n, m, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  have hz' :
      (η_ (ModuleCat.of F N) (ModuleCat.of F M)) 1 = ∑ j, n j ⊗ₜ[F] m j := by
    simpa [z] using hz
  -- The coefficient map records evaluation against the finitely many dual vectors `n j`.
  let i : M →ₗ[F] (Fin k → F) :=
    { toFun := fun x j =>
        (ε_ (ModuleCat.of F N) (ModuleCat.of F M)) (x ⊗ₜ[F] n j)
      map_add' := by
        intro x y
        ext j
        simp [TensorProduct.add_tmul]
      map_smul' := by
        intro a x
        ext j
        rw [← TensorProduct.smul_tmul', map_smul]
        rfl }
  -- The synthesis map rebuilds a vector from the finitely many homogeneous generators `m j`.
  let s : (Fin k → F) →ₗ[F] M :=
    { toFun := fun a => ∑ j, a j • m j
      map_add' := by
        intro a b
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro a b
        simp [Finset.smul_sum, mul_smul] }
  have hs_surj : Function.Surjective s := by
    intro x
    refine ⟨i x, ?_⟩
    -- Evaluate the `M`-triangle identity on `x`; after rewriting by `hz`, this becomes
    -- `s (i x) = x`.
    have htriangle :
        (ρ_ (ModuleCat.of F M)).inv ≫
            (ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M) ≫
              (α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv ≫
                ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M) ≫
          (λ_ (ModuleCat.of F M)).hom =
        𝟙 (ModuleCat.of F M) := by
      calc
        (ρ_ (ModuleCat.of F M)).inv ≫
            (ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M) ≫
              (α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv ≫
                ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M) ≫
            (λ_ (ModuleCat.of F M)).hom =
          (ρ_ (ModuleCat.of F M)).inv ≫
              ((ρ_ (ModuleCat.of F M)).hom ≫ (λ_ (ModuleCat.of F M)).inv) ≫
                (λ_ (ModuleCat.of F M)).hom := by
            rw [ExactPairing.coevaluation_evaluation]
        _ = 𝟙 (ModuleCat.of F M) := by
            simp [Category.assoc]
    have htriangle_apply := congrArg (fun f => f x) htriangle
    change
      ((λ_ (ModuleCat.of F M)).hom)
          (((ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M)
            (((α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv)
              (((ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M))
                (((ρ_ (ModuleCat.of F M)).inv) x)))))) =
        x at htriangle_apply
    have hcomposite :
        ((λ_ (ModuleCat.of F M)).hom)
            (((ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M)
              (((α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv)
                (((ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M))
                  (((ρ_ (ModuleCat.of F M)).inv) x)))))) =
          ∑ j, (ε_ (ModuleCat.of F N) (ModuleCat.of F M)) (x ⊗ₜ[F] n j) • m j := by
      have hsum :
          (Finset.univ.sum fun j : Fin k =>
            (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm (x ⊗ₜ[F] (n j ⊗ₜ[F] m j))))) =
            (Finset.univ.sum fun j : Fin k =>
              (ε_ (ModuleCat.of F N) (ModuleCat.of F M)) (x ⊗ₜ[F] n j) • m j) :=
        Finset.sum_congr rfl fun j _ => by simp
      have hsumExpr :
          (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  (x ⊗ₜ[F] ∑ j : Fin k, n j ⊗ₜ[F] m j))) =
            (∑ j : Fin k,
              (TensorProduct.lid F M)
                ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                  ((TensorProduct.assoc F M N M).symm
                    (x ⊗ₜ[F] (n j ⊗ₜ[F] m j))))) := by
        simp only [TensorProduct.tmul_sum, map_sum]
      have h0 :
          ((λ_ (ModuleCat.of F M)).hom)
              (((ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M)
                (((α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv)
                  (((ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M))
                    (((ρ_ (ModuleCat.of F M)).inv) x)))))) =
            (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  ((LinearMap.lTensor M (η_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                    (x ⊗ₜ[F] 1)))) := by
        simp only [ModuleCat.hom_hom_leftUnitor, ModuleCat.hom_inv_rightUnitor,
          ModuleCat.hom_inv_associator, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
          LinearEquiv.coe_coe, TensorProduct.rid_symm_apply]
      have h1 :
          (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  ((LinearMap.lTensor M (η_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                    (x ⊗ₜ[F] 1)))) =
            (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  (x ⊗ₜ[F] (η_ (ModuleCat.of F N) (ModuleCat.of F M)) 1))) := by
        simpa using
          congrArg
            (fun t =>
              (TensorProduct.lid F M)
                ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                  ((TensorProduct.assoc F M N M).symm t)))
            (LinearMap.lTensor_tmul
              (f := (η_ (ModuleCat.of F N) (ModuleCat.of F M)).hom) (M := M) x (1 : F))
      have h2 :
          (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  (x ⊗ₜ[F] (η_ (ModuleCat.of F N) (ModuleCat.of F M)) 1))) =
            (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  (x ⊗ₜ[F] ∑ j : Fin k, n j ⊗ₜ[F] m j))) := by
        rw [hz']
      exact h0.trans (h1.trans (h2.trans (hsumExpr.trans hsum)))
    simpa [i, s, LinearMap.comp_apply, LinearMap.id_apply] using
      hcomposite.symm.trans htriangle_apply
  exact FiniteDimensional.of_surjective s hs_surj

/-- Helper for Lemma 12.17.5: the module-level evaluation coming from an exact pairing is
left-separating. -/
private theorem module_exactPairing_evaluation_separatingLeft
    {M N : Type u} [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [ExactPairing (ModuleCat.of F N) (ModuleCat.of F M)] :
    (((TensorProduct.curry (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom) :
        M →ₗ[F] N →ₗ[F] F)).SeparatingLeft := by
  let z : N ⊗[F] M := (η_ (ModuleCat.of F N) (ModuleCat.of F M)) 1
  obtain ⟨k, n, m, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  have hz' :
      (η_ (ModuleCat.of F N) (ModuleCat.of F M)) 1 = ∑ j, n j ⊗ₜ[F] m j := by
    simpa [z] using hz
  let B : M →ₗ[F] N →ₗ[F] F :=
    TensorProduct.curry (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom
  let s : (N →ₗ[F] F) →ₗ[F] M :=
    { toFun := fun a => ∑ j, a (n j) • m j
      map_add' := by
        intro a b
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro a b
        simp [Finset.smul_sum, mul_smul] }
  have hs_leftInverse : s.comp B = LinearMap.id := by
    ext x
    -- Evaluate the `M`-triangle identity on `x` and rewrite it through the chosen finite
    -- expansion of `η(1)`.
    have htriangle :
        (ρ_ (ModuleCat.of F M)).inv ≫
            (ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M) ≫
              (α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv ≫
                ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M) ≫
          (λ_ (ModuleCat.of F M)).hom =
        𝟙 (ModuleCat.of F M) := by
      calc
        (ρ_ (ModuleCat.of F M)).inv ≫
            (ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M) ≫
              (α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv ≫
                ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M) ≫
            (λ_ (ModuleCat.of F M)).hom =
          (ρ_ (ModuleCat.of F M)).inv ≫
              ((ρ_ (ModuleCat.of F M)).hom ≫ (λ_ (ModuleCat.of F M)).inv) ≫
                (λ_ (ModuleCat.of F M)).hom := by
            rw [ExactPairing.coevaluation_evaluation]
        _ = 𝟙 (ModuleCat.of F M) := by
            simp [Category.assoc]
    have htriangle_apply := congrArg (fun f => f x) htriangle
    change
      ((λ_ (ModuleCat.of F M)).hom)
          (((ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M)
            (((α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv)
              (((ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M))
                (((ρ_ (ModuleCat.of F M)).inv) x)))))) =
        x at htriangle_apply
    have hcomposite :
        ((λ_ (ModuleCat.of F M)).hom)
            (((ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M)
              (((α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv)
                (((ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M))
                  (((ρ_ (ModuleCat.of F M)).inv) x)))))) =
          ∑ j, (ε_ (ModuleCat.of F N) (ModuleCat.of F M)) (x ⊗ₜ[F] n j) • m j := by
      have hsum :
          (Finset.univ.sum fun j : Fin k =>
            (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm (x ⊗ₜ[F] (n j ⊗ₜ[F] m j))))) =
            (Finset.univ.sum fun j : Fin k =>
              (ε_ (ModuleCat.of F N) (ModuleCat.of F M)) (x ⊗ₜ[F] n j) • m j) :=
        Finset.sum_congr rfl fun j _ => by simp
      have hsumExpr :
          (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  (x ⊗ₜ[F] ∑ j : Fin k, n j ⊗ₜ[F] m j))) =
            (∑ j : Fin k,
              (TensorProduct.lid F M)
                ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                  ((TensorProduct.assoc F M N M).symm
                    (x ⊗ₜ[F] (n j ⊗ₜ[F] m j))))) := by
        simp only [TensorProduct.tmul_sum, map_sum]
      have h0 :
          ((λ_ (ModuleCat.of F M)).hom)
              (((ε_ (ModuleCat.of F N) (ModuleCat.of F M) ▷ ModuleCat.of F M)
                (((α_ (ModuleCat.of F M) (ModuleCat.of F N) (ModuleCat.of F M)).inv)
                  (((ModuleCat.of F M ◁ η_ (ModuleCat.of F N) (ModuleCat.of F M))
                    (((ρ_ (ModuleCat.of F M)).inv) x)))))) =
            (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  ((LinearMap.lTensor M (η_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                    (x ⊗ₜ[F] 1)))) := by
        simp only [ModuleCat.hom_hom_leftUnitor, ModuleCat.hom_inv_rightUnitor,
          ModuleCat.hom_inv_associator, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
          LinearEquiv.coe_coe, TensorProduct.rid_symm_apply]
      have h1 :
          (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  ((LinearMap.lTensor M (η_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                    (x ⊗ₜ[F] 1)))) =
            (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  (x ⊗ₜ[F] (η_ (ModuleCat.of F N) (ModuleCat.of F M)) 1))) := by
        simpa using
          congrArg
            (fun t =>
              (TensorProduct.lid F M)
                ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                  ((TensorProduct.assoc F M N M).symm t)))
            (LinearMap.lTensor_tmul
              (f := (η_ (ModuleCat.of F N) (ModuleCat.of F M)).hom) (M := M) x (1 : F))
      have h2 :
          (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  (x ⊗ₜ[F] (η_ (ModuleCat.of F N) (ModuleCat.of F M)) 1))) =
            (TensorProduct.lid F M)
              ((LinearMap.rTensor M (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom)
                ((TensorProduct.assoc F M N M).symm
                  (x ⊗ₜ[F] ∑ j : Fin k, n j ⊗ₜ[F] m j))) := by
        rw [hz']
      exact h0.trans (h1.trans (h2.trans (hsumExpr.trans hsum)))
    simpa [B, s, LinearMap.comp_apply, TensorProduct.curry_apply, LinearMap.id_apply] using
      hcomposite.symm.trans htriangle_apply
  intro x hx
  -- Apply the explicit left inverse to the vanished functional `B x`.
  have hx' : B x = 0 := by
    ext y
    exact hx y
  have hxEval := congrArg (fun f : M →ₗ[F] M => f x) hs_leftInverse
  simpa [hx', B] using hxEval

/-- Helper for Lemma 12.17.5: the module-level evaluation coming from an exact pairing is
nondegenerate. -/
private theorem module_exactPairing_evaluation_nondegenerate
    {M N : Type u} [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [ExactPairing (ModuleCat.of F N) (ModuleCat.of F M)] :
    (((TensorProduct.curry (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom) :
        M →ₗ[F] N →ₗ[F] F)).Nondegenerate := by
  let B : M →ₗ[F] N →ₗ[F] F :=
    TensorProduct.curry (ε_ (ModuleCat.of F N) (ModuleCat.of F M)).hom
  have hleft : B.SeparatingLeft :=
    module_exactPairing_evaluation_separatingLeft (F := F) (M := M) (N := N)
  have hflipLeft : B.flip.SeparatingLeft := by
    -- Route correction: obtain right-separation by swapping the exact pairing and identifying
    -- the swapped module evaluation with the flipped original bilinear map.
    letI : ExactPairing (ModuleCat.of F M) (ModuleCat.of F N) :=
      BraidedCategory.exactPairing_swap (ModuleCat.of F N) (ModuleCat.of F M)
    simpa [B, TensorProduct.curry_apply, LinearMap.flip_apply] using
      (module_exactPairing_evaluation_separatingLeft (F := F) (M := N) (N := M))
  have hright : B.SeparatingRight := by
    exact (LinearMap.flip_separatingLeft (B := B)).mp hflipLeft
  exact ⟨hleft, hright⟩

/-- Helper for Lemma 12.17.5: projecting the first global triangle identity to degree `n`
produces the degreewise triangle identity for `V n` and `W (-n)` in the raw exact-pairing order.
-/
private theorem degreewise_coevaluation_evaluation_projection
    (n : ℤ) :
    (V n : ModuleCat F) ◁ degreewiseCoevaluationHom V W n ≫
        (α_ (V n : ModuleCat F) (W (-n) : ModuleCat F) (V n : ModuleCat F)).inv ≫
        degreewiseRawEvaluationHom V W n ▷ (V n : ModuleCat F) =
      (ρ_ (V n : ModuleCat F)).hom ≫
        (λ_ (V n : ModuleCat F)).inv := by
  -- First isolate the degree-`n` component of the global triangle identity.
  have htriangle :
      (V ◁ η_ W V ≫ (α_ V W V).inv ≫ ε_ W V ▷ V) n =
        ((ρ_ V).hom ≫ (λ_ V).inv) n := by
    simpa using congrArg (fun f ↦ f n) (ExactPairing.coevaluation_evaluation (X := W) (Y := V))
  -- Then expand the degree-`n` component in terms of the diagonal summand maps.
  simpa [degreewiseCoevaluationHom, degreewiseRawEvaluationHom, Category.assoc] using htriangle

/-- Helper for Lemma 12.17.5: projecting the second global triangle identity to degree `n`
produces the degreewise triangle identity for `V n` and `W (-n)` in the raw exact-pairing order.
-/
private theorem degreewise_evaluation_coevaluation_projection
    (n : ℤ) :
    degreewiseCoevaluationHom V W n ▷ (W (-n) : ModuleCat F) ≫
        (α_ (W (-n) : ModuleCat F) (V n : ModuleCat F) (W (-n) : ModuleCat F)).hom ≫
        (W (-n) : ModuleCat F) ◁ degreewiseRawEvaluationHom V W n =
      (λ_ (W (-n) : ModuleCat F)).hom ≫
        (ρ_ (W (-n) : ModuleCat F)).inv := by
  -- First isolate the degree-`(-n)` component of the symmetric global triangle identity.
  have htriangle :
      ((η_ W V) ▷ W ≫ (α_ W V W).hom ≫ W ◁ ε_ W V) (-n) =
        ((λ_ W).hom ≫ (ρ_ W).inv) (-n) := by
    simpa using congrArg (fun f ↦ f (-n)) (ExactPairing.evaluation_coevaluation (X := W) (Y := V))
  -- Then rewrite the displayed component as the diagonal degreewise composite.
  simpa [degreewiseCoevaluationHom, degreewiseRawEvaluationHom, Category.assoc] using htriangle

/-- Helper for Lemma 12.17.5: the restricted degreewise coevaluation and raw evaluation assemble
to an exact pairing between `V n` and `W (-n)`.
-/
@[implicit_reducible]
private noncomputable def degreewise_exactPairing
    (n : ℤ) : ExactPairing (W (-n) : ModuleCat F) (V n : ModuleCat F) where
  coevaluation' := degreewiseCoevaluationHom V W n
  evaluation' := degreewiseRawEvaluationHom V W n
  coevaluation_evaluation' := by
    -- The first triangle identity is the projected global triangle identity.
    simpa using degreewise_coevaluation_evaluation_projection (V := V) (W := W) n
  evaluation_coevaluation' := by
    -- The second triangle identity is the symmetric projected global triangle identity.
    simpa using degreewise_evaluation_coevaluation_projection (V := V) (W := W) n

/-- Helper for Lemma 12.17.5: if the diagonal coevaluation component in degree `n` vanishes, then
both degreewise terms in degree `n` and `-n` are zero objects.
-/
private theorem degreewise_coevaluation_zero_implies_terms_zero
    (n : ℤ) (hcoevaluation : degreewiseCoevaluationHom V W n = 0) :
    IsZero (V n : ModuleCat F) ∧ IsZero (W (-n) : ModuleCat F) := by
  -- Substitute the vanishing coevaluation into the two projected triangle identities.
  have hVInv :
      (ρ_ (V n : ModuleCat F)).inv = 0 := by
    simpa [hcoevaluation, Category.assoc] using
      (degreewise_coevaluation_evaluation_projection (V := V) (W := W) n).symm
  have hWInv :
      (λ_ (W (-n) : ModuleCat F)).inv = 0 := by
    simpa [hcoevaluation, Category.assoc] using
      (degreewise_evaluation_coevaluation_projection (V := V) (W := W) n).symm
  have hVId :
      𝟙 (V n : ModuleCat F) = 0 := by
    calc
      𝟙 (V n : ModuleCat F) =
          (ρ_ (V n : ModuleCat F)).inv ≫ (ρ_ (V n : ModuleCat F)).hom := by simp
      _ = 0 := by simp [hVInv]
  have hWId :
      𝟙 (W (-n) : ModuleCat F) = 0 := by
    calc
      𝟙 (W (-n) : ModuleCat F) =
          (λ_ (W (-n) : ModuleCat F)).inv ≫ (λ_ (W (-n) : ModuleCat F)).hom := by simp
      _ = 0 := by simp [hWInv]
  exact
    ⟨(CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2 hVId,
      (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2 hWId⟩

/-- Helper for Lemma 12.17.5: the indexing type of total-degree-zero tensor summands in
`(V ⊗ W) 0`. -/
omit [ExactPairing W V] in
private abbrev degreeZeroTensorIndex :
    Type u :=
  (fun ij : ℤ × ℤ => ij.1 + ij.2) ⁻¹' ({0} : Set ℤ)

/-- Helper for Lemma 12.17.5: the family of total-degree-zero tensor summands in `(V ⊗ W) 0`. -/
omit [ExactPairing W V] in
private abbrev degreeZeroTensorSummands
    (V W : GradedObject ℤ (ModuleCat F)) :
    degreeZeroTensorIndex → ModuleCat F :=
  ((((mapBifunctor (curriedTensor (ModuleCat F)) ℤ ℤ).obj V).obj W).mapObjFun
    (fun ij : ℤ × ℤ => ij.1 + ij.2) 0)

/-- Helper for Lemma 12.17.5: the diagonal index `(n, -n)` in the direct-sum model of
`(V ⊗ W) 0`. -/
omit [ExactPairing W V] in
private abbrev diagonalTensorIndex
    (n : ℤ) : degreeZeroTensorIndex :=
  ⟨(n, -n), by simp [degreeZeroTensorIndex]⟩

/-- Helper for Lemma 12.17.5: the degree-`0` tensor piece is the coproduct/direct-sum of its
homogeneous summands. -/
omit [ExactPairing W V] in
private noncomputable abbrev degreeZeroTensorIsoDirectSum
    (V W : GradedObject ℤ (ModuleCat F)) :
    (V ⊗ W) 0 ≅ ModuleCat.of F (⨁ s : degreeZeroTensorIndex, degreeZeroTensorSummands V W s) :=
  ModuleCat.coprodIsoDirectSum (degreeZeroTensorSummands V W)

/-- Helper for Lemma 12.17.5: under the direct-sum model of `(V ⊗ W) 0`, the summand inclusion
`ιTensorObj V W p q 0 h` becomes the corresponding `DirectSum.lof`. -/
@[reassoc]
omit [ExactPairing W V] in
private theorem ιTensorObj_degreeZeroTensorIsoDirectSum_hom
    (V W : GradedObject ℤ (ModuleCat F)) (p q : ℤ) (h : p + q = 0) :
    ιTensorObj V W p q 0 h ≫ (degreeZeroTensorIsoDirectSum V W).hom =
      ModuleCat.ofHom
        (DirectSum.lof F degreeZeroTensorIndex (degreeZeroTensorSummands V W)
          ⟨(p, q), by simpa [degreeZeroTensorIndex] using h⟩) := by
  -- Compare the graded summand injection with the canonical coproduct injection, then transport
  -- across the standard `ModuleCat` coproduct/direct-sum identification.
  simpa [degreeZeroTensorIsoDirectSum, degreeZeroTensorSummands, degreeZeroTensorIndex,
    tensorObj, ιTensorObj, mapBifunctorMapObj, ιMapBifunctorMapObj, GradedObject.mapObj,
    GradedObject.ιMapObj] using
    (ModuleCat.ι_coprodIsoDirectSum_hom
      (R := F) (Z := degreeZeroTensorSummands V W)
      ⟨(p, q), by simpa [degreeZeroTensorIndex] using h⟩)

/-- Helper for Lemma 12.17.5: under the direct-sum model of `(V ⊗ W) 0`, the projector to the
`(n, -n)` tensor summand is the corresponding `DirectSum.component`. -/
omit [ExactPairing W V] in
private theorem degreewiseTensorProjection_eq_directSum_component
    (V W : GradedObject ℤ (ModuleCat F)) (n : ℤ) :
    degreewiseTensorProjection V W n =
      (degreeZeroTensorIsoDirectSum V W).hom ≫
        ModuleCat.ofHom
          (DirectSum.component F degreeZeroTensorIndex (degreeZeroTensorSummands V W)
            (diagonalTensorIndex n)) := by
  -- Route correction: identify the graded coproduct with a concrete direct sum once, then the
  -- intended diagonal projector is literally the corresponding coordinate projection.
  apply tensorObj_ext
  intro p q h
  by_cases hdiag : p = n ∧ q = -n
  · rcases hdiag with ⟨hp, hq⟩
    subst hp
    subst hq
    rw [degreewiseTensorProjection_diag]
    rw [Category.assoc, ιTensorObj_degreeZeroTensorIsoDirectSum_hom]
    simp [diagonalTensorIndex, degreeZeroTensorIndex]
  · have hneq : (⟨(p, q), by simpa [degreeZeroTensorIndex] using h⟩ : degreeZeroTensorIndex) ≠
        diagonalTensorIndex n := by
      intro hs
      apply hdiag
      have hpair : (p, q) = (n, -n) := congrArg Subtype.val hs
      exact Prod.mk.inj_iff.mp hpair
    have hoff : p ≠ n ∨ q ≠ -n := by
      by_cases hp : p = n
      · right
        intro hq
        exact hdiag ⟨hp, hq⟩
      · exact Or.inl hp
    rw [degreewiseTensorProjection_off_diagonal (V := V) (W := W) (n := n) (p := p) (q := q)
      (h := h) hoff]
    rw [Category.assoc, ιTensorObj_degreeZeroTensorIsoDirectSum_hom]
    ext x
    simpa [diagonalTensorIndex, hneq] using
      (DirectSum.component.of F degreeZeroTensorIndex (degreeZeroTensorSummands V W)
        (diagonalTensorIndex n)
        ⟨(p, q), by simpa [degreeZeroTensorIndex] using h⟩ x)

/-- Helper for Lemma 12.17.5: every element of the degree-`0` tensor piece has only finitely many
nonzero diagonal components. -/
private theorem finite_diagonal_projection_support
    (z : (W ⊗ V) 0) :
    Set.Finite {n : ℤ | degreewiseTensorProjection W V (-n) z ≠ 0} := by
  classical
  let z' : ⨁ s : degreeZeroTensorIndex, degreeZeroTensorSummands W V s :=
    (degreeZeroTensorIsoDirectSum W V).hom z
  let T : Finset ℤ := (DFinsupp.support z').image fun s : degreeZeroTensorIndex => s.1.2
  refine T.finite_toSet.subset ?_
  intro n hn
  have hcomponent :
      DirectSum.component F degreeZeroTensorIndex (degreeZeroTensorSummands W V)
          (diagonalTensorIndex (-n)) z' ≠ 0 := by
    -- Transport the diagonal projector across the coproduct/direct-sum identification and then
    -- evaluate it on `z`.
    rw [← degreewiseTensorProjection_eq_directSum_component (V := W) (W := V) (n := -n)] at hn
    simpa [z'] using hn
  have hsupport :
      diagonalTensorIndex (-n) ∈ DFinsupp.support z' := by
    exact DFinsupp.mem_support_toFun.mpr (by
      simpa [DirectSum.apply_eq_component] using hcomponent)
  refine Finset.mem_image.mpr ?_
  exact ⟨diagonalTensorIndex (-n), hsupport, by simp [diagonalTensorIndex]⟩

/-- Helper for Lemma 12.17.5: a nonzero degreewise coevaluation morphism gives a nonzero
diagonal component of the degree-`0` coevaluation element `η(1)`. -/
private theorem diagonal_component_nonzero_of_degreewiseCoevaluationHom_ne_zero
    (n : ℤ) (hcoevaluation : degreewiseCoevaluationHom V W n ≠ 0) :
    degreewiseTensorProjection W V (-n) ((tensorUnit₀.inv ≫ (η_ W V) 0) (1 : F)) ≠ 0 := by
  -- Keep the source object `η(1)` fixed: for a linear map out of `F`, vanishing on `1` forces
  -- vanishing everywhere by linearity.
  intro hdiag
  apply hcoevaluation
  ext a
  calc
    degreewiseCoevaluationHom V W n a = a • degreewiseCoevaluationHom V W n 1 := by
      simpa using (degreewiseCoevaluationHom V W n).map_smul a (1 : F)
    _ = 0 := by simp [degreewiseCoevaluationHom, hdiag]

/-- Helper for Lemma 12.17.5: each graded piece `V^n` is finite dimensional because the
projected exact-pairing data gives `W^{-n}` as a left dual of `V^n`. -/
private theorem finiteDimensional_degreewise_term
    (n : ℤ) :
    FiniteDimensional F (V n) := by
  -- Specialize the module-level left-dual argument to the degreewise exact pairing.
  letI := degreewise_exactPairing (V := V) (W := W) n
  exact module_exactPairing_target_finiteDimensional (F := F) (M := V n) (N := W (-n))

/-- Helper for Lemma 12.17.5: each graded piece `W^{-n}` is finite dimensional by swapping the
degreewise exact pairing in the braided monoidal category of `F`-vector spaces. -/
private theorem finiteDimensional_degreewise_leftDual_term
    (n : ℤ) :
    FiniteDimensional F (W (-n)) := by
  -- Swap the degreewise exact pairing and reuse the same module-level finite-dimensionality step.
  letI : ExactPairing (V n : ModuleCat F) (W (-n) : ModuleCat F) :=
    BraidedCategory.exactPairing_swap (W (-n) : ModuleCat F) (V n : ModuleCat F)
  exact module_exactPairing_target_finiteDimensional (F := F) (M := W (-n)) (N := V n)

/-- Helper for Lemma 12.17.5: a nonzero degree `n` piece of `V` forces the diagonal coevaluation
component in degree `n` to be nonzero. -/
private theorem nonzero_degreewise_term_implies_coevaluation_nonzero
    (n : ℤ) (hV : ¬ IsZero (V n : ModuleCat F)) :
    degreewiseCoevaluationHom V W n ≠ 0 := by
  -- Contrapositively, a vanishing diagonal coevaluation kills both degreewise terms.
  intro hcoevaluation
  exact hV (degreewise_coevaluation_zero_implies_terms_zero (V := V) (W := W) n hcoevaluation).1

/-- Helper for Lemma 12.17.5: the diagonal degreewise coevaluation components are nonzero in only
finitely many degrees. -/
private theorem finite_degreewise_coevaluation_support :
    Set.Finite {n : ℤ | degreewiseCoevaluationHom V W n ≠ 0} := by
  let z : (W ⊗ V) 0 := (tensorUnit₀.inv ≫ (η_ W V) 0) (1 : F)
  -- The source proof controls the finite support of the concrete coevaluation element `η(1)`.
  refine (finite_diagonal_projection_support (V := V) (W := W) z).subset ?_
  intro n hn
  exact diagonal_component_nonzero_of_degreewiseCoevaluationHom_ne_zero (V := V) (W := W) n hn

/-- Helper for Lemma 12.17.5: the textbook evaluation in degree `n` is the Koszul-signed swap of
the raw degreewise evaluation coming from the exact-pairing order. -/
private theorem degreewiseEvaluationHom_eq_signed_swap_raw
    (n : ℤ) :
    degreewiseEvaluationHom V W n =
      koszulBraidingComponent W V (-n) n ≫ degreewiseRawEvaluationHom V W n := by
  -- Restrict the graded Koszul braiding to the diagonal `(-n, n)` summand before refolding the
  -- remaining composite as the raw evaluation map.
  unfold degreewiseEvaluationHom degreewiseRawEvaluationHom
  rw [Category.assoc]
  rw [koszulBraiding_hom_app W V (-n) n 0 (neg_add_cancel n)]
  simpa [Category.assoc]

/-- Helper for Lemma 12.17.5: the raw degreewise evaluation attached to the projected exact
pairing is nondegenerate. -/
private theorem degreewise_rawEvaluation_nondegenerate
    (n : ℤ) :
    (((TensorProduct.curry (degreewiseRawEvaluationHom V W n).hom) :
        V n →ₗ[F] W (-n) →ₗ[F] F)).Nondegenerate := by
  -- Specialize the module-level exact-pairing nondegeneracy to the fixed degree `n`.
  letI := degreewise_exactPairing (V := V) (W := W) n
  simpa using
    (module_exactPairing_evaluation_nondegenerate (F := F) (M := V n) (N := W (-n)))

/-- Helper for Lemma 12.17.5: after currying, the textbook pairing is the Koszul sign times the
flip of the raw degreewise evaluation. -/
private theorem degreewiseEvaluation_eq_signed_flip_raw
    (n : ℤ) :
    degreewiseEvaluation V W n =
      (((((-n) * n).negOnePow : F)) •
        (((TensorProduct.curry (degreewiseRawEvaluationHom V W n).hom) :
          V n →ₗ[F] W (-n) →ₗ[F] F).flip)) := by
  -- Evaluate both bilinear maps on pure tensors and reduce the braiding to the signed swap.
  ext w v
  rw [degreewiseEvaluationHom_eq_signed_swap_raw (V := V) (W := W) n]
  simp [degreewiseEvaluation, GradedObject.Monoidal.koszulBraidingComponent,
    TensorProduct.curry_apply, LinearMap.flip_apply, Category.assoc]

/-- Helper for Lemma 12.17.5: the textbook degreewise pairing `W^{-n} × V^n → F` is
nondegenerate. -/
private theorem degreewiseEvaluation_nondegenerate
    (n : ℤ) :
    (degreewiseEvaluation V W n).Nondegenerate := by
  let raw : V n →ₗ[F] W (-n) →ₗ[F] F :=
    TensorProduct.curry (degreewiseRawEvaluationHom V W n).hom
  let sign : F := (((-n) * n).negOnePow : F)
  have hsign : sign ≠ 0 := by
    rcases Int.even_or_odd ((-n) * n) with hEven | hOdd
    · rw [show sign = ((((-n) * n).negOnePow : F)) by rfl, Int.negOnePow_even _ hEven]
      norm_num
    · rw [show sign = ((((-n) * n).negOnePow : F)) by rfl, Int.negOnePow_odd _ hOdd]
      norm_num
  have hraw : raw.Nondegenerate :=
    degreewise_rawEvaluation_nondegenerate (V := V) (W := W) n
  have hrawFlip : raw.flip.Nondegenerate := by
    exact (LinearMap.flip_nondegenerate (B := raw)).2 hraw
  have hscaled : (sign • raw.flip).Nondegenerate := by
    constructor
    · intro w hw
      refine hrawFlip.1 w ?_
      intro v
      have hwv : sign • raw.flip w v = 0 := by
        simpa [LinearMap.smul_apply] using hw v
      exact (smul_eq_zero.mp hwv).resolve_left hsign
    · intro v hv
      refine hrawFlip.2 v ?_
      intro w
      have hvw : sign • raw.flip w v = 0 := by
        simpa [LinearMap.smul_apply] using hv w
      exact (smul_eq_zero.mp hvw).resolve_left hsign
  -- Replace the textbook pairing by the signed flip computed on pure tensors.
  simpa [raw, sign, degreewiseEvaluation_eq_signed_flip_raw (V := V) (W := W) n] using hscaled

/-- Lemma 12.17.5: if `V` in the monoidal category of graded `F`-vector spaces has left dual
`W`, then `V` has finite total dimension and the evaluation morphism induces nondegenerate
pairings `W^{-n} × V^n → F` in every degree. -/
-- Proof sketch: write the coevaluation of the exact pairing as a finite sum of homogeneous pure
-- tensors. The triangle identities force the finitely many homogeneous vectors appearing there to
-- generate both graded objects, which gives finite dimensionality of each graded piece and leaves
-- only finitely many nonzero degrees. The same identities identify the degreewise evaluation maps
-- with dual-basis pairings, hence each resulting bilinear map is nondegenerate.
theorem leftDual_hasFiniteTotalDimension_and_nondegenerate_degreewiseEvaluation
    :
    hasFiniteTotalDimension V ∧
      ∀ n : ℤ, (degreewiseEvaluation V W n).Nondegenerate := by
  -- Route correction: the projected triangle identities already package the source proof
  -- degreewise, so the remaining global work is only finite support of the diagonal coevaluation
  -- and the final nondegeneracy transfer to textbook order.
  have hfiniteDimensional : ∀ n : ℤ, FiniteDimensional F (V n) := by
    -- Each degree inherits a left dual from the projected exact pairing.
    intro n
    exact finiteDimensional_degreewise_term (V := V) (W := W) n
  have hfiniteNonzero : Set.Finite {n : ℤ | ¬ IsZero (V n)} := by
    -- Any nonzero degree of `V` must contribute a nonzero diagonal coevaluation component.
    refine (finite_degreewise_coevaluation_support (V := V) (W := W)).subset ?_
    intro n hn
    exact nonzero_degreewise_term_implies_coevaluation_nonzero (V := V) (W := W) n hn
  refine ⟨?_, ?_⟩
  · -- Translate the finite-support statement back to the textbook formulation of total dimension.
    exact (hasFiniteTotalDimension_iff (V := V)).2 ⟨hfiniteNonzero, hfiniteDimensional⟩
  · -- The remaining degreewise claim is isolated in a dedicated helper theorem.
    intro n
    exact degreewiseEvaluation_nondegenerate (V := V) (W := W) n

end CategoryTheory

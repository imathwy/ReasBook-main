import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_166_5
import stacks_proof.stacks_project.Chap15.Lemma_15_9_14
import stacks_proof.stacks_project.Chap15.Lemma_15_11_6
import stacks_proof.stacks_project.Chap15.Lemma_15_13_1
import stacks_proof.stacks_project.Chap15.Definition_15_50_1
import stacks_proof.stacks_project.Chap15.Lemma_15_50_14
import stacks_proof.stacks_project.Chap15.Lemma_15_50_15
import stacks_proof.stacks_project.Chap15.Lemma_15_51_7
import stacks_proof.stacks_project.Chap16.Theorem_16_12_1_Popescu

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open RingPairCat
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- Helper for Lemma 16.14.1: a surjective ring map with elementwise nilpotent kernel induces a
bijection on idempotents. -/
private theorem bijectiveIdempotentMapOfSurjectiveOfNilpotentKernelElements
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hsurj : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Function.Bijective f.idempotentMap := by
  constructor
  · intro e₁ e₂ h
    apply Subtype.ext
    -- Proof comment: unique lifting across a nilpotent kernel identifies equal target
    -- idempotents with equal source lifts.
    obtain ⟨e, -, huniq⟩ :=
      existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
        f hker (f e₁.1) (hsurj _) (e₁.2.map f)
    exact (huniq _ ⟨e₁.2, rfl⟩).trans
      (huniq _ ⟨e₂.2, by simpa using (congrArg Subtype.val h).symm⟩).symm
  · intro e
    -- Proof comment: surjectivity gives a lift, and the same nilpotent-kernel theorem makes it
    -- idempotent.
    obtain ⟨e', he', -⟩ :=
      existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
        f hker e.1 (hsurj _) e.2
    refine ⟨⟨e', he'.1⟩, ?_⟩
    exact Subtype.ext he'.2

/-- Helper for Lemma 16.14.1: composing with a bijection preserves bijectivity. -/
private theorem bijectiveIffBijectiveComp
    {α β γ : Type u} (f : α → β) (g : β → γ) (hg : Function.Bijective g) :
    Function.Bijective f ↔ Function.Bijective (g ∘ f) := by
  constructor
  · intro hf
    exact hg.comp hf
  · intro hgf
    constructor
    · intro x y hxy
      exact hgf.1 (by simpa [Function.comp, hxy])
    · intro z
      obtain ⟨x, hx⟩ := hgf.2 (g z)
      exact ⟨x, hg.1 <| by simpa [Function.comp] using hx⟩

/-- Helper for Lemma 16.14.1: the quotient map from `B / K^N` to `B / K` is surjective for every
positive power. -/
private theorem powQuotientFactorSurjective {B : Type u} [CommRing B]
    (K : Ideal B) (N : ℕ+) :
    Function.Surjective
      (Ideal.Quotient.factor (Ideal.pow_le_self (N := (N : ℕ)) N.ne_zero : K ^ (N : ℕ) ≤ K)) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  -- Proof comment: every class modulo `K` already comes from the same representative modulo
  -- `K^N`.
  exact ⟨Ideal.Quotient.mk (K ^ (N : ℕ)) y, rfl⟩

/-- Helper for Lemma 16.14.1: every element in the kernel of `B / K^N → B / K` is nilpotent. -/
private theorem powQuotientFactorKerNilpotentElements {B : Type u} [CommRing B]
    (K : Ideal B) (N : ℕ+) :
    ∀ x ∈ RingHom.ker
        (Ideal.Quotient.factor
          (Ideal.pow_le_self (N := (N : ℕ)) N.ne_zero : K ^ (N : ℕ) ≤ K)),
      IsNilpotent x := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  change Ideal.Quotient.mk K y = 0 at hx
  have hy : y ∈ K := Ideal.Quotient.eq_zero_iff_mem.mp hx
  refine ⟨N, ?_⟩
  change Ideal.Quotient.mk (K ^ (N : ℕ)) (y ^ (N : ℕ)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hy)

/-- Helper for Lemma 16.14.1: the quotient map `B / K^N → B / K` induces a bijection on
idempotents. -/
private theorem powQuotientFactorBijectiveIdempotentMap {B : Type u} [CommRing B]
    (K : Ideal B) (N : ℕ+) :
    Function.Bijective
      (Ideal.Quotient.factor
        (Ideal.pow_le_self (N := (N : ℕ)) N.ne_zero : K ^ (N : ℕ) ≤ K)).idempotentMap := by
  exact bijectiveIdempotentMapOfSurjectiveOfNilpotentKernelElements
    (Ideal.Quotient.factor
      (Ideal.pow_le_self (N := (N : ℕ)) N.ne_zero : K ^ (N : ℕ) ≤ K))
    (powQuotientFactorSurjective K N)
    (powQuotientFactorKerNilpotentElements K N)

namespace Algebra

/-- Helper for Lemma 16.14.1: the tensor-product map induced by a quotient map on the left factor
and a chosen quotient-valued algebra map on the right respects the `A`-algebra structure. -/
private theorem tensorBaseChangeToQuotientCommutes
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S]
    (I : Ideal A) (f : S →ₐ[R] A ⧸ I) :
    ∀ a : A,
      (Algebra.TensorProduct.productMap (Ideal.Quotient.mkₐ R I) f)
          ((algebraMap A (A ⊗[R] S)) a) =
        algebraMap A (A ⧸ I) a := by
  -- Proof comment: the left tensor factor is the canonical `A`-algebra structure on the base
  -- change, so the product map restricts to the quotient map on that factor.
  intro a
  simp [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.includeLeft_apply]

/-- Helper for Lemma 16.14.1: the quotient-valued map on the smooth base change `A ⊗[R] S`. -/
private def tensorBaseChangeToQuotient
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S]
    (I : Ideal A) (f : S →ₐ[R] A ⧸ I) :
    A ⊗[R] S →ₐ[A] A ⧸ I :=
  { toRingHom := (Algebra.TensorProduct.productMap (Ideal.Quotient.mkₐ R I) f).toRingHom
    commutes' := tensorBaseChangeToQuotientCommutes (R := R) (A := A) (S := S) I f }

/-- Helper for Lemma 16.14.1: restricting the base-changed quotient map along `includeRight`
recovers the original algebra map. -/
private theorem tensorBaseChangeToQuotientCompIncludeRightEq
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S]
    (I : Ideal A) (f : S →ₐ[R] A ⧸ I) :
    ((tensorBaseChangeToQuotient (R := R) (A := A) (S := S) I f).restrictScalars R).comp
        (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) =
      f := by
  -- Proof comment: `includeRight` sends `s` to `1 ⊗ s`, and the product map sends that tensor to
  -- `f s`.
  ext s
  simp [tensorBaseChangeToQuotient, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.productMap_apply_tmul]

/-- Helper for Lemma 16.14.1: if a reduction modulo `I` map out of a smooth algebra is given and
`(A, I)` is henselian, then the map lifts to `A`. -/
private theorem smooth_exists_lift_of_henselianRing
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S]
    (I : Ideal A) [Algebra.Smooth R S] [HenselianRing A I]
    (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := by
  let T : Type u := A ⊗[R] S
  let _ : CommRing T := inferInstance
  let _ : Algebra A T := inferInstance
  let _ : Algebra.Smooth A T := inferInstance
  let φT : T →ₐ[A] A ⧸ I :=
    tensorBaseChangeToQuotient (R := R) (A := A) (S := S) I f
  -- Proof comment: smoothness of the base change gives an étale neighborhood lifting the
  -- quotient map `φT`.
  obtain ⟨A', _, _, _, eIso, φ', hφ'⟩ :=
    exists_etale_lift_to_quotient_of_smooth (A := A) (B := T) I φT
  let I' : Ideal A' := Ideal.map (algebraMap A A') I
  let g : A' →ₐ[A] A ⧸ I :=
    (eIso.symm.toAlgHom.restrictScalars A).comp
      ((Ideal.Quotient.mkₐ A' I').restrictScalars A)
  -- Proof comment: the henselian pair lifts the resulting étale section back to `A`.
  obtain ⟨σ, hσ⟩ := exists_etale_section_of_henselianRing (R := A) (I := I) g
  have hdescend :
      ((Ideal.Quotient.mkₐ A I).comp σ).comp φ' = φT := by
    calc
      ((Ideal.Quotient.mkₐ A I).comp σ).comp φ'
          = g.comp φ' := by
              rw [hσ]
      _ = (eIso.symm.toAlgHom.restrictScalars A).comp
            (((Ideal.Quotient.mkₐ A' I').restrictScalars A).comp φ') := by
              rw [AlgHom.comp_assoc]
      _ = (eIso.symm.toAlgHom.restrictScalars A).comp
            ((eIso.toAlgHom.restrictScalars A).comp φT) := by
              rw [hφ']
      _ = ((eIso.symm.toAlgHom.restrictScalars A).comp
            (eIso.toAlgHom.restrictScalars A)).comp φT := by
              rw [AlgHom.comp_assoc]
      _ = φT := by
              simp
  have hdescendR :
      ((((Ideal.Quotient.mkₐ A I).comp σ).comp φ').restrictScalars R) =
        φT.restrictScalars R := by
    -- Proof comment: the `A`-algebra identity remains valid after forgetting scalars to `R`.
    exact congrArg (fun ψ : T →ₐ[A] A ⧸ I ↦ ψ.restrictScalars R) hdescend
  refine
    ⟨(σ.restrictScalars R).comp
        ((φ'.restrictScalars R).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S)),
      ?_⟩
  -- Proof comment: compose the smooth-stage lift with the henselian section and restrict back
  -- along the right tensor inclusion.
  calc
    (Ideal.Quotient.mkₐ R I).comp
        ((σ.restrictScalars R).comp
          ((φ'.restrictScalars R).comp
            (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S)))
        = ((((Ideal.Quotient.mkₐ A I).comp σ).comp φ').restrictScalars R).comp
            (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) := by
              rfl
    _ = (φT.restrictScalars R).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) := by
            rw [hdescendR]
    _ = f := by
            simpa [φT] using
              tensorBaseChangeToQuotientCompIncludeRightEq
                (R := R) (A := A) (S := S) I f

end Algebra

/-- Helper for Lemma 16.14.1: if the formal tuple `aHat` is a root of every polynomial in the
chosen finite family, then the ideal generated by those polynomials lies in the kernel of the
completion-valued evaluation map. -/
lemma formalRootMapSpanLeKer {m n : ℕ}
    (f : Fin m → MvPolynomial (Fin n) A)
    (aHat : Fin n → AdicCompletion I A)
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0) :
    Ideal.span (Set.range f) ≤ RingHom.ker (MvPolynomial.aeval aHat).toRingHom := by
  -- Proof comment: generators of the span are exactly the listed equations, and each generator
  -- already vanishes by the formal-root hypothesis.
  rw [Ideal.span_le]
  rintro p ⟨j, rfl⟩
  exact RingHom.mem_ker.mpr (hroots j)

/-- Helper for Lemma 16.14.1: any `A`-algebra map out of the quotient
`A[x_1, ..., x_n] / (f_1, ..., f_m)` sends the quotient-variable tuple to an exact root of the
defining polynomial family. -/
lemma quotientVariableTuple_exactRoots {m n : ℕ} {B : Type*} [CommRing B] [Algebra A B]
    (f : Fin m → MvPolynomial (Fin n) A)
    (u : (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) →ₐ[A] B) :
    let b : Fin n → B := fun i ↦ u (Ideal.Quotient.mk _ (MvPolynomial.X i))
    ∀ j, MvPolynomial.aeval b (f j) = 0 := by
  intro b j
  let q : MvPolynomial (Fin n) A →ₐ[A] B :=
    u.comp (Ideal.Quotient.mkₐ A (Ideal.span (Set.range f)))
  have hq : q = MvPolynomial.aeval b := by
    -- Proof comment: both `A`-algebra maps agree on every polynomial variable, so extensionality
    -- identifies the quotient-factorization map with the direct evaluation map.
    ext i
    simp [q, b]
  have hzero :
      (Ideal.Quotient.mk (Ideal.span (Set.range f))) (f j) = 0 := by
    -- Proof comment: each listed polynomial becomes zero in the quotient by the ideal it
    -- generates.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  -- Proof comment: evaluate through the quotient map and then use that the chosen polynomial class
  -- is zero in the quotient.
  calc
    MvPolynomial.aeval b (f j) = q (f j) := by rw [← hq]
    _ = u ((Ideal.Quotient.mk (Ideal.span (Set.range f))) (f j)) := by rfl
    _ = 0 := by simp [hzero]

/-- Helper for Lemma 16.14.1: henselianity depends only on the zero locus of the ideal, so it
passes from `I` to every positive power `I^N`. -/
lemma henselianRing_pow (N : ℕ+) [HenselianRing A I] :
    HenselianRing A (I ^ (N : ℕ)) := by
  let P : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := A)
  let Q : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A)
  let T (K : Ideal A) : List Prop :=
    [ HenselianRing A K
    , K.HasEtaleLiftProperty
    , Q K
    , P K
    , K.SatisfiesGabberRootCriterion
    ]
  have hIff :
      HenselianRing A I ↔ P I := by
    -- Proof comment: isolate the integral-idempotent lifting clause in the Chapter 15 TFAE.
    simpa [T, Q, P] using
      (henselianRing_tfae_etaleLift_idempotents_gabberCriterion (A := A) I).out 0 3
  have hIntegral : P I := hIff.mp inferInstance
  have hIntegralPow : P (I ^ (N : ℕ)) := by
    intro B _ _ _
    let K : Ideal B := Ideal.map (algebraMap A B) I
    have hK : Function.Bijective (Ideal.Quotient.mk K).idempotentMap := by
      simpa [K] using hIntegral (B := B)
    have hFactor :
        Function.Bijective
          (Ideal.Quotient.factor
            (Ideal.pow_le_self (N := (N : ℕ)) N.ne_zero : K ^ (N : ℕ) ≤ K)).idempotentMap :=
      powQuotientFactorBijectiveIdempotentMap K N
    have hComp :
        (Ideal.Quotient.factor
            (Ideal.pow_le_self (N := (N : ℕ)) N.ne_zero : K ^ (N : ℕ) ≤ K)).idempotentMap ∘
          (Ideal.Quotient.mk (K ^ (N : ℕ))).idempotentMap =
        (Ideal.Quotient.mk K).idempotentMap := by
      funext e
      rfl
    have hPow :
        Function.Bijective (Ideal.Quotient.mk (K ^ (N : ℕ))).idempotentMap := by
      simpa [hComp] using
        (bijectiveIffBijectiveComp
          (Ideal.Quotient.mk (K ^ (N : ℕ))).idempotentMap
          (Ideal.Quotient.factor
            (Ideal.pow_le_self (N := (N : ℕ)) N.ne_zero : K ^ (N : ℕ) ≤ K)).idempotentMap
          hFactor).mpr hK
    simpa [K] using hPow
  have hPowIff :
      HenselianRing A (I ^ (N : ℕ)) ↔ P (I ^ (N : ℕ)) := by
    -- Proof comment: apply the same TFAE to the positive power ideal.
    simpa [T, Q, P] using
      (henselianRing_tfae_etaleLift_idempotents_gabberCriterion
        (A := A) (I ^ (N : ℕ))).out 0 3
  exact hPowIff.mpr hIntegralPow

/-- Helper for Lemma 16.14.1: Popescu's theorem factors the quotient algebra defined by the formal
roots through one smooth `A`-algebra stage mapping to the completion. -/
lemma existsSmoothFactorizationOfFormalRootMap {m n : ℕ}
    [(algebraMap A (AdicCompletion I A)).IsRegularRingMap]
    (f : Fin m → MvPolynomial (Fin n) A)
    (aHat : Fin n → AdicCompletion I A)
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0) :
    let P := MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)
    let rootMap : P →ₐ[A] AdicCompletion I A :=
      Ideal.Quotient.liftₐ _ (MvPolynomial.aeval aHat)
        (formalRootMapSpanLeKer (I := I) f aHat hroots)
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Smooth A B)
      (alpha : P →ₐ[A] B) (beta : B →ₐ[A] AdicCompletion I A),
      beta.comp alpha = rootMap := by
  classical
  intro P rootMap
  let _ : Algebra P (AdicCompletion I A) := rootMap.toAlgebra
  let _ : Algebra (ULift P) (ULift (AdicCompletion I A)) :=
    ULift.algebra' P (ULift (AdicCompletion I A))
  let _ : Algebra.FinitePresentation A P := by
    -- Proof comment: the quotient algebra is finitely presented because the polynomial ideal is
    -- generated by the finite family `f`.
    let hfg : (Ideal.span (Set.range f)).FG := Ideal.fg_span (Set.finite_range _)
    exact Algebra.FinitePresentation.quotient hfg
  have hcolim : (algebraMap A (AdicCompletion I A)).IsFilteredColimitOfSmooth := by
    -- Proof comment: Popescu packages regularity of the completion map as a filtered colimit of
    -- smooth algebras.
    exact Algebra.isFilteredColimitOfSmooth (R := A) (Λ := AdicCompletion I A)
  let _ : Algebra A (ULift P) := ULift.algebra
  let _ : Algebra (ULift A) (ULift P) := ULift.algebra' A (ULift P)
  let _ : Algebra A (ULift (AdicCompletion I A)) := ULift.algebra
  let _ : Algebra (ULift A) (ULift (AdicCompletion I A)) :=
    ULift.algebra' A (ULift (AdicCompletion I A))
  have hp :
      CategoryTheory.MorphismProperty.isFinitelyPresentable CommRingCat
        (CommRingCat.ofHom (algebraMap (ULift A) (ULift P))) := by
    -- Proof comment: finite presentation of `P` is exactly the finite-presentability condition on
    -- its lifted structure map in `CommRingCat`.
    simpa using
      (CommRingCat.isFinitelyPresentable_hom
        (CommRingCat.ofHom (algebraMap (ULift A) (ULift P)))
        (by infer_instance))
  have hpg :
      CommRingCat.ofHom (algebraMap (ULift A) (ULift P)) ≫
          CommRingCat.ofHom (algebraMap (ULift P) (ULift (AdicCompletion I A))) =
        CommRingCat.ofHom (algebraMap (ULift A) (ULift (AdicCompletion I A))) := by
    -- Proof comment: the lifted quotient-point map is an `A`-algebra map, so the source algebra
    -- maps compose exactly as expected.
    apply CommRingCat.hom_ext_iff.mpr
    intro x
    rfl
  have huliftColim :
      CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.Smooth)
        (CommRingCat.ofHom (algebraMap (ULift A) (ULift (AdicCompletion I A)))) := by
    -- Proof comment: unwrap the source-facing filtered-colimit hypothesis once so the
    -- factorization criterion can be applied directly to the lifted finitely presented quotient.
    simpa [RingHom.IsFilteredColimitOfSmooth] using hcolim
  -- Route correction: the previous route stalled in categorical `ULift` normal forms. Here we
  -- extract one smooth lifted stage and immediately descend it to ordinary `A`-algebra maps.
  obtain ⟨B, u, v, huv, hSmoothStage⟩ :=
    ((CategoryTheory.MorphismProperty.ind_iff_exists
      (C := CommRingCat)
      (P := RingHom.toMorphismProperty RingHom.Smooth)
      (H := commRingCatIsFinitelyPresentableHom_of_smooth)
      (CommRingCat.ofHom (algebraMap (ULift A) (ULift (AdicCompletion I A))))).1 huliftColim)
      (CommRingCat.ofHom (algebraMap (ULift A) (ULift P)))
      (CommRingCat.ofHom (algebraMap (ULift P) (ULift (AdicCompletion I A))))
      hp hpg
  let sourceToB : ULift A →+* B := u.hom.comp (algebraMap (ULift A) (ULift P))
  have hsourceToBSmooth : sourceToB.Smooth := by
    -- Proof comment: the stage extracted from `ind_iff_exists` is smooth over `ULift A`.
    simpa [sourceToB, RingHom.toMorphismProperty, CommRingCat.hom_comp] using hSmoothStage
  let fA : A →+* ULift A := (ULift.ringEquiv.symm : A ≃+* ULift A).toRingHom
  let _ : Algebra A B := (sourceToB.comp fA).toAlgebra
  have hsourceSmooth : (algebraMap A B).Smooth := by
    -- Proof comment: composing with the bijective source equivalence `A ≃ ULift A` preserves
    -- smoothness of the chosen stage.
    let hbase : fA.Smooth :=
      RingHom.Smooth.of_bijective (ULift.ringEquiv.symm : A ≃+* ULift A).bijective
    simpa [sourceToB, fA, RingHom.algebraMap_toAlgebra] using
      RingHom.Smooth.comp hbase hsourceToBSmooth
  have hBSmooth : Algebra.Smooth A B := by
    simpa [RingHom.smooth_algebraMap] using hsourceSmooth
  let _ : Algebra.Smooth A B := hBSmooth
  let fP : P →+* ULift P := (ULift.ringEquiv.symm : P ≃+* ULift P).toRingHom
  have hAlphaComm :
      ∀ r : A, (u.hom.comp fP) (algebraMap A P r) = algebraMap A B r := by
    -- Proof comment: the descended map `alpha` respects the transported `A`-algebra structures on
    -- the quotient and the smooth stage.
    intro r
    simp [sourceToB, fA, fP, RingHom.algebraMap_toAlgebra]
  let alpha : P →ₐ[A] B :=
    { toRingHom := u.hom.comp fP
      commutes' := hAlphaComm }
  let betaDown : ULift (AdicCompletion I A) →+* AdicCompletion I A :=
    (ULift.ringEquiv : ULift (AdicCompletion I A) ≃+* AdicCompletion I A).toRingHom
  have hsourceComp :
      v.hom.comp sourceToB = algebraMap (ULift A) (ULift (AdicCompletion I A)) := by
    -- Proof comment: the extracted stage still maps to the completion through the original
    -- completion-valued quotient point.
    ext r
    have huvr :=
      congrArg
        (fun ψ : CommRingCat.of (ULift P) ⟶ CommRingCat.of (ULift (AdicCompletion I A)) ↦
          ψ.hom ((algebraMap (ULift A) (ULift P)) r))
        huv
    have hpgr :=
      congrArg
        (fun ψ : CommRingCat.of (ULift A) ⟶ CommRingCat.of (ULift (AdicCompletion I A)) ↦
          ψ.hom r)
        hpg
    calc
      v.hom (sourceToB r) =
          (algebraMap (ULift P) (ULift (AdicCompletion I A)))
            ((algebraMap (ULift A) (ULift P)) r) := by
              simpa [sourceToB, CommRingCat.hom_comp] using huvr
      _ = (algebraMap (ULift A) (ULift (AdicCompletion I A))) r := by
            simpa [CommRingCat.hom_comp] using hpgr
  have hBetaComm :
      ∀ r : A, (betaDown.comp v.hom) (algebraMap A B r) = algebraMap A (AdicCompletion I A) r := by
    -- Proof comment: the descended map `beta` is compatible with the transported `A`-algebra
    -- structure because the lifted source map still composes to the canonical completion map.
    intro r
    have hcompR := DFunLike.congr_fun hsourceComp (ULift.up r)
    simpa [sourceToB, fA, RingHom.algebraMap_toAlgebra] using congrArg ULift.down hcompR
  let beta : B →ₐ[A] AdicCompletion I A :=
    { toRingHom := betaDown.comp v.hom
      commutes' := hBetaComm }
  have hBetaAlpha : beta.comp alpha = rootMap := by
    -- Proof comment: evaluate the lifted factorization on each quotient element, then erase the
    -- `ULift` wrappers on source and target.
    ext x
    have huvx :=
      congrArg
        (fun ψ : CommRingCat.of (ULift P) ⟶ CommRingCat.of (ULift (AdicCompletion I A)) ↦
          ψ.hom (ULift.up x))
        huv
    simpa [alpha, beta, fP, betaDown, CommRingCat.hom_comp] using congrArg ULift.down huvx
  exact ⟨B, inferInstance, inferInstance, inferInstance, alpha, beta, hBetaAlpha⟩

/-- Helper for Lemma 16.14.1: after factoring the quotient root map through a smooth stage, the
images of the quotient variables recover the chosen formal coordinates in the completion. -/
lemma factorizedVariables_map_to_formalCoordinates {m n : ℕ} {B : Type u}
    [CommRing B] [Algebra A B]
    (f : Fin m → MvPolynomial (Fin n) A)
    (aHat : Fin n → AdicCompletion I A)
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0)
    (alpha :
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) →ₐ[A] B)
    (beta : B →ₐ[A] AdicCompletion I A)
    (hβα :
      beta.comp alpha =
        Ideal.Quotient.liftₐ _ (MvPolynomial.aeval aHat)
          (formalRootMapSpanLeKer (I := I) f aHat hroots)) :
    let xB : Fin n → B := fun i ↦ alpha (Ideal.Quotient.mk _ (MvPolynomial.X i))
    ∀ i, beta (xB i) = aHat i := by
  intro xB i
  -- Proof comment: evaluate the factorization identity on the class of the `i`th polynomial
  -- variable and compute the quotient lift by its defining formula.
  have hcoord :=
    congrArg
      (fun φ :
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) →ₐ[A] AdicCompletion I A ↦
          φ (Ideal.Quotient.mk _ (MvPolynomial.X i)))
      hβα
  simpa [xB] using hcoord

/-- Helper for Lemma 16.14.1: evaluating the lifted smooth-stage point modulo `I^N` matches the
given formal coordinates modulo `I^N`. -/
lemma liftedVariables_reduce_mod_pow {m n : ℕ} {B : Type u}
    [CommRing B] [Algebra A B]
    (f : Fin m → MvPolynomial (Fin n) A)
    (aHat : Fin n → AdicCompletion I A)
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0)
    (N : ℕ+)
    (alpha :
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range f)) →ₐ[A] B)
    (beta : B →ₐ[A] AdicCompletion I A)
    (hβα :
      beta.comp alpha =
        Ideal.Quotient.liftₐ _ (MvPolynomial.aeval aHat)
          (formalRootMapSpanLeKer (I := I) f aHat hroots))
    (sigma : B →ₐ[A] A)
    (hσ :
      (Ideal.Quotient.mkₐ A (I ^ (N : ℕ))).comp sigma =
        (AdicCompletion.evalₐ I (N : ℕ)).comp beta) :
    let xB : Fin n → B := fun i ↦ alpha (Ideal.Quotient.mk _ (MvPolynomial.X i))
    ∀ i,
      AdicCompletion.evalₐ I (N : ℕ) (aHat i) =
        Ideal.Quotient.mk (I ^ (N : ℕ)) (sigma (xB i)) := by
  intro xB i
  -- Proof comment: first identify the `i`th smooth-stage coordinate with the formal coordinate,
  -- then evaluate the lift identity at that stage element.
  have hcoord :
      beta (xB i) = aHat i :=
    factorizedVariables_map_to_formalCoordinates
      (I := I) f aHat hroots alpha beta hβα i
  have hlift :=
    congrArg (fun φ : B →ₐ[A] A ⧸ I ^ (N : ℕ) ↦ φ (xB i)) hσ
  calc
    AdicCompletion.evalₐ I (N : ℕ) (aHat i) =
        AdicCompletion.evalₐ I (N : ℕ) (beta (xB i)) := by
          rw [hcoord.symm]
    _ = Ideal.Quotient.mk (I ^ (N : ℕ)) (sigma (xB i)) := by
          simpa using hlift.symm

/- Domain-style sampling:
- primary domain: Artin approximation for Noetherian henselian pairs, organized around the owner
  predicates `HenselianRing A I`, `IsRegularRingMap A (AdicCompletion I A)`, and the chosen
  pair-henselization owner API `henselizationRing (pairOfIdeal I)` and
  `(henselizationPair (pairOfIdeal I)).ideal`;
- sampled owner declarations in this domain:
  `IsRegularRingMap`,
  `IsGRing`,
  `(inferInstance : (algebraMap A (AdicCompletion I A)).IsRegularRingMap)`,
  `henselizationRing`,
  `henselizationPair`,
  `RingPairCat.pairHenselization_isGRing`;
- best owner abstraction: the source-facing lemma should expose the textbook alternatives on the
  henselian pair, while the regularity of `A → A^` remains the core/canonical bridge hypothesis;
- primitive vs. derived API: the approximation conclusion is source-facing, the regularity of the
  completion map is the core owner input, and both `IsGRing A` and the chosen pair-henselization
  of a `G`-ring are derived bridge hypotheses already absorbed upstream by Chapter 15. For the
  henselization case, the ring and ideal are derived from the canonical pair-henselization owners
  `henselizationRing (pairOfIdeal J)` and `(henselizationPair (pairOfIdeal J)).ideal`, so the
  theorem surface should use those owners directly rather than a parallel local wrapper.

Source/core/bridge triage:
- `source-facing`: the three approximation statements matching Stacks Lemma `16.14.1`, namely the
  regular-completion, `G`-ring, and henselization-of-a-`G`-ring cases;
- `core/canonical`: `HenselianRing A I` and `IsRegularRingMap A (AdicCompletion I A)`;
- `bridge/view`: the Chapter 15 owner instance
  `(inferInstance : (algebraMap A (AdicCompletion I A)).IsRegularRingMap)` and
  `RingPairCat.pairHenselization_isGRing`, which convert source alternatives to the canonical
  regularity hypothesis.
-/

-- Proof sketch: first reduce the source alternatives to the case where `A → A^` is a regular ring
-- map. Then apply Popescu to factor the completed solution through a smooth `A`-algebra carrying
-- an exact solution, lift the induced section modulo `I^N` along an étale neighborhood, and use
-- the henselian pair property to retract that neighborhood back to `A`.
/-- Lemma 16.14.1, regular-completion case: for a Noetherian henselian pair `(A, I)`, if the
completion map `A → A^` is regular, then every finite polynomial system over `A` with a solution
in the `I`-adic completion has, for each `N ≥ 1`, a solution in `A` congruent to the completed
solution modulo `I^N`. -/
@[stacks 0AH5]
theorem exists_polynomial_solution_of_adicCompletion_solution_of_isRegularRingMap
    [HenselianRing A I]
    (hreg : (algebraMap A (AdicCompletion I A)).IsRegularRingMap)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) A)
    (aHat : Fin n → AdicCompletion I A)
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0) (N : ℕ+) :
    ∃ a : Fin n → A,
      (∀ i,
        AdicCompletion.evalₐ I (N : ℕ) (aHat i) =
          Ideal.Quotient.mk (I ^ (N : ℕ)) (a i)) ∧
      ∀ j, MvPolynomial.eval a (f j) = 0 := by
  -- Proof comment: factor the completion-valued quotient point through one smooth `A`-algebra
  -- stage, then lift its reduction modulo `I ^ N` back to `A` using the henselian smooth-lifting
  -- theorem.
  let _ : (algebraMap A (AdicCompletion I A)).IsRegularRingMap := hreg
  rcases existsSmoothFactorizationOfFormalRootMap (I := I) f aHat hroots with
    ⟨B, _instB, _instAlgB, _instSmoothB, alpha, beta, hβα⟩
  let xB : Fin n → B := fun i ↦ alpha (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have hxB : ∀ j, MvPolynomial.aeval xB (f j) = 0 :=
    quotientVariableTuple_exactRoots (A := A) (B := B) f alpha
  let q : B →ₐ[A] A ⧸ I ^ (N : ℕ) :=
    (AdicCompletion.evalₐ I (N : ℕ)).comp beta
  letI : HenselianRing A (I ^ (N : ℕ)) := henselianRing_pow (A := A) (I := I) N
  obtain ⟨sigma, hσ⟩ :=
    smooth_exists_lift_of_henselianRing
      (R := A) (A := A) (S := B) (I := I ^ (N : ℕ)) q
  let a : Fin n → A := fun i ↦ sigma (xB i)
  refine ⟨a, ?_, ?_⟩
  · intro i
    -- Proof comment: evaluate the lifted smooth-stage point modulo `I ^ N` and rewrite it back
    -- to the original formal coordinate.
    simpa [a, xB] using
      liftedVariables_reduce_mod_pow
        (I := I) f aHat hroots N alpha beta hβα sigma hσ i
  · intro j
    -- Proof comment: apply the lifted map `sigma` to the exact polynomial identity already valid
    -- in the smooth stage.
    simpa [a, xB] using congrArg sigma.toRingHom (hxB j)

/-- Lemma 16.14.1, `G`-ring case: if `A` is a `G`-ring, then the canonical regularity theorem for
`A → A^` reduces the approximation statement to the regular-completion case. -/
@[stacks 0AH5]
theorem exists_polynomial_solution_of_adicCompletion_solution
    [HenselianRing A I] [IsGRing A]
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) A)
    (aHat : Fin n → AdicCompletion I A)
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0) (N : ℕ+) :
    ∃ a : Fin n → A,
      (∀ i,
        AdicCompletion.evalₐ I (N : ℕ) (aHat i) =
          Ideal.Quotient.mk (I ^ (N : ℕ)) (a i)) ∧
      ∀ j, MvPolynomial.eval a (f j) = 0 := by
  let hreg : (algebraMap A (AdicCompletion I A)).IsRegularRingMap := inferInstance
  simpa using
    exists_polynomial_solution_of_adicCompletion_solution_of_isRegularRingMap I
      hreg f aHat hroots N

section

variable {B : Type u} [CommRing B]
variable (J : Ideal B)

/-- Lemma 16.14.1, henselization case: if `(A, I)` is the chosen henselization of a pair
`(B, J)` with `B` a `G`-ring, then the upstream `G`-ring instance on the henselization
reduces the approximation statement to the `G`-ring case. -/
@[stacks 0AH5]
theorem exists_polynomial_solution_of_adicCompletion_solution_of_pairHenselization
    [IsGRing B]
    {m n : ℕ}
    (f : Fin m → MvPolynomial (Fin n) (henselizationRing (pairOfIdeal J)))
    (aHat : Fin n → AdicCompletion (henselizationPair (pairOfIdeal J)).ideal
      (henselizationRing (pairOfIdeal J)))
    (hroots : ∀ j, MvPolynomial.aeval aHat (f j) = 0)
    (N : ℕ+) :
    ∃ a : Fin n → henselizationRing (pairOfIdeal J),
      (∀ i,
        AdicCompletion.evalₐ (henselizationPair (pairOfIdeal J)).ideal (N : ℕ) (aHat i) =
          Ideal.Quotient.mk (((henselizationPair (pairOfIdeal J)).ideal) ^ (N : ℕ)) (a i)) ∧
      ∀ j, MvPolynomial.eval a (f j) = 0 := by
  let _ :
      HenselianRing (henselizationRing (pairOfIdeal J)) (henselizationPair (pairOfIdeal J)).ideal :=
    (henselization (pairOfIdeal J)).property
  simpa using
    exists_polynomial_solution_of_adicCompletion_solution
      ((henselizationPair (pairOfIdeal J)).ideal) f aHat hroots N

end

end

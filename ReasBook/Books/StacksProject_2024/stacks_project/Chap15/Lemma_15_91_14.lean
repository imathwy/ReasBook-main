import Mathlib
import Mathlib.CategoryTheory.Monoidal.Tor
import StacksProject_2024.stacks_project.Chap10.Lemma_10_75_2
import StacksProject_2024.stacks_project.Chap15.Definition_15_61_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_89_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped IdealPowerTorsion TensorProduct

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for the quotient by `f^∞`-torsion.
* sampled owner declarations:
  `Ideal.primaryComponent`,
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `Tor`,
  `IsZero`.
* owner abstraction: the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f` for the exact
  Beauville-Laszlo hypotheses, together with the canonical torsion owner `R[f^∞]`; the Tor
  bifunctor `Tor (ModuleCat R) 1` is the ambient canonical owner.
* primitive data: the algebra map `R → R'` and the element `f : R`.
* derived API: the vanishing statement for `Tor₁^R(R', R / R[f^∞])`, recorded by the canonical
  zero-object interface `IsZero`.
* triage: this theorem is `source-facing`; `IsBeauvilleLaszloGlueingPairAlong`, `R[f^∞]`, and
  `Tor` and `IsZero` are `core/canonical`.
-/

-- Proof sketch: write `R / R[f^∞]` as the filtered colimit of the quotients `R / R[f^n]`, or
-- equivalently of the principal ideals `(f^n)`. The functor `Tor_1^R(R', -)` commutes with filtered
-- colimits, so the previous lemma reduces the claim to the vanishing of
-- `Tor_1^R(R', (f^n))` for each positive integer `n`.
/-- Helper for Lemma 15.91.14: the quotient comparison modulo `(f^n)` can be rewritten as the
ideal-theoretic quotient map for the principal ideal `(f)`. -/
private theorem principal_ideal_power_quotientMap_bijective_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (n : ℕ+) :
    Function.Bijective
      (Ideal.quotientMap
        (((principalIdeal f) ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map) := by
  let I : Ideal R := principalIdeal f
  let σ : R →+* R' := algebraMap R R'
  have hmap :
      Ideal.map σ (I ^ (n : ℕ)) = principalPowerIdeal (σ f) n := by
    -- Proof comment: rewrite the image of the principal power ideal using the standard map lemmas.
    simp [I, σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
      Set.image_singleton]
  have htransport :
      principalPowerIdealImageQuotientMap σ f n =
        (Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map) := by
    -- Proof comment: both quotient maps agree on the class of every element of `R`.
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap]
    simpa [I, principalPowerIdeal, Ideal.quotientMap_mk] using
      (Ideal.quotientEquivAlgOfEq_mk (R₁ := R) (h := hmap) (x := σ r))
  have hcomp :
      Function.Bijective
        ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map)) := by
    -- Proof comment: transport the Beauville-Laszlo quotient bijection to the ideal-theoretic form.
    have hpairQuot :
        Function.Bijective (principalPowerIdealImageQuotientMap σ f n) := by
      simpa [σ] using hpair.quotientMapBijective n
    rw [htransport] at hpairQuot
    exact hpairQuot
  constructor
  · intro x y hxy
    have hxy' :
        ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (n : ℕ)))
              σ
              Ideal.le_comap_map)) x =
          ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (n : ℕ)))
              σ
              Ideal.le_comap_map)) y := by
      exact congrArg (Ideal.quotientEquivAlgOfEq R hmap) hxy
    exact hcomp.1 hxy'
  · intro z
    -- Proof comment: lift `z` through the transported bijection, then cancel the quotient
    -- equivalence.
    obtain ⟨x, hx⟩ := hcomp.2 ((Ideal.quotientEquivAlgOfEq R hmap) z)
    refine ⟨x, ?_⟩
    exact (Ideal.quotientEquivAlgOfEq R hmap).injective hx

/-- Helper for Lemma 15.91.14: the `f^∞`-torsion submodule is `(f)`-power torsion as a module in
its own right. -/
private theorem fPowerTorsion_is_ideal_power_torsion
    (f : R) :
    Module.IsIdealPowerTorsion (principalIdeal f) (R[f^∞] : Submodule R R) := by
  have htors : Module.IsTorsion' (R[f^∞] : Submodule R R) (Submonoid.powers f) := by
    intro x
    -- Proof comment: every element of the torsion submodule already carries the needed witness.
    rcases (Submodule.mem_torsion'_iff (Submonoid.powers f) (x : R)).1 x.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa using ha
  exact (Module.isIdealPowerTorsion_principalIdeal_iff (M := (R[f^∞] : Submodule R R)) f).2 htors

/-- Helper for Lemma 15.91.14: the Beauville-Laszlo hypotheses make base change along `R → R'`
bijective on the `f^∞`-torsion submodule. -/
private theorem fPowerTorsion_tensorBaseChange_bijective_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective (TensorProduct.mk R R' (R[f^∞] : Submodule R R) 1) := by
  -- Proof comment: apply the ideal-power torsion base-change theorem to the torsion submodule
  -- itself, using the quotient comparison from the glueing-pair hypotheses.
  exact
    tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
      (I := principalIdeal f)
      (R' := R')
      (M := (R[f^∞] : Submodule R R))
      (fPowerTorsion_is_ideal_power_torsion (R := R) f)
      (fun n ↦
        principal_ideal_power_quotientMap_bijective_of_glueingPair
          (R := R) (R' := R') f hpair n)

/-- Helper for Lemma 15.91.14: on generators `1 ⊗ x`, tensoring the inclusion
`R[f^∞] ↪ R` and then evaluating via `TensorProduct.rid` agrees with the Beauville-Laszlo torsion
comparison map. -/
private theorem fPowerTorsion_tensor_restriction
    (f : R)
    (x : (R[f^∞] : Submodule R R)) :
    (((TensorProduct.rid R R').toLinearMap.comp
        (((R[f^∞] : Submodule R R)).subtype.lTensor R')).comp
        (TensorProduct.mk R R' (R[f^∞] : Submodule R R) 1)) x =
      ((fPowerTorsionToExtension (algebraMap R R') f) x : R') := by
  -- Proof comment: both composites are the canonical image of `x` under `algebraMap R R'`.
  simp [fPowerTorsionToExtension, Algebra.smul_def]
  rfl

/-- Helper for Lemma 15.91.14: for a Beauville-Laszlo glueing pair, tensoring the inclusion
`R[f^∞] ↪ R` with `R'` is injective. -/
private theorem fPowerTorsion_lTensor_injective_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Injective (((R[f^∞] : Submodule R R)).subtype.lTensor R') := by
  let T : Submodule R R := (R[f^∞] : Submodule R R)
  have hmk : Function.Bijective (TensorProduct.mk R R' T 1) := by
    simpa [T] using
      fPowerTorsion_tensorBaseChange_bijective_of_glueingPair (R := R) (R' := R') f hpair
  have hTorsionInj :
      Function.Injective (fPowerTorsionToExtension (algebraMap R R') f) := by
    exact
      (isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsionToExtension
        (φ := algebraMap R R')
        (f := f)
        hpair.quotientMapBijective).1 hpair |>.1
  have hTensorGeneratorInj :
      Function.Injective
        ((((TensorProduct.rid R R').toLinearMap.comp (T.subtype.lTensor R')).comp
          (TensorProduct.mk R R' T 1))) := by
    intro x y hxy
    -- Proof comment: compare the tensorized inclusion with the Beauville-Laszlo torsion map,
    -- which is injective for a glueing pair.
    exact hTorsionInj <| by
      apply Subtype.ext
      simpa [T, fPowerTorsion_tensor_restriction (R := R) (R' := R') f x,
        fPowerTorsion_tensor_restriction (R := R) (R' := R') f y, Algebra.smul_def] using hxy
  intro z₁ z₂ hz
  rcases hmk.2 z₁ with ⟨x₁, rfl⟩
  rcases hmk.2 z₂ with ⟨x₂, rfl⟩
  -- Proof comment: every tensor comes from a generator `1 ⊗ x`, so injectivity reduces to the
  -- generator comparison above.
  have hridEq :
      (((TensorProduct.rid R R').toLinearMap.comp (T.subtype.lTensor R')).comp
          (TensorProduct.mk R R' T 1)) x₁ =
        (((TensorProduct.rid R R').toLinearMap.comp (T.subtype.lTensor R')).comp
          (TensorProduct.mk R R' T 1)) x₂ := by
    simpa [LinearMap.comp_apply] using congrArg (TensorProduct.rid R R').toLinearMap hz
  have hx : x₁ = x₂ := hTensorGeneratorInj hridEq
  simpa [hx]

/-- Helper for Lemma 15.91.14: the quotient map `R → R / R[f^∞]` kills the torsion submodule. -/
private theorem fPowerTorsion_subtype_mkQ_comp_eq_zero
    (f : R) :
    let T : Submodule R R := (R[f^∞] : Submodule R R)
    T.mkQ.comp T.subtype = 0 := by
  intro T
  ext x
  -- Proof comment: the image of a torsion element vanishes in the quotient by the torsion
  -- submodule itself.
  exact (Submodule.Quotient.mk_eq_zero T).2 x.2

/-- Helper for Lemma 15.91.14: the canonical row
`0 → R[f^∞] → R → R / R[f^∞] → 0` is short exact. -/
private theorem fPowerTorsion_quotient_shortExact
    (f : R) :
    let T : Submodule R R := (R[f^∞] : Submodule R R)
    (ShortComplex.moduleCatMk T.subtype T.mkQ
      (fPowerTorsion_subtype_mkQ_comp_eq_zero (R := R) f)).ShortExact := by
  intro T
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: exactness is the standard `subtype`/`mkQ` exactness for a submodule quotient.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa using (LinearMap.exact_subtype_mkQ T)
  · exact (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype T)
  · exact (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective T)

/-- Helper for Lemma 15.91.14: the product `x * f^n` lies in the principal ideal `(f^n)`. -/
private theorem mul_mem_principalPowerIdeal
    (f : R) (n : ℕ) (x : R) :
    x * f ^ n ∈ principalPowerIdeal f n := by
  -- Proof comment: rewrite `(f^n)` as the span of the generator `f^n`.
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr ⟨x, by simpa [mul_comm]⟩

/-- Helper for Lemma 15.91.14: multiplication by `f^n` with codomain restricted to `(f^n)`. -/
private abbrev principalPowerMulRight
    (f : R) (n : ℕ) :
    R →ₗ[R] principalPowerIdeal f n :=
  LinearMap.codRestrict (principalPowerIdeal f n) (LinearMap.mulRight R (f ^ n))
    (mul_mem_principalPowerIdeal (R := R) f n)

/-- Helper for Lemma 15.91.14: the restricted multiplication map still evaluates as ordinary
multiplication by `f^n`. -/
@[simp] private theorem principalPowerMulRight_apply
    (f : R) (n : ℕ) (x : R) :
    principalPowerMulRight (R := R) f n x =
      ⟨x * f ^ n, mul_mem_principalPowerIdeal (R := R) f n x⟩ :=
  rfl

/-- Helper for Lemma 15.91.14: every element of `(f^n)` has a preimage under multiplication by
`f^n`. -/
private theorem principalPowerMulRight_surjective
    (f : R) (n : ℕ) :
    Function.Surjective (principalPowerMulRight (R := R) f n) := by
  intro y
  -- Proof comment: membership in `(f^n)` is divisibility by the generator `f^n`.
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using y.2)) with
    ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  simpa [principalPowerMulRight, LinearMap.mulRight_apply, mul_comm] using hx.symm

/-- Helper for Lemma 15.91.14: the kernels of the principal-power multiplication maps form the
increasing system from the source proof. -/
private theorem principal_power_mulRight_ker_mono
    (f : R) {n m : ℕ+} (hnm : n ≤ m) :
    LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ)) ≤
      LinearMap.ker (principalPowerMulRight (R := R) f (m : ℕ)) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have hx0 : x * f ^ (n : ℕ) = 0 := by
    exact congrArg Subtype.val hx
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show (n : ℕ) ≤ (m : ℕ) from hnm)
  -- Proof comment: once `x * f^n = 0`, multiplying by one more power keeps the product zero.
  apply Subtype.ext
  rw [hk]
  calc
    x * f ^ ((n : ℕ) + k) = x * (f ^ (n : ℕ) * f ^ k) := by
      rw [pow_add]
    _ = (x * f ^ (n : ℕ)) * f ^ k := by rw [mul_assoc]
    _ = 0 := by simp [hx0]

/-- Helper for Lemma 15.91.14: each quotient stage `R / ker(*f^n)` is canonically `(f^n)`. -/
private noncomputable def principal_power_mulRight_quotient_equiv
    (f : R) (n : ℕ+) :
    (R ⧸ LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))) ≃ₗ[R]
      principalPowerIdeal f (n : ℕ) :=
  LinearMap.quotKerEquivOfSurjective
    (principalPowerMulRight (R := R) f (n : ℕ))
    (principalPowerMulRight_surjective (R := R) f (n : ℕ))

/-- Helper for Lemma 15.91.14: the directed union of the kernels `ker(*f^n)` is exactly the
`f^∞`-torsion submodule. -/
private theorem iSup_principal_power_mulRight_ker_eq_fPowerTorsion
    (f : R) :
    (⨆ n : ℕ+, LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))) =
      (R[f^∞] : Submodule R R) := by
  apply le_antisymm
  · intro x hx
    have hdir :
        Directed (· ≤ ·)
          (fun n : ℕ+ ↦ LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))) := by
      intro i j
      refine ⟨max i j, ?_, ?_⟩
      · exact principal_power_mulRight_ker_mono (R := R) f (le_max_left _ _)
      · exact principal_power_mulRight_ker_mono (R := R) f (le_max_right _ _)
    obtain ⟨n, hn⟩ :=
      (Submodule.mem_iSup_of_directed
        (fun n : ℕ+ ↦ LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))) hdir).mp hx
    -- Proof comment: a stage-kernel relation `x * f^n = 0` is exactly an `f`-power torsion
    -- witness.
    rw [Submodule.mem_torsion'_iff (Submonoid.powers f)]
    refine ⟨⟨f ^ (n : ℕ), ⟨(n : ℕ), rfl⟩⟩, ?_⟩
    have hn0 : x * f ^ (n : ℕ) = 0 := by
      exact congrArg Subtype.val (show principalPowerMulRight (R := R) f (n : ℕ) x = 0 by
        simpa [LinearMap.mem_ker] using hn)
    have hn0' : f ^ (n : ℕ) * x = 0 := by
      simpa [mul_comm] using hn0
    simpa [smul_eq_mul] using hn0'
  · intro x hx
    rw [Submodule.mem_torsion'_iff (Submonoid.powers f)] at hx
    rcases hx with ⟨⟨a, ⟨n, rfl⟩⟩, hx0⟩
    let q : ℕ+ := ⟨n + 1, Nat.succ_pos _⟩
    have hx0' : f ^ n * x = 0 := by
      simpa [smul_eq_mul] using hx0
    have hx1 : x * f ^ (q : ℕ) = 0 := by
      -- Proof comment: any witness `f^n • x = 0` also gives `f^(n+1) • x = 0`.
      have hx1' : f ^ (n + 1) * x = 0 := by
        calc
          f ^ (n + 1) * x = f * (f ^ n * x) := by
            rw [pow_succ', ← mul_assoc]
          _ = 0 := by simpa using congrArg (fun y : R => f * y) hx0'
      simpa [q, mul_comm, mul_left_comm, mul_assoc] using hx1'
    refine Submodule.mem_iSup_of_mem q ?_
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simpa using hx1

/-- Helper for Lemma 15.91.14: the short exact row
`0 → R[f^∞] → R → R / R[f^∞] → 0` identifies the target Tor term with the kernel of the
tensorized inclusion of the torsion submodule. -/
private noncomputable def
    tor_one_extension_quotientByFPowerTorsion_equiv_kernel_tensorized_torsion_inclusion
    (f : R) :
    let T : Submodule R R := (R[f^∞] : Submodule R R)
    Tor[R, 1](R', R ⧸ T) ≃ₗ[R]
      LinearMap.ker (T.subtype.lTensor R') := by
  intro T
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk T.subtype T.mkQ
      (fPowerTorsion_subtype_mkQ_comp_eq_zero (R := R) f)
  have hS : S.ShortExact := by
    -- Proof comment: the explicit torsion row already proved above is exactly the short exact row
    -- needed for the six-term Tor sequence.
    simpa [S, T] using (fPowerTorsion_quotient_shortExact (R := R) f)
  let U := ModuleCat.torTensorSixTermSequence (ModuleCat.of R R') hS
  have hU : U.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of R R') hS
  have hTorR :
      IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R R')).obj (ModuleCat.of R R)) := by
    -- Proof comment: the middle module of the short exact row is free of rank one, so its first
    -- Tor term vanishes.
    simpa using
      CategoryTheory.isZero_Tor_succ_of_projective
        (ModuleCat R) (ModuleCat.of R R') (ModuleCat.of R R) 0
  have hmap12 : U.map' 1 2 = 0 := hTorR.eq_of_src _ _
  have hmono23 : Mono (U.map' 2 3) := by
    -- Proof comment: exactness at the previous spot forces the next map to be mono.
    have : Mono (U.sc hU.toIsComplex 1).g := (hU.exact 1).mono_g (by simpa using hmap12)
    simpa using this
  have hExact23 : Function.Exact (U.map' 2 3).hom (U.map' 3 4).hom := by
    -- Proof comment: exactness of the six-term sequence at the Tor-to-tensor step identifies the
    -- target Tor object with a kernel object.
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (U.sc hU.toIsComplex 2)).1
        (hU.exact 2)
  have hmap34' :
      U.map' 3 4 = MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R R') S.f := by
    -- Proof comment: unfold the six-term sequence once to expose the concrete tensorized
    -- inclusion map.
    dsimp [U]
    unfold ModuleCat.torTensorSixTermSequence ComposableArrows.mk₅ ComposableArrows.mk₄
    rfl
  have hmap34 : (U.map' 3 4).hom = T.subtype.lTensor R' := by
    -- Proof comment: whiskering the torsion inclusion by `R'` is exactly the linear map
    -- `T ⊗ R' → R ⊗ R'` induced by the inclusion.
    rw [hmap34']
    change ModuleCat.Hom.hom
        (MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R R') (ModuleCat.ofHom T.subtype)) =
      T.subtype.lTensor R'
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hkernel_exact : Function.Exact (U.map' 2 3).hom (T.subtype.lTensor R') := by
    -- Proof comment: replace the abstract fourth arrow in the six-term sequence by the concrete
    -- tensorized torsion inclusion.
    simpa [hmap34] using hExact23
  have hkernel_injective : Function.Injective (U.map' 2 3).hom :=
    (ModuleCat.mono_iff_injective _).1 hmono23
  let hker :
      IsLimit
        (KernelFork.ofι
          (ModuleCat.ofHom (U.map' 2 3).hom)
          (ModuleCat.hom_ext hkernel_exact.linearMap_comp_eq_zero)) :=
    ModuleCat.isLimitKernelFork
      (ModuleCat.ofHom (U.map' 2 3).hom)
      (ModuleCat.ofHom (T.subtype.lTensor R'))
      hkernel_exact
      hkernel_injective
  -- Proof comment: compare the Tor object with the explicit kernel object produced by the
  -- tensorized torsion inclusion.
  exact
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫
      ModuleCat.kernelIsoKer (ModuleCat.ofHom (T.subtype.lTensor R'))).toLinearEquiv)

/-- Lemma 15.91.14: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the first Tor group
`Tor_1^R(R', R / R[f^\infty])` vanishes. Lean records this vanishing with the canonical owner
`IsZero` of the Tor object, with `R[f^\infty]` represented by the chapter notation for the
principal-ideal primary component. -/
theorem torOne_extension_quotientByFPowerTorsion_isZero_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    IsZero (Tor[R, 1](R', R ⧸ (R[f^∞] : Submodule R R))) := by
  -- Route correction: the earlier in-file attempt stalled while rebuilding the quotient-stage
  -- filtered-colimit model. The existing short exact row
  -- `0 → R[f^∞] → R → R / R[f^∞] → 0` already lets Lean identify the target Tor term with a
  -- kernel, so the proof closes once the tensorized torsion inclusion is known to be injective.
  let T : Submodule R R := (R[f^∞] : Submodule R R)
  let e :
      Tor[R, 1](R', R ⧸ T) ≃ₗ[R]
        LinearMap.ker (T.subtype.lTensor R') :=
    tor_one_extension_quotientByFPowerTorsion_equiv_kernel_tensorized_torsion_inclusion
      (R := R) (R' := R') f
  have hTorsionInj : Function.Injective (T.subtype.lTensor R') := by
    -- Proof comment: the Beauville-Laszlo glueing-pair hypotheses already give injectivity of the
    -- tensorized torsion inclusion.
    simpa [T] using
      (fPowerTorsion_lTensor_injective_of_glueingPair (R := R) (R' := R') f hpair)
  rw [ModuleCat.isZero_iff_subsingleton]
  have hKernelSubsingleton :
      Subsingleton (LinearMap.ker (T.subtype.lTensor R')) := by
    -- Proof comment: the torsion inclusion remains injective after tensoring with `R'`, so its
    -- kernel is the zero submodule.
    rw [LinearMap.ker_eq_bot.2 hTorsionInj]
    infer_instance
  letI : Subsingleton (LinearMap.ker (T.subtype.lTensor R')) := hKernelSubsingleton
  -- Proof comment: transport the subsingleton structure back across the explicit Tor-kernel
  -- identification.
  exact e.toEquiv.subsingleton

end

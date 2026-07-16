import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Monoidal.Tor
import stacks_proof.stacks_project.Chap10.Lemma_10_75_2
import stacks_proof.stacks_project.Chap15.Definition_15_61_1
import stacks_proof.stacks_project.Chap15.Lemma_15_89_9
import stacks_proof.stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and Tor-vanishing for principal-power ideals.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Tor[R, p](N, M)`,
  `principalPowerIdeal`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `Tor`,
  `IsZero`.
* owner abstraction: the canonical Tor object `Tor (ModuleCat R) 1` together with the chapter owner
  `IsBeauvilleLaszloGlueingPairAlong`; the source-facing ideal owner is `principalPowerIdeal`.
* primitive data: the algebra map `R → R'`, the element `f : R`, and the positive integer `n`.
* derived API: the Tor-vanishing conclusion for the principal ideal `(f^n)`.
* triage: this theorem is `source-facing`; `IsBeauvilleLaszloGlueingPairAlong`, `Tor`, and
  `principalPowerIdeal` and `IsZero` are `core/canonical`; the tensor-base-change argument from
  Lemma `15.89.9` is the supporting `bridge/view`.
-/

open scoped TensorProduct IdealPowerTorsion

/-- Helper for Lemma 15.91.13: the product `x * f^n` lies in the principal ideal `(f^n)`. -/
theorem mul_mem_principalPowerIdeal
    (f : R) (n : ℕ) (x : R) :
    x * f ^ n ∈ principalPowerIdeal f n := by
  -- Rewrite the principal-power ideal as the span of `f ^ n`, then use the obvious generator.
  rw [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr ⟨x, by simpa [mul_comm]⟩

/-- Helper for Lemma 15.91.13: multiplication by `f^n` with codomain restricted to `(f^n)`. -/
abbrev principalPowerMulRight
    (f : R) (n : ℕ) :
    R →ₗ[R] principalPowerIdeal f n :=
  LinearMap.codRestrict (principalPowerIdeal f n) (LinearMap.mulRight R (f ^ n))
    (mul_mem_principalPowerIdeal (R := R) f n)

/-- Helper for Lemma 15.91.13: the restricted multiplication map still evaluates as ordinary
multiplication by `f^n`. -/
@[simp] theorem principalPowerMulRight_apply
    (f : R) (n : ℕ) (x : R) :
    principalPowerMulRight (R := R) f n x = ⟨x * f ^ n, mul_mem_principalPowerIdeal (R := R) f n x⟩ :=
  rfl

/-- Helper for Lemma 15.91.13: every element of `(f^n)` has a preimage under multiplication by
`f^n`. -/
theorem principalPowerMulRight_surjective
    (f : R) (n : ℕ) :
    Function.Surjective (principalPowerMulRight (R := R) f n) := by
  intro y
  -- Unpack membership in `(f^n)` as divisibility by `f^n`.
  rcases
      (Ideal.mem_span_singleton.mp
        (by
          simpa [principalPowerIdeal, principalIdeal, Ideal.span_singleton_pow] using y.2)) with
    ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  simpa [principalPowerMulRight, LinearMap.mulRight_apply, mul_comm] using hx.symm

/-- Helper for Lemma 15.91.13: the source-faithful row
`0 → Ann_R(f^n) → R --(* f^n)→ (f^n) → 0` is short exact. -/
theorem principal_power_mulRight_shortExact
    (f : R) (n : ℕ+) :
    let μ := principalPowerMulRight (R := R) f (n : ℕ)
    (ShortComplex.moduleCatMk (LinearMap.ker μ).subtype μ (by
      ext x
      simpa [LinearMap.mem_ker] using x.2)).ShortExact := by
  intro μ
  -- Package the kernel inclusion and the restricted multiplication map as a short exact sequence.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa using (LinearMap.exact_subtype_ker_map μ)
  · exact (ModuleCat.mono_iff_injective _).2 (LinearMap.ker μ).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).2 (principalPowerMulRight_surjective (R := R) f (n : ℕ))

/-- Helper for Lemma 15.91.13: an element in the kernel of multiplication by `f^n` is `f`-power
torsion. -/
theorem principal_power_mulRight_ker_mem_fPowerTorsion
    (f : R) (n : ℕ+)
    (x : LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))) :
    (x : R) ∈ (R[f^∞] : Submodule R R) := by
  rcases x with ⟨x, hx⟩
  -- The defining kernel equation says `x * f^n = 0`, so `x` is killed by a power of `f`.
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f)]
  refine ⟨⟨f ^ (n : ℕ), ⟨(n : ℕ), rfl⟩⟩, ?_⟩
  have hx0 : (x : R) * f ^ (n : ℕ) = 0 := by
    simpa [LinearMap.mem_ker, principalPowerMulRight, LinearMap.mulRight_apply] using hx
  have hx0' : f ^ (n : ℕ) * x = 0 := by
    simpa [mul_comm] using hx0
  simpa [smul_eq_mul] using hx0'

/-- Helper for Lemma 15.91.13: the kernel of multiplication by `f^n` maps canonically into the
ambient `f^∞`-torsion submodule of `R`. -/
abbrev principal_power_mulRight_ker_to_fPowerTorsion
    (f : R) (n : ℕ+) :
    LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ)) →ₗ[R] (R[f^∞] : Submodule R R) :=
  ((LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))).subtype).codRestrict
    (R[f^∞] : Submodule R R)
    (principal_power_mulRight_ker_mem_fPowerTorsion (R := R) f n)

/-- Helper for Lemma 15.91.13: the kernel of multiplication by `f^n` is `(f)`-power torsion. -/
theorem ker_principal_power_mulRight_is_ideal_power_torsion
    (f : R) (n : ℕ+) :
    Module.IsIdealPowerTorsion
      (principalIdeal f)
      (LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))) := by
  -- Every kernel element is killed by the fixed power `f^n`.
  rw [Module.isIdealPowerTorsion_principalIdeal_iff]
  intro x
  rcases x with ⟨x, hx⟩
  refine ⟨⟨f ^ (n : ℕ), ⟨(n : ℕ), rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have hx0 : (x : R) * f ^ (n : ℕ) = 0 := by
    simpa [LinearMap.mem_ker, principalPowerMulRight, LinearMap.mulRight_apply] using hx
  have hx0' : f ^ (n : ℕ) * x = 0 := by
    simpa [mul_comm] using hx0
  simpa [smul_eq_mul] using hx0'

/-- Helper for Lemma 15.91.13: on generators `1 ⊗ x`, tensoring the kernel inclusion
`Ann_R(f^n) ↪ R` and then evaluating by `TensorProduct.rid` agrees with the canonical map from the
kernel into the target-side `f^∞`-torsion submodule. -/
theorem ker_principal_power_mulRight_tensor_restriction
    (f : R) (n : ℕ+)
    (x : LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))) :
    (((TensorProduct.rid R R').toLinearMap.comp
        ((LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))).subtype.lTensor R')).comp
        (TensorProduct.mk R R' (LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))) 1)) x =
      ((fPowerTorsionToExtension (algebraMap R R') f)
        (principal_power_mulRight_ker_to_fPowerTorsion (R := R) f n x) : R') := by
  -- Both routes send a generator `x` to the same element `algebraMap R R' x` of `R'`.
  simp [principal_power_mulRight_ker_to_fPowerTorsion, fPowerTorsionToExtension, Algebra.smul_def]
  rfl

/-- Helper for Lemma 15.91.13: for a glueing pair, tensoring the kernel inclusion
`Ann_R(f^n) ↪ R` with `R'` stays injective. -/
theorem ker_principal_power_mulRight_lTensor_injective_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (n : ℕ+) :
    let K := LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))
    Function.Injective (K.subtype.lTensor R') := by
  intro K
  have hquot :
      ∀ q : ℕ+, Function.Bijective
        (Ideal.quotientMap
          (((principalIdeal f) ^ (q : ℕ)).map (algebraMap R R'))
          (algebraMap R R')
          Ideal.le_comap_map) := by
    intro q
    let I : Ideal R := principalIdeal f
    let σ : R →+* R' := algebraMap R R'
    have hmap :
        Ideal.map σ (I ^ (q : ℕ)) = principalPowerIdeal (σ f) q := by
      simp [I, σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
        Set.image_singleton]
    have htransport :
        principalPowerIdealImageQuotientMap σ f q =
          (Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (q : ℕ)))
              σ
              Ideal.le_comap_map) := by
      apply Ideal.Quotient.ringHom_ext
      ext r
      dsimp [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap]
      simpa [I, principalPowerIdeal, Ideal.quotientMap_mk] using
        (Ideal.quotientEquivAlgOfEq_mk (R₁ := R) (h := hmap) (x := σ r))
    have hcomp :
        Function.Bijective
          ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (q : ℕ)))
              σ
              Ideal.le_comap_map)) := by
      have hcomp0 : Function.Bijective (principalPowerIdealImageQuotientMap σ f q) := by
        simpa [σ] using hpair.quotientMapBijective q
      rw [htransport] at hcomp0
      exact hcomp0
    constructor
    · intro x y hxy
      have hxy' :
          ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (q : ℕ)))
              σ
              Ideal.le_comap_map)) x =
            ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
              (Ideal.quotientMap
                (Ideal.map σ (I ^ (q : ℕ)))
                σ
                Ideal.le_comap_map)) y := by
        exact congrArg (Ideal.quotientEquivAlgOfEq R hmap) hxy
      exact hcomp.1 hxy'
    · intro z
      obtain ⟨x, hx⟩ := hcomp.2 ((Ideal.quotientEquivAlgOfEq R hmap) z)
      refine ⟨x, ?_⟩
      exact (Ideal.quotientEquivAlgOfEq R hmap).injective hx
  have hmk :
      Function.Bijective (TensorProduct.mk R R' K 1) :=
    tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
      (I := principalIdeal f)
      (R' := R')
      (M := K)
      (ker_principal_power_mulRight_is_ideal_power_torsion (R := R) f n)
      hquot
  have hTorsionInj :
      Function.Injective (fPowerTorsionToExtension (algebraMap R R') f) := by
    exact
      (isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsionToExtension
        (algebraMap R R')
        f
        hpair.quotientMapBijective).1 hpair |>.1
  have hkerToTorsionInj :
      Function.Injective (principal_power_mulRight_ker_to_fPowerTorsion (R := R) f n) := by
    intro x y hxy
    apply Subtype.ext
    simpa using congrArg Subtype.val hxy
  have hTensorGeneratorInj :
      Function.Injective
        ((((TensorProduct.rid R R').toLinearMap.comp (K.subtype.lTensor R')).comp
          (TensorProduct.mk R R' K 1))) := by
    -- Route correction: compare the tensorized inclusion with the Beauville-Laszlo torsion map
    -- before using the base-change bijection for the torsion module `K`.
    intro x y hxy
    exact hkerToTorsionInj <| hTorsionInj <| by
      apply Subtype.ext
      simpa [ker_principal_power_mulRight_tensor_restriction (R := R) (R' := R') f n x,
        ker_principal_power_mulRight_tensor_restriction (R := R) (R' := R') f n y,
        Algebra.smul_def] using hxy
  intro z₁ z₂ hz
  rcases hmk.2 z₁ with ⟨x₁, rfl⟩
  rcases hmk.2 z₂ with ⟨x₂, rfl⟩
  -- Apply the faithful generators `x ↦ 1 ⊗ x`, compare in `R'` via `TensorProduct.rid`, and then
  -- pull back through the bijective tensor-base-change unit.
  have hridEq :
      (((TensorProduct.rid R R').toLinearMap.comp (K.subtype.lTensor R')).comp
          (TensorProduct.mk R R' K 1)) x₁ =
        (((TensorProduct.rid R R').toLinearMap.comp (K.subtype.lTensor R')).comp
          (TensorProduct.mk R R' K 1)) x₂ := by
    simpa [LinearMap.comp_apply] using congrArg (TensorProduct.rid R R').toLinearMap hz
  have hx : x₁ = x₂ := hTensorGeneratorInj hridEq
  simpa [hx]

/-- Helper for Lemma 15.91.13: the short exact row
`0 → Ann_R(f^n) → R --(* f^n)→ (f^n) → 0` identifies the Tor term with the kernel of the
tensorized kernel inclusion. -/
noncomputable def tor_one_extension_principalPowerIdeal_equiv_kernel_tensorized_kernel_inclusion
    (f : R) (n : ℕ+) :
    let K := LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))
    Tor[R, 1](R', principalPowerIdeal f (n : ℕ)) ≃ₗ[R]
      LinearMap.ker (K.subtype.lTensor R') := by
  intro K
  let μ : R →ₗ[R] principalPowerIdeal f (n : ℕ) := principalPowerMulRight (R := R) f (n : ℕ)
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk K.subtype μ (by
      ext x
      simpa [LinearMap.mem_ker] using x.2)
  have hS : S.ShortExact := by
    -- Reuse the source-faithful short exact row already isolated above.
    simpa [S, K, μ] using (principal_power_mulRight_shortExact (R := R) f n)
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of R R') hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of R R') hS
  have hTorR :
      IsZero (((Tor (ModuleCat R) 1).obj (ModuleCat.of R R')).obj (ModuleCat.of R R)) := by
    -- The middle module is the free rank-one module `R`, hence projective.
    simpa using
      CategoryTheory.isZero_Tor_succ_of_projective
        (ModuleCat R) (ModuleCat.of R R') (ModuleCat.of R R) 0
  have hmap12 : T.map' 1 2 = 0 := hTorR.eq_of_src _ _
  have hmono23 : Mono (T.map' 2 3) := by
    -- Exactness at the previous spot identifies the Tor term with a kernel object.
    have : Mono (T.sc hT.toIsComplex 1).g := (hT.exact 1).mono_g (by simpa using hmap12)
    simpa using this
  have hExact23 : Function.Exact (T.map' 2 3).hom (T.map' 3 4).hom := by
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (T.sc hT.toIsComplex 2)).1
        (hT.exact 2)
  have hmap34' :
      T.map' 3 4 = MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R R') S.f := by
    -- Unfold the six-term sequence once to expose the concrete tensor map at stage `3 → 4`.
    dsimp [T]
    unfold ModuleCat.torTensorSixTermSequence ComposableArrows.mk₅ ComposableArrows.mk₄
    rfl
  have hmap34 : (T.map' 3 4).hom = K.subtype.lTensor R' := by
    -- After whiskering, the map is exactly `R' ⊗ K → R' ⊗ R`.
    rw [hmap34']
    change ModuleCat.Hom.hom
        (MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R R') (ModuleCat.ofHom K.subtype)) =
      K.subtype.lTensor R'
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hkernel_exact : Function.Exact (T.map' 2 3).hom (K.subtype.lTensor R') := by
    simpa [hmap34] using hExact23
  have hkernel_injective : Function.Injective (T.map' 2 3).hom :=
    (ModuleCat.mono_iff_injective _).1 hmono23
  let hker :
      IsLimit
        (KernelFork.ofι
          (ModuleCat.ofHom (T.map' 2 3).hom)
          (ModuleCat.hom_ext hkernel_exact.linearMap_comp_eq_zero)) :=
    ModuleCat.isLimitKernelFork
      (ModuleCat.ofHom (T.map' 2 3).hom)
      (ModuleCat.ofHom (K.subtype.lTensor R'))
      hkernel_exact
      hkernel_injective
  exact
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫
      ModuleCat.kernelIsoKer (ModuleCat.ofHom (K.subtype.lTensor R'))).toLinearEquiv)

-- Proof sketch: tensor the short exact sequence
-- `0 → Ann_R(f^n) → R --(* f^n)→ (f^n) → 0` with `R'`.
-- The needed exactness package is the Beauville-Laszlo glueing-pair owner
-- `IsBeauvilleLaszloGlueingPairAlong f`.
-- Under those hypotheses, the argument from the source reduces the vanishing of
-- `Tor_1^R(R', f^n R)` to injectivity on the `f^n`-torsion submodule after base change; Lemma
-- `15.89.9` identifies that base change with the original torsion submodule, and Lemma `15.91.6`
-- supplies the required injectivity for a glueing pair.
/-- Lemma 15.91.13: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then for every positive
integer `n` the first Tor group `Tor_1^R(R', f^n R)` vanishes. In Lean, `f^n R` is represented by
the chapter owner `principalPowerIdeal f n`, and vanishing is recorded by the canonical owner
`IsZero` of the Tor object. -/
@[stacks 0BNZ]
theorem torOne_extension_principalPowIdeal_isZero_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (n : ℕ+) :
    IsZero (Tor[R, 1](R', principalPowerIdeal f (n : ℕ))) := by
  let K := LinearMap.ker (principalPowerMulRight (R := R) f (n : ℕ))
  let e :
      Tor[R, 1](R', principalPowerIdeal f (n : ℕ)) ≃ₗ[R]
        LinearMap.ker (K.subtype.lTensor R') :=
    tor_one_extension_principalPowerIdeal_equiv_kernel_tensorized_kernel_inclusion
      (R := R) (R' := R') f n
  rw [ModuleCat.isZero_iff_subsingleton]
  have hKernelSubsingleton :
      Subsingleton (LinearMap.ker (K.subtype.lTensor R')) := by
    -- Once the tensorized inclusion is injective, its kernel is the zero submodule.
    rw [LinearMap.ker_eq_bot.2
      (ker_principal_power_mulRight_lTensor_injective_of_glueingPair
        (R := R) (R' := R') f hpair n)]
    infer_instance
  letI : Subsingleton (LinearMap.ker (K.subtype.lTensor R')) := hKernelSubsingleton
  exact e.toEquiv.subsingleton

end

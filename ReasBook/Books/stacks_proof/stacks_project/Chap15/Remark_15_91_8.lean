import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_97_2
import stacks_proof.stacks_project.Chap15.Definition_15_89_1
import stacks_proof.stacks_project.Chap15.Lemma_15_89_9
import stacks_proof.stacks_project.Chap15.Lemma_15_91_1
import stacks_proof.stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped IdealPowerTorsion
open scoped TensorProduct

/-
Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs for principal-adic completion, with fixed-power
  torsion as a bridge statement;
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`,
  `tensorBaseChangeUnitPrimaryComponent_bijective`,
  `Submodule.torsionBy`,
  `principalAdicCompletion`;
* owner abstraction: the chapter-level glueing-pair owner
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f`;
* primitive data: a commutative ring `R`, an element `f : R`, and flatness of
  `R → principalAdicCompletion f`;
* derived API: the induced map on `f ^ n`-torsion, its bijectivity consequences, and the resulting
  Beauville-Laszlo glueing-pair criterion.

Source/core/bridge triage:
* `source-facing`: the fixed-power torsion comparison together with the concluding
  Beauville-Laszlo glueing-pair statement in Remark `15.91.8`;
* `core/canonical`: `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`, and
  `tensorBaseChangeUnitPrimaryComponent_bijective`;
* `bridge/view`: the restricted completion map between the two torsion submodules.
-/

section

variable {R : Type u} [CommRing R]

-- Proof sketch: if `x` is killed by `f^n` in `R`, then applying the algebra map to the equality
-- `(f^n) * x = 0` shows that the image of `x` is killed by the image of `f^n` in the completion.
/-- The algebra map sends `f^n`-torsion elements of `R` to `f^n`-torsion elements of the
principal adic completion. -/
private theorem completionMap_mem_powTorsion
    (f : R) (n : ℕ) (x : (R[f ^ n] : Submodule R R)) :
    Algebra.linearMap R (principalAdicCompletion f) x ∈
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) := by
  -- Proof comment: transport the annihilating equation for `x` through the algebra map.
  have hxmem : x.1 ∈ (R[f ^ n] : Submodule R R) := x.2
  have hx0 : x.1 * f ^ n = 0 := by
    rw [Submodule.mem_torsionBy_iff] at hxmem
    simpa [smul_eq_mul, mul_comm] using hxmem
  rw [Submodule.mem_torsionBy_iff]
  have hx :
      Algebra.linearMap R (principalAdicCompletion f) (x.1 * f ^ n) = 0 := by
    simpa using congrArg (Algebra.linearMap R (principalAdicCompletion f)) hx0
  simpa [map_mul, Algebra.smul_def, smul_eq_mul, mul_comm] using hx

/-- Helper for Remark 15.91.8: an element is `f^∞`-torsion exactly when it lies in some finite
stage `f^n`-torsion submodule. -/
private theorem mem_fPowerTorsion_iff_exists_powTorsion
    {S : Type u} [CommRing S] [Algebra R S] (f : R) (x : S) :
    x ∈ (S[f^∞] : Submodule R S) ↔ ∃ n : ℕ, x ∈ (S[f ^ n] : Submodule R S) := by
  constructor
  · intro hx
    rw [Submodule.mem_torsion'_iff] at hx
    rcases hx with ⟨⟨a, ha⟩, hx⟩
    rcases (Submonoid.mem_powers_iff a f).mp ha with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simpa [Submodule.mem_torsionBy_iff] using hx
  · rintro ⟨n, hx⟩
    rw [Submodule.mem_torsion'_iff]
    rw [Submodule.mem_torsionBy_iff] at hx
    exact ⟨⟨f ^ n, ⟨n, rfl⟩⟩, by simpa using hx⟩

/-- The canonical map from the `f^n`-torsion of `R` to the `f^n`-torsion of its principal adic
completion. -/
abbrev powTorsionToPrincipalAdicCompletion (f : R) (n : ℕ) :
    (R[f ^ n] : Submodule R R) →ₗ[R]
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) :=
  ((Algebra.linearMap R (principalAdicCompletion f)).domRestrict
      (R[f ^ n] : Submodule R R)).codRestrict
    ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f))
    (completionMap_mem_powTorsion f n)

/-- Helper for Remark 15.91.8: the positive-stage quotient comparison from Lemma `15.91.1`
rewrites to the generic `Ideal.quotientMap` family required by Lemma `15.89.9`. -/
private theorem principalIdeal_power_quotientMap_bijective_of_completion
    (f : R) :
    ∀ q : ℕ+, Function.Bijective
      (Ideal.quotientMap
        (((principalIdeal f) ^ (q : ℕ)).map (algebraMap R (principalAdicCompletion f)))
        (algebraMap R (principalAdicCompletion f))
        Ideal.le_comap_map) := by
  intro q
  let I : Ideal R := principalIdeal f
  let σ : R →+* principalAdicCompletion f := algebraMap R (principalAdicCompletion f)
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
    -- Compare the principal-power quotient owner with the generic quotient map via the target
    -- quotient equivalence.
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
    have hcomp0 :
        Function.Bijective (principalPowerIdealImageQuotientMap σ f q) := by
      simpa [σ] using principalAdicCompletion_quotientMap_bijective (R := R) f q
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

/-- Helper for Remark 15.91.8: the source-facing sequence
`0 → R[f^n] → R --(* f^n)→ R` is exact. -/
private theorem pow_torsion_subtype_exact_mulRight
    (f : R) (n : ℕ) :
    Function.Exact
      (Submodule.subtype (R[f ^ n] : Submodule R R))
      (LinearMap.mulRight R (f ^ n)) := by
  -- Identify the kernel of multiplication by `f^n` with the finite-stage torsion submodule.
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_range]
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [Submodule.mem_torsionBy_iff]
    simpa [LinearMap.mem_ker, LinearMap.mulRight_apply, smul_eq_mul, mul_comm] using hx
  · rintro ⟨x, rfl⟩
    have hxmem : x.1 ∈ (R[f ^ n] : Submodule R R) := x.2
    have hx : x.1 * f ^ n = 0 := by
      rw [Submodule.mem_torsionBy_iff] at hxmem
      simpa [smul_eq_mul, mul_comm] using hxmem
    rw [LinearMap.mem_ker]
    simpa [LinearMap.mulRight_apply] using hx

/-- Helper for Remark 15.91.8: the module `R[f^n]` is `(f)`-power torsion. -/
private theorem pow_torsion_isIdealPowerTorsion
    (f : R) (n : ℕ) :
    Module.IsIdealPowerTorsion (principalIdeal f) (R[f ^ n] : Submodule R R) := by
  -- Every element is killed by the fixed power `f^n`, so the whole module is `(f)`-power
  -- torsion.
  rw [Module.isIdealPowerTorsion_principalIdeal_iff]
  intro x
  refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
  have hxmem : x.1 ∈ (R[f ^ n] : Submodule R R) := x.2
  have hx : x.1 * f ^ n = 0 := by
    rw [Submodule.mem_torsionBy_iff] at hxmem
    simpa [smul_eq_mul, mul_comm] using hxmem
  change ((f ^ n : R) • x) = 0
  apply Subtype.ext
  simpa [smul_eq_mul, mul_comm] using hx

/-- Helper for Remark 15.91.8: on the completion, the kernel of multiplication by `f^n` is the
finite-stage torsion submodule. -/
private theorem principalAdicCompletion_mulRight_ker_eq_pow_torsion
    (f : R) (n : ℕ) :
    LinearMap.ker (LinearMap.mulRight R (algebraMap R (principalAdicCompletion f) (f ^ n))) =
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) := by
  -- Rewrite both sides as the same annihilation condition.
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_torsionBy_iff]
  simp [LinearMap.mulRight_apply, Algebra.smul_def, mul_comm]

/-- Helper for Remark 15.91.8: tensoring the finite-stage torsion submodule with the completion
lands in the finite-stage torsion submodule of the completion. -/
private theorem principalAdicCompletionTensorToPowTorsion_mem
    (f : R) (n : ℕ)
    (z : principalAdicCompletion f ⊗[R] (R[f ^ n] : Submodule R R)) :
    ((TensorProduct.rid R (principalAdicCompletion f)).toLinearMap
        (((Submodule.subtype (R[f ^ n] : Submodule R R)).lTensor
          (principalAdicCompletion f)) z)) ∈
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) := by
  -- Check the annihilation relation on pure tensors and extend by linearity.
  rw [Submodule.mem_torsionBy_iff]
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro z x
    have hxmem : x.1 ∈ (R[f ^ n] : Submodule R R) := x.2
    have hx : x.1 * f ^ n = 0 := by
      rw [Submodule.mem_torsionBy_iff] at hxmem
      simpa [smul_eq_mul, mul_comm] using hxmem
    have hx' : (f ^ n : R) • (x.1 • z) = 0 := by
      simpa [smul_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun r : R => r • z) hx
    simpa [TensorProduct.rid_tmul, LinearMap.lTensor_tmul] using hx'
  · intro z₁ z₂ hz₁ hz₂
    have hz :
        (f ^ n : R) •
            (((TensorProduct.rid R (principalAdicCompletion f)).toLinearMap
                  (((Submodule.subtype (R[f ^ n] : Submodule R R)).lTensor
                    (principalAdicCompletion f)) z₁)) +
              ((TensorProduct.rid R (principalAdicCompletion f)).toLinearMap
                (((Submodule.subtype (R[f ^ n] : Submodule R R)).lTensor
                  (principalAdicCompletion f)) z₂))) = 0 := by
      rw [smul_add, hz₁, hz₂]
      simp
    simpa [map_add] using hz

/-- Helper for Remark 15.91.8: the tensorized inclusion of `R[f^n]` into `R` followed by
`TensorProduct.rid` is the canonical map to `R^∧[f^n]`. -/
private abbrev principalAdicCompletionTensorToPowTorsion
    (f : R) (n : ℕ) :
    principalAdicCompletion f ⊗[R] (R[f ^ n] : Submodule R R) →ₗ[R]
      ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) :=
  (((TensorProduct.rid R (principalAdicCompletion f)).toLinearMap).comp
      ((Submodule.subtype (R[f ^ n] : Submodule R R)).lTensor
        (principalAdicCompletion f))).codRestrict
    ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f))
    (principalAdicCompletionTensorToPowTorsion_mem f n)

/-- Helper for Remark 15.91.8: on tensors of the form `1 ⊗ x`, the tensor-side map is exactly the
restricted completion map on finite-stage torsion. -/
@[simp] private theorem principalAdicCompletionTensorToPowTorsion_apply_mk
    (f : R) (n : ℕ) (x : (R[f ^ n] : Submodule R R)) :
    principalAdicCompletionTensorToPowTorsion f n
        (TensorProduct.mk R (principalAdicCompletion f) (R[f ^ n] : Submodule R R) 1 x) =
      powTorsionToPrincipalAdicCompletion f n x := by
  -- Both maps evaluate to the image of `x` under the completion algebra map.
  apply Subtype.ext
  simp [principalAdicCompletionTensorToPowTorsion, powTorsionToPrincipalAdicCompletion,
    Algebra.smul_def]

/-- Helper for Remark 15.91.8: flatness identifies the tensor product
`R^∧ ⊗[R] R[f^n]` with `R^∧[f^n]`. -/
private theorem principalAdicCompletion_tensor_pow_torsion_bijective_of_flat
    (f : R)
    (hflat : (algebraMap R (principalAdicCompletion f)).Flat)
    (n : ℕ) :
    Function.Bijective (principalAdicCompletionTensorToPowTorsion f n) := by
  let C := principalAdicCompletion f
  let S : Submodule R R := (R[f ^ n] : Submodule R R)
  let ι : S →ₗ[R] R := Submodule.subtype S
  let μ : R →ₗ[R] R := LinearMap.mulRight R (f ^ n)
  let _ : Module.Flat R C := RingHom.flat_algebraMap_iff.mp hflat
  have hιTensorInj : Function.Injective (ι.lTensor C) := by
    -- Flatness preserves injectivity of the torsion-submodule inclusion.
    simpa [ι] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := C) ι S.injective_subtype
  have hTensorExact : Function.Exact (ι.lTensor C) (μ.lTensor C) := by
    -- Tensor the source exact sequence `0 → R[f^n] → R → R` with the flat completion.
    simpa [ι, μ] using
      Module.Flat.lTensor_exact (R := R) C (pow_torsion_subtype_exact_mulRight f n)
  constructor
  · intro x y hxy
    -- Forget the codomain restriction and use injectivity of the tensorized inclusion.
    apply hιTensorInj
    apply (TensorProduct.rid R C).injective
    simpa [principalAdicCompletionTensorToPowTorsion, ι] using congrArg Subtype.val hxy
  · intro y
    have hy : (f ^ n : R) • (y : C) = 0 := by
      simpa [Submodule.mem_torsionBy_iff] using y.2
    have hyKer :
        (TensorProduct.rid R C).symm (y : C) ∈ LinearMap.ker (μ.lTensor C) := by
      -- Transport the torsion equation for `y` back across `TensorProduct.rid`.
      rw [LinearMap.mem_ker]
      apply (TensorProduct.rid R C).injective
      simpa [μ, LinearMap.mulRight_apply] using hy
    have hyRange :
        (TensorProduct.rid R C).symm (y : C) ∈ LinearMap.range (ι.lTensor C) := by
      rw [(LinearMap.exact_iff.1 hTensorExact)] at hyKer
      exact hyKer
    rcases hyRange with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    simpa [principalAdicCompletionTensorToPowTorsion, ι] using
      congrArg (TensorProduct.rid R C) hz

-- Proof sketch: tensor the exact sequence `0 → R[f^n] → R → R` with the flat completion
-- `principalAdicCompletion f`. Flatness preserves exactness, so the tensor product identifies with
-- the kernel of multiplication by `f^n` on the completion. Apply
-- `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective` with
-- `R' = principalAdicCompletion f`, using `principalAdicCompletion_quotientMap_bijective` to
-- discharge the quotient-map hypothesis, to identify `R[f^n]` with that tensor product.
/-- Remark 15.91.8: if the canonical map from `R` to its `(f)`-adic completion is flat, then for
every natural number `n` the induced map `R[f^n] → R^∧[f^n]` is bijective; this source-faithful
statement is generalized from positive `n` by the canonical trivial case `n = 0`. -/
@[stacks 0BNT]
theorem powTorsionToPrincipalAdicCompletion_bijective_of_flat
    (f : R)
    (hflat : (algebraMap R (principalAdicCompletion f)).Flat)
    (n : ℕ) :
    Function.Bijective (powTorsionToPrincipalAdicCompletion f n) := by
  let C := principalAdicCompletion f
  let S : Submodule R R := (R[f ^ n] : Submodule R R)
  -- Route correction: avoid the broken `15.90.3` import surface and follow the textbook finite
  -- exact-sequence argument directly inside this file.
  have hunit :
      Function.Bijective (TensorProduct.mk R C S 1) := by
    -- Lemma `15.89.9` identifies `R[f^n]` with its base change once the completion quotient maps
    -- are rewritten into the generic `Ideal.quotientMap` form.
    exact
      tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
        (I := principalIdeal f)
        (R' := C)
        (M := S)
        (pow_torsion_isIdealPowerTorsion f n)
        (principalIdeal_power_quotientMap_bijective_of_completion (R := R) f)
  have htensor :
      Function.Bijective (principalAdicCompletionTensorToPowTorsion f n) :=
    principalAdicCompletion_tensor_pow_torsion_bijective_of_flat f hflat n
  constructor
  · intro x y hxy
    -- Compare `x` and `y` after the two bijective transitions through the tensor product.
    have hxyTensor :
        principalAdicCompletionTensorToPowTorsion f n (TensorProduct.mk R C S 1 x) =
          principalAdicCompletionTensorToPowTorsion f n (TensorProduct.mk R C S 1 y) := by
      rw [principalAdicCompletionTensorToPowTorsion_apply_mk,
        principalAdicCompletionTensorToPowTorsion_apply_mk]
      exact hxy
    exact hunit.1 (htensor.1 hxyTensor)
  · intro y
    -- First lift `y` through the tensor/completion identification, then pull that tensor back to
    -- an element of `R[f^n]` using Lemma `15.89.9`.
    obtain ⟨z, hz⟩ := htensor.2 y
    rcases hunit.2 z with ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    rw [principalAdicCompletionTensorToPowTorsion_apply_mk] at hz
    exact hz

-- Proof sketch: the chapter owner theorem
-- `principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion`
-- reduces the Beauville-Laszlo condition to bijectivity on `f^∞`-torsion, and the finite-stage
-- bijections proved just above assemble to the required infinite-stage bijection.
/-- Remark 15.91.8: if the canonical map from `R` to its `(f)`-adic completion is flat, then
`(R, f)` is a Beauville-Laszlo glueing pair. -/
@[stacks 0BNT]
theorem isBeauvilleLaszloGlueingPair_of_flat
    (f : R)
    (hflat : (algebraMap R (principalAdicCompletion f)).Flat) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  -- Proof comment: an `f^∞`-torsion element is killed by some finite power, so the finite-stage
  -- bijections just proved assemble directly into bijectivity on `f^∞`-torsion.
  rw [principalAdicCompletion_isBeauvilleLaszloGlueingPairAlong_iff_bijective_fPowerTorsion]
  constructor
  · intro x y hxy
    obtain ⟨nx, hx⟩ :=
      (mem_fPowerTorsion_iff_exists_powTorsion (R := R) (S := R) f (x : R)).1 x.2
    obtain ⟨ny, hy⟩ :=
      (mem_fPowerTorsion_iff_exists_powTorsion (R := R) (S := R) f (y : R)).1 y.2
    let m := max nx ny
    have hxm : (x : R) ∈ (R[f ^ m] : Submodule R R) := by
      exact
        (Submodule.torsionBy_le_torsionBy_of_dvd
          (f ^ nx) (f ^ m) (pow_dvd_pow f (Nat.le_max_left _ _))) hx
    have hym : (y : R) ∈ (R[f ^ m] : Submodule R R) := by
      exact
        (Submodule.torsionBy_le_torsionBy_of_dvd
          (f ^ ny) (f ^ m) (pow_dvd_pow f (Nat.le_max_right _ _))) hy
    let x' : (R[f ^ m] : Submodule R R) := ⟨x, hxm⟩
    let y' : (R[f ^ m] : Submodule R R) := ⟨y, hym⟩
    have hxy' :
        powTorsionToPrincipalAdicCompletion f m x' =
          powTorsionToPrincipalAdicCompletion f m y' := by
      apply Subtype.ext
      simpa [powTorsionToPrincipalAdicCompletion, fPowerTorsionToExtension] using
        congrArg Subtype.val hxy
    have hstage : x' = y' :=
      (powTorsionToPrincipalAdicCompletion_bijective_of_flat f hflat m).injective hxy'
    apply Subtype.ext
    have hxy0 : (x : R) = (y : R) := by
      simpa [x', y'] using congrArg (fun z : (R[f ^ m] : Submodule R R) => (z : R)) hstage
    exact hxy0
  · intro y
    obtain ⟨n, hy⟩ :=
      (mem_fPowerTorsion_iff_exists_powTorsion
        (R := R)
        (S := principalAdicCompletion f)
        f
        (y : principalAdicCompletion f)).1 y.2
    let y' :
        ((principalAdicCompletion f)[f ^ n] : Submodule R (principalAdicCompletion f)) :=
      ⟨y, hy⟩
    rcases
        (powTorsionToPrincipalAdicCompletion_bijective_of_flat f hflat n).surjective y' with
      ⟨x', hx'⟩
    refine ⟨⟨x', ?_⟩, ?_⟩
    · exact
        (mem_fPowerTorsion_iff_exists_powTorsion (R := R) (S := R) f (x' : R)).2
          ⟨n, x'.2⟩
    · apply Subtype.ext
      simpa [powTorsionToPrincipalAdicCompletion, fPowerTorsionToExtension] using
        congrArg Subtype.val hx'

-- Proof sketch: for a Noetherian ring, Algebra Lemma `10.97.2` gives flatness of the canonical
-- map `R → principalAdicCompletion f`. Applying the previous theorem supplies the bijectivity for
-- each natural number `n`.
/-- Over a Noetherian ring, the map on `f^n`-torsion from `R` to its `(f)`-adic completion is
bijective for every natural number `n`. -/
theorem powTorsionToPrincipalAdicCompletion_bijective_of_isNoetherianRing
    [IsNoetherianRing R] (f : R) (n : ℕ) :
    Function.Bijective (powTorsionToPrincipalAdicCompletion f n) := by
  simpa using powTorsionToPrincipalAdicCompletion_bijective_of_flat f
    (adicCompletion_algebraMap_flat (Ideal.span ({f} : Set R))) n

-- Proof sketch: for Noetherian `R`, Lemma `10.97.2` gives flatness of the completion map, and the
-- previous theorem upgrades this to the canonical Beauville-Laszlo owner statement.
/-- In particular, if `R` is Noetherian, then `(R, f)` is a Beauville-Laszlo glueing pair. -/
theorem isBeauvilleLaszloGlueingPair_of_isNoetherianRing
    [IsNoetherianRing R] (f : R) :
    IsBeauvilleLaszloGlueingPairAlong (algebraMap R (principalAdicCompletion f)) f := by
  simpa using isBeauvilleLaszloGlueingPair_of_flat f
    (adicCompletion_algebraMap_flat (Ideal.span ({f} : Set R)))

end

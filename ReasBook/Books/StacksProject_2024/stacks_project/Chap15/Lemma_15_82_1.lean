import Mathlib
import StacksProject_2024.Chap13.Lemma_13_12_1
import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open Polynomial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "ev0" => Polynomial.evalRingHom (0 : R)

/-- Helper for Lemma 15.82.1: if `p * X = 0` in `R[X]`, then `p = 0`. -/
private theorem polynomial_eq_zero_of_mul_X_eq_zero {p : R[X]} (h : p * X = 0) :
    p = 0 := by
  -- Compare the coefficient of `X^(n + 1)` to recover each coefficient of `p`.
  ext n
  simpa [h] using (Polynomial.coeff_mul_X p n).symm

/-- Helper for Lemma 15.82.1: multiplication by `X` on `R[X]` is injective. -/
private theorem mul_X_injective :
    Function.Injective (LinearMap.mulRight (R[X]) (X : R[X])) := by
  intro p q hpq
  have hsub : (LinearMap.mulRight (R[X]) X) (p - q) = 0 := by
    rw [LinearMap.map_sub, hpq, sub_self]
  have hzero : p - q = 0 := by
    apply polynomial_eq_zero_of_mul_X_eq_zero
    simpa [LinearMap.mulRight_apply] using hsub
  exact sub_eq_zero.mp hzero

/-- Helper for Lemma 15.82.1: the sequence of underlying functions
`R[X] --(·X)--> R[X] --ev₀--> R` is exact. -/
private theorem evalAtZero_exact_mul_X :
    Function.Exact (fun p : R[X] ↦ p * X) (fun p : R[X] ↦ ev0 p) := by
  -- Proof comment: evaluation at `0` kills every multiple of `X`, and a polynomial vanishing at
  -- `0` is divisible by `X`.
  intro p
  constructor
  · intro hp
    have hroot : p.IsRoot 0 := (Polynomial.IsRoot.def).2 hp
    obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).2 hroot
    refine ⟨q, ?_⟩
    calc
      q * X = X * q := by
        rw [mul_comm]
      _ = p := by
        simpa using hq.symm
  · rintro ⟨q, rfl⟩
    simp [map_mul]

/-- Helper for Lemma 15.82.1: evaluation at `0` on `R[X]` is surjective. -/
private theorem evalAtZero_surjective :
    Function.Surjective (fun p : R[X] ↦ ev0 p) := by
  -- Proof comment: every element of `R` is the evaluation of the corresponding constant
  -- polynomial.
  intro r
  refine ⟨Polynomial.C r, ?_⟩
  simp

/-- Helper for Lemma 15.82.1: the underlying `R`-linear map `R[X] → R[X]` given by
multiplication by `X`. -/
private abbrev polynomial_mulX_linear :
    R[X] →ₗ[R] R[X] :=
  (LinearMap.mulRight (R[X]) (X : R[X])).restrictScalars R

/-- Helper for Lemma 15.82.1: the underlying `R`-linear evaluation map `R[X] → R` at `X = 0`. -/
private abbrev polynomial_evalAtZero_linear :
    R[X] →ₗ[R] R where
  toFun := ev0
  map_add' := map_add ev0
  map_smul' := fun r p ↦ by
    simp [Algebra.smul_def, map_mul]

/-- Helper for Lemma 15.82.1: the tensor map induced by multiplication by `X` on the polynomial
factor. -/
private noncomputable abbrev tensor_polynomial_mulX_hom
    (M : ModuleCat R) :
    ModuleCat.of R (TensorProduct R R[X] (M : Type u)) ⟶
      ModuleCat.of R (TensorProduct R R[X] (M : Type u)) :=
  ModuleCat.ofHom <|
    LinearMap.rTensor (M : Type u) (polynomial_mulX_linear (R := R))

/-- Helper for Lemma 15.82.1: tensoring `ev₀ : R[X] → R` with `M`, then collapsing
`R ⊗[R] M ≅ M`. -/
private noncomputable abbrev tensor_polynomial_evalAtZero_hom
    (M : ModuleCat R) :
    ModuleCat.of R (TensorProduct R R[X] (M : Type u)) ⟶ M :=
  ModuleCat.ofHom <|
    (TensorProduct.lid R (M : Type u)).toLinearMap.comp
      (LinearMap.rTensor (M : Type u) (polynomial_evalAtZero_linear (R := R)))

/-- Helper for Lemma 15.82.1: the underlying tensor row
`R[X] ⊗[R] M --·X--> R[X] ⊗[R] M --ev₀--> M`
forms a short complex of `R`-modules. -/
private noncomputable abbrev tensor_polynomial_mulX_shortComplex
    (M : ModuleCat R) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (tensor_polynomial_mulX_hom (R := R) M)
    (tensor_polynomial_evalAtZero_hom (R := R) M)
    (by
      -- Proof comment: evaluation at `0` kills the `X`-multiple on every pure tensor.
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp
      · intro p m
        change ev0 (p * X) • m = 0
        rw [map_mul]
        simp
      · intro x y hx hy
        calc
          (ModuleCat.Hom.hom (tensor_polynomial_mulX_hom M ≫ tensor_polynomial_evalAtZero_hom M))
              (x + y)
              =
            (ModuleCat.Hom.hom (tensor_polynomial_mulX_hom M ≫ tensor_polynomial_evalAtZero_hom M))
                x +
              (ModuleCat.Hom.hom (tensor_polynomial_mulX_hom M ≫ tensor_polynomial_evalAtZero_hom M))
                y := by
                  simp [LinearMap.comp_apply, LinearMap.map_add]
          _ = 0 := by rw [hx, hy]; simp)

/-- Helper for Lemma 15.82.1: tensoring the exact polynomial row with a flat `R`-module `M`
produces a short exact row of `R`-modules on the underlying tensor products. -/
private theorem tensor_polynomial_mulX_shortExact_evalAtZero
    (M : ModuleCat R) [Module.Flat R M] :
    (tensor_polynomial_mulX_shortComplex (R := R) M).ShortExact := by
  let f₀ : TensorProduct R R[X] (M : Type u) →ₗ[R] TensorProduct R R[X] (M : Type u) :=
    LinearMap.rTensor (M : Type u) (polynomial_mulX_linear (R := R))
  let g₀ : TensorProduct R R[X] (M : Type u) →ₗ[R] TensorProduct R R (M : Type u) :=
    LinearMap.rTensor (M : Type u) (polynomial_evalAtZero_linear (R := R))
  have hExactBase :
      Function.Exact (polynomial_mulX_linear (R := R)) (polynomial_evalAtZero_linear (R := R)) := by
    simpa [polynomial_mulX_linear, polynomial_evalAtZero_linear, LinearMap.mulRight_apply] using
      (evalAtZero_exact_mul_X (R := R))
  have hTensorExact : Function.Exact f₀ g₀ := by
    simpa [f₀, g₀] using
      (Module.Flat.rTensor_exact (M := (M : Type u)) hExactBase)
  have hMulXInjective :
      Function.Injective (polynomial_mulX_linear (R := R)) := by
    simpa [polynomial_mulX_linear] using (mul_X_injective (R := R))
  have hTensorInjective : Function.Injective f₀ := by
    simpa [f₀] using
      (Module.Flat.rTensor_preserves_injective_linearMap
        (M := (M : Type u)) (polynomial_mulX_linear (R := R)) hMulXInjective)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro z
    constructor
    · intro hz
      have hz0 : g₀ z = 0 := by
        apply (TensorProduct.lid R (M : Type u)).injective
        simpa [g₀, tensor_polynomial_evalAtZero_hom] using hz
      rcases (hTensorExact z).1 hz0 with ⟨w, hw⟩
      exact ⟨w, by simpa [f₀, tensor_polynomial_mulX_hom] using hw⟩
    · rintro ⟨w, hw⟩
      have hw0 : f₀ w = z := by
        simpa [f₀, tensor_polynomial_mulX_hom] using hw
      have hz0 : g₀ z = 0 := (hTensorExact z).2 ⟨w, hw0⟩
      simp [g₀, tensor_polynomial_evalAtZero_hom, hz0]
  · refine (ModuleCat.mono_iff_injective _).2 ?_
    intro x y hxy
    apply hTensorInjective
    simpa [f₀, tensor_polynomial_mulX_hom] using hxy
  · refine (ModuleCat.epi_iff_surjective _).2 ?_
    intro m
    refine ⟨(1 : R[X]) ⊗ₜ[R] (m : M), ?_⟩
    -- Proof comment: `1 ⊗ m` evaluates to `m` because `ev₀(1) = 1`.
    simp [tensor_polynomial_evalAtZero_hom]

/-- Helper for Lemma 15.82.1: multiplication by `X` on the tensor model
`R[X] ⊗[R] M` as an `R[X]`-module. -/
private noncomputable abbrev tensor_polynomial_mulX_hom_over_polynomial
    (M : ModuleCat R) :
    ModuleCat.of R[X] (TensorProduct R R[X] (M : Type u)) ⟶
      ModuleCat.of R[X] (TensorProduct R R[X] (M : Type u)) :=
  ModuleCat.ofHom
    (LinearMap.lsmul R[X] (TensorProduct R R[X] (M : Type u)) (X : R[X]))

/-- Helper for Lemma 15.82.1: the identity map from `M` to its restriction of scalars along
`ev₀`, viewed as an `R`-linear map. -/
private noncomputable abbrev restricted_evalAtZero_identity_linear
    (M : ModuleCat R) :
    (M : Type u) →ₗ[R] ↑((ModuleCat.restrictScalars ev0).obj M) where
  toFun := fun m ↦ m
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- Helper for Lemma 15.82.1: the underlying `R`-linear evaluation map from the tensor model to
the restricted target module. -/
private noncomputable abbrev tensor_polynomial_evalAtZero_linear_raw
    (M : ModuleCat R) :
    TensorProduct R R[X] (M : Type u) →ₗ[R] ↑((ModuleCat.restrictScalars ev0).obj M) :=
  (restricted_evalAtZero_identity_linear (R := R) M).comp
    (tensor_polynomial_evalAtZero_hom (R := R) M).hom

/-- Helper for Lemma 15.82.1: the raw evaluation map on a pure tensor is `ev₀(p) • m`. -/
private theorem tensor_polynomial_evalAtZero_linear_raw_tmul
    (M : ModuleCat R) (p : R[X]) (m : M) :
    tensor_polynomial_evalAtZero_linear_raw (R := R) M (p ⊗ₜ[R] (m : M)) = ev0 p • (m : M) := by
  -- Proof comment: the raw map is just the earlier `R`-linear evaluation map, followed by the
  -- identity on the underlying module of the restricted target.
  change (tensor_polynomial_evalAtZero_hom (R := R) M).hom (p ⊗ₜ[R] (m : M)) = ev0 p • (m : M)
  simp [tensor_polynomial_evalAtZero_hom, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

/-- Helper for Lemma 15.82.1: the raw evaluation map is `R[X]`-linear with respect to the
restricted scalar action on the target. -/
private theorem tensor_polynomial_evalAtZero_linear_raw_map_smul
    (M : ModuleCat R) (p : R[X]) (z : TensorProduct R R[X] (M : Type u)) :
    tensor_polynomial_evalAtZero_linear_raw (R := R) M (p • z) =
      p • tensor_polynomial_evalAtZero_linear_raw (R := R) M z := by
  -- Proof comment: the `R[X]`-action on the tensor product is through the polynomial factor, so
  -- the pure-tensor computation reduces to `ev₀ (p * q) = ev₀ p * ev₀ q`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro q m
    rw [TensorProduct.smul_tmul']
    rw [tensor_polynomial_evalAtZero_linear_raw_tmul, tensor_polynomial_evalAtZero_linear_raw_tmul]
    simp [map_mul, smul_smul]
  · intro x y hx hy
    calc
      tensor_polynomial_evalAtZero_linear_raw (R := R) M (p • (x + y))
          =
        tensor_polynomial_evalAtZero_linear_raw (R := R) M (p • x + p • y) := by
            rw [smul_add]
      _ =
        tensor_polynomial_evalAtZero_linear_raw (R := R) M (p • x) +
          tensor_polynomial_evalAtZero_linear_raw (R := R) M (p • y) := by
            rw [(tensor_polynomial_evalAtZero_linear_raw (R := R) M).map_add]
      _ = p • tensor_polynomial_evalAtZero_linear_raw (R := R) M x +
            p • tensor_polynomial_evalAtZero_linear_raw (R := R) M y := by
            rw [hx, hy]
      _ = p •
            (tensor_polynomial_evalAtZero_linear_raw (R := R) M x +
              tensor_polynomial_evalAtZero_linear_raw (R := R) M y) := by
            rw [smul_add]
      _ = p • tensor_polynomial_evalAtZero_linear_raw (R := R) M (x + y) := by
            rw [(tensor_polynomial_evalAtZero_linear_raw (R := R) M).map_add]

/-- Helper for Lemma 15.82.1: evaluation at `X = 0` on the tensor model
`R[X] ⊗[R] M`, viewed as an `R[X]`-linear map to the restricted module `M`. -/
private noncomputable abbrev tensor_polynomial_evalAtZero_hom_over_polynomial
    (M : ModuleCat R) :
    ModuleCat.of R[X] (TensorProduct R R[X] (M : Type u)) ⟶
      (ModuleCat.restrictScalars ev0).obj M :=
  show ModuleCat.of R[X] (TensorProduct R R[X] (M : Type u)) ⟶
      ModuleCat.of R[X] ↑((ModuleCat.restrictScalars ev0).obj M) from
    ModuleCat.ofHom <|
      (show TensorProduct R R[X] (M : Type u) →ₗ[R[X]] ↑((ModuleCat.restrictScalars ev0).obj M) from
      { toFun := fun z ↦
          ((tensor_polynomial_evalAtZero_hom (R := R) M).hom z :
            ↑((ModuleCat.restrictScalars ev0).obj M))
        map_add' := fun x y ↦ (tensor_polynomial_evalAtZero_hom (R := R) M).hom.map_add x y
        map_smul' := tensor_polynomial_evalAtZero_linear_raw_map_smul (R := R) M })

/-- Helper for Lemma 15.82.1: the `R[X]`-linear tensor multiplication map agrees pointwise with
the previously proved `R`-linear tensor multiplication map. -/
private theorem tensor_polynomial_mulX_hom_over_polynomial_apply
    (M : ModuleCat R) (z : TensorProduct R R[X] (M : Type u)) :
    (tensor_polynomial_mulX_hom_over_polynomial (R := R) M).hom z =
      (tensor_polynomial_mulX_hom (R := R) M).hom z := by
  -- Proof comment: both maps are `R[X]`-multiplication by `X` on the left tensor factor, so
  -- they agree on pure tensors and hence on the whole tensor product.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensor_polynomial_mulX_hom_over_polynomial, tensor_polynomial_mulX_hom]
  · intro p m
    change (X * p) ⊗ₜ[R] (m : M) = (p * X) ⊗ₜ[R] (m : M)
    simp [mul_comm]
  · intro x y hx hy
    calc
      (tensor_polynomial_mulX_hom_over_polynomial (R := R) M).hom (x + y)
          =
        (tensor_polynomial_mulX_hom_over_polynomial (R := R) M).hom x +
          (tensor_polynomial_mulX_hom_over_polynomial (R := R) M).hom y := by
            simp
      _ =
        (tensor_polynomial_mulX_hom (R := R) M).hom x +
          (tensor_polynomial_mulX_hom (R := R) M).hom y := by
            rw [hx, hy]
      _ = (tensor_polynomial_mulX_hom (R := R) M).hom (x + y) := by
            simp

/-- Helper for Lemma 15.82.1: the `R[X]`-linear evaluation map on the tensor model agrees
pointwise with the previously proved `R`-linear evaluation map. -/
private theorem tensor_polynomial_evalAtZero_hom_over_polynomial_apply
    (M : ModuleCat R) (z : TensorProduct R R[X] (M : Type u)) :
    (tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) M).hom z =
      (tensor_polynomial_evalAtZero_hom (R := R) M).hom z := by
  -- Proof comment: the new owner morphism was defined using exactly the same underlying function
  -- as the earlier `R`-linear evaluation map, only with the restricted `R[X]`-module codomain.
  simp [tensor_polynomial_evalAtZero_hom_over_polynomial]

/-- Helper for Lemma 15.82.1: in the tensor `R[X]`-module model, evaluation at `0` kills the
`X`-multiple map. -/
private theorem tensor_polynomial_mulX_comp_evalAtZero_over_polynomial
    (M : ModuleCat R) :
    tensor_polynomial_mulX_hom_over_polynomial (R := R) M ≫
      tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) M = 0 := by
  -- Proof comment: after evaluating both owner maps on an element, this is exactly the earlier
  -- vanishing of the underlying `R`-linear tensor row.
  apply ModuleCat.hom_ext
  ext z
  have hzero :
      (tensor_polynomial_evalAtZero_hom (R := R) M).hom
        ((tensor_polynomial_mulX_hom (R := R) M).hom z) = 0 :=
    LinearMap.congr_fun
      (congrArg ModuleCat.Hom.hom ((tensor_polynomial_mulX_shortComplex (R := R) M).zero)) z
  calc
    (tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) M).hom
        ((tensor_polynomial_mulX_hom_over_polynomial (R := R) M).hom z)
        =
      (tensor_polynomial_evalAtZero_hom (R := R) M).hom
        ((tensor_polynomial_mulX_hom (R := R) M).hom z) := by
          rw [tensor_polynomial_mulX_hom_over_polynomial_apply,
            tensor_polynomial_evalAtZero_hom_over_polynomial_apply]
    _ = 0 := hzero

/-- Helper for Lemma 15.82.1: the tensor-model row
`R[X] ⊗[R] M --·X--> R[X] ⊗[R] M --ev₀--> M`
as a short complex of `R[X]`-modules. -/
private noncomputable abbrev tensor_polynomial_mulX_shortComplex_over_polynomial
    (M : ModuleCat R) :
    ShortComplex (ModuleCat R[X]) :=
  ShortComplex.mk
    (tensor_polynomial_mulX_hom_over_polynomial (R := R) M)
    (tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) M)
    (tensor_polynomial_mulX_comp_evalAtZero_over_polynomial (R := R) M)

/-- Helper for Lemma 15.82.1: the tensor-model row is short exact already in `ModuleCat R[X]`.
This is the same underlying function sequence as the previously proved `R`-linear tensor row. -/
private theorem tensor_polynomial_mulX_shortExact_evalAtZero_over_polynomial
    (M : ModuleCat R) [Module.Flat R M] :
    (tensor_polynomial_mulX_shortComplex_over_polynomial (R := R) M).ShortExact := by
  have hShort :
      (tensor_polynomial_mulX_shortComplex (R := R) M).ShortExact :=
    tensor_polynomial_mulX_shortExact_evalAtZero (R := R) M
  have hExact :
      Function.Exact
        (tensor_polynomial_mulX_hom (R := R) M).hom
        (tensor_polynomial_evalAtZero_hom (R := R) M).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (tensor_polynomial_mulX_shortComplex (R := R) M)).1 hShort.exact
  have hInjective :
      Function.Injective (tensor_polynomial_mulX_hom (R := R) M).hom :=
    (ModuleCat.mono_iff_injective _).1 hShort.mono_f
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: the owner `R[X]`-linear row has the same underlying functions as the
    -- previously proved `R`-linear row, so exactness transports pointwise.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro z
    constructor
    · intro hz
      have hz' : (tensor_polynomial_evalAtZero_hom (R := R) M).hom z = 0 := by
        rw [tensor_polynomial_evalAtZero_hom_over_polynomial_apply (R := R) M z] at hz
        exact hz
      rcases (hExact z).1 hz' with ⟨w, hw⟩
      refine ⟨w, ?_⟩
      rw [tensor_polynomial_mulX_hom_over_polynomial_apply (R := R) M w]
      exact hw
    · rintro ⟨w, hw⟩
      have hw' : (tensor_polynomial_mulX_hom (R := R) M).hom w = z := by
        rw [tensor_polynomial_mulX_hom_over_polynomial_apply (R := R) M w] at hw
        exact hw
      have hz' : (tensor_polynomial_evalAtZero_hom (R := R) M).hom z = 0 :=
        (hExact z).2 ⟨w, hw'⟩
      rw [tensor_polynomial_evalAtZero_hom_over_polynomial_apply (R := R) M z]
      exact hz'
  · -- Proof comment: injectivity is inherited from the identical underlying multiplication map.
    refine (ModuleCat.mono_iff_injective _).2 ?_
    intro x y hxy
    rw [tensor_polynomial_mulX_hom_over_polynomial_apply (R := R) M x,
      tensor_polynomial_mulX_hom_over_polynomial_apply (R := R) M y] at hxy
    apply hInjective
    exact hxy
  · -- Proof comment: `1 ⊗ m` still evaluates to `m` in the restricted target.
    refine (ModuleCat.epi_iff_surjective _).2 ?_
    intro m
    refine ⟨(1 : R[X]) ⊗ₜ[R] (m : M), ?_⟩
    simpa [tensor_polynomial_evalAtZero_hom_over_polynomial_apply (R := R) M
      ((1 : R[X]) ⊗ₜ[R] (m : M))] using
      (tensor_polynomial_evalAtZero_linear_raw_tmul (R := R) M (1 : R[X]) m)

/-- Helper for Lemma 15.82.1: after restricting scalars along `R → R[X]`, the regular
`R[X]`-module is canonically itself. -/
private noncomputable abbrev restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars Polynomial.C).obj (ModuleCat.of R[X] R[X])) ≃ₗ[R[X]] R[X] :=
  { __ := AddEquiv.refl R[X]
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.82.1: the restricted scalar action on `R[X]` still forms the expected
scalar tower over `R`. -/
private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower R R[X]
      ↑((ModuleCat.restrictScalars Polynomial.C).obj (ModuleCat.of R[X] R[X])) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Lemma 15.82.1: polynomial scalar extension is the tensor-product module
`R[X] ⊗[R] M`. -/
private noncomputable def extendScalars_tensor_module_iso
    (M : ModuleCat R) :
    ((ModuleCat.extendScalars Polynomial.C).obj M) ≅
      ModuleCat.of R[X] (TensorProduct R R[X] (M : Type u)) := by
  -- Proof comment: normalize `ModuleCat.extendScalars` to the explicit tensor model so the later
  -- short exact row can be transported once instead of rebuilt through coercions.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv (R := R))
      (LinearEquiv.refl R (M : Type u))).toModuleIso

/-- Helper for Lemma 15.82.1: under the tensor normalization, the distinguished element
`1 ⊗ m` is preserved. -/
private theorem extendScalars_tensor_module_iso_hom_one_tmul
    (M : ModuleCat R) (m : M) :
    (extendScalars_tensor_module_iso (R := R) M).hom ((1 : R[X]) ⊗ₜ[R] (m : M)) =
      (1 : R[X]) ⊗ₜ[R] (m : M) := by
  -- Proof comment: the normalization is built from identity linear equivalences on both tensor
  -- factors, so it acts trivially on pure tensors.
  rfl

/-- Helper for Lemma 15.82.1: multiplication by `X` on the actual owner object
`ModuleCat.extendScalars Polynomial.C M`, defined by transport from the tensor model. -/
private noncomputable abbrev extendScalars_mulX_hom
    (M : ModuleCat R) :
    ((ModuleCat.extendScalars Polynomial.C).obj M) ⟶
      ((ModuleCat.extendScalars Polynomial.C).obj M) :=
  (extendScalars_tensor_module_iso (R := R) M).hom ≫
    tensor_polynomial_mulX_hom_over_polynomial (R := R) M ≫
      (extendScalars_tensor_module_iso (R := R) M).inv

/-- Helper for Lemma 15.82.1: evaluation at `0` on the actual owner object
`ModuleCat.extendScalars Polynomial.C M`, again transported from the tensor model. -/
private noncomputable abbrev extendScalars_evalAtZero_hom
    (M : ModuleCat R) :
    ((ModuleCat.extendScalars Polynomial.C).obj M) ⟶
      (ModuleCat.restrictScalars ev0).obj M :=
  (extendScalars_tensor_module_iso (R := R) M).hom ≫
    tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) M

/-- Helper for Lemma 15.82.1: the owner row
`extendScalars(M) --·X--> extendScalars(M) --ev₀--> restrictScalars(M)` is a short complex. -/
private theorem extendScalars_mulX_comp_evalAtZero
    (M : ModuleCat R) :
    extendScalars_mulX_hom (R := R) M ≫ extendScalars_evalAtZero_hom (R := R) M = 0 := by
  -- Proof comment: after transporting to the tensor model, this is exactly the vanishing of the
  -- tensor-model composite already isolated above.
  simp [extendScalars_mulX_hom, extendScalars_evalAtZero_hom,
    tensor_polynomial_mulX_comp_evalAtZero_over_polynomial]

/-- Helper for Lemma 15.82.1: the actual owner row on `ModuleCat.extendScalars` packaged as a
short complex. -/
private noncomputable abbrev extendScalars_mulX_shortComplex
    (M : ModuleCat R) :
    ShortComplex (ModuleCat R[X]) :=
  ShortComplex.mk
    (extendScalars_mulX_hom (R := R) M)
    (extendScalars_evalAtZero_hom (R := R) M)
    (extendScalars_mulX_comp_evalAtZero (R := R) M)

/-- Helper for Lemma 15.82.1: under the tensor normalization, the owner multiplication map is the
tensor-model multiplication map. -/
private theorem extendScalars_mulX_tensor_shortComplex_left_square
    (M : ModuleCat R) :
    (extendScalars_tensor_module_iso (R := R) M).hom ≫
        (tensor_polynomial_mulX_shortComplex_over_polynomial (R := R) M).f =
      (extendScalars_mulX_shortComplex (R := R) M).f ≫
        (extendScalars_tensor_module_iso (R := R) M).hom := by
  -- Proof comment: the left map was defined by conjugating the tensor-model multiplication map.
  simp [extendScalars_mulX_shortComplex, extendScalars_mulX_hom,
    tensor_polynomial_mulX_shortComplex_over_polynomial]

/-- Helper for Lemma 15.82.1: under the tensor normalization, the owner evaluation map is the
tensor-model evaluation map. -/
private theorem extendScalars_mulX_tensor_shortComplex_right_square
    (M : ModuleCat R) :
    (extendScalars_tensor_module_iso (R := R) M).hom ≫
        (tensor_polynomial_mulX_shortComplex_over_polynomial (R := R) M).g =
      (extendScalars_mulX_shortComplex (R := R) M).g ≫ (Iso.refl _).hom := by
  -- Proof comment: the right map was defined directly as the tensor-model evaluation after the
  -- normalization isomorphism.
  rfl

/-- Helper for Lemma 15.82.1: the actual owner row is isomorphic to the explicit tensor-model
row in `ModuleCat R[X]`. -/
private noncomputable abbrev extendScalars_mulX_tensor_shortComplex_iso
    (M : ModuleCat R) :
    extendScalars_mulX_shortComplex (R := R) M ≅
      tensor_polynomial_mulX_shortComplex_over_polynomial (R := R) M :=
  ShortComplex.isoMk
    (extendScalars_tensor_module_iso (R := R) M)
    (extendScalars_tensor_module_iso (R := R) M)
    (Iso.refl _)
    (extendScalars_mulX_tensor_shortComplex_left_square (R := R) M)
    (extendScalars_mulX_tensor_shortComplex_right_square (R := R) M)

/-- Helper for Lemma 15.82.1: for a flat module `M`, the actual owner row
`extendScalars(M) --·X--> extendScalars(M) --ev₀--> restrictScalars(M)` is short exact in
`ModuleCat R[X]`. -/
private theorem extendScalars_mulX_component_shortExact_evalAtZero
    (M : ModuleCat R) [Module.Flat R M] :
    (extendScalars_mulX_shortComplex (R := R) M).ShortExact := by
  have hTensor :
      (tensor_polynomial_mulX_shortComplex_over_polynomial (R := R) M).ShortExact :=
    tensor_polynomial_mulX_shortExact_evalAtZero_over_polynomial (R := R) M
  -- Proof comment: transport short exactness once across the tensor-normalization isomorphism.
  exact ShortComplex.shortExact_of_iso
    (extendScalars_mulX_tensor_shortComplex_iso (R := R) M).symm
    hTensor

/-- Helper for Lemma 15.82.1: tensoring a module morphism on the second factor gives the canonical
map between the explicit tensor models for scalar extension. -/
private noncomputable abbrev tensor_polynomial_map
    {M N : ModuleCat R} (f : M ⟶ N) :
    ModuleCat.of R[X] (TensorProduct R R[X] (M : Type u)) ⟶
      ModuleCat.of R[X] (TensorProduct R R[X] (N : Type u)) :=
  ModuleCat.ofHom (LinearMap.baseChange R[X] f.hom)

/-- Helper for Lemma 15.82.1: multiplication by `X` on the tensor model is natural in the module
argument. -/
private theorem tensor_polynomial_mulX_hom_over_polynomial_naturality
    {M N : ModuleCat R} (f : M ⟶ N) :
    tensor_polynomial_map (R := R) f ≫ tensor_polynomial_mulX_hom_over_polynomial (R := R) N =
      tensor_polynomial_mulX_hom_over_polynomial (R := R) M ≫
        tensor_polynomial_map (R := R) f := by
  -- Proof comment: both composites send a pure tensor `p ⊗ m` to `(X * p) ⊗ f(m)`.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensor_polynomial_map, tensor_polynomial_mulX_hom_over_polynomial]
  · intro p m
    simp [tensor_polynomial_map, tensor_polynomial_mulX_hom_over_polynomial,
      LinearMap.baseChange_tmul]
  · intro x y hx hy
    simp [LinearMap.map_add]

/-- Helper for Lemma 15.82.1: evaluation at `0` on the tensor model is natural in the module
argument. -/
private theorem tensor_polynomial_evalAtZero_hom_over_polynomial_naturality
    {M N : ModuleCat R} (f : M ⟶ N) :
    tensor_polynomial_map (R := R) f ≫ tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) N =
      tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) M ≫
        (ModuleCat.restrictScalars ev0).map f := by
  -- Proof comment: on a pure tensor `p ⊗ m`, both sides evaluate to `ev₀(p) • f(m)`.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensor_polynomial_map, tensor_polynomial_evalAtZero_hom_over_polynomial]
  · intro p m
    simp [tensor_polynomial_map, tensor_polynomial_evalAtZero_hom_over_polynomial,
      tensor_polynomial_evalAtZero_hom, LinearMap.baseChange_tmul, TensorProduct.lid_tmul,
      map_smul]
  · intro x y hx hy
    let L :=
      ModuleCat.Hom.hom
        (tensor_polynomial_map (R := R) f ≫
          tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) N)
    let Rm :=
      ModuleCat.Hom.hom
        (tensor_polynomial_evalAtZero_hom_over_polynomial (R := R) M ≫
          (ModuleCat.restrictScalars ev0).map f)
    change L (x + y) = Rm (x + y)
    calc
      L (x + y) = L x + L y := by exact L.map_add x y
      _ = Rm x + Rm y := by rw [hx, hy]
      _ = Rm (x + y) := by exact (Rm.map_add x y).symm

/-- Helper for Lemma 15.82.1: in `D(R)`, the mapping cone of the zero self-map of a cochain
complex is isomorphic to the original object together with its shift. -/
private theorem mappingCone_zero_isomorphic_biprod_shift
    (P : CochainComplex (ModuleCat R) ℤ) :
    IsIsomorphic
      (DerivedCategory.Q.obj (CochainComplex.mappingCone (0 : P ⟶ P)))
      (DerivedCategory.Q.obj P ⊞ (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧) := by
  let β : P ⟶ P := 0
  let T : Triangle DModR :=
    DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β)
  have hT : T ∈ distTriang DModR := by
    -- Proof comment: the standard mapping-cone triangle is distinguished after passing to
    -- the derived category.
    simpa [T, β] using DerivedCategory.mappingCone_triangle_distinguished β
  have hTrot : T.rotate ∈ distTriang DModR := by
    -- Proof comment: rotate once so the zero map becomes the third edge, where the split-triangle
    -- theorem applies directly.
    exact rot_of_distTriang _ hT
  have hzero_rot : T.rotate.mor₃ = 0 := by
    -- Proof comment: in the rotated triangle the third morphism is the shifted negative of
    -- `Q.map β`, which vanishes because `β = 0`.
    change -((DerivedCategory.Q.map β)⟦(1 : ℤ)⟧') = 0
    simp [β]
  obtain ⟨e, _, _⟩ :=
    exists_iso_binaryBiproduct_of_distTriang T.rotate hTrot hzero_rot
  -- Proof comment: after unfolding the rotated mapping-cone triangle, the split triangle theorem
  -- gives exactly the desired isomorphism shape.
  change IsIsomorphic T.rotate.obj₂ (T.rotate.obj₁ ⊞ T.rotate.obj₃)
  exact ⟨e⟩

/-- Helper for Lemma 15.82.1: a natural isomorphism of exact functors induces an objectwise
isomorphism on the derived categories. -/
private noncomputable def mapDerivedCategory_obj_iso_of_natIso
    {S T : Type u} [CommRing S] [CommRing T]
    {F G : ModuleCat S ⥤ ModuleCat T}
    [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory (ModuleCat S)) :
    (F.mapDerivedCategory.obj K) ≅ (G.mapDerivedCategory.obj K) :=
  let C := DerivedCategory.Q.objPreimage K
  -- Proof comment: normalize both derived objects to the same strict representative and insert
  -- the cochain-level image of the functor isomorphism.
  (F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (F.mapDerivedCategoryFactors.app C) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app C) ≪≫
    (G.mapDerivedCategoryFactors.app C).symm ≪≫
    (G.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K)

/-- Helper for Lemma 15.82.1: the derived object of a composite of exact functors agrees with the
iterated exact derived images. -/
private noncomputable def mapDerivedCategory_comp_obj_iso
    {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
    (F : ModuleCat S ⥤ ModuleCat T) (G : ModuleCat T ⥤ ModuleCat U)
    [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    (K : DerivedCategory (ModuleCat S)) :
    ((F ⋙ G).mapDerivedCategory.obj K) ≅
      (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) :=
  let C := DerivedCategory.Q.objPreimage K
  -- Proof comment: both sides are computed by the same strict image `G(F(C))`, so only the
  -- canonical exact-functor comparison isomorphisms need to be inserted.
  ((F ⋙ G).mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    ((F ⋙ G).mapDerivedCategoryFactors.app C) ≪≫
    (G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).symm ≪≫
    (G.mapDerivedCategory).mapIso ((F.mapDerivedCategoryFactors.app C).symm) ≪≫
    (G.mapDerivedCategory).mapIso
      ((F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K))

/- Domain-style sampling for Lemma 15.82.1:
- primary domain: derived base change for the polynomial evaluation map `R[X] → R`;
- sampled owner declarations:
  `Polynomial.evalRingHom`,
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars f).mapDerivedCategory`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction: the source-facing theorem should use the chapter owner
  `derivedTensorWithAlgebra (Polynomial.evalRingHom 0)`, with restriction of scalars along
  `Polynomial.evalRingHom 0` kept as the bridge/view that places `K` in `D(R[X])`; since the
  comparison is only needed as an object-level existence statement, the public surface should
  remain at the theorem-level `IsIsomorphic` API rather than expose a chosen concrete isomorphism;
- primitive data: the ring hom `R[X] →+* R`;
- derived API: the derived restriction functor, the owner functor
  `derivedTensorWithAlgebra (Polynomial.evalRingHom 0)`, and the theorem that the displayed
  object is isomorphic to `K ⊞ K⟦(1 : ℤ)⟧`.

Source/core/bridge triage:
- `source-facing`: the main isomorphism theorem below;
- `core/canonical`: `Polynomial.evalRingHom`, `derivedTensorWithAlgebra`,
  `ModuleCat.restrictScalars`;
- `bridge/view`: the derived restriction-of-scalars functor
  `(ModuleCat.restrictScalars (Polynomial.evalRingHom 0)).mapDerivedCategory` along
  `Polynomial.evalRingHom 0`. -/

-- Proof sketch: resolve `K` by an `R`-flat complex, view it over `R[X]` via the action with
-- `X = 0`, compute the derived tensor product using the two-term free resolution
-- `R[X] \xrightarrow{X} R[X]` of `R`, and identify the resulting total complex with the split
-- object `K ⊞ K[1]`.
/-- Lemma 15.82.1: if a derived `R`-complex is viewed as an `R[X]`-complex through the map
`R[X] → R` sending `X` to `0`, then derived tensoring back with `R` over `R[X]` is isomorphic to
`K^• ⊞ K^•[1]` in `D(R)`. -/
theorem derivedTensor_restrictScalars_evalAtZero_isomorphic_biprod_shift
    (K : DModR) :
    IsIsomorphic
      ((derivedTensorWithAlgebra ev0).obj
        (((ModuleCat.restrictScalars ev0).mapDerivedCategory).obj K))
      (K ⊞ K⟦(1 : ℤ)⟧) := by
  -- Route correction: follow the source proof through a K-flat termwise-flat resolution, the
  -- polynomial `X` short exact sequence on its scalar extension, and the split rotated triangle
  -- obtained after derived base change to `R`.
  -- Proof comment: the transport blocker has now been reduced to the cone/derived layer. The
  -- polynomial scalar extension object is normalized to the tensor model by
  -- `extendScalars_tensor_module_iso`, so the remaining work is to package the owner short
  -- complex, apply `mappingCone.quasiIso_descShortComplex`, and then compute derived tensor on
  -- that K-flat cone exactly as in the source proof.
  -- TODO for Lemma 15.82.1: use a K-flat termwise-flat resolution `P ⟶ Q.objPreimage K`,
  -- build the cone of multiplication by `X` on `((ModuleCat.extendScalars Polynomial.C)
  -- .mapHomologicalComplex (up ℤ)).obj P`, then upgrade the underlying tensor short exact row
  -- from `tensor_polynomial_mulX_shortExact_evalAtZero` through
  -- `extendScalars_tensor_module_iso (R := R)` to the actual
  -- `ModuleCat.extendScalars`/`ModuleCat.restrictScalars` row in `ModuleCat R[X]`, assemble the
  -- degreewise rows into a complex short exact row, identify the cone with the restricted complex
  -- using `mappingCone.quasiIso_descShortComplex`, and finally compute derived tensor on that
  -- K-flat cone and split the resulting zero-cone with
  -- `mappingCone_zero_isomorphic_biprod_shift (R := R)`.
  sorry

end

end CategoryTheory

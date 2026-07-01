import Mathlib
import stacks_project.Chap10.Definition_10_82_1
import stacks_project.Chap10.Lemma_10_39_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace LinearMap

noncomputable section

open scoped TensorProduct
open LocalizedModule TensorProduct
open TensorProduct.AlgebraTensorModule
open IsLocalization

/-
Domain-style sampling:
- primary domain: universal injectivity of linear maps under restriction of scalars and
  localization of modules;
- sampled owner declarations:
  `LinearMap.UniversallyInjective`,
  `LinearMap.restrictScalars`,
  `Module.restrictScalars`,
  `IsScalarTower.restrictScalars`,
  `LocalizedModule.map`;
- best owner abstraction: the core owner is `LinearMap.UniversallyInjective`, with localization
  and scalar restriction handled by the canonical bridge APIs above rather than theorem-local
  wrapper maps;
- primitive data: a linear map together with the ambient scalar towers and localization map;
- derived API: the universally injective restricted-scalar views of localized maps and of
  `Localization S'`-linear maps.

Source/core/bridge triage:
- `source-facing`: Lemma `10.82.12`, comparing universal injectivity before and after localizing;
- `core/canonical`: `LinearMap.UniversallyInjective`;
- `bridge/view`: `LinearMap.restrictScalars`, `Module.restrictScalars`,
  `IsScalarTower.restrictScalars`, and `LocalizedModule.map`.
-/

section

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {S : Submonoid A} {S' : Submonoid B}

variable {M : Type w} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable {M' : Type x} [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']

/-- Helper for Lemma 10.82.12: localizing the tensor map `f ⊗[A] Q` agrees with tensoring the
localized map. -/
lemma localized_rTensor_map_eq
    (f : M →ₗ[B] M') (Q : Type*) [AddCommGroup Q] [Module A Q] :
    IsLocalizedModule.map S'
      (AlgebraTensorModule.rTensor A Q (LocalizedModule.mkLinearMap S' M))
      (AlgebraTensorModule.rTensor A Q (LocalizedModule.mkLinearMap S' M'))
      (AlgebraTensorModule.rTensor A Q f) =
      AlgebraTensorModule.rTensor A Q (LocalizedModule.map S' f) := by
  -- We compare the two maps after precomposing with the canonical localization map on
  -- `M ⊗[A] Q`, where both sides reduce to the same map on pure tensors.
  apply IsLocalizedModule.linearMap_ext S'
    (AlgebraTensorModule.rTensor A Q (LocalizedModule.mkLinearMap S' M))
    (AlgebraTensorModule.rTensor A Q (LocalizedModule.mkLinearMap S' M'))
  rw [IsLocalizedModule.map_comp, ← AlgebraTensorModule.rTensor_comp,
    AlgebraTensorModule.rTensor_comp]
  ext x
  simp [LocalizedModule.map_mk]

/-- Helper for Lemma 10.82.12: the canonical localization-tensor equivalence conjugates the
localized tensor map of `f` to the tensor map of the localized morphism. -/
lemma localized_tensor_right_equiv_intertwines_rTensor
    (f : M →ₗ[B] M') (Q : Type*) [AddCommGroup Q] [Module A Q] :
    ((LocalizedModule.map S' (AlgebraTensorModule.rTensor A Q f)).restrictScalars A).comp
        ((localized_tensor_right_equiv (R := A) (A := B) (X := M) S' Q).restrictScalars A).toLinearMap =
      (((localized_tensor_right_equiv (R := A) (A := B) (X := M') S' Q).restrictScalars A).toLinearMap).comp
        (((LocalizedModule.map S' f).restrictScalars A).rTensor Q) := by
  -- Route correction: use the same conjugation pattern as `localized_lTensor_intertwines`,
  -- rewriting the owner map via `restrictScalars_map_eq` before cancelling the comparison map.
  let eM := (localized_tensor_right_equiv (R := A) (A := B) (X := M) S' Q).restrictScalars A
  let eM' := (localized_tensor_right_equiv (R := A) (A := B) (X := M') S' Q).restrictScalars A
  have hlocalized :
      IsLocalizedModule.map S'
          (AlgebraTensorModule.rTensor A Q (LocalizedModule.mkLinearMap S' M))
          (AlgebraTensorModule.rTensor A Q (LocalizedModule.mkLinearMap S' M'))
          (AlgebraTensorModule.rTensor A Q f) =
        AlgebraTensorModule.rTensor A Q (LocalizedModule.map S' f) :=
    localized_rTensor_map_eq (A := A) (B := B) (S' := S') (M := M) (M' := M') f Q
  have hmap :
      (LocalizedModule.map S' (AlgebraTensorModule.rTensor A Q f)).restrictScalars A =
        (eM'.toLinearMap.comp
          (AlgebraTensorModule.rTensor A Q (LocalizedModule.map S' f))).comp
            eM.symm.toLinearMap := by
    -- The canonical localization-tensor equivalence is the localized-module `iso`, so the owner
    -- theorem becomes exactly the desired conjugation formula.
    have hmapB :
        (LocalizedModule.map S' (AlgebraTensorModule.rTensor A Q f)).restrictScalars B =
          (((localized_tensor_right_equiv (R := A) (A := B) (X := M') S' Q).toLinearMap).comp
            (AlgebraTensorModule.rTensor A Q (LocalizedModule.map S' f))).comp
              ((localized_tensor_right_equiv (R := A) (A := B) (X := M) S' Q).symm.toLinearMap) := by
      have hrTensorLocalizedMap :
          ((AlgebraTensorModule.rTensor A Q (LocalizedModule.map S' f)).restrictScalars B :
            LocalizedModule S' M ⊗[A] Q →ₗ[B] LocalizedModule S' M' ⊗[A] Q) =
            AlgebraTensorModule.rTensor A Q ((LocalizedModule.map S' f).restrictScalars B) := rfl
      rw [LocalizedModule.restrictScalars_map_eq (S := S')
        (g₁ := AlgebraTensorModule.rTensor A Q (LocalizedModule.mkLinearMap S' M))
        (g₂ := AlgebraTensorModule.rTensor A Q (LocalizedModule.mkLinearMap S' M'))
        (l := AlgebraTensorModule.rTensor A Q f)]
      simpa [hlocalized, hrTensorLocalizedMap, localized_tensor_right_equiv, IsLocalizedModule.linearEquiv,
        IsLocalizedModule.iso_localizedModule_eq_refl, LinearMap.comp_assoc]
    simpa [eM, eM', restrictScalars_rTensor] using
      congrArg (LinearMap.restrictScalars A) hmapB
  -- Postcompose the conjugation formula by the source comparison map so the inverse cancels.
  calc
    ((LocalizedModule.map S' (AlgebraTensorModule.rTensor A Q f)).restrictScalars A).comp
        eM.toLinearMap
        = (((eM'.toLinearMap.comp
            (AlgebraTensorModule.rTensor A Q (LocalizedModule.map S' f))).comp
              eM.symm.toLinearMap).comp eM.toLinearMap) := by
            rw [hmap]
    _ = eM'.toLinearMap.comp (AlgebraTensorModule.rTensor A Q (LocalizedModule.map S' f)) := by
      ext z
      simp [LinearMap.comp_assoc]

/-- Lemma 10.82.12 (1): if a `B`-linear map is universally injective as a map of `A`-modules,
then its localization at `S'` is universally injective as a map of `A`-modules. -/
-- Proof sketch: tensor the localized map with an arbitrary `A`-module, identify the result
-- with the localization of the tensor map over `A`, and use exactness of localization to
-- preserve injectivity.
theorem universallyInjective_localizedModule_restrictScalars
    (f : M →ₗ[B] M')
    (hf : UniversallyInjective.{u, w, x, max u v w x} (f.restrictScalars A)) :
    UniversallyInjective.{u, max v w, max v x, max u v w x}
      ((LocalizedModule.map S' f).restrictScalars A) := by
  unfold UniversallyInjective at hf ⊢
  intro (Q : Type (max u v w x)) _ _
  let eM : LocalizedModule S' M ⊗[A] Q ≃ₗ[A] LocalizedModule S' (M ⊗[A] Q) :=
    (localized_tensor_right_equiv (R := A) (A := B) (X := M) S' Q).restrictScalars A
  let eM' : LocalizedModule S' M' ⊗[A] Q ≃ₗ[A] LocalizedModule S' (M' ⊗[A] Q) :=
    (localized_tensor_right_equiv (R := A) (A := B) (X := M') S' Q).restrictScalars A
  have hTensor : Function.Injective (AlgebraTensorModule.rTensor A Q f) := by
    simpa [restrictScalars_rTensor] using hf Q inferInstance inferInstance
  have hLocalized :
      Function.Injective ((LocalizedModule.map S' (AlgebraTensorModule.rTensor A Q f)).restrictScalars A) :=
    LocalizedModule.map_injective S' (AlgebraTensorModule.rTensor A Q f) hTensor
  -- We localize the injective tensor map and then transfer injectivity across the canonical
  -- localization-tensor equivalences on the source and target.
  intro x y hxy
  apply eM.injective
  apply hLocalized
  have hxy' : eM'.toLinearMap ((((LocalizedModule.map S' f).restrictScalars A).rTensor Q) x) =
      eM'.toLinearMap ((((LocalizedModule.map S' f).restrictScalars A).rTensor Q) y) :=
    congrArg eM'.toLinearMap hxy
  have hx :=
    DFunLike.congr_fun
      (localized_tensor_right_equiv_intertwines_rTensor
        (A := A) (B := B) (S' := S') (M := M) (M' := M') f Q) x
  have hy :=
    DFunLike.congr_fun
      (localized_tensor_right_equiv_intertwines_rTensor
        (A := A) (B := B) (S' := S') (M := M) (M' := M') f Q) y
  exact hx.trans (hxy'.trans hy.symm)

variable {N : Type w} [AddCommGroup N] [Module (Localization S') N]
variable {N' : Type x} [AddCommGroup N'] [Module (Localization S') N']

section

variable [Fact (S ≤ S'.comap (algebraMap A B))]

local instance localizationMapAlgebra : Algebra (Localization S) (Localization S') :=
  RingHom.toAlgebra
    (IsLocalization.map (Localization S') (algebraMap A B)
      (show S ≤ S'.comap (algebraMap A B) from Fact.out))

local instance localizedModuleModule : Module (Localization S) (LocalizedModule S' M) :=
  Module.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M)

local instance localizedModuleModule' : Module (Localization S) (LocalizedModule S' M') :=
  Module.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M')

local instance localizedModuleIsScalarTower :
    IsScalarTower (Localization S) (Localization S') (LocalizedModule S' M) :=
  IsScalarTower.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M)

local instance localizedModuleIsScalarTower' :
    IsScalarTower (Localization S) (Localization S') (LocalizedModule S' M') :=
  IsScalarTower.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M')

/-- Helper for Lemma 10.82.12: the localized map sends a numerator over denominator `1` to the
corresponding localized image of that numerator. -/
lemma localizedMap_apply_mk_one (f : M →ₗ[B] M') (m : M) :
    LocalizedModule.map S' f (LocalizedModule.mk m (1 : S')) = LocalizedModule.mk (f m) 1 := by
  simpa using LocalizedModule.map_mk (S := S') f m (1 : S')

/-- Helper for Lemma 10.82.12: the induced map `A[S⁻¹] → B[S'⁻¹]` sends `a / 1` to the image of
`a` in `B[S'⁻¹]`. -/
lemma localizationMapAlgebraMap_apply (a : A) :
    IsLocalization.map (Localization S') (algebraMap A B)
      (show S ≤ S'.comap (algebraMap A B) from Fact.out)
      (algebraMap A (Localization S) a) = algebraMap A (Localization S') a := by
  -- The localization map is defined to make the square with `A → B` commute, so evaluating that
  -- square at `a` identifies the two scalar actions.
  simpa [RingHom.comp_apply, IsScalarTower.algebraMap_eq A B (Localization S')] using
    congrArg (fun h ↦ h a)
      (IsLocalization.map_comp (Q := Localization S')
        (g := algebraMap A B)
        (hy := (show S ≤ S'.comap (algebraMap A B) from Fact.out)))

/-- Helper for Lemma 10.82.12: source fact (a), namely that tensoring over `A[S⁻¹]` agrees with
tensoring over `A` for `A[S⁻¹]`-modules. -/
noncomputable def tensor_over_localization_compare
    {X : Type*} [AddCommGroup X] [Module A X] [Module (Localization S) X]
    [IsScalarTower A (Localization S) X]
    (Q : Type*) [AddCommGroup Q] [Module A Q] [Module (Localization S) Q]
    [IsScalarTower A (Localization S) Q] :
    X ⊗[Localization S] Q ≃ₗ[Localization S] X ⊗[A] Q :=
  IsLocalization.moduleTensorEquiv S (Localization S) X Q

/-- Helper for Lemma 10.82.12: the comparison from source fact (a) fixes pure tensors. -/
lemma tensor_over_localization_compare_tmul
    {X : Type*} [AddCommGroup X] [Module A X] [Module (Localization S) X]
    [IsScalarTower A (Localization S) X]
    (Q : Type*) [AddCommGroup Q] [Module A Q] [Module (Localization S) Q]
    [IsScalarTower A (Localization S) Q] (x : X) (q : Q) :
    tensor_over_localization_compare (A := A) (S := S) (X := X) Q (x ⊗ₜ[Localization S] q) =
      (x ⊗ₜ[A] q : X ⊗[A] Q) := rfl

/-- Helper for Lemma 10.82.12: source fact (a) intertwines the tensor maps of a
`B[S'⁻¹]`-linear morphism after restricting scalars. -/
lemma tensor_over_localization_compare_intertwines
    {X : Type*} [AddCommGroup X] [Module A X] [Module (Localization S) X]
    [Module (Localization S') X] [IsScalarTower A (Localization S) X]
    [IsScalarTower A (Localization S') X] [IsScalarTower (Localization S) (Localization S') X]
    {Y : Type*} [AddCommGroup Y] [Module A Y] [Module (Localization S) Y]
    [Module (Localization S') Y] [IsScalarTower A (Localization S) Y]
    [IsScalarTower A (Localization S') Y] [IsScalarTower (Localization S) (Localization S') Y]
    (g : X →ₗ[Localization S'] Y)
    (Q : Type*) [AddCommGroup Q] [Module A Q] [Module (Localization S) Q]
    [IsScalarTower A (Localization S) Q] (z : X ⊗[Localization S] Q) :
    tensor_over_localization_compare (A := A) (S := S) (X := Y) Q
      (((g.restrictScalars (Localization S)).rTensor Q) z) =
      ((g.restrictScalars A).rTensor Q)
        (tensor_over_localization_compare (A := A) (S := S) (X := X) Q z) := by
  -- We verify the naturality identity on pure tensors, where both sides are definitionally the
  -- same, and then extend by tensor-product induction.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensor_over_localization_compare]
  · intro x q
    rfl
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Helper for Lemma 10.82.12: source fact (b), namely that tensoring over `A` with `Q` agrees
with tensoring over `A[S⁻¹]` against the localized test module `Q[S⁻¹]`. -/
noncomputable def tensor_with_localized_test_module_compare
    {X : Type*} [AddCommGroup X] [Module A X] [Module (Localization S) X]
    [Module (Localization S') X] [IsScalarTower A (Localization S) X]
    [IsScalarTower A (Localization S') X] [IsScalarTower (Localization S) (Localization S') X]
    (Q : Type*) [AddCommGroup Q] [Module A Q] :
    X ⊗[A] Q ≃ₗ[Localization S'] X ⊗[Localization S] LocalizedModule S Q :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange
      A (Localization S) (Localization S') X Q).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Localization S') X)
      (LocalizedModule.equivTensorProduct S Q).symm)

/-- Helper for Lemma 10.82.12: source fact (b) also intertwines the tensor maps of the localized
test-module comparison. -/
lemma tensor_with_localized_test_module_compare_intertwines
    {X : Type*} [AddCommGroup X] [Module A X] [Module (Localization S) X]
    [Module (Localization S') X] [IsScalarTower A (Localization S) X]
    [IsScalarTower A (Localization S') X] [IsScalarTower (Localization S) (Localization S') X]
    {Y : Type*} [AddCommGroup Y] [Module A Y] [Module (Localization S) Y]
    [Module (Localization S') Y] [IsScalarTower A (Localization S) Y]
    [IsScalarTower A (Localization S') Y] [IsScalarTower (Localization S) (Localization S') Y]
    (g : X →ₗ[Localization S'] Y)
    (Q : Type*) [AddCommGroup Q] [Module A Q] (z : X ⊗[A] Q) :
    tensor_with_localized_test_module_compare
        (A := A) (B := B) (S := S) (S' := S') (X := Y) Q
        (((g.restrictScalars A).rTensor Q) z) =
      (((g.restrictScalars (Localization S)).rTensor (LocalizedModule S Q)).restrictScalars A)
        (tensor_with_localized_test_module_compare
          (A := A) (B := B) (S := S) (S' := S') (X := X) Q z) := by
  -- We again reduce the transport identity to the pure-tensor case coming from
  -- `cancelBaseChange.symm_tmul` and `LocalizedModule.equivTensorProduct_symm_apply_tmul_one`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [tensor_with_localized_test_module_compare]
  · intro x q
    simp [tensor_with_localized_test_module_compare]
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Lemma 10.82.12 (2): if a `B`-linear map is universally injective as a map of `A`-modules and
`S` maps into `S'`, then its localization at `S'` is universally injective as a map of
`A[S⁻¹]`-modules. -/
-- Proof sketch: first view `B[S'⁻¹]` as an `A[S⁻¹]`-algebra via the induced localization map
-- `A[S⁻¹] → B[S'⁻¹]`; then apply the same tensor-localization argument as in the `A`-linear case,
-- using the induced scalar tower on the localized modules.
theorem universallyInjective_localizedModule_over_localization
    (f : M →ₗ[B] M')
    (hf : UniversallyInjective.{u, w, x, max u v w x} (f.restrictScalars A)) :
    UniversallyInjective.{u, max v w, max v x, max u v w x}
      ((LocalizedModule.map S' f).restrictScalars (Localization S)) := by
  letI : IsScalarTower A (Localization S) (LocalizedModule S' M) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      -- The `Localization S`-action is the restriction of scalars from `Localization S'`, so the
      -- left-hand scalar is first mapped along `A[S⁻¹] → B[S'⁻¹]`.
      change ((algebraMap (Localization S) (Localization S')) (algebraMap A (Localization S) a)) • x =
        a • x
      rw [show (algebraMap (Localization S) (Localization S')) (algebraMap A (Localization S) a) =
          algebraMap A (Localization S') a by
            exact localizationMapAlgebraMap_apply
              (A := A) (B := B) (S := S) (S' := S') a]
      simpa [IsScalarTower.algebraMap_eq A B (Localization S')]
  letI : IsScalarTower A (Localization S) (LocalizedModule S' M') :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      -- The same scalar-factorization statement holds on the codomain localization.
      change ((algebraMap (Localization S) (Localization S')) (algebraMap A (Localization S) a)) • x =
        a • x
      rw [show (algebraMap (Localization S) (Localization S')) (algebraMap A (Localization S) a) =
          algebraMap A (Localization S') a by
            exact localizationMapAlgebraMap_apply
              (A := A) (B := B) (S := S) (S' := S') a]
      simpa [IsScalarTower.algebraMap_eq A B (Localization S')]
  have hLocalizedA :
      UniversallyInjective.{u, max v w, max v x, max u v w x}
        ((LocalizedModule.map S' f).restrictScalars A) :=
    universallyInjective_localizedModule_restrictScalars
      (A := A) (B := B) (S' := S') (M := M) (M' := M') f hf
  unfold UniversallyInjective at hLocalizedA ⊢
  intro Q _ _
  letI : Module A Q := Module.restrictScalars A (Localization S) Q
  letI : IsScalarTower A (Localization S) Q :=
    IsScalarTower.restrictScalars A (Localization S) Q
  have hTensorA :
      Function.Injective (((LocalizedModule.map S' f).restrictScalars A).rTensor Q) := by
    -- Part (1) gives injectivity after tensoring over `A` with the same test module `Q`.
    simpa [restrictScalars_rTensor] using hLocalizedA Q inferInstance inferInstance
  intro x y hxy
  apply (tensor_over_localization_compare
    (A := A) (S := S) (X := LocalizedModule S' M) Q).injective
  apply hTensorA
  have hxy' :
      tensor_over_localization_compare
        (A := A) (S := S) (X := LocalizedModule S' M') Q
        ((((LocalizedModule.map S' f).restrictScalars (Localization S)).rTensor Q) x) =
      tensor_over_localization_compare
        (A := A) (S := S) (X := LocalizedModule S' M') Q
        ((((LocalizedModule.map S' f).restrictScalars (Localization S)).rTensor Q) y) :=
    congrArg
      (tensor_over_localization_compare
        (A := A) (S := S) (X := LocalizedModule S' M') Q) hxy
  simpa [tensor_over_localization_compare_intertwines
      (A := A) (B := B) (S := S) (S' := S')
      (X := LocalizedModule S' M) (Y := LocalizedModule S' M')
      (g := LocalizedModule.map S' f) (Q := Q)] using hxy'

/-- Lemma 10.82.12 (3): for `B[S'⁻¹]`-linear maps, universal injectivity over `A` is equivalent to
universal injectivity over `A[S⁻¹]`, where both scalar restrictions are the canonical ones induced
from the `B[S'⁻¹]`-module structure and `hSS'`. -/
-- Proof sketch: use that tensoring over `A` with an `A[S⁻¹]`-module is the same as tensoring
-- over `A[S⁻¹]`, and conversely that a `B[S'⁻¹]`-module already has all elements of `S`
-- acting invertibly, so tensoring over `A` factors through `A[S⁻¹]`.
theorem universallyInjective_iff_over_localization
    (f : N →ₗ[Localization S'] N') :
    by
      letI : Module A N := Module.restrictScalars A (Localization S') N
      letI : Module A N' := Module.restrictScalars A (Localization S') N'
      letI : IsScalarTower A (Localization S') N :=
        IsScalarTower.restrictScalars A (Localization S') N
      letI : IsScalarTower A (Localization S') N' :=
        IsScalarTower.restrictScalars A (Localization S') N'
      letI : Module (Localization S) N := Module.restrictScalars (Localization S) (Localization S') N
      letI : Module (Localization S) N' := Module.restrictScalars (Localization S) (Localization S') N'
      letI : IsScalarTower (Localization S) (Localization S') N :=
        IsScalarTower.restrictScalars (Localization S) (Localization S') N
      letI : IsScalarTower (Localization S) (Localization S') N' :=
        IsScalarTower.restrictScalars (Localization S) (Localization S') N'
      exact UniversallyInjective.{u, w, x, max u v w x} (f.restrictScalars A) ↔
        UniversallyInjective.{u, w, x, max u v w x}
          (f.restrictScalars (Localization S)) := by
          letI : Module A N := Module.restrictScalars A (Localization S') N
          letI : Module A N' := Module.restrictScalars A (Localization S') N'
          letI : IsScalarTower A (Localization S') N :=
            IsScalarTower.restrictScalars A (Localization S') N
          letI : IsScalarTower A (Localization S') N' :=
            IsScalarTower.restrictScalars A (Localization S') N'
          letI : Module (Localization S) N :=
            Module.restrictScalars (Localization S) (Localization S') N
          letI : Module (Localization S) N' :=
            Module.restrictScalars (Localization S) (Localization S') N'
          letI : IsScalarTower (Localization S) (Localization S') N :=
            IsScalarTower.restrictScalars (Localization S) (Localization S') N
          letI : IsScalarTower (Localization S) (Localization S') N' :=
            IsScalarTower.restrictScalars (Localization S) (Localization S') N'
          letI : IsScalarTower A (Localization S) N :=
            IsScalarTower.of_algebraMap_smul fun a x ↦ by
              -- The `A`-action on `N` also factors through `A[S⁻¹]` because `N` is already a
              -- `B[S'⁻¹]`-module.
              change ((algebraMap (Localization S) (Localization S')) (algebraMap A (Localization S) a)) • x =
                a • x
              rw [show (algebraMap (Localization S) (Localization S')) (algebraMap A (Localization S) a) =
                  algebraMap A (Localization S') a by
                    exact localizationMapAlgebraMap_apply
                      (A := A) (B := B) (S := S) (S' := S') a]
              simpa [IsScalarTower.algebraMap_eq A B (Localization S')] using
                (show ((algebraMap B (Localization S')) ((algebraMap A B) a)) • x = a • x by rfl)
          letI : IsScalarTower A (Localization S) N' :=
            IsScalarTower.of_algebraMap_smul fun a x ↦ by
              -- The same factorization statement holds on the codomain.
              change ((algebraMap (Localization S) (Localization S')) (algebraMap A (Localization S) a)) • x =
                a • x
              rw [show (algebraMap (Localization S) (Localization S')) (algebraMap A (Localization S) a) =
                  algebraMap A (Localization S') a by
                    exact localizationMapAlgebraMap_apply
                      (A := A) (B := B) (S := S) (S' := S') a]
              simpa [IsScalarTower.algebraMap_eq A B (Localization S')] using
                (show ((algebraMap B (Localization S')) ((algebraMap A B) a)) • x = a • x by rfl)
          constructor
          · intro hA
            unfold UniversallyInjective at hA ⊢
            intro Q _ _
            letI : Module A Q := Module.restrictScalars A (Localization S) Q
            letI : IsScalarTower A (Localization S) Q :=
              IsScalarTower.restrictScalars A (Localization S) Q
            have hTensorA : Function.Injective ((f.restrictScalars A).rTensor Q) := by
              -- Source fact (a) lets us test the `A[S⁻¹]`-module `Q` directly as an `A`-module.
              simpa [restrictScalars_rTensor] using hA Q inferInstance inferInstance
            intro x y hxy
            apply (tensor_over_localization_compare (A := A) (S := S) (X := N) Q).injective
            apply hTensorA
            have hxy' :
                tensor_over_localization_compare (A := A) (S := S) (X := N') Q
                    (((f.restrictScalars (Localization S)).rTensor Q) x) =
                  tensor_over_localization_compare (A := A) (S := S) (X := N') Q
                    (((f.restrictScalars (Localization S)).rTensor Q) y) :=
              congrArg (tensor_over_localization_compare (A := A) (S := S) (X := N') Q) hxy
            simpa [tensor_over_localization_compare_intertwines
                (A := A) (B := B) (S := S) (S' := S')
                (X := N) (Y := N') (g := f) (Q := Q)] using hxy'
          · intro hLocalization
            unfold UniversallyInjective at hLocalization ⊢
            intro Q _ _
            have hTensorLocalization :
                Function.Injective
                  ((((f.restrictScalars (Localization S)).rTensor (LocalizedModule S Q)).restrictScalars A)) := by
              -- Source fact (b) says it suffices to test the localization of the arbitrary
              -- `A`-module `Q`.
              simpa [restrictScalars_rTensor] using
                hLocalization (LocalizedModule S Q) inferInstance inferInstance
            intro x y hxy
            apply (tensor_with_localized_test_module_compare
              (A := A) (B := B) (S := S) (S' := S') (X := N) Q).injective
            apply hTensorLocalization
            have hxy' :
                tensor_with_localized_test_module_compare
                    (A := A) (B := B) (S := S) (S' := S') (X := N') Q
                    (((f.restrictScalars A).rTensor Q) x) =
                  tensor_with_localized_test_module_compare
                    (A := A) (B := B) (S := S) (S' := S') (X := N') Q
                    (((f.restrictScalars A).rTensor Q) y) :=
              congrArg
                (tensor_with_localized_test_module_compare
                  (A := A) (B := B) (S := S) (S' := S') (X := N') Q) hxy
            simpa [tensor_with_localized_test_module_compare_intertwines
                (A := A) (B := B) (S := S) (S' := S')
                (X := N) (Y := N') (g := f) (Q := Q)] using hxy'

end

end

end

end LinearMap

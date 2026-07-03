import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_82_12 (from Chap10) -/
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

/-! ### Lemma_10_82_13 (from Chap10) -/
universe u v w z

namespace LinearMap

open CategoryTheory
open CategoryTheory.ShortComplex
open CategoryTheory.MonoidalCategory
open RelSeries

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- The map on quotients modulo `I` induced by an `R`-linear map. -/
abbrev quotientMapByIdeal (f : M →ₗ[R] M') (I : Ideal R) :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R] M' ⧸ (I • (⊤ : Submodule R M')) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M')) f
    (Submodule.smul_top_le_comap_smul_top I f)

end

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

private theorem quotientMapByIdeal_lTensor_naturality {I : Ideal R} (f : M →ₗ[R] M') :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul M I =
      TensorProduct.quotTensorEquivQuotSMul M' I ∘ₗ f.lTensor (R ⧸ I) := by
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 10.82.13: every element of `I • ⊤` already lies in `J • ⊤` for some
finitely generated subideal `J ≤ I`. -/
private theorem exists_fg_subideal_of_mem_smul_top
    {N : Type*} [AddCommGroup N] [Module R N] {I : Ideal R} {x : N}
    (hx : x ∈ I • (⊤ : Submodule R N)) :
    ∃ J : Ideal R, J ≤ I ∧ J.FG ∧ x ∈ J • (⊤ : Submodule R N) := by
  -- Realize the membership by a finite linear combination and collect the coefficients into one
  -- finitely generated subideal.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    refine ⟨Ideal.span ({r} : Set R), ?_, ?_, ?_⟩
    · exact Ideal.span_le.2 (by
        intro s hs
        simp at hs
        simpa [hs] using hr)
    · simpa [Ideal.submodule_span_eq] using
        (Submodule.fg_span (R := R) (s := ({r} : Set R)) (by simpa))
    · exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) (by simpa using hy)
  · intro y z hy hz
    classical
    rcases hy with ⟨Jy, hJyI, hJyfg, hymem⟩
    rcases hz with ⟨Jz, hJzI, hJzfg, hzmem⟩
    rcases hJyfg with ⟨Sy, hSy⟩
    rcases hJzfg with ⟨Sz, hSz⟩
    refine ⟨Jy ⊔ Jz, sup_le hJyI hJzI, ⟨Sy ∪ Sz, ?_⟩, ?_⟩
    · rw [Finset.coe_union, Ideal.span_union, hSy, hSz]
    exact Submodule.add_mem _ ((Submodule.smul_mono_left le_sup_left) hymem)
      ((Submodule.smul_mono_left le_sup_right) hzmem)

private theorem injective_of_ladder_linearEquiv
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply e₁.symm.injective
  apply hf
  apply e₂.injective
  calc
    e₂ (f (e₁.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = g y := hxy
    _ = e₂ (f (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

/-- Helper for Lemma 10.82.13: changing the right tensor factor by a linear equivalence preserves
injectivity of the tensorized map. -/
private theorem injective_rTensor_of_linearEquiv
    {Q P : Type*} [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] M') (e : Q ≃ₗ[R] P) (hP : Function.Injective (f.rTensor P)) :
    Function.Injective (f.rTensor Q) := by
  -- Compare the two tensorized maps through the linear equivalence induced by `e`.
  let eM : TensorProduct R M Q ≃ₗ[R] TensorProduct R M P := e.lTensor M
  let eM' : TensorProduct R M' Q ≃ₗ[R] TensorProduct R M' P := e.lTensor M'
  have hSquare :
      (f.rTensor Q).comp eM.symm.toLinearMap =
        eM'.symm.toLinearMap.comp (f.rTensor P) := by
    apply TensorProduct.ext'
    intro x y
    simp [eM, eM', LinearEquiv.lTensor]
  exact injective_of_ladder_linearEquiv hSquare hP

/-- Helper for Lemma 10.82.13: tensoring with the zero submodule gives an injective map because
the source tensor product is a subsingleton. -/
private theorem injective_rTensor_bot_submodule {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] M') :
    Function.Injective (f.rTensor ↥(⊥ : Submodule R Q)) := by
  -- The bottom submodule has only one element, so every map out of its tensor product is injective.
  intro x y _
  exact Subsingleton.elim x y

/-- A universally injective linear map stays injective after reduction modulo any ideal. -/
theorem injective_quotientMapByIdeal_of_universallyInjective (f : M →ₗ[R] M')
    (hf : UniversallyInjective.{u, v, w, max u v w z} f) (I : Ideal R) :
    Function.Injective (f.quotientMapByIdeal I) := by
  -- Specialize universal injectivity to a lifted copy of `R ⧸ I` in the fixed test-module
  -- universe `max u v w z`, then transport injectivity back along `ULift.moduleEquiv`.
  have hRTensorInj :
      Function.Injective (f.rTensor (ULift.{max v w z} (R ⧸ I))) := by
    exact hf (ULift.{max v w z} (R ⧸ I)) inferInstance inferInstance
  have hRTensorBase :
      Function.Injective (f.rTensor (R ⧸ I)) := by
    exact injective_rTensor_of_linearEquiv f ULift.moduleEquiv.symm hRTensorInj
  -- Rewrite the resulting right-tensor injectivity as injectivity of the left-tensor map
  -- appearing in the quotient/tensor comparison square.
  have hTensorInj : Function.Injective (f.lTensor (R ⧸ I)) := by
    simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using
      hRTensorBase
  -- The quotient module is canonically identified with tensoring by `R ⧸ I`, so the comparison
  -- square transports injectivity back to the quotient map.
  exact injective_of_ladder_linearEquiv
    (quotientMapByIdeal_lTensor_naturality (f := f) (I := I)) hTensorInj

/-- Helper for Lemma 10.82.13: injectivity of the quotient map modulo `I` implies injectivity of
the tensorized map with `R ⧸ I`. -/
private theorem injective_rTensor_of_injective_quotientMapByIdeal (f : M →ₗ[R] M')
    (I : Ideal R) (hI : Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective (f.rTensor (R ⧸ I)) := by
  -- Rewrite the quotient module as `(R ⧸ I) ⊗ M` and transport injectivity back to tensor form.
  let eM := TensorProduct.quotTensorEquivQuotSMul M I
  let eM' := TensorProduct.quotTensorEquivQuotSMul M' I
  have hTensorInj : Function.Injective (f.lTensor (R ⧸ I)) := by
    have hSquare :
      (f.lTensor (R ⧸ I)).comp eM.symm.toLinearMap =
        eM'.symm.toLinearMap.comp (f.quotientMapByIdeal I) := by
      apply DFunLike.ext
      intro z
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) z
      simp [eM, eM', LinearMap.quotientMapByIdeal]
    exact injective_of_ladder_linearEquiv hSquare hI
  simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using hTensorInj

/-- Helper for Lemma 10.82.13: injectivity modulo finitely generated ideals upgrades to arbitrary
ideals because any specific congruence in `I • ⊤` uses only finitely many coefficients from `I`. -/
private theorem injective_quotientMapByIdeal_of_injective_mod_fg (f : M →ₗ[R] M')
    (hfg : ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I))
    (I : Ideal R) :
    Function.Injective (f.quotientMapByIdeal I) := by
  -- Route correction: realize the filtered-colimit sentence pointwise by shrinking one witness in
  -- `I • ⊤` to a finitely generated subideal.
  intro x y hxy
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) y
  have hmem :
      f (m - n) ∈ (I • (⊤ : Submodule R M') : Submodule R M') := by
    have hxy' :
        ((I • (⊤ : Submodule R M')).mkQ (f m)) =
          ((I • (⊤ : Submodule R M')).mkQ (f n)) := by
      simpa [LinearMap.quotientMapByIdeal] using hxy
    exact by
      simpa [map_sub] using
        (Submodule.Quotient.eq (I • (⊤ : Submodule R M') : Submodule R M')).mp hxy'
  obtain ⟨J, hJI, hJfg, hJmem⟩ :=
    exists_fg_subideal_of_mem_smul_top (R := R) hmem
  have hxyJ :
      ((J • (⊤ : Submodule R M)).mkQ m) = ((J • (⊤ : Submodule R M)).mkQ n) := by
    apply hfg J hJfg
    change ((J • (⊤ : Submodule R M')).mkQ (f m)) =
      ((J • (⊤ : Submodule R M')).mkQ (f n))
    exact (Submodule.Quotient.eq (J • (⊤ : Submodule R M') : Submodule R M')).2 <| by
      simpa [map_sub] using hJmem
  exact (Submodule.Quotient.eq (I • (⊤ : Submodule R M) : Submodule R M)).2 <| by
    have hJzero :
        m - n ∈ (J • (⊤ : Submodule R M) : Submodule R M) := by
      exact (Submodule.Quotient.eq (J • (⊤ : Submodule R M) : Submodule R M)).mp hxyJ
    exact (Submodule.smul_mono_left hJI) hJzero

/-- Helper for Lemma 10.82.13: in a short exact sequence of test modules, injectivity of
`f ⊗ -` on the ends forces injectivity in the middle once the target module is flat. -/
private theorem injective_rTensor_of_shortExact_step [Module.Flat R M']
    (f : M →ₗ[R] M')
    {Q₁ Q₂ Q₃ : Type*}
    [AddCommGroup Q₁] [Module R Q₁]
    [AddCommGroup Q₂] [Module R Q₂]
    [AddCommGroup Q₃] [Module R Q₃]
    {i : Q₁ →ₗ[R] Q₂} {π : Q₂ →ₗ[R] Q₃}
    (hi : Function.Injective i) (hex : Function.Exact i π) (hπ : Function.Surjective π)
    (hQ₁ : Function.Injective (f.rTensor Q₁))
    (hQ₃ : Function.Injective (f.rTensor Q₃)) :
    Function.Injective (f.rTensor Q₂) := by
  -- Chase a difference through the tensorized quotient map, then pull it back to the left term and
  -- kill that preimage using flatness of `M'` together with injectivity on `Q₁`.
  intro x y hxy
  let d : TensorProduct R M Q₂ := x - y
  have hdQ₃ : (π.lTensor M) d = 0 := by
    apply hQ₃
    calc
      (f.rTensor Q₃) ((π.lTensor M) d)
          = ((π.lTensor M').comp (f.rTensor Q₂)) d := by
              rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
                LinearMap.lTensor_comp_rTensor]
      _ = 0 := by
            change ((π.lTensor M').comp (f.rTensor Q₂)) (x - y) = 0
            rw [LinearMap.comp_apply, map_sub, hxy, sub_self]
            simp
  obtain ⟨z, hz⟩ := ((lTensor_exact M hex hπ) d).mp hdQ₃
  have hiTensor : Function.Injective (i.lTensor M') := by
    -- Flatness keeps the left map injective after tensoring with `M'`.
    exact Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hfd : (f.rTensor Q₂) d = 0 := by
    change (f.rTensor Q₂) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hzTensor : (f.rTensor Q₁) z = 0 := by
    apply hiTensor
    calc
      (i.lTensor M') ((f.rTensor Q₁) z)
          = ((f.rTensor Q₂).comp (i.lTensor M)) z := by
              change ((i.lTensor M').comp (f.rTensor Q₁)) z =
                ((f.rTensor Q₂).comp (i.lTensor M)) z
              rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
      _ = (f.rTensor Q₂) d := by
            rw [LinearMap.comp_apply, hz]
      _ = 0 := hfd
  have hzZero : z = 0 := hQ₁ hzTensor
  have hdZero : d = 0 := by simpa [hzZero] using hz.symm
  simpa [d, sub_eq_zero] using hdZero

/-- Helper for Lemma 10.82.13: a cyclic filtration propagates injectivity of `f ⊗ -` from the
initial stage to the final stage once every cyclic quotient `R ⧸ I` is controlled. -/
private theorem injective_rTensor_of_cyclic_filtration [Module.Flat R M']
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] M') (s : CyclicFiltration R Q)
    (hquot : ∀ I : Ideal R, Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective (f.rTensor ↥(s.head)) → Function.Injective (f.rTensor ↥(s.last)) := by
  -- Follow the filtration one snoc step at a time, using the short exact tensor step for each
  -- cyclic quotient.
  induction s using RelSeries.inductionOn' with
  | singleton N =>
      intro hN
      simpa using hN
  | snoc s K hrel ih =>
      rcases hrel with ⟨hle, I, hIquot⟩
      intro hs
      have hprevLast : Function.Injective (f.rTensor ↥(s.last)) := ih hs
      have hprev :
          Function.Injective (f.rTensor ↥(s.last.submoduleOf K)) := by
        -- Rewrite the previous stage through the canonical equivalence `s.last.submoduleOf K ≃ s.last`.
        exact injective_rTensor_of_linearEquiv f (Submodule.submoduleOfEquivOfLe hle) hprevLast
      obtain ⟨e⟩ := hIquot
      have hquotRI : Function.Injective (f.rTensor (R ⧸ I)) :=
        injective_rTensor_of_injective_quotientMapByIdeal f I (hquot I)
      have hquotStep :
          Function.Injective (f.rTensor (↥K ⧸ s.last.submoduleOf K)) := by
        -- Transport the cyclic-quotient injectivity back across the chosen equivalence with `R ⧸ I`.
        exact injective_rTensor_of_linearEquiv f e hquotRI
      rw [RelSeries.last_snoc]
      exact injective_rTensor_of_shortExact_step (f := f)
        (Q₁ := ↥(s.last.submoduleOf K)) (Q₂ := ↥K)
        (Q₃ := ↥K ⧸ s.last.submoduleOf K)
        (i := (s.last.submoduleOf K).subtype) (π := (s.last.submoduleOf K).mkQ)
        (Submodule.injective_subtype (s.last.submoduleOf K))
        (LinearMap.exact_subtype_mkQ (s.last.submoduleOf K))
        (Submodule.mkQ_surjective (s.last.submoduleOf K))
        hprev hquotStep

/-- Helper for Lemma 10.82.13: the cyclic-filtration argument from the source proof shows that
injectivity on every cyclic quotient `R ⧸ I` already implies injectivity after tensoring with an
arbitrary finite module. -/
private theorem injective_rTensor_of_finite_module_of_injective_mod_finite_ideal
    [Module.Flat R M'] {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (f : M →ₗ[R] M') (hquot : ∀ I : Ideal R, Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective (f.rTensor Q) := by
  obtain ⟨s, hs_head, hs_last⟩ := exists_finite_cyclic_filtration (R := R) (M := Q)
  -- Start at `⊥`, where the tensor source is subsingleton, and propagate injectivity through the
  -- cyclic filtration to the final stage `⊤ = Q`.
  have hhead : Function.Injective (f.rTensor ↥(s.head)) := by
    rw [hs_head]
    exact injective_rTensor_bot_submodule (R := R) (M := M) (M' := M') f
  have hlast : Function.Injective (f.rTensor ↥(s.last)) :=
    injective_rTensor_of_cyclic_filtration (R := R) (M := M) (M' := M')
      (Q := Q) f s hquot hhead
  rw [hs_last] at hlast
  -- Identify the final stage `⊤` with the ambient module `Q`.
  exact injective_rTensor_of_linearEquiv (R := R) (M := M) (M' := M') f
    Submodule.topEquiv.symm hlast

/-- Helper for Lemma 10.82.13: testing the finitely generated ideal criterion at `I = ⊥` already
forces the original map `f` to be injective. -/
private theorem injective_of_injective_mod_finite_ideal
    (f : M →ₗ[R] M')
    (hfg : ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective f := by
  -- The quotient modulo the zero ideal is just the original map viewed through the trivial
  -- quotient, so injectivity there descends back to `f`.
  have hquot : Function.Injective (f.quotientMapByIdeal (⊥ : Ideal R)) :=
    hfg ⊥ (by simpa using (Submodule.fg_bot : (⊥ : Ideal R).FG))
  intro x y hxy
  have hxyQ :
      (((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ x) =
        (((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ y) := by
    apply hquot
    simp [LinearMap.quotientMapByIdeal, hxy]
  have hmem : x - y ∈ ((⊥ : Ideal R) • (⊤ : Submodule R M) : Submodule R M) :=
    (Submodule.Quotient.eq (((⊥ : Ideal R) • (⊤ : Submodule R M) : Submodule R M))).mp hxyQ
  simpa [sub_eq_zero] using hmem

/-- Helper for Lemma 10.82.13: the already-closed finite-module filtration argument applies in
particular to finitely presented test modules. -/
private theorem injective_rTensor_of_finitelyPresented_of_injective_mod_finite_ideal
    [Module.Flat R M'] {Q : Type*} [AddCommGroup Q] [Module R Q]
    [Module.FinitePresentation R Q]
    (f : M →ₗ[R] M')
    (hfg : ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective (f.rTensor Q) := by
  -- Route correction: the cyclic-filtration proof is already finished for finite modules, so the
  -- finitely presented case is just the typeclass bridge `FinitePresentation -> Finite`.
  letI : Module.Finite R Q := inferInstance
  exact injective_rTensor_of_finite_module_of_injective_mod_finite_ideal
    (R := R) (M := M) (M' := M') (Q := Q) f
    (fun I ↦ injective_quotientMapByIdeal_of_injective_mod_fg
      (R := R) (M := M) (M' := M') f hfg I)

/-- Helper for Lemma 10.82.13: injectivity of `f ⊗ Q` for every finite module `Q` already implies
universal injectivity, because any tensor equality uses only a finite submodule of the right-hand
tensor factor and flatness of `M'` makes the ambient inclusion detectable after tensoring. -/
private theorem universallyInjective_of_injective_rTensor_finite_modules
    [Module.Flat R M'] (f : M →ₗ[R] M')
    (hfinite :
      ∀ {Q : Type z} [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
        Function.Injective (f.rTensor Q)) :
    UniversallyInjective.{u, v, w, z} f := by
  unfold UniversallyInjective
  intro Q _ _
  intro x y hxy
  let s : Set (TensorProduct R M Q) := {x, y}
  have hs : s.Finite := by
    simp [s]
  obtain ⟨Q', hQ'finite, hsQ'⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite (R := R) (M := M) (N := Q) s hs
  have hx_mem : x ∈ s := by
    simp [s]
  have hy_mem : y ∈ s := by
    simp [s]
  obtain ⟨x', hx'⟩ := hsQ' hx_mem
  obtain ⟨y', hy'⟩ := hsQ' hy_mem
  have hSubtypeInj : Function.Injective (Q'.subtype.lTensor M') := by
    -- Flatness of `M'` keeps the finite-submodule inclusion injective after tensoring.
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M') Q'.subtype
      (Submodule.injective_subtype Q')
  have hxy' : (f.rTensor Q') x' = (f.rTensor Q') y' := by
    -- Compare `x` and `y` inside the finite submodule through tensor naturality.
    apply hSubtypeInj
    calc
      (Q'.subtype.lTensor M') ((f.rTensor Q') x')
          = (f.rTensor Q) ((Q'.subtype.lTensor M) x') := by
              rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
                LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
      _ = (f.rTensor Q) x := by
            rw [hx']
      _ = (f.rTensor Q) y := hxy
      _ = (f.rTensor Q) ((Q'.subtype.lTensor M) y') := by
            rw [hy']
      _ = (Q'.subtype.lTensor M') ((f.rTensor Q') y') := by
            rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
              LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hQ'inj : Function.Injective (f.rTensor Q') := hfinite (Q := Q')
  have hxy0 : x' = y' := hQ'inj hxy'
  -- Once the equality is proved in the finite tensor factor, transport it back to `M ⊗ Q`.
  calc
    x = (Q'.subtype.lTensor M) x' := hx'.symm
    _ = (Q'.subtype.lTensor M) y' := by
          rw [hxy0]
    _ = y := hy'

/-- Helper for Lemma 10.82.13: universal injectivity proved in the fixed test universe descends to
the public hidden-universe formulation by testing any module through its `ULift`. -/
private theorem universallyInjective_max_test_universe_to_test_universe
    (f : M →ₗ[R] M')
    (hf : UniversallyInjective.{u, v, w, max u v w z} f) :
    UniversallyInjective.{u, v, w, z} f := by
  unfold UniversallyInjective at hf ⊢
  intro Q _ _
  have hLift :
      Function.Injective (f.rTensor (ULift.{max u v w z} Q)) := by
    exact hf (ULift.{max u v w z} Q) inferInstance inferInstance
  -- Transport injectivity back across the canonical equivalence `ULift Q ≃ Q`.
  exact injective_rTensor_of_linearEquiv
    (R := R) (M := M) (M' := M') f ULift.moduleEquiv.symm hLift

/-- Helper for Lemma 10.82.13: the criterion proved at the explicit test-module universe
`max u v w z`, which is the stable universe in which the source-proof filtration argument closes. -/
private theorem universallyInjective_max_test_universe_iff_injective_mod_finite_ideal
    [Module.Flat R M'] (f : M →ₗ[R] M') :
    UniversallyInjective.{u, v, w, max u v w z} f ↔
      ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I) := by
  constructor
  · intro hf I hI
    -- The forward implication is the existing reduction-modulo-`I` specialization of universal
    -- injectivity at the stable test-module universe.
    exact injective_quotientMapByIdeal_of_universallyInjective
      (R := R) (M := M) (M' := M') f hf I
  · intro hfg
    have hfinite :
        ∀ {Q : Type (max u v w z)} [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
          Function.Injective (f.rTensor Q) := by
      intro Q _ _ _
      -- The source-proof cyclic-filtration argument is already closed for every finite module.
      exact injective_rTensor_of_finite_module_of_injective_mod_finite_ideal
        (R := R) (M := M) (M' := M') (Q := Q) f
        (fun I ↦ injective_quotientMapByIdeal_of_injective_mod_fg
          (R := R) (M := M) (M' := M') f hfg I)
    exact universallyInjective_of_injective_rTensor_finite_modules
      (R := R) (M := M) (M' := M') f
      (fun {Q} _ _ _ ↦ hfinite (Q := Q))

/-- Lemma 10.82.13: if `M'` is a flat `R`-module, then an `R`-linear map `M → M'` is universally
injective if and only if the induced map `M / I M → M' / I M'` is injective for every finitely
generated ideal `I` of `R`. -/
theorem universallyInjective_iff_injective_mod_finite_ideal [Module.Flat R M']
    (f : M →ₗ[R] M') :
    UniversallyInjective.{u, v, w, max u v w z} f ↔
      ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I) := by
  -- Route correction: the theorem statement must expose the fixed test-module universe in which
  -- the source-proof filtration argument closes; this is a meaning-preserving universe repair.
  exact universallyInjective_max_test_universe_iff_injective_mod_finite_ideal
    (R := R) (M := M) (M' := M') f

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Flat A N]

open IsLocalRing

-- Proof sketch: apply `universallyInjective_iff_injective_mod_finite_ideal`. For a finitely
-- generated ideal `J`, pass to the quotient local ring `A / J`; the induced map on
-- `M / J M → N / J N` has injective reduction modulo its maximal ideal by the hypothesis on
-- `u`, and flatness descends to the quotient modules, so the local criterion over `A / J`
-- upgrades that closed-fiber injectivity to injectivity modulo `J`.
/-- Over a local ring, a linear map between flat modules is universally injective as soon as its
reduction modulo the maximal ideal is injective. -/
theorem universallyInjective_of_injective_mod_maximalIdeal (u : M →ₗ[A] N)
    (hu : Function.Injective (u.quotientMapByIdeal (maximalIdeal A))) :
    UniversallyInjective.{u, v, w, u} u := by
  have hmax :
      UniversallyInjective.{u, v, w, max u v w u} u := by
    refine (universallyInjective_iff_injective_mod_finite_ideal u).2 ?_
    intro J hJ
    sorry
  exact universallyInjective_max_test_universe_to_test_universe
    (R := A) (M := M) (M' := N) u hmax

end

end

end LinearMap

/-! ### Lemma_10_82_14 (from Chap10) -/
open scoped TensorProduct

universe u v w x

namespace LinearMap

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} {N : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- Helper for Lemma 10.82.14: after identifying `M` with `R ⊗[R] M` and commuting the factors,
the tensor of `R → S` agrees with the canonical map `m ↦ m ⊗ₜ 1`. -/
lemma tensorProduct_mk_one_eq
    (M : Type w) [AddCommGroup M] [Module R M] :
    (TensorProduct.comm R S M).toLinearMap.comp
        (((Algebra.linearMap R S).rTensor M).comp (TensorProduct.lid R M).symm.toLinearMap) =
      (TensorProduct.mk R M S).flip (1 : S) := by
  -- Compare the two linear maps on an arbitrary element of `M`.
  ext m
  simp [TensorProduct.lid_symm_apply]

/-- Helper for Lemma 10.82.14: universal injectivity of `R → S` makes the canonical map
`m ↦ m ⊗ₜ 1` injective for every `R`-module `M`. -/
lemma tensorProduct_mk_one_injective_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max w x} (Algebra.linearMap R S)) :
    Function.Injective ((TensorProduct.mk R M S).flip (1 : S)) := by
  let eM : ULift.{x} M ≃ₗ[R] M := ULift.moduleEquiv
  let eTensor : ULift.{x} M ⊗[R] S ≃ₗ[R] M ⊗[R] S :=
    TensorProduct.congr eM (LinearEquiv.refl R S)
  have hLiftedInjective :
      Function.Injective ((TensorProduct.mk R (ULift.{x} M) S).flip (1 : S)) := by
    -- On the lifted module, the universal injectivity hypothesis applies directly.
    rw [← tensorProduct_mk_one_eq (R := R) (S := S) (ULift.{x} M)]
    exact (TensorProduct.comm R S (ULift.{x} M)).injective.comp
      ((hS (ULift.{x} M) inferInstance inferInstance).comp
        (TensorProduct.lid R (ULift.{x} M)).symm.injective)
  have hCompat :
      eTensor.toLinearMap.comp ((TensorProduct.mk R (ULift.{x} M) S).flip (1 : S)) =
        ((TensorProduct.mk R M S).flip (1 : S)).comp eM.toLinearMap := by
    -- The tensor canonical map commutes with the linear equivalence `ULift M ≃ₗ[R] M`.
    ext m
    simp [eM, eTensor]
  intro m₁ m₂ hm
  have hLiftedEq : ULift.up m₁ = ULift.up m₂ := by
    -- Transport the equality to the lifted module, where injectivity is available.
    apply hLiftedInjective
    apply eTensor.injective
    calc
      eTensor (((TensorProduct.mk R (ULift.{x} M) S).flip (1 : S)) (ULift.up m₁)) =
          ((TensorProduct.mk R M S).flip (1 : S)) (eM (ULift.up m₁)) := by
            simpa [LinearMap.comp_apply] using LinearMap.congr_fun hCompat (ULift.up m₁)
      _ = ((TensorProduct.mk R M S).flip (1 : S)) m₁ := by
            simp [eM]
      _ = ((TensorProduct.mk R M S).flip (1 : S)) m₂ := hm
      _ = ((TensorProduct.mk R M S).flip (1 : S)) (eM (ULift.up m₂)) := by
            simp [eM]
      _ = eTensor (((TensorProduct.mk R (ULift.{x} M) S).flip (1 : S)) (ULift.up m₂)) := by
            symm
            simpa [LinearMap.comp_apply] using LinearMap.congr_fun hCompat (ULift.up m₂)
  simpa using hLiftedEq

/-- Helper for Lemma 10.82.14: tensoring commutes with the canonical map `m ↦ m ⊗ₜ 1`. -/
lemma rTensor_comp_tensorProduct_mk_one {f : M →ₗ[R] N} :
    (f.rTensor S).comp ((TensorProduct.mk R M S).flip (1 : S)) =
      ((TensorProduct.mk R N S).flip (1 : S)).comp f := by
  -- This is the standard `rTensor` naturality formula specialized at the tensor factor `1`.
  simpa using (LinearMap.rTensor_comp_flip_mk (M := S) (f := f) (m := (1 : S)))

/-- Helper for Lemma 10.82.14: if `f ⊗[R] S` is surjective, then the tensor of the quotient map to
the cokernel `N ⧸ range f` is zero. -/
lemma quotientMap_rTensor_eq_zero_of_rTensor_surjective {f : M →ₗ[R] N}
    (hf : Function.Surjective (f.rTensor S)) :
    (((LinearMap.range f).mkQ).rTensor S) = 0 := by
  -- Evaluate on pure tensors and pull each one back along the surjective tensor map.
  apply LinearMap.ext
  intro z
  obtain ⟨y, rfl⟩ := hf z
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.range_mkQ_comp]
  simp

-- Proof sketch: injectivity is detected by applying the universal injectivity hypothesis to the
-- kernel inclusion `ker f → M`.
/-- Lemma 10.82.14 (injective clause): if `R → S` is universally injective as an `R`-module map,
then tensoring an `R`-linear map with `S` reflects injectivity. -/
theorem injective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Injective (f.rTensor S)) : Function.Injective f := by
  intro x y hxy
  -- Apply the naturality square for `m ↦ m ⊗ₜ 1` and cancel with the injectivity of `f ⊗[R] S`.
  have hTensor :
      ((TensorProduct.mk R M S).flip (1 : S)) x =
        ((TensorProduct.mk R M S).flip (1 : S)) y := by
    apply hf
    calc
      (f.rTensor S) (((TensorProduct.mk R M S).flip (1 : S)) x) =
          ((TensorProduct.mk R N S).flip (1 : S)) (f x) := by
            simpa [LinearMap.comp_apply] using
              LinearMap.congr_fun (rTensor_comp_tensorProduct_mk_one (R := R) (S := S) (f := f)) x
      _ = ((TensorProduct.mk R N S).flip (1 : S)) (f y) := by
            rw [hxy]
      _ = (f.rTensor S) (((TensorProduct.mk R M S).flip (1 : S)) y) := by
            simpa [LinearMap.comp_apply] using
              (LinearMap.congr_fun
                (rTensor_comp_tensorProduct_mk_one (R := R) (S := S) (f := f)) y).symm
  -- The universally injective base-change map detects equality back in `M`.
  exact tensorProduct_mk_one_injective_of_universallyInjective (R := R) (S := S) (M := M) hS hTensor

-- Proof sketch: surjectivity is detected from the cokernel after tensoring and the same universal
-- injectivity hypothesis applied to the canonical map `Q → Q ⊗[R] S`.
/-- Lemma 10.82.14 (surjective clause): if `R → S` is universally injective as an `R`-module map,
then tensoring an `R`-linear map with `S` reflects surjectivity. -/
theorem surjective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Surjective (f.rTensor S)) : Function.Surjective f := by
  intro y
  -- The tensor of the cokernel quotient map vanishes because `f ⊗[R] S` is surjective.
  have hQuotZero :
      (((LinearMap.range f).mkQ).rTensor S) = 0 :=
    quotientMap_rTensor_eq_zero_of_rTensor_surjective (R := R) (S := S) (f := f) hf
  have hCompZero :
      ((TensorProduct.mk R (N ⧸ LinearMap.range f) S).flip (1 : S)).comp (LinearMap.range f).mkQ =
        0 := by
    -- Tensor naturality turns the zero quotient tensor map into a zero canonical map on the
    -- quotient itself.
    calc
      ((TensorProduct.mk R (N ⧸ LinearMap.range f) S).flip (1 : S)).comp (LinearMap.range f).mkQ =
          (((LinearMap.range f).mkQ).rTensor S).comp ((TensorProduct.mk R N S).flip (1 : S)) := by
            symm
            exact rTensor_comp_tensorProduct_mk_one
              (R := R) (S := S) (f := (LinearMap.range f).mkQ)
      _ = 0 := by
            rw [hQuotZero, zero_comp]
  have hTensorZero :
      ((TensorProduct.mk R (N ⧸ LinearMap.range f) S).flip (1 : S)) ((LinearMap.range f).mkQ y) =
        0 := by
    -- Evaluate the zero composite at the class of `y`.
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hCompZero y
  have hClassZero : (LinearMap.range f).mkQ y = 0 := by
    -- Universal injectivity applied to the quotient module detects that the cokernel class is
    -- already zero.
    apply tensorProduct_mk_one_injective_of_universallyInjective
      (R := R) (S := S) (M := N ⧸ LinearMap.range f) hS
    simpa using hTensorZero
  have hy_range : y ∈ LinearMap.range f := by
    -- Zero class in the cokernel is exactly membership in the range.
    exact (Submodule.Quotient.mk_eq_zero (p := LinearMap.range f) (x := y)).1 <|
      by simpa [Submodule.mkQ_apply] using hClassZero
  -- Unpack range membership to produce a preimage of `y`.
  simpa [LinearMap.mem_range] using hy_range

-- Proof sketch: bijectivity is the conjunction of injectivity and surjectivity.
/-- If tensoring with `S` makes an `R`-linear map bijective, then the original map is bijective,
provided `R → S` is universally injective as an `R`-module map. -/
theorem bijective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective.{u, u, v, max w x} (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Bijective (f.rTensor S)) : Function.Bijective f :=
  ⟨injective_of_rTensor_of_universallyInjective hS hf.1,
    surjective_of_rTensor_of_universallyInjective hS hf.2⟩

end

end LinearMap

/-! ### Lemma_10_82_15 (from Chap10) -/
universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Lemma 10.82.15: if `R → S` is faithfully flat, then for every `R`-module `N` the canonical
map `N →ₗ[R] S ⊗[R] N` is injective, which is the Lean form of saying that `R → S` is
universally injective as a map of `R`-modules. This is exactly the canonical theorem
`Module.FaithfullyFlat.tensorProduct_mk_injective`. -/
recall Module.FaithfullyFlat.tensorProduct_mk_injective

/- Companion check: the textbook corollary `R ∩ IS = I` is the canonical contraction statement
`(I.map (algebraMap R S)).comap (algebraMap R S) = I`. This is exactly
`Ideal.comap_map_eq_self_of_faithfullyFlat`. -/
recall Ideal.comap_map_eq_self_of_faithfullyFlat

end

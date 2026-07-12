import Mathlib
import StacksProject_2024.Chap10.Lemma_10_82_14
import StacksProject_2024.Chap15.Lemma_15_105_7
import StacksProject_2024.Chap15.Lemma_15_106_2
import StacksProject_2024.Chap15.Lemma_15_106_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped MaximalWeaklyEtaleSubalgebraNotation

variable {K : Type u} [Field K]
variable {L : Type v} [Field L] [Algebra K L]
variable {A : Type w} [CommRing A] [Algebra K A]
variable (K) (L) (A)

/- Domain-style sampling for Lemma 15.106.4:
- primary domain: commutative algebra of maximal weakly étale subalgebras under base change along
  a field extension;
- sampled owner declarations:
  `maximalWeaklyEtaleSubalgebra`,
  `isWeaklyEtale_maximalWeaklyEtaleSubalgebra`,
  `le_maximalWeaklyEtaleSubalgebra`,
  `Algebra.IsWeaklyEtale.baseChange`;
- target layer: `source-facing`, since the Stacks lemma identifies the base change of `B_max(A⁄K)`
  with `B_max((A ⊗[K] L)⁄L)`;
- core/canonical owner abstraction: the source-facing owner remains `B_max` from
  `Lemma_15_106_2`; the only primitive bridge data here is the tensor-base-change hom obtained
  from the inclusion `B_max(A⁄K) ↪ A`;
- primitive vs. derived: the primitive data is the ambient tensor-base-change hom
  `B_max(A⁄K) ⊗[K] L →ₐ[L] A ⊗[K] L`; landing in `B_max((A ⊗[K] L)⁄L)` and bijectivity are
  derived API.

This file should therefore state the canonical map directly as an `L`-algebra hom into
`B_max((A ⊗[K] L)⁄L)`, rather than routing the public surface through a `K`-algebra map into a
`restrictScalars` codomain.
-/

/-- The ambient tensor-base-change map `B_max(A/K) ⊗[K] L → A ⊗[K] L` obtained by tensoring the
inclusion `B_max(A/K) ↪ A` with `L`, viewed in its natural `L`-algebra form. -/
def maximalWeaklyEtaleSubalgebraTensorBaseChangeMap :
    B_max(A⁄K) ⊗[K] L →ₐ[L] A ⊗[K] L :=
  { __ := (Algebra.TensorProduct.map B_max(A⁄K).val (AlgHom.id K L)).toRingHom
    commutes' := by
      intro l
      change (Algebra.TensorProduct.map B_max(A⁄K).val (AlgHom.id K L))
          ((includeRight : L →ₐ[K] B_max(A⁄K) ⊗[K] L) l) =
        (includeRight : L →ₐ[K] A ⊗[K] L) l
      simp }

/-- Helper for Lemma 15.106.4: the range of the ambient tensor-base-change map is contained in the
maximal weakly étale `L`-subalgebra of `A ⊗[K] L`. -/
theorem range_maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_le :
    (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A).range ≤
      B_max((A ⊗[K] L)⁄L) := by
  let f := maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A
  have hfinj : Function.Injective (f : B_max(A⁄K) ⊗[K] L → A ⊗[K] L) := by
    -- Tensoring the inclusion `B_max(A/K) ↪ A` with the flat field extension preserves injectivity.
    change Function.Injective
      (TensorProduct.map B_max(A⁄K).val.toLinearMap (LinearMap.id : L →ₗ[K] L))
    simpa using TensorProduct.map_injective_of_flat_flat
      B_max(A⁄K).val.toLinearMap (LinearMap.id : L →ₗ[K] L)
      Subtype.val_injective (fun _ _ h ↦ h)
  -- Base change preserves weak étaleness of the source maximal weakly étale subalgebra.
  have hsource :
      Algebra.IsWeaklyEtale L (B_max(A⁄K) ⊗[K] L) := by
    have hbase :
        Algebra.IsWeaklyEtale L (L ⊗[K] B_max(A⁄K)) := by
      exact
        Algebra.IsWeaklyEtale.baseChange (A := K) (A' := L) (B := B_max(A⁄K))
          (isWeaklyEtale_maximalWeaklyEtaleSubalgebra (K := K) (A := A))
    -- Commute the tensor factors to match the source-facing tensor order used in this file.
    exact
      isWeaklyEtale_of_algEquiv (K := L)
        (Algebra.TensorProduct.commRight K L B_max(A⁄K)) hbase
  -- Route correction: prove weak étaleness of the actual image by the injective range equivalence.
  have hrange : Algebra.IsWeaklyEtale L f.range := by
    exact isWeaklyEtale_range_of_injective (K := L) f hfinj hsource
  -- Maximality then forces the image range into `B_max((A ⊗[K] L)/L)`.
  exact le_maximalWeaklyEtaleSubalgebra (K := L) (A := A ⊗[K] L) f.range hrange

-- Proof sketch: `B_max(A/K)` is weakly étale over `K` by Lemma `15.106.2`, so after base change
-- along `K → L` it remains weakly étale over `L`. Since the tensor-base-change map lands inside
-- `A ⊗[K] L`, maximality of `B_max((A ⊗[K] L)/L)` forces its image to lie in that subalgebra.
/-- The tensor-base-change map from `B_max(A/K) ⊗[K] L` lands in the maximal weakly étale
`L`-subalgebra of `A ⊗[K] L`. -/
theorem maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_mem
    (x : B_max(A⁄K) ⊗[K] L) :
    (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A :
      B_max(A⁄K) ⊗[K] L → A ⊗[K] L) x ∈ B_max((A ⊗[K] L)⁄L) := by
  -- Membership follows by applying the range inclusion to the image point itself.
  exact range_maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_le (K := K) (L := L) (A := A)
    ⟨x, rfl⟩

/-- Helper for Lemma 15.106.4: on a pure tensor, the ambient tensor-base-change map is the obvious
ambient pure tensor in `A ⊗[K] L`. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_apply_tmul
    (x : B_max(A⁄K)) (l : L) :
    (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A :
      B_max(A⁄K) ⊗[K] L → A ⊗[K] L) (x ⊗ₜ[K] l) =
      (((x : A) ⊗ₜ[K] l) : A ⊗[K] L) := by
  -- The map is induced by tensoring the inclusion `B_max(A/K) ↪ A`.
  simp [maximalWeaklyEtaleSubalgebraTensorBaseChangeMap]

/-- Helper for Lemma 15.106.4: the ambient tensor-base-change map is injective because tensoring
the inclusion `B_max(A/K) ↪ A` with the flat `K`-module `L` preserves injectivity. -/
theorem injective_maximalWeaklyEtaleSubalgebraTensorBaseChangeMap :
    Function.Injective
      (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A :
        B_max(A⁄K) ⊗[K] L → A ⊗[K] L) := by
  -- This is the standard tensor-product injectivity statement for a flat right factor.
  change Function.Injective
    (TensorProduct.map B_max(A⁄K).val.toLinearMap (LinearMap.id : L →ₗ[K] L))
  simpa using TensorProduct.map_injective_of_flat_flat
    B_max(A⁄K).val.toLinearMap (LinearMap.id : L →ₗ[K] L)
    Subtype.val_injective (fun _ _ h ↦ h)

/-- The canonical map from `B_max(A/K) ⊗[K] L` to the maximal weakly étale `L`-subalgebra of
`A ⊗[K] L`. -/
def maximalWeaklyEtaleSubalgebraTensorBaseChange :
    B_max(A⁄K) ⊗[K] L →ₐ[L] B_max((A ⊗[K] L)⁄L) :=
  (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A).codRestrict
    B_max((A ⊗[K] L)⁄L)
    (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_mem K L A)

/-- The codomain-restricted tensor-base-change map agrees with the ambient tensor-base-change map
after forgetting the target subalgebra. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraTensorBaseChange_apply
    (x : B_max(A⁄K) ⊗[K] L) :
    ↑((maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
      B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) x) =
      (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A :
        B_max(A⁄K) ⊗[K] L → A ⊗[K] L) x := rfl

/-- Helper for Lemma 15.106.4: the codomain-restricted base-change map has the same pure-tensor
formula as the ambient map after forgetting the target subalgebra. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraTensorBaseChange_apply_tmul
    (x : B_max(A⁄K)) (l : L) :
    ↑((maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
      B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) (x ⊗ₜ[K] l)) =
      (((x : A) ⊗ₜ[K] l) : A ⊗[K] L) := by
  -- Forget the codomain subalgebra and use the ambient pure-tensor formula.
  simp

/-- Helper for Lemma 15.106.4: the codomain-restricted tensor-base-change map is injective. -/
theorem injective_maximalWeaklyEtaleSubalgebraTensorBaseChange :
    Function.Injective
      (maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
        B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) := by
  intro x y hxy
  -- Forgetting the target subalgebra reduces injectivity to the ambient tensor map.
  apply injective_maximalWeaklyEtaleSubalgebraTensorBaseChangeMap
    (K := K) (L := L) (A := A)
  exact congrArg Subtype.val hxy

/-- Helper for Lemma 15.106.4: the canonical source-faithful identification
`((A ⊗[K] L) ⊗[L] Ω) ≃ A ⊗[K] Ω`, built by commuting the outer tensor factor, swapping
`A ⊗[K] L` to `L ⊗[K] A`, cancelling the base change, and commuting back. -/
noncomputable def maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv
    {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] :
    (A ⊗[K] L) ⊗[L] Ω ≃ₐ[Ω] A ⊗[K] Ω :=
  (Algebra.TensorProduct.commRight L Ω (A ⊗[K] L)).symm.trans
    ((show Ω ⊗[L] (A ⊗[K] L) ≃ₐ[Ω] Ω ⊗[L] (L ⊗[K] A) from
        Algebra.TensorProduct.congr
          (show Ω ≃ₐ[Ω] Ω from AlgEquiv.refl)
          (Algebra.TensorProduct.commRight K L A).symm).trans
      ((Algebra.TensorProduct.cancelBaseChange K L Ω Ω A).trans
        (Algebra.TensorProduct.commRight K Ω A)))

/-- Helper for Lemma 15.106.4: the tower identification sends a pure tensor
`((a ⊗ l) ⊗ ω)` to `a ⊗ (σ(l)ω)` in the one-step base change. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv_apply_tmul
    {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (a : A) (l : L) (ω : Ω) :
    maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv (K := K) (L := L) (A := A)
        (((a ⊗ₜ[K] l) : A ⊗[K] L) ⊗ₜ[L] ω) =
      (a ⊗ₜ[K] ((algebraMap L Ω l) * ω) : A ⊗[K] Ω) := by
  -- Evaluate the composite equivalence on a pure tensor and simplify each source-proof step.
  simp [maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv]
  rw [show l • ω = ((algebraMap L Ω) l) * ω by simpa [Algebra.smul_def]]

/-- Helper for Lemma 15.106.4: after base changing the `L`-version to an overfield `Ω`, the
canonical tower identification yields a comparison map into the `Ω`-version. -/
noncomputable def maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower
    {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] :
    B_max((A ⊗[K] L)⁄L) ⊗[L] Ω →ₐ[Ω] B_max((A ⊗[K] Ω)⁄Ω) :=
  (AlgHom.maximalWeaklyEtaleSubalgebraMap
      (K := Ω)
      (A' := (A ⊗[K] L) ⊗[L] Ω)
      (A := A ⊗[K] Ω)
      (maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv
        (K := K) (L := L) (A := A) (Ω := Ω)).toAlgHom).comp
    (maximalWeaklyEtaleSubalgebraTensorBaseChange
      (K := L) (L := Ω) (A := A ⊗[K] L))

/-- Helper for Lemma 15.106.4: forgetting the codomain subalgebra shows that the comparison map
is exactly the ambient `Ω`-base-change map transported along the tower equivalence. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower_apply
    {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (x : B_max((A ⊗[K] L)⁄L) ⊗[L] Ω) :
    ↑(maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower
        (K := K) (L := L) (A := A) (Ω := Ω) x) =
      maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv
        (K := K) (L := L) (A := A) (Ω := Ω)
        ((maximalWeaklyEtaleSubalgebraTensorBaseChangeMap
            L Ω (A ⊗[K] L) : B_max((A ⊗[K] L)⁄L) ⊗[L] Ω → (A ⊗[K] L) ⊗[L] Ω) x) := by
  -- Unfold the codomain restriction from `B_max` and the induced map along the tower equivalence.
  simp [maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower,
    AlgHom.maximalWeaklyEtaleSubalgebraMap_apply]

/-- Helper for Lemma 15.106.4: on pure tensors from `B_max((A ⊗[K] L)/L)`, the comparison map is
the tower equivalence applied to the ambient pure tensor. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower_apply_tmul
    {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (x : B_max((A ⊗[K] L)⁄L)) (ω : Ω) :
    ↑(maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower
        (K := K) (L := L) (A := A) (Ω := Ω) (x ⊗ₜ[L] ω)) =
      maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv
        (K := K) (L := L) (A := A) (Ω := Ω) (((x : A ⊗[K] L) ⊗ₜ[L] ω)) := by
  -- Specialize the previous ambient comparison formula to a pure tensor generator.
  simp [maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower_apply]

/-- Helper for Lemma 15.106.4: after transporting the iterated source tensor
`((B_max(A/K) ⊗[K] L) ⊗[L] Ω)` to `B_max(A/K) ⊗[K] Ω`, the `Ω`-version of the canonical map
factors through the `Ω`-tensor of the `L`-version followed by the tower comparison map. -/
theorem maximalWeaklyEtaleSubalgebraTensorBaseChange_factor_over_tower
    {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] :
    (maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower
        (K := K) (L := L) (A := A) (Ω := Ω)).toLinearMap ∘ₗ
      (maximalWeaklyEtaleSubalgebraTensorBaseChange
        (K := K) (L := L) (A := A)).toLinearMap.rTensor Ω =
    (maximalWeaklyEtaleSubalgebraTensorBaseChange
        (K := K) (L := Ω) (A := A)).toLinearMap ∘ₗ
      (maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv
        (K := K) (L := L) (A := B_max(A⁄K)) (Ω := Ω)).toLinearMap := by
  -- Compare the two `Ω`-linear maps on generators of the iterated source tensor product.
  apply TensorProduct.ext'
  intro z ω
  induction z using TensorProduct.induction_on with
  | zero =>
      simp [LinearMap.comp_apply]
  | tmul x l =>
      -- On a pure tensor, both routes reduce to the same ambient pure tensor in `A ⊗[K] Ω`.
      apply Subtype.ext
      simp [LinearMap.comp_apply]
  | add z₁ z₂ hz₁ hz₂ =>
      simp [LinearMap.comp_apply, hz₁, hz₂]

/-- Helper for Lemma 15.106.4: the tower comparison map is injective because forgetting to the
ambient tensor and transporting back along the tower equivalence reduces to the already-injective
base-change map over `L → Ω`. -/
theorem injective_maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower
    {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] :
    Function.Injective
      (maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower
        (K := K) (L := L) (A := A) (Ω := Ω) :
          B_max((A ⊗[K] L)⁄L) ⊗[L] Ω → B_max((A ⊗[K] Ω)⁄Ω)) := by
  intro x y hxy
  -- Forget the codomain subalgebra and transport the equality back to `(A ⊗[K] L) ⊗[L] Ω`.
  apply injective_maximalWeaklyEtaleSubalgebraTensorBaseChangeMap
    (K := L) (L := Ω) (A := A ⊗[K] L)
  apply (maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv
    (K := K) (L := L) (A := A) (Ω := Ω)).injective
  simpa [maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower_apply] using
    congrArg Subtype.val hxy

/-- Helper for Lemma 15.106.4: the scalar-extension linear map of a field extension is
universally injective, because tensoring an injective map between vector spaces stays injective. -/
theorem universallyInjective_algebraLinearMap_of_field_extension
    {Ω : Type*} [Field Ω] [Algebra L Ω] :
    LinearMap.UniversallyInjective (Algebra.linearMap L Ω) := by
  intro Q _ _
  -- Over a field, both tensor factors are flat, so tensoring preserves injectivity.
  change Function.Injective
    (TensorProduct.map (Algebra.linearMap L Ω) (LinearMap.id : Q →ₗ[L] Q))
  simpa using TensorProduct.map_injective_of_flat_flat
    (Algebra.linearMap L Ω) (LinearMap.id : Q →ₗ[L] Q)
    (fun _ _ h ↦ (algebraMap L Ω).injective h) (fun _ _ h ↦ h)

/-- Helper for Lemma 15.106.4: surjectivity of the canonical map can be checked after passing to
any overfield `Ω/L`. This is the source-faithful overfield reduction step. -/
theorem surjective_maximalWeaklyEtaleSubalgebraTensorBaseChange_of_overfield
    {Ω : Type*} [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (hΩ :
      Function.Surjective
        (maximalWeaklyEtaleSubalgebraTensorBaseChange K Ω A :
          B_max(A⁄K) ⊗[K] Ω → B_max((A ⊗[K] Ω)⁄Ω))) :
    Function.Surjective
      (maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
        B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) := by
  let f := (maximalWeaklyEtaleSubalgebraTensorBaseChange K L A).toLinearMap
  let g :=
    (maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower
      (K := K) (L := L) (A := A) (Ω := Ω)).toLinearMap
  let e :=
    maximalWeaklyEtaleSubalgebraTensorTowerAlgEquiv
      (K := K) (L := L) (A := B_max(A⁄K)) (Ω := Ω)
  have hcomp_surj : Function.Surjective (g ∘ₗ f.rTensor Ω) := by
    -- The factorization identifies the composite with the surjective `Ω`-version after source transport.
    rw [maximalWeaklyEtaleSubalgebraTensorBaseChange_factor_over_tower
      (K := K) (L := L) (A := A) (Ω := Ω)]
    intro y
    obtain ⟨x, hx⟩ := hΩ y
    refine ⟨e.symm x, ?_⟩
    simpa [e, LinearMap.comp_apply] using hx
  have hg_inj : Function.Injective g :=
    injective_maximalWeaklyEtaleSubalgebraTensorBaseChange_compare_over_tower
      (K := K) (L := L) (A := A) (Ω := Ω)
  have hf_rTensor_surj : Function.Surjective (f.rTensor Ω) := by
    intro y
    -- Surjectivity of the composite plus injectivity of the comparison map forces surjectivity
    -- of the `Ω`-tensor of the `L`-version.
    obtain ⟨x, hx⟩ := hcomp_surj (g y)
    refine ⟨x, hg_inj ?_⟩
    simpa [g, f, LinearMap.comp_apply] using hx
  -- Reflect surjectivity back across the universally injective scalar extension `L → Ω`.
  simpa [f] using
    LinearMap.surjective_of_rTensor_of_universallyInjective
      (universallyInjective_algebraLinearMap_of_field_extension (L := L) (Ω := Ω))
      (f := f) hf_rTensor_surj

/-- Helper for Lemma 15.106.4: surjectivity over `L` follows from surjectivity after extending
scalars further to the algebraic closure of `L`. -/
theorem surjective_maximalWeaklyEtaleSubalgebraTensorBaseChange_via_algClosure
    (hclosed :
      Function.Surjective
        (maximalWeaklyEtaleSubalgebraTensorBaseChange K (AlgebraicClosure L) A :
          B_max(A⁄K) ⊗[K] AlgebraicClosure L →
            B_max((A ⊗[K] AlgebraicClosure L)⁄AlgebraicClosure L))) :
    Function.Surjective
      (maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
        B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) := by
  -- Specialize the packaged overfield descent to the canonical overfield `AlgebraicClosure L`.
  exact surjective_maximalWeaklyEtaleSubalgebraTensorBaseChange_of_overfield
    (K := K) (L := L) (A := A) (Ω := AlgebraicClosure L) hclosed

/-- Helper for Lemma 15.106.4: after the overfield reduction, it remains to prove surjectivity in
the algebraically closed target-field case. -/
theorem surjective_maximalWeaklyEtaleSubalgebraTensorBaseChange_of_isAlgClosed
    [IsAlgClosed L] :
    Function.Surjective
      (maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
        B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) := by
  -- Route correction: the overfield descent is already packaged above, so the remaining Lean work
  -- is the source-faithful algebraically closed reduction ladder.
  -- TODO for Lemma 15.106.4: reduce from arbitrary `A` to finite type and reduced `K`-algebras,
  -- pass to the total quotient ring, and finish the finitely generated field case via the
  -- separable-closure description of `B_max(A/K)`.
  sorry

-- Proof sketch: first reduce to the case where `L` is algebraically closed, then to finite type
-- and reduced `K`-algebras, then to total quotient rings, and finally to finitely generated field
-- extensions. In the field case, decompose after base change using the separable field
-- `B_max(A/K)` and show each factor has maximal weakly étale subalgebra equal to `L`.
/-- Lemma 15.106.4: the canonical map
`B_max(A/K) ⊗[K] L → B_max((A ⊗[K] L)/L)` is bijective, i.e. base change carries the maximal
weakly étale `K`-subalgebra of `A` to the maximal weakly étale `L`-subalgebra of `A ⊗[K] L`. -/
theorem bijective_maximalWeaklyEtaleSubalgebraTensorBaseChange :
    Function.Bijective
      (maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
        B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) := by
  constructor
  · -- The injective half is the flatness argument above.
    exact injective_maximalWeaklyEtaleSubalgebraTensorBaseChange
      (K := K) (L := L) (A := A)
  · -- Reduce surjectivity to the algebraically closed target case, then apply that packaged case.
    have hclosed :
        Function.Surjective
          (maximalWeaklyEtaleSubalgebraTensorBaseChange K (AlgebraicClosure L) A :
            B_max(A⁄K) ⊗[K] AlgebraicClosure L →
              B_max((A ⊗[K] AlgebraicClosure L)⁄AlgebraicClosure L)) := by
      -- The canonical overfield `AlgebraicClosure L` satisfies the algebraically closed hypothesis.
      exact surjective_maximalWeaklyEtaleSubalgebraTensorBaseChange_of_isAlgClosed
        (K := K) (L := AlgebraicClosure L) (A := A)
    exact surjective_maximalWeaklyEtaleSubalgebraTensorBaseChange_via_algClosure
      (K := K) (L := L) (A := A) hclosed

end

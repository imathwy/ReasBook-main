import Mathlib
import StacksProject_2024.Chap10.Lemma_10_131_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

variable (I : Ideal S) (n : ℕ)

local notation "Sbar" => S ⧸ I ^ (n + 1)
local notation "Tbar" => S ⧸ I ^ n

/-- The canonical quotient-transition algebra structure on `S / I^n` over `S / I^(n + 1)`. -/
instance quotientPowSuccAlgebra : Algebra Sbar Tbar :=
  RingHom.toAlgebra (Ideal.Quotient.factorPowSucc I n)

/-- The quotient transition `S → S / I^(n + 1) → S / I^n` is a scalar tower. -/
instance quotientPowSuccIsScalarTower : IsScalarTower S Sbar Tbar :=
  IsScalarTower.of_algebraMap_eq' rfl

/- Domain triage:
- primary domain: base change of Kähler differentials along the quotient tower
  `S → S / I^(n + 1) → S / I^n`;
- sampled owner API:
  `KaehlerDifferential.mapBaseChange`,
  `TensorProduct.AlgebraTensorModule.lTensor`,
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`,
  `Ideal.Quotient.factorPowSucc`;
- source-facing layer: the canonical comparison on the actual base-changed modules
  `Tbar ⊗[S] Ω[S⁄R]` and `Tbar ⊗[Sbar] Ω[Sbar⁄R]`;
- core/canonical owner: `KaehlerDifferential.mapBaseChange R S Sbar`, base-changed further along
  `Sbar → Tbar`;
- bridge/view: if one wants the textbook tensor order
  `Ω[S⁄R] ⊗[S] Tbar ≃ Ω[S / I^(n + 1)⁄R] ⊗[S / I^(n + 1)] Tbar`, it is obtained afterward
  from the source-facing comparison by the standard tensor symmetries.

The previous file encoded only the restricted-scalars shadow of this comparison. The primitive
owner is the base-change map on Kähler differentials, and the correct public statement is its
further base change along `Sbar → Tbar`.
-/

private noncomputable def kaehlerDifferentialTensorQuotientPowSuccLinearMap :
    Tbar ⊗[S] Ω[S⁄R] →ₗ[Tbar] Tbar ⊗[Sbar] Ω[Sbar⁄R] :=
  lTensor Tbar Tbar (KaehlerDifferential.mapBaseChange R S Sbar) ∘ₗ
    (cancelBaseChange S Sbar Tbar Tbar Ω[S⁄R]).symm.toLinearMap

/-- Helper for Lemma 10.131.11: the Leibniz-rule step gives
`d(I ^ (n + 1)) ⊆ I ^ n Ω[S⁄R]`. -/
private lemma differential_mem_pow_smul_top_of_mem_pow_succ {x : S} (hx : x ∈ I ^ (n + 1)) :
    KaehlerDifferential.D R S x ∈ (I ^ n) • (⊤ : Submodule S Ω[S⁄R]) := by
  -- Prove the stronger induction statement `d(I^k) ⊆ I^(k-1) Ω` for all `k`.
  have hpow :
      ∀ {k : ℕ} {y : S}, y ∈ I ^ k →
        KaehlerDifferential.D R S y ∈ (I ^ k.pred) • (⊤ : Submodule S Ω[S⁄R]) := by
    intro k y hy
    refine Submodule.pow_induction_on_left'
        (M := I)
        (C := fun k y _ =>
          KaehlerDifferential.D R S y ∈ (I ^ k.pred) • (⊤ : Submodule S Ω[S⁄R])) ?_ ?_ ?_ hy
    · intro r
      simp
    · intro a b i ha hb ha_mem hb_mem
      -- The differential is additive, so the target submodule is closed under sums.
      simpa [map_add] using Submodule.add_mem _ ha_mem hb_mem
    · intro m hm i y hy hDy
      cases i with
      | zero =>
        -- At the first power, the target is `⊤`, so Leibniz closes immediately.
        simp [Derivation.leibniz]
      | succ i =>
        -- For higher powers, each Leibniz summand lands in `I^(i+1) Ω`.
        have hmDy :
            m • KaehlerDifferential.D R S y ∈
              I • ((I ^ i) • (⊤ : Submodule S Ω[S⁄R])) := by
          exact Submodule.smul_mem_smul hm hDy
        have hmDy' :
            m • KaehlerDifferential.D R S y ∈
              (I ^ (i + 1)) • (⊤ : Submodule S Ω[S⁄R]) := by
          have hEq :
              (I ^ (i + 1) : Ideal S) • (⊤ : Submodule S Ω[S⁄R]) =
                I • ((I ^ i) • (⊤ : Submodule S Ω[S⁄R])) := by
            rw [pow_succ', ← Ideal.smul_eq_mul I (I ^ i)]
            exact Submodule.smul_assoc I (I ^ i) (⊤ : Submodule S Ω[S⁄R])
          exact hEq.symm ▸ hmDy
        have hyDm :
            y • KaehlerDifferential.D R S m ∈
              (I ^ (i + 1)) • (⊤ : Submodule S Ω[S⁄R]) := by
          exact Submodule.smul_mem_smul hy (by trivial)
        simpa [Derivation.leibniz] using Submodule.add_mem _ hmDy' hyDm
  simpa using hpow hx

/-- Helper for Lemma 10.131.11: modulo `I ^ n`, the differential of any element of
`I ^ (n + 1)` becomes zero in the tensor product. -/
private lemma tensor_differential_eq_zero_of_mem_pow_succ {x : S} (hx : x ∈ I ^ (n + 1)) :
    ((1 : Tbar) ⊗ₜ[S] KaehlerDifferential.D R S x) = 0 := by
  -- The tensor-product kernel is exactly `I ^ n Ω[S⁄R]`.
  have hker :
      KaehlerDifferential.D R S x ∈
        LinearMap.ker (TensorProduct.mk S Tbar Ω[S⁄R] 1) := by
    simpa [LinearMap.ker_tensorProductMk (I := I ^ n) (Q := Ω[S⁄R])] using
      (differential_mem_pow_smul_top_of_mem_pow_succ (R := R) (S := S) (I := I) (n := n) hx)
  exact LinearMap.mem_ker.mp hker

/-- Helper for Lemma 10.131.11: the conormal map for `S → S / I^(n+1)` promoted to an
`S / I^(n+1)`-linear map. -/
private noncomputable def kernel_identified_conormal_map_over_quotient
    (hker : RingHom.ker (algebraMap S Sbar) = I ^ (n + 1))
    (hsurj : Function.Surjective (algebraMap S Sbar)) :
    (I ^ (n + 1)).Cotangent →ₗ[Sbar] Sbar ⊗[S] Ω[S⁄R] :=
  letI : IsScalarTower S Sbar (I ^ (n + 1)).Cotangent :=
    Module.IsTorsionBySet.isScalarTower
      (Ideal.isTorsionBySet_cotangent (R := S) (I := I ^ (n + 1)))
  let cotangentToTensor :
      (I ^ (n + 1)).Cotangent →ₗ[S] Sbar ⊗[S] Ω[S⁄R] :=
    (KaehlerDifferential.kerCotangentToTensor R S Sbar).comp
      (Ideal.Cotangent.equivOfEq
        (I ^ (n + 1))
        (RingHom.ker (algebraMap S Sbar))
        hker.symm).toLinearMap
  cotangentToTensor.extendScalarsOfSurjective hsurj

/-- Helper for Lemma 10.131.11: on cotangent generators, the scalar-upgraded conormal map still
sends `f` to `1 ⊗ d f`. -/
private lemma kernel_identified_conormal_map_over_quotient_toCotangent
    (hker : RingHom.ker (algebraMap S Sbar) = I ^ (n + 1))
    (hsurj : Function.Surjective (algebraMap S Sbar))
    (x : ↥(I ^ (n + 1))) :
    kernel_identified_conormal_map_over_quotient
        (R := R) (S := S) (I := I) (n := n) hker hsurj
        (Ideal.toCotangent (I ^ (n + 1)) x) =
      1 ⊗ₜ[S] KaehlerDifferential.D R S x := by
  -- Scalar extension preserves the underlying function, so Lemma 10.131.9 applies verbatim.
  simpa [kernel_identified_conormal_map_over_quotient] using
    (kerCotangentToTensorOfKerEq_toCotangent
      (R := R) (S := S) (S' := Sbar) (I := I ^ (n + 1)) hker x)

/-- Helper for Lemma 10.131.11: after tensoring further with `S / I^n`, the promoted conormal
map becomes zero. -/
private lemma lTensor_kernel_identified_conormal_map_over_quotient_eq_zero
    (hker : RingHom.ker (algebraMap S Sbar) = I ^ (n + 1))
    (hsurj : Function.Surjective (algebraMap S Sbar)) :
    lTensor Tbar Tbar
        (kernel_identified_conormal_map_over_quotient
          (R := R) (S := S) (I := I) (n := n) hker hsurj) = 0 := by
  -- Generators of the cotangent space come from `I^(n+1)`, and each such generator dies mod `I^n`.
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | add z w hz hw =>
      rw [LinearMap.map_add, hz, hw]
      simp
  | tmul t x =>
      obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (I ^ (n + 1)) x
      apply (cancelBaseChange S Sbar Tbar Tbar Ω[S⁄R]).injective
      have hbase :
          t ⊗ₜ[S] KaehlerDifferential.D R S y = 0 := by
        have hzero := congrArg
          (fun z : Tbar ⊗[S] Ω[S⁄R] => t • z)
          (tensor_differential_eq_zero_of_mem_pow_succ
            (R := R) (S := S) (I := I) (n := n) y.2)
        simpa [TensorProduct.smul_tmul'] using hzero
      -- `cancelBaseChange` turns the outer tensor generator into the literal tensor over `S`.
      have hcancel :
          (cancelBaseChange S Sbar Tbar Tbar Ω[S⁄R])
              (((lTensor Tbar Tbar
                    (kernel_identified_conormal_map_over_quotient
                      (R := R) (S := S) (I := I) (n := n) hker hsurj))
                  (t ⊗ₜ[Sbar] Ideal.toCotangent (I ^ (n + 1)) y))) = 0 := by
        rw [TensorProduct.AlgebraTensorModule.lTensor_tmul,
          kernel_identified_conormal_map_over_quotient_toCotangent,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
        simpa using hbase
      exact hcancel

/-- Helper for Lemma 10.131.11: the owner-level base-change map becomes bijective after
tensoring with `S / I^n`. -/
private theorem lTensor_mapBaseChange_bijective_quotientPowSucc :
    Function.Bijective
      ((lTensor Tbar Tbar (KaehlerDifferential.mapBaseChange R S Sbar)) :
        Tbar ⊗[Sbar] (Sbar ⊗[S] Ω[S⁄R]) →ₗ[Tbar] Tbar ⊗[Sbar] Ω[Sbar⁄R]) := by
  have hker : RingHom.ker (algebraMap S Sbar) = I ^ (n + 1) := by
    simpa using (Ideal.Quotient.mkₐ_ker R (I ^ (n + 1)))
  have hsurj : Function.Surjective (algebraMap S Sbar) := by
    simpa using (Ideal.Quotient.mkₐ_surjective R (I ^ (n + 1)))
  have hExact :
      Function.Exact
        (kernel_identified_conormal_map_over_quotient
          (R := R) (S := S) (I := I) (n := n) hker hsurj)
        (KaehlerDifferential.mapBaseChange R S Sbar) := by
    -- Reuse Lemma 10.131.9 after identifying the quotient kernel with `I^(n+1)`.
    simpa [kernel_identified_conormal_map_over_quotient] using
      (kaehlerDifferential_exact_cotangent_tensor_of_surjective
        (R := R) (S := S) (S' := Sbar) (I := I ^ (n + 1)) hker hsurj).1
  have hSurj :
      Function.Surjective (KaehlerDifferential.mapBaseChange R S Sbar) := by
    exact (kaehlerDifferential_exact_cotangent_tensor_of_surjective
      (R := R) (S := S) (S' := Sbar) (I := I ^ (n + 1)) hker hsurj).2
  have hTensorExact :
      Function.Exact
        (lTensor Tbar Tbar
          (kernel_identified_conormal_map_over_quotient
            (R := R) (S := S) (I := I) (n := n) hker hsurj))
        (lTensor Tbar Tbar (KaehlerDifferential.mapBaseChange R S Sbar)) := by
    simpa using lTensor_exact Tbar hExact hSurj
  have hTensorSurj :
      Function.Surjective
        (lTensor Tbar Tbar (KaehlerDifferential.mapBaseChange R S Sbar)) := by
    simpa using LinearMap.lTensor_surjective Tbar hSurj
  have hKer :
      LinearMap.ker (lTensor Tbar Tbar (KaehlerDifferential.mapBaseChange R S Sbar)) = ⊥ := by
    -- Exactness plus the zero left map forces the tensorized base-change map to be injective.
    rw [Function.Exact.linearMap_ker_eq hTensorExact,
      lTensor_kernel_identified_conormal_map_over_quotient_eq_zero
        (R := R) (S := S) (I := I) (n := n) hker hsurj,
      LinearMap.range_zero]
  have hInj :
      Function.Injective (lTensor Tbar Tbar (KaehlerDifferential.mapBaseChange R S Sbar)) := by
    exact LinearMap.ker_eq_bot.mp hKer
  exact ⟨hInj, hTensorSurj⟩

-- Proof sketch: apply Lemma `10.131.9` to the surjection `S → S / I^(n + 1)` with kernel
-- `I^(n + 1)`, then tensor the resulting exact sequence with `S / I^n`. The map from
-- `I^(n + 1)/(I^(2n + 2))` dies modulo `I^n` because `d(I^(n + 1)) ⊆ I^n Ω[S⁄R]` by Leibniz, so
-- the induced tensor map is bijective.
private theorem kaehlerDifferentialTensorQuotientPowSuccLinearMap_bijective :
    Function.Bijective
      ((kaehlerDifferentialTensorQuotientPowSuccLinearMap I n) :
        Tbar ⊗[S] Ω[S⁄R] →ₗ[Tbar] Tbar ⊗[Sbar] Ω[Sbar⁄R]) := by
  -- First prove bijectivity for the owner map on `Tbar ⊗[Sbar] (Sbar ⊗[S] Ω[S⁄R])`.
  have hOwner :
      Function.Bijective
        ((lTensor Tbar Tbar (KaehlerDifferential.mapBaseChange R S Sbar)) :
          Tbar ⊗[Sbar] (Sbar ⊗[S] Ω[S⁄R]) →ₗ[Tbar] Tbar ⊗[Sbar] Ω[Sbar⁄R]) :=
    lTensor_mapBaseChange_bijective_quotientPowSucc
      (R := R) (S := S) (I := I) (n := n)
  constructor
  · -- The displayed map is the owner map precomposed with the source `cancelBaseChange` equivalence.
    exact hOwner.1.comp (cancelBaseChange S Sbar Tbar Tbar Ω[S⁄R]).symm.injective
  · intro y
    obtain ⟨x, hx⟩ := hOwner.2 y
    refine ⟨(cancelBaseChange S Sbar Tbar Tbar Ω[S⁄R]) x, ?_⟩
    simpa [kaehlerDifferentialTensorQuotientPowSuccLinearMap] using hx

/-- Lemma 10.131.11: the quotient morphism `S → S / I^(n + 1)` induces the canonical
`S / I^n`-linear identification of the two base changes
`S / I^n ⊗[S] Ω[S⁄R] ≃ S / I^n ⊗[S / I^(n + 1)] Ω[S / I^(n + 1)⁄R]`.
The source text states this for `n ≥ 1`, but that hypothesis is mathematically redundant: the
`n = 0` case is the trivial zero-module comparison. -/
noncomputable def kaehlerDifferentialTensorQuotientPowSuccEquiv
    : Tbar ⊗[S] Ω[S⁄R] ≃ₗ[Tbar] Tbar ⊗[Sbar] Ω[Sbar⁄R] :=
  LinearEquiv.ofBijective
    (kaehlerDifferentialTensorQuotientPowSuccLinearMap I n)
    (kaehlerDifferentialTensorQuotientPowSuccLinearMap_bijective I n)

end

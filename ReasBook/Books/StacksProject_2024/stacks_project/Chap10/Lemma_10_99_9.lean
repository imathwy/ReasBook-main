import Mathlib
import StacksProject_2024.stacks_project.Chap10.«10_69_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open TensorProduct
open LinearMap
open RingTheory.Sequence

universe u

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

-- Domain-style sampling:
-- * primary domain: commutative algebra of tensor products and successive ideal-power quotients.
-- * source-facing owner: the canonical map
--   `idealPowTensorToModuleSuccQuotient M :
--      M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M`.
-- * sampled core/canonical owners of the same construction style:
--   `Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`,
--   `idealAssociatedGradedPiece`,
--   `TensorProduct.tensorQuotientEquiv`,
--   `Submodule.mapQ`,
--   `LinearMap.codRestrict`,
--   `TensorProduct.rid`.
-- * primitive data: the tensor-to-smul map `M ⊗[R] I^n → I^n M`.
-- * derived API: the descent to the canonical owner types for `I^n / I^(n+1)` and
--   `idealAssociatedGradedPiece I M n`, together with the pure-tensor evaluation lemma.
-- * refinement target: keep the source-facing map and remove the one-off public quotient aliases in
--   favor of the chapter/mathlib owners above.

-- Proof sketch: an element of `I ^ n` acts on `M` by scalar multiplication, so its image lies in
-- the submodule `I ^ n M = I ^ n • ⊤`.
/-- Scalar multiplication by an element of `I ^ n` lands in the submodule `I ^ n M`. -/
private theorem idealPowSmul_mem (I : Ideal R) (n : ℕ) (m : M) (a : ↥(I ^ n : Ideal R)) :
    a.1 • m ∈ idealAssociatedGradedStage I M n := sorry

private noncomputable def idealPowTensorToSmul (I : Ideal R) (n : ℕ) :
    M ⊗[R] ↥(I ^ n : Ideal R) →ₗ[R] ↥(idealAssociatedGradedStage I M n) :=
  LinearMap.codRestrict (idealAssociatedGradedStage I M n)
    ((TensorProduct.rid R M).toLinearMap.comp
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M) ((I ^ n : Ideal R).subtype)))
    (by
      intro x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro m a
        simpa using idealPowSmul_mem I n m a
      · intro x y hx hy
        simpa using Submodule.add_mem (idealAssociatedGradedStage I M n) hx hy)

-- Proof sketch: the tensor-to-smul map carries the quotienting submodule
-- `M ⊗[R] I(I^n)` into `I(I^n M)`.
private theorem idealPowTensorToSmul_range_le (I : Ideal R) (n : ℕ) :
    LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype)) ≤
      Submodule.comap (idealPowTensorToSmul I n)
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))) := by
  rintro _ ⟨x, rfl⟩
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [idealPowTensorToSmul]
  · intro m a
    change idealPowTensorToSmul I n (m ⊗ₜ[R] a.1) ∈
      I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))
    refine Submodule.smul_induction_on a.2 ?_ ?_
    · intro r hr b hb
      let c : ↥(idealAssociatedGradedStage I M n) := ⟨b.1 • m, idealPowSmul_mem I n m b⟩
      have hc : c ∈ (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)) := by simp
      have hs : idealPowTensorToSmul I n (m ⊗ₜ[R] (r • b : ↥(I ^ n : Ideal R))) = r • c := by
        ext
        simp [idealPowTensorToSmul, c]
      rw [hs]
      exact Submodule.smul_mem_smul hr hc
    · intro x y hx hy
      simpa [tmul_add, map_add] using
        Submodule.add_mem (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n))) hx hy
  · intro x y hx hy
    simpa using Submodule.add_mem
      (Submodule.comap (idealPowTensorToSmul I n)
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))) hx hy

private theorem idealPowModuleInternalDenominator_eq (I : Ideal R) (n : ℕ) :
    I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)) =
      (idealAssociatedGradedStage I M (n + 1)).submoduleOf (idealAssociatedGradedStage I M n) := by
  ext x
  rw [Submodule.mem_smul_top_iff]
  change ((x : M) ∈ I • idealAssociatedGradedStage I M n) ↔
    ((x : M) ∈ idealAssociatedGradedStage I M (n + 1))
  simp [idealAssociatedGradedStage, ← mul_smul, Ideal.mul_comm, pow_succ]

private noncomputable def idealPowModuleInternalPieceEquiv (I : Ideal R) (n : ℕ) :
    (↥(idealAssociatedGradedStage I M n) ⧸
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))) ≃ₗ[R]
      idealAssociatedGradedPiece I M n :=
  Submodule.quotEquivOfEq _ _ (idealPowModuleInternalDenominator_eq I n)

variable (M) in
/-- The canonical map `M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M`, with codomain given by the
`n`th associated graded piece. -/
noncomputable def idealPowTensorToModuleSuccQuotient (I : Ideal R) (n : ℕ) :
    M ⊗[R] ((I ^ n : Ideal R) ⧸ (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))) →ₗ[R]
      idealAssociatedGradedPiece I M n :=
  (idealPowModuleInternalPieceEquiv I n).toLinearMap.comp
    (((LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype))).mapQ
      (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))
      (idealPowTensorToSmul I n)
      (idealPowTensorToSmul_range_le I n)).comp
      (TensorProduct.tensorQuotientEquiv M
        (I • (⊤ : Submodule R ↥(I ^ n : Ideal R)))).toLinearMap)

/-- The canonical tensor-to-quotient map sends `m ⊗ a` to the class of `a • m`. -/
theorem idealPowTensorToModuleSuccQuotient_tmul_mk
    (I : Ideal R) (n : ℕ) (m : M) (a : ↥(I ^ n : Ideal R)) :
    idealPowTensorToModuleSuccQuotient M I n (m ⊗ₜ[R] Submodule.Quotient.mk a) =
      Submodule.Quotient.mk
        ⟨a.1 • m, idealPowSmul_mem I n m a⟩ := by
  have hsmul :
      idealPowTensorToSmul I n (m ⊗ₜ[R] a) =
        (⟨a.1 • m, idealPowSmul_mem I n m a⟩ : ↥(idealAssociatedGradedStage I M n)) := rfl
  simp only [idealPowTensorToModuleSuccQuotient, LinearMap.comp_apply]
  change
    idealPowModuleInternalPieceEquiv I n
      (((LinearMap.range
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          ((I • (⊤ : Submodule R ↥(I ^ n : Ideal R))).subtype))).mapQ
        (I • (⊤ : Submodule R ↥(idealAssociatedGradedStage I M n)))
        (idealPowTensorToSmul I n)
        (idealPowTensorToSmul_range_le I n))
      (Submodule.Quotient.mk (m ⊗ₜ[R] a))) =
    _
  rw [Submodule.mapQ_apply, hsmul]
  simp [idealPowModuleInternalPieceEquiv]

-- Proof sketch: apply the flatness criterion of Lemma `10.99.8` to `R / I²` and `M / I² M`. By
-- Remark `10.75.9`, the injectivity of the displayed tensor map identifies with the vanishing of
-- the relevant `Tor₁`, which is exactly the hypothesis needed there.
/-- Lemma 10.99.9 (1): if `M / IM` is flat over `R / I` and the canonical map
`M ⊗[R] (I / I^2) → IM / I^2 M` is injective, then `M / I^2 M` is flat over `R / I^2`. -/
theorem flat_mod_ideal_sq_of_flat_mod_ideal_and_injective_tensor_ideal_quotient
    {I : Ideal R}
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj : Function.Injective (idealPowTensorToModuleSuccQuotient M I 1)) :
    Module.Flat (R ⧸ I ^ 2) (M ⧸ (I ^ 2 • (⊤ : Submodule R M))) := sorry

-- Proof sketch: argue by induction on `k`. The case `k = 0` is the given flatness of `M / IM`,
-- and the induction step applies part (1) over the ring `R / I^(n+1)` using Remark `10.75.9` to
-- translate the injectivity hypothesis for `I^n / I^(n+1)` into the needed `Tor₁`-vanishing.
/-- Lemma 10.99.9 (2): if `M / IM` is flat over `R / I` and for every `1 ≤ n ≤ k` the canonical
map `M ⊗[R] (I^n / I^(n+1)) → I^n M / I^(n+1) M` is injective, then `M / I^(k+1) M` is flat over
`R / I^(k+1)`. -/
theorem flat_mod_ideal_pow_succ_of_flat_mod_ideal_and_injective_tensor_successive_quotients
    {I : Ideal R} (k : ℕ)
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))))
    (hinj :
      ∀ n : ℕ, 1 ≤ n → n ≤ k →
        Function.Injective (idealPowTensorToModuleSuccQuotient M I n)) :
    Module.Flat (R ⧸ I ^ (k + 1)) (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M))) := sorry

end

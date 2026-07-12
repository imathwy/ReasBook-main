import Mathlib

open Module
open scoped BigOperators TensorProduct

noncomputable section
universe u v

namespace Representation

structure SemilinearGaloisAction (k : Type u) [Field k] (L : Type u) [Field L] [Algebra k L]
    (M : Type v) [AddCommGroup M] [Module L M] where
  act : (L ≃ₐ[k] L) → (M ≃+ M)
  map_smul' : ∀ (σ : L ≃ₐ[k] L) (c : L) (m : M), act σ (c • m) = σ c • act σ m
  act_one' : act 1 = AddEquiv.refl M
  act_mul' : ∀ (σ τ : L ≃ₐ[k] L) (m : M), act (σ * τ) m = act σ (act τ m)

/-- **Galois orthogonality** of a `k`-basis `c` of `L` and its trace-dual `c'`:
`∑ᵢ cᵢ · τ(c'ᵢ) = if τ = 1 then 1 else 0`.  Proved from `Tr(c'ᵢ cⱼ) = δᵢⱼ`
(`trace_eq_sum_automorphisms` + `trace_traceDual_mul`) by flipping the square matrix
`(σ(cᵢ))` against `(σ(c'ᵢ))` (`Matrix.mul_eq_one_comm_of_card_eq`, using `|Gal| = [L:k]`). -/
theorem galoisOrthogonality {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq (L ≃ₐ[k] L)] (c : Module.Basis ι k L) (τ : L ≃ₐ[k] L) :
    ∑ i, c i * τ (c.traceDual i) = if τ = 1 then 1 else 0 := by
  classical
  let U : Matrix (L ≃ₐ[k] L) ι L := fun σ i => σ (c i)
  let V : Matrix ι (L ≃ₐ[k] L) L := fun i σ => σ (c.traceDual i)
  have hVU : V * U = 1 := by
    ext i j
    simp only [Matrix.mul_apply, V, U]
    rw [show (∑ σ : L ≃ₐ[k] L, σ (c.traceDual i) * σ (c j))
        = ∑ σ : L ≃ₐ[k] L, σ (c.traceDual i * c j) from
        Finset.sum_congr rfl (fun σ _ => (map_mul σ _ _).symm)]
    rw [← trace_eq_sum_automorphisms, c.trace_traceDual_mul i j, Matrix.one_apply,
      apply_ite (algebraMap k L), map_one, map_zero]
    simp only [eq_comm]
  have hcard : Fintype.card (L ≃ₐ[k] L) = Fintype.card ι := by
    rw [← Nat.card_eq_fintype_card (α := L ≃ₐ[k] L), IsGalois.card_aut_eq_finrank,
      Module.finrank_eq_card_basis c]
  have hUV : U * V = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (L ≃ₐ[k] L) ι L hcard).mpr hVU
  have hflip := congrFun (congrFun hUV 1) τ
  simp only [Matrix.mul_apply, U, V, Matrix.one_apply, AlgEquiv.one_apply] at hflip
  simp only [eq_comm (a := (1 : L ≃ₐ[k] L)) (b := τ)] at hflip
  exact hflip

namespace SemilinearGaloisAction

variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]
variable {M : Type v} [AddCommGroup M] [Module L M] [Module k M] [IsScalarTower k L M]
variable (A : SemilinearGaloisAction k L M)

theorem act_smul (σ : L ≃ₐ[k] L) (c : L) (m : M) : A.act σ (c • m) = σ c • A.act σ m :=
  A.map_smul' σ c m
theorem act_mul (σ τ : L ≃ₐ[k] L) (m : M) : A.act (σ * τ) m = A.act σ (A.act τ m) :=
  A.act_mul' σ τ m
@[simp] theorem act_one_apply (m : M) : A.act 1 m = m := by rw [A.act_one']; rfl

def fixed : Submodule k M where
  carrier := {m | ∀ σ : L ≃ₐ[k] L, A.act σ m = m}
  add_mem' {m₁ m₂} h₁ h₂ σ := by simp [map_add, h₁ σ, h₂ σ]
  zero_mem' σ := by simp
  smul_mem' c m h σ := by
    have hc : (c : k) • m = (algebraMap k L c) • m := by rw [algebraMap_smul]
    rw [hc, A.act_smul σ (algebraMap k L c) m, AlgEquiv.commutes σ c, h σ]

@[simp] theorem mem_fixed_iff {m : M} : m ∈ A.fixed ↔ ∀ σ : L ≃ₐ[k] L, A.act σ m = m := Iff.rfl

variable [FiniteDimensional k L] [IsGalois k L]

/-- The fixed-vector producer `g(a) = ∑_τ τ(a) • act τ m`. -/
def avg (m : M) (a : L) : M := ∑ τ : L ≃ₐ[k] L, τ a • A.act τ m

theorem avg_mem_fixed (m : M) (a : L) : A.avg m a ∈ A.fixed := by
  intro σ
  simp only [avg, map_sum]
  rw [show (∑ τ : L ≃ₐ[k] L, A.act σ (τ a • A.act τ m))
      = ∑ τ : L ≃ₐ[k] L, (σ * τ) a • A.act (σ * τ) m from
      Finset.sum_congr rfl (fun τ _ => by
        rw [A.act_smul σ (τ a) (A.act τ m), ← A.act_mul σ τ m, AlgEquiv.mul_apply])]
  exact Fintype.sum_bijective (fun τ => σ * τ) (Group.mulLeft_bijective σ) _ _ (fun τ => rfl)

/-- KEY collapse: for a fixed `n` and `l : L`, `avg (l • n) a = Tr(a*l) • n`. -/
theorem avg_smul_fixed (n : M) (hn : n ∈ A.fixed) (l a : L) :
    A.avg (l • n) a = (Algebra.trace k L (a * l)) • n := by
  simp only [avg]
  -- ∑_τ τ(a) • act τ (l • n) = ∑_τ τ(a) • (τ l • act τ n) = ∑_τ τ(a) τ(l) • n = ∑_τ τ(a*l) • n
  rw [show (∑ τ : L ≃ₐ[k] L, τ a • A.act τ (l • n))
      = ∑ τ : L ≃ₐ[k] L, (τ (a * l)) • n from
      Finset.sum_congr rfl (fun τ _ => by
        rw [A.act_smul τ l n, hn τ, smul_smul, ← map_mul])]
  -- ∑_τ τ(a*l) • n = (algebraMap k L (Tr (a*l))) • n = Tr(a*l) • n
  rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms, algebraMap_smul]

/-- `act τ` as a `k`-linear endomorphism (it fixes `k`-scalars). -/
def actₗ (τ : L ≃ₐ[k] L) : M →ₗ[k] M where
  toFun := A.act τ
  map_add' := map_add _
  map_smul' c m := by
    show A.act τ (c • m) = c • A.act τ m
    rw [show (c : k) • m = (algebraMap k L c) • m from (algebraMap_smul L c m).symm,
      A.act_smul τ (algebraMap k L c) m, AlgEquiv.commutes τ c, algebraMap_smul]

/-- `avg · a` as a `k`-linear map `M → M`. -/
def avgₗ (a : L) : M →ₗ[k] M := ∑ τ : L ≃ₐ[k] L, (τ a) • A.actₗ τ

@[simp] theorem avgₗ_apply (a : L) (m : M) : A.avgₗ a m = A.avg m a := by
  simp only [avgₗ, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, actₗ,
    LinearMap.coe_mk, AddHom.coe_mk, avg]

/-- `avg · a` as a `k`-linear map into the fixed submodule. -/
def avgFixed (a : L) : M →ₗ[k] A.fixed :=
  LinearMap.codRestrict A.fixed (A.avgₗ a) (fun m => by
    rw [A.avgₗ_apply]; exact A.avg_mem_fixed m a)

@[simp] theorem avgFixed_coe (a : L) (m : M) : (A.avgFixed a m : M) = A.avg m a := by
  rw [avgFixed, LinearMap.codRestrict_apply, A.avgₗ_apply]

/-- Descent map. -/
def descentMap : (L ⊗[k] A.fixed) →ₗ[L] M :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton L (A.fixed →ₗ[k] M) A.fixed.subtype)

@[simp] theorem descentMap_tmul (l : L) (m : A.fixed) :
    A.descentMap (l ⊗ₜ[k] m) = l • (m : M) := by
  rw [descentMap, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp [LinearMap.toSpanSingleton]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι k L)

/-- The explicit inverse `ψ : M → L ⊗[k] M^Γ`, `m ↦ ∑_i b'_i ⊗ avgFixed(b_i)(m)`. -/
def psi : M →ₗ[k] (L ⊗[k] A.fixed) :=
  ∑ i, (TensorProduct.mk k L A.fixed (b.traceDual i)).comp (A.avgFixed (b i))

@[simp] theorem psi_apply (m : M) :
    A.psi b m = ∑ i, (b.traceDual i) ⊗ₜ[k] (A.avgFixed (b i) m) := by
  simp only [psi, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.comp_apply,
    TensorProduct.mk_apply]

/-- `descentMap ∘ ψ = id` (surjectivity / spanning). -/
theorem descentMap_psi (m : M) : A.descentMap (A.psi b m) = m := by
  classical
  rw [psi_apply, map_sum]
  simp only [descentMap_tmul, avgFixed_coe]
  -- ∑_i b'_i • avg(m, b_i) = m  (the spanning identity)
  rw [show (∑ i, b.traceDual i • A.avg m (b i))
      = ∑ τ : L ≃ₐ[k] L, (∑ i, b.traceDual i * τ (b i)) • A.act τ m from by
        simp only [avg, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun τ _ => (Finset.sum_smul ..).symm)]
  -- coefficient ∑_i b'_i τ(b_i) = δ_{1,τ}, via orthogonality on basis b.traceDual
  rw [Finset.sum_eq_single (1 : L ≃ₐ[k] L)]
  · rw [show (∑ i, b.traceDual i * (1 : L ≃ₐ[k] L) (b i)) = 1 from by
        have h := galoisOrthogonality b.traceDual 1
        rw [Module.Basis.traceDual_traceDual] at h
        simpa using h, one_smul, A.act_one_apply]
  · intro τ _ hτ
    have h := galoisOrthogonality b.traceDual τ
    rw [Module.Basis.traceDual_traceDual] at h
    rw [h, if_neg hτ, zero_smul]
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

/-- `ψ ∘ descentMap = id` (injectivity), via the collapse `avg_smul_fixed` and dual-basis. -/
theorem psi_descentMap (z : L ⊗[k] A.fixed) :
    A.psi b (A.descentMap z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul l n =>
    rw [descentMap_tmul, psi_apply]
    -- ∑_i b'_i ⊗ avgFixed(b_i)(l • n) = ∑_i b'_i ⊗ (Tr(b_i l) • n) = (∑_i Tr(b_i l) • b'_i) ⊗ n = l ⊗ n
    have key : ∀ i, A.avgFixed (b i) (l • (n : M)) = (Algebra.trace k L (b i * l)) • n := by
      intro i
      apply Subtype.ext
      rw [avgFixed_coe, A.avg_smul_fixed n n.2 l (b i), Submodule.coe_smul]
    rw [Finset.sum_congr rfl (fun i _ => by rw [key i])]
    -- ∑_i b'_i ⊗ (Tr(b_i l) • n) = (∑_i Tr(b_i l) • b'_i) ⊗ n
    rw [show (∑ i, b.traceDual i ⊗ₜ[k] ((Algebra.trace k L (b i * l)) • n))
        = (∑ i, (Algebra.trace k L (b i * l)) • b.traceDual i) ⊗ₜ[k] n from by
        rw [TensorProduct.sum_tmul]
        exact Finset.sum_congr rfl (fun i _ => by rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul])]
    -- ∑_i Tr(b_i l) • b'_i = l  (dual basis expansion)
    congr 1
    conv_rhs => rw [← b.traceDual.sum_repr l]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, mul_comm]

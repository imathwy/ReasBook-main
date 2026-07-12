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

variable [FiniteDimensional k L] [IsGalois k L]

/-- The fixed-vector producer `g(a) = ∑_τ τ(a) • act τ m`, landing in `M^Γ`. -/
def avg (m : M) (a : L) : M := ∑ τ : L ≃ₐ[k] L, τ a • A.act τ m

theorem avg_mem_fixed (m : M) (a : L) : A.avg m a ∈ A.fixed := by
  intro σ
  simp only [avg, map_sum]
  -- act σ (∑_τ τ(a) • act τ m) = ∑_τ σ(τ a) • act σ (act τ m) = ∑_τ (σ*τ)(a) • act (σ*τ) m
  rw [show (∑ τ : L ≃ₐ[k] L, A.act σ (τ a • A.act τ m))
      = ∑ τ : L ≃ₐ[k] L, (σ * τ) a • A.act (σ * τ) m from
      Finset.sum_congr rfl (fun τ _ => by
        rw [A.act_smul σ (τ a) (A.act τ m), ← A.act_mul σ τ m, AlgEquiv.mul_apply])]
  -- reindex τ ↦ σ * τ
  exact Fintype.sum_bijective (fun τ => σ * τ) (Group.mulLeft_bijective σ) _ _
    (fun τ => rfl)

/-- Surjectivity: every `m` is recovered as `∑_i b'_i • g(b_i)`. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι k L)
    (ortho : ∀ (c : Basis ι k L) (τ : L ≃ₐ[k] L) [DecidableEq (L ≃ₐ[k] L)],
        ∑ i, c i * τ (c.traceDual i) = if τ = 1 then 1 else 0)
    (m : M) :
    m = ∑ i, b.traceDual i • A.avg m (b i) := by
  classical
  -- expand avg and swap sums
  rw [show (∑ i, b.traceDual i • A.avg m (b i))
      = ∑ τ : L ≃ₐ[k] L, (∑ i, b.traceDual i * τ (b i)) • A.act τ m from ?_]
  · -- coefficient ∑_i b'_i τ(b_i) = δ_{1,τ}; apply ortho to basis b.traceDual
    rw [Finset.sum_eq_single (1 : L ≃ₐ[k] L)]
    · have : (∑ i, b.traceDual i * (1 : L ≃ₐ[k] L) (b i)) = 1 := by
        have h := ortho b.traceDual 1
        simpa using h
      rw [this, one_smul, A.act_one_apply]
    · intro τ _ hτ
      have h := ortho b.traceDual τ
      rw [Module.Basis.traceDual_traceDual] at h
      rw [h, if_neg hτ, zero_smul]
    · intro hcontra; exact absurd (Finset.mem_univ _) hcontra
  · simp only [avg, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.sum_smul]

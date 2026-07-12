import Mathlib

/-!
# Base change of a split semisimple quotient

Given a finite-dimensional `F`-algebra `B` and a surjective `F`-algebra map onto a finite product
of matrix algebras over `F` with nilpotent kernel, base change to a field extension `k` yields a
surjective `k`-algebra map `k ⊗_F B → ∏ Mₙᵢ(k)` whose kernel is again nilpotent.

The map `Φ` is built as the composite of:
1. `idₖ ⊗ π : k ⊗[F] B → k ⊗[F] (∏ Mₙᵢ(F))`,
2. `Algebra.TensorProduct.piRight : k ⊗[F] (∏ Mₙᵢ(F)) ≃ₐ[k] ∏ (k ⊗[F] Mₙᵢ(F))`,
3. per factor, the `k`-algebra upgrade of `(matrixEquivTensor n F k).symm`.

Surjectivity is clear (composite of surjections and equivalences).  For the nilpotent kernel,
`Algebra.TensorProduct.lTensor_ker` (flatness of `k`/`F`) identifies the kernel of `idₖ ⊗ π` with
`Ideal.map includeRight (ker π)`, which is nilpotent since `Ideal.map` is a ring homomorphism on
ideals; the postcomposed equivalences do not change the kernel.
-/

noncomputable section
universe u
open scoped TensorProduct Pointwise

namespace Serre.SplitBaseChange

/-- Upgrade `(matrixEquivTensor (Fin n) F k).symm` to a `k`-algebra equivalence
`k ⊗[F] Matrix (Fin n) (Fin n) F ≃ₐ[k] Matrix (Fin n) (Fin n) k`.  The underlying ring equivalence
is the same; it is `k`-linear because it sends `a ⊗ M ↦ a • M.map (algebraMap F k)`. -/
def matrixBaseChangeAlgEquiv {F : Type u} [Field F] {k : Type u} [Field k] [Algebra F k]
    (n : ℕ) :
    (k ⊗[F] Matrix (Fin n) (Fin n) F) ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor (Fin n) F k).symm.toRingEquiv) <| by
    intro x
    change (matrixEquivTensor (Fin n) F k).symm (algebraMap k _ x) = algebraMap k _ x
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp [matrixEquivTensor_apply_symm, Algebra.algebraMap_eq_smul_one]

section Helpers

variable {F : Type u} [Field F] {k : Type u} [Field k] [Algebra F k]
  {B : Type u} [Ring B] [Algebra F B]

/-- Shorthand for the right inclusion `B →ₐ[F] k ⊗[F] B`. -/
private abbrev incR : B →ₐ[F] k ⊗[F] B := Algebra.TensorProduct.includeRight

/-- A pure tensor `1 ⊗ x` with `x` in a two-sided ideal `I`, multiplied on the right by anything,
stays in `Ideal.map includeRight I`. -/
private lemma incR_tmul_mul_mem (I : Ideal B) [I.IsTwoSided] {x : B} (hx : x ∈ I)
    (b : k ⊗[F] B) :
    (1 ⊗ₜ[F] x : k ⊗[F] B) * b ∈ Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul t c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hmem : (t ⊗ₜ[F] (x * c) : k ⊗[F] B) = (t ⊗ₜ[F] 1) * (1 ⊗ₜ[F] (x * c)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hmem]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (I.mul_mem_right c hx))
  | add b1 b2 h1 h2 => rw [mul_add]; exact Ideal.add_mem _ h1 h2

/-- `Ideal.map includeRight I` is a two-sided ideal (the extra generators `k` are central). -/
private instance incR_map_isTwoSided (I : Ideal B) [I.IsTwoSided] :
    (Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I).IsTwoSided := by
  constructor
  intro a b ha
  have ha' : a ∈ Submodule.span (k ⊗[F] B)
      ((incR : B →ₐ[F] k ⊗[F] B) '' (I : Set B)) := ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem y hy => obtain ⟨x, hx, rfl⟩ := hy; exact incR_tmul_mul_mem I hx b
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Ideal.add_mem _ hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ hx

/-- `Ideal.map includeRight` is submultiplicative: `map I * map K ≤ map (I * K)`. -/
private lemma incR_map_mul_le (I K : Ideal B) [I.IsTwoSided] :
    Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I * Ideal.map (incR : B →ₐ[F] k ⊗[F] B) K
      ≤ Ideal.map (incR : B →ₐ[F] k ⊗[F] B) (I * K) := by
  haveI : (Ideal.span ((incR : B →ₐ[F] k ⊗[F] B) '' (I : Set B))).IsTwoSided :=
    incR_map_isTwoSided I
  calc Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I * Ideal.map (incR : B →ₐ[F] k ⊗[F] B) K
      = Ideal.span (((incR : B →ₐ[F] k ⊗[F] B) '' (I : Set B)) *
          ((incR : B →ₐ[F] k ⊗[F] B) '' (K : Set B))) := Ideal.span_mul_span' _ _
    _ ≤ Ideal.map (incR : B →ₐ[F] k ⊗[F] B) (I * K) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        change incR x * incR y ∈ Ideal.map (incR : B →ₐ[F] k ⊗[F] B) (I * K)
        rw [← map_mul]
        exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul hx hy)

/-- Powers of the mapped ideal land in the mapped powers (for `n ≥ 1`). -/
private lemma incR_map_pow_le (I : Ideal B) [I.IsTwoSided] (n : ℕ) :
    Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I ^ (n + 1)
      ≤ Ideal.map (incR : B →ₐ[F] k ⊗[F] B) (I ^ (n + 1)) := by
  induction n with
  | zero => refine le_of_eq ?_; simp only [zero_add, Submodule.pow_one]
  | succ j ih =>
    calc Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I ^ (j + 1 + 1)
        = Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I ^ (j + 1)
            * Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I := Submodule.pow_succ _
      _ ≤ Ideal.map (incR : B →ₐ[F] k ⊗[F] B) (I ^ (j + 1))
            * Ideal.map (incR : B →ₐ[F] k ⊗[F] B) I := Ideal.mul_mono ih le_rfl
      _ ≤ Ideal.map (incR : B →ₐ[F] k ⊗[F] B) (I ^ (j + 1) * I) := incR_map_mul_le _ _
      _ = Ideal.map (incR : B →ₐ[F] k ⊗[F] B) (I ^ (j + 1 + 1)) := by
          rw [← Submodule.pow_succ]

end Helpers

/-- The `k`-algebra isomorphism `k ⊗[F] (∏ Mₙᵢ(F)) ≃ₐ[k] ∏ Mₙᵢ(k)`. -/
def splitEquiv {F : Type u} [Field F] {k : Type u} [Field k] [Algebra F k]
    {ι : Type u} [Fintype ι] [DecidableEq ι] (d : ι → ℕ) :
    (k ⊗[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F) ≃ₐ[k]
      Π i, Matrix (Fin (d i)) (Fin (d i)) k :=
  (Algebra.TensorProduct.piRight F k k (fun i ↦ Matrix (Fin (d i)) (Fin (d i)) F)).trans
    (AlgEquiv.piCongrRight fun i ↦ matrixBaseChangeAlgEquiv (d i))

/-- Base change of a split semisimple quotient. Given a finite-dimensional `F`-algebra `B` and a
surjective `F`-algebra map `π` onto a product of matrix algebras over `F` whose kernel is
nilpotent, base change to an extension field `k` yields a surjective `k`-algebra map
`k ⊗_F B → ∏ Mₙᵢ(k)` whose kernel is again nilpotent. -/
theorem baseChange_surjective_nilpotent_ker
    {F : Type u} [Field F] {k : Type u} [Field k] [Algebra F k]
    {ι : Type u} [Fintype ι] (d : ι → ℕ)
    (B : Type u) [Ring B] [Algebra F B] [Module.Finite F B]
    (π : B →ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F)
    (hsurj : Function.Surjective π)
    (hnil : IsNilpotent (RingHom.ker (π : B →+* Π i, Matrix (Fin (d i)) (Fin (d i)) F))) :
    ∃ Φ : (k ⊗[F] B) →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k,
      Function.Surjective Φ ∧
      IsNilpotent (RingHom.ker (Φ : (k ⊗[F] B) →+* Π i, Matrix (Fin (d i)) (Fin (d i)) k)) := by
  classical
  set e := splitEquiv (F := F) (k := k) d with he
  refine ⟨e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id k k) π), ?_, ?_⟩
  · -- Surjectivity: composite of surjections.
    have hm1 : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id k k) π) :=
      Algebra.TensorProduct.map_surjective (f := AlgHom.id k k) (g := π) (fun x ↦ ⟨x, rfl⟩) hsurj
    exact e.surjective.comp hm1
  · -- Nilpotent kernel.
    have hbridge : ∀ x : k ⊗[F] B,
        Algebra.TensorProduct.map (AlgHom.id k k) π x
          = Algebra.TensorProduct.map (AlgHom.id F k) π x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have hker : RingHom.ker
        (e.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id k k) π))
          = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id F k) π) := by
      ext x
      simp only [RingHom.mem_ker, AlgHom.comp_apply, AlgEquiv.coe_algHom]
      rw [← hbridge x]
      constructor
      · intro h; exact e.injective (h.trans (map_zero e).symm)
      · intro h; rw [h, map_zero]
    rw [RingHom.ker_coe_toRingHom, hker,
      Algebra.TensorProduct.lTensor_ker (A := k) (g := π) hsurj]
    -- `Ideal.map includeRight` of a nilpotent ideal is nilpotent.  As `k ⊗[F] B` is not
    -- commutative we cannot use `Ideal.map_pow`; instead we use the submultiplicativity
    -- `incR_map_mul_le` (valid because the mapped ideal is two-sided).
    obtain ⟨m, hm⟩ := hnil
    rw [RingHom.ker_coe_toRingHom] at hm
    refine ⟨m + 1, ?_⟩
    have hbot : Ideal.map (incR : B →ₐ[F] k ⊗[F] B) ((RingHom.ker π) ^ (m + 1)) = ⊥ := by
      rw [Submodule.pow_succ, hm, zero_mul]; exact Ideal.map_bot
    exact le_bot_iff.1 ((incR_map_pow_le (RingHom.ker π) m).trans (le_of_eq hbot))

end Serre.SplitBaseChange

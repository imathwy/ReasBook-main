import Mathlib

/-!
# Finite Galois descent for semilinear actions (additive Speiser / Hilbert 90)

This module is the reusable, **abstract** Galois-descent core (the "G-core") behind the
characteristic-`p` modular splitting argument of Remark 14-14.5-1.  It is purely a statement about a
finite-dimensional vector space carrying a semilinear action of a finite Galois group, with no
reference to representations, Brauer characters, or `FDRep`.

## Setup

Let `L / k` be a **finite Galois** extension with `Γ = L ≃ₐ[k] L` its Galois group, and let `M` be a
finite-dimensional `L`-vector space equipped with a `k`-linear **semilinear** `Γ`-action: an additive
automorphism `act σ : M ≃+ M` for each `σ ∈ Γ` satisfying

* `act σ (c • m) = σ c • act σ m`  (`σ`-semilinearity over `L`),
* `act 1 = id` and `act (σ * τ) = act σ ∘ act τ`  (a group action).

The **fixed points** `M^Γ = {m | ∀ σ, act σ m = m}` form a `k`-subspace of `M`.

## Main result

* `SemilinearGaloisAction.descentEquiv` : the canonical `L`-linear map
  `L ⊗[k] M^Γ → M`, `l ⊗ m ↦ l • m`, is an **isomorphism**.

Equivalently `dim_k M^Γ = dim_L M`, and `M` is recovered from its `Γ`-fixed `k`-structure by
extension of scalars.  This is the additive form of Hilbert's Theorem 90 / Speiser's theorem.

## Proof strategy (classical)

The canonical map `φ : L ⊗[k] M^Γ → M` is shown to be a linear isomorphism by:

1. **Injectivity** (`descentMap_injective`) — Dedekind's linear independence of the distinct field
   automorphisms `σ : L → L` (`linearIndependent_monoidHom`).  A nontrivial kernel element of `φ`
   produces a nontrivial `L`-linear relation among the `σ`, contradicting independence.

2. **Surjectivity** (`descentMap_surjective`) — the trace-averaging argument.  Because `L / k` is
   separable, `Algebra.trace k L` is surjective (`Algebra.trace_surjective`); picking `a ∈ L` with
   `Tr(a) = 1`, the averaged operator `m ↦ ∑_{σ∈Γ} σ a • act σ m` lands in `M^Γ` and, summed over a
   suitable family, reconstructs any `m`.  Equivalently every `m ∈ M` lies in the `L`-span of `M^Γ`.

Both facts use the identification `FixedPoints.subfield Γ L = k` coming from `IsGalois k L`, which
gives `FaithfulSMul Γ L` and the dimension count `finrank k L = card Γ`.

The relevant Mathlib API: `linearIndependent_monoidHom` (Dedekind), `Algebra.trace_surjective`,
`Algebra.trace_eq_sum_automorphisms` (Galois trace = sum over `Γ`), `FixedPoints.finrank_eq_card`,
`Module.finrank_tensorProduct`, `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`.
-/

noncomputable section

universe u v

open scoped TensorProduct
open Module

namespace Representation

/-- A `k`-linear **semilinear** action of the Galois group `Γ = L ≃ₐ[k] L` on an `L`-module `M`:
for each `σ` an additive automorphism `act σ` of `M` that is `σ`-semilinear over `L` and respects
the group structure.  This is the descent datum whose fixed points descend `M` to `k`. -/
structure SemilinearGaloisAction (k : Type u) [Field k] (L : Type u) [Field L] [Algebra k L]
    (M : Type v) [AddCommGroup M] [Module L M] where
  /-- The additive automorphism of `M` attached to a Galois element `σ`. -/
  act : (L ≃ₐ[k] L) → (M ≃+ M)
  /-- `σ`-semilinearity: `act σ (c • m) = σ c • act σ m`. -/
  map_smul' : ∀ (σ : L ≃ₐ[k] L) (c : L) (m : M), act σ (c • m) = σ c • act σ m
  /-- The identity automorphism acts trivially. -/
  act_one' : act 1 = AddEquiv.refl M
  /-- Compatibility with composition. -/
  act_mul' : ∀ (σ τ : L ≃ₐ[k] L) (m : M), act (σ * τ) m = act σ (act τ m)

namespace SemilinearGaloisAction

variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]
variable {M : Type v} [AddCommGroup M] [Module L M] [Module k M] [IsScalarTower k L M]
variable (A : SemilinearGaloisAction k L M)

omit [Module k M] [IsScalarTower k L M] in
@[simp] theorem act_one_apply (m : M) : A.act 1 m = m := by rw [A.act_one']; rfl

omit [Module k M] [IsScalarTower k L M] in
theorem act_smul (σ : L ≃ₐ[k] L) (c : L) (m : M) : A.act σ (c • m) = σ c • A.act σ m :=
  A.map_smul' σ c m

omit [Module k M] [IsScalarTower k L M] in
theorem act_mul (σ τ : L ≃ₐ[k] L) (m : M) : A.act (σ * τ) m = A.act σ (A.act τ m) :=
  A.act_mul' σ τ m

/-- The set of `Γ`-fixed points, as a `k`-submodule of `M`.  (It is only `k`-linear: an `L`-scalar
multiple of a fixed point is generally *not* fixed.) -/
def fixed : Submodule k M where
  carrier := {m | ∀ σ : L ≃ₐ[k] L, A.act σ m = m}
  add_mem' {m₁ m₂} h₁ h₂ σ := by simp [map_add, h₁ σ, h₂ σ]
  zero_mem' σ := by simp
  smul_mem' c m h σ := by
    -- `c : k` acts via `algebraMap k L`, which is fixed by every `σ`.
    have hc : (c : k) • m = (algebraMap k L c) • m := by rw [algebraMap_smul]
    rw [hc, A.act_smul σ (algebraMap k L c) m, AlgEquiv.commutes σ c, h σ]

@[simp] theorem mem_fixed_iff {m : M} : m ∈ A.fixed ↔ ∀ σ : L ≃ₐ[k] L, A.act σ m = m := Iff.rfl

/-- The canonical `L`-linear descent map `L ⊗[k] M^Γ → M`, `l ⊗ m ↦ l • (m : M)`.

Built via `TensorProduct.AlgebraTensorModule.lift` from the `L`-linear-in-`l`, `k`-linear-in-`m`
bilinear map `l ↦ (m ↦ l • m)`, i.e. `toSpanSingleton L _ A.fixed.subtype`. -/
def descentMap : (L ⊗[k] A.fixed) →ₗ[L] M :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton L (A.fixed →ₗ[k] M) A.fixed.subtype)

@[simp] theorem descentMap_tmul (l : L) (m : A.fixed) :
    A.descentMap (l ⊗ₜ[k] m) = l • (m : M) := by
  rw [descentMap, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp [LinearMap.toSpanSingleton]

/-! ### The descent isomorphism (additive Speiser / Hilbert 90) -/

section Descent

variable [FiniteDimensional k L] [IsGalois k L]

/-- The trace-averaging operator `avg c m = ∑_{σ ∈ Γ} σ(c) • act σ m`.  For any `c` and `m` this
lands in the `Γ`-fixed points (`avg_mem_fixed`); it is the additive analogue of the trace. -/
def avg (c : L) (m : M) : M := ∑ σ : L ≃ₐ[k] L, σ c • A.act σ m

omit [Module k M] [IsScalarTower k L M] [IsGalois k L] in
theorem avg_def (c : L) (m : M) :
    A.avg c m = ∑ σ : L ≃ₐ[k] L, σ c • A.act σ m := rfl

omit [IsGalois k L] in
theorem avg_mem_fixed (c : L) (m : M) : A.avg c m ∈ A.fixed := by
  rw [A.mem_fixed_iff]
  intro τ
  rw [avg_def, map_sum]
  have hstep : ∀ σ : L ≃ₐ[k] L,
      A.act τ (σ c • A.act σ m) = (τ * σ) c • A.act (τ * σ) m := by
    intro σ
    rw [A.act_smul, A.act_mul, AlgEquiv.mul_apply]
  simp_rw [hstep]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)

/-- **Reconstruction identity.**  For a `k`-basis `b` of `L` with trace-dual basis `b.traceDual`,
`∑_{σ ∈ Γ} (∑_j b j · σ(b.traceDual j)) · σ(x) = x` for every `x ∈ L`. -/
private theorem galSum_recon {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι k L) (x : L) :
    ∑ σ : L ≃ₐ[k] L, (∑ j, b j * σ (b.traceDual j)) * σ x = x := by
  have step2 : ∀ j, ∑ σ : L ≃ₐ[k] L, b j * σ (b.traceDual j * x)
      = (Algebra.trace k L (b.traceDual j * x)) • b j := by
    intro j
    rw [← Finset.mul_sum, ← trace_eq_sum_automorphisms, Algebra.smul_def]
    ring
  have step3 : ∀ j, Algebra.trace k L (b.traceDual j * x) = b.repr x j := by
    intro j
    rw [mul_comm, ← Algebra.traceForm_apply, ← Module.Basis.traceDual_repr_apply,
      Module.Basis.traceDual_traceDual]
  calc ∑ σ : L ≃ₐ[k] L, (∑ j, b j * σ (b.traceDual j)) * σ x
      = ∑ σ : L ≃ₐ[k] L, ∑ j, b j * σ (b.traceDual j * x) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_mul]; ring
    _ = ∑ j, ∑ σ : L ≃ₐ[k] L, b j * σ (b.traceDual j * x) := Finset.sum_comm
    _ = ∑ j, (Algebra.trace k L (b.traceDual j * x)) • b j := by
        exact Finset.sum_congr rfl (fun j _ => step2 j)
    _ = ∑ j, (b.repr x j) • b j := by
        exact Finset.sum_congr rfl (fun j _ => by rw [step3 j])
    _ = x := b.sum_repr x

open Classical in
/-- **Dedekind step.**  The scalar `∑_j b j · σ(b.traceDual j)` equals the Kronecker delta
`δ_{σ,1}`.  This is linear independence of the field automorphisms (`linearIndependent_monoidHom`)
applied to the reconstruction identity. -/
private theorem galSum_traceDual {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι k L)
    (σ₀ : L ≃ₐ[k] L) :
    ∑ j, b j * σ₀ (b.traceDual j) = if σ₀ = 1 then 1 else 0 := by
  have hLI : LinearIndependent L (fun σ : L ≃ₐ[k] L => ((σ : L →* L) : L → L)) :=
    (linearIndependent_monoidHom L L).comp _ (fun σ τ h => by
      ext x; exact DFunLike.congr_fun h x)
  have hrel : ∑ σ : L ≃ₐ[k] L,
      ((∑ j, b j * σ (b.traceDual j)) - if σ = 1 then 1 else 0) •
        ((σ : L →* L) : L → L) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, MonoidHom.coe_coe, Pi.zero_apply]
    have h1 : ∑ σ : L ≃ₐ[k] L, (∑ j, b j * σ (b.traceDual j)) * σ x = x :=
      galSum_recon b x
    have h2 : ∑ σ : L ≃ₐ[k] L, (if σ = 1 then (1 : L) else 0) * σ x = x := by
      rw [Finset.sum_eq_single (1 : L ≃ₐ[k] L) (fun σ _ hσ => by simp [hσ])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [AlgEquiv.one_apply]
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, h1, h2, sub_self]
  have hcoeff := linearIndependent_iff'.mp hLI Finset.univ
    (fun σ => (∑ j, b j * σ (b.traceDual j)) - if σ = 1 then 1 else 0) hrel σ₀
    (Finset.mem_univ σ₀)
  exact sub_eq_zero.mp hcoeff

/-- **Surjectivity** of the descent map `L ⊗[k] M^Γ → M`: trace averaging shows every `m ∈ M` is an
`L`-combination of fixed vectors. -/
theorem descentMap_surjective : Function.Surjective A.descentMap := by
  intro m
  let b : Basis (Fin (finrank k L)) k L := Module.finBasis k L
  refine ⟨∑ j, b j ⊗ₜ[k] (⟨A.avg (b.traceDual j) m, A.avg_mem_fixed _ _⟩ : A.fixed), ?_⟩
  rw [map_sum]
  have hval : ∀ j, A.descentMap (b j ⊗ₜ[k]
      (⟨A.avg (b.traceDual j) m, A.avg_mem_fixed _ _⟩ : A.fixed))
      = b j • A.avg (b.traceDual j) m := fun j => A.descentMap_tmul _ _
  simp_rw [hval]
  have hrearr : ∑ j, b j • A.avg (b.traceDual j) m
      = ∑ σ : L ≃ₐ[k] L, (∑ j, b j * σ (b.traceDual j)) • A.act σ m := by
    simp only [A.avg_def, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_smul]
  rw [hrearr, Finset.sum_eq_single (1 : L ≃ₐ[k] L)]
  · rw [galSum_traceDual b (1 : L ≃ₐ[k] L), if_pos rfl, one_smul, A.act_one_apply]
  · intro σ _ hσ
    rw [galSum_traceDual b σ, if_neg hσ, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

variable [FiniteDimensional L M]

/-- **Injectivity** of the descent map `L ⊗[k] M^Γ → M`: a `k`-basis of `M^Γ` remains
`L`-linearly independent in `M` (additive Speiser), via nondegeneracy of the trace form. -/
theorem descentMap_injective : Function.Injective A.descentMap := by
  haveI : FiniteDimensional k M := Module.Finite.trans L M
  let B : Basis (Fin (finrank k A.fixed)) k A.fixed := Module.finBasis k A.fixed
  -- abbreviation for the coordinates of `x` in the base-changed basis
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  rw [LinearMap.mem_ker] at hx
  -- the fixed-point vectors are `Γ`-invariant
  have hBfix : ∀ (i) (σ : L ≃ₐ[k] L), A.act σ ((B i : M)) = (B i : M) :=
    fun i σ => (A.mem_fixed_iff.mp (B i).2) σ
  -- `descentMap x` written in coordinates
  have hdx : A.descentMap x = ∑ i, ((B.baseChange L).repr x i) • (B i : M) := by
    conv_lhs => rw [← (B.baseChange L).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Module.Basis.baseChange_apply, A.descentMap_tmul, one_smul]
  -- averaging `s • (descentMap x)` over `Γ` produces a `k`-relation among `B i`
  have e3 : ∀ s : L, ∑ σ : L ≃ₐ[k] L, A.act σ (s • A.descentMap x)
      = ∑ i, (algebraMap k L (Algebra.trace k L (s * (B.baseChange L).repr x i))) • (B i : M) := by
    intro s
    have e2 : ∀ σ : L ≃ₐ[k] L, A.act σ (s • A.descentMap x)
        = ∑ i, σ (s * (B.baseChange L).repr x i) • (B i : M) := by
      intro σ
      rw [hdx, Finset.smul_sum, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, A.act_smul, hBfix i σ]
    simp_rw [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms]
  -- the relation vanishes because `descentMap x = 0`
  have hzero : ∀ s : L,
      ∑ i, (Algebra.trace k L (s * (B.baseChange L).repr x i)) • (B i : M) = 0 := by
    intro s
    have h0 : ∑ σ : L ≃ₐ[k] L, A.act σ (s • A.descentMap x) = 0 := by
      rw [hx]; simp
    rw [e3] at h0
    rw [← h0]
    exact Finset.sum_congr rfl (fun i _ => by rw [algebraMap_smul])
  -- `B i` are `k`-linearly independent in `M`, so the trace coefficients vanish
  have hLI_M : LinearIndependent k (fun i => (B i : M)) :=
    B.linearIndependent.map' A.fixed.subtype (Submodule.ker_subtype _)
  have key : ∀ (s : L) (i), Algebra.trace k L (s * (B.baseChange L).repr x i) = 0 := fun s i =>
    linearIndependent_iff'.mp hLI_M Finset.univ
      (fun i => Algebra.trace k L (s * (B.baseChange L).repr x i)) (hzero s) i (Finset.mem_univ i)
  -- nondegeneracy of the trace form forces every coordinate to vanish
  have hl0 : ∀ i, (B.baseChange L).repr x i = 0 := by
    intro i
    refine (traceForm_nondegenerate k L).1 ((B.baseChange L).repr x i) (fun s => ?_)
    rw [Algebra.traceForm_apply, mul_comm]
    exact key s i
  rw [← (B.baseChange L).sum_repr x]
  simp [hl0]

/-- **The descent isomorphism** (additive Speiser / Hilbert 90): the canonical `L`-linear map
`L ⊗[k] M^Γ → M`, `l ⊗ m ↦ l • m`, is a linear isomorphism. -/
def descentEquiv : (L ⊗[k] A.fixed) ≃ₗ[L] M :=
  LinearEquiv.ofBijective A.descentMap ⟨A.descentMap_injective, A.descentMap_surjective⟩

@[simp] theorem descentEquiv_tmul (l : L) (m : A.fixed) :
    A.descentEquiv (l ⊗ₜ[k] m) = l • (m : M) := by
  change A.descentMap (l ⊗ₜ[k] m) = l • (m : M)
  exact A.descentMap_tmul l m

/-- The dimension count behind the descent: `dim_k M^Γ = dim_L M`. -/
theorem finrank_fixed_eq : finrank k A.fixed = finrank L M := by
  rw [← Module.finrank_baseChange (R := L) (S := k) (M' := A.fixed)]
  exact A.descentEquiv.finrank_eq

end Descent

end SemilinearGaloisAction

end Representation

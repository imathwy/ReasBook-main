import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SeparableAveraging

/-!
# Separable base change preserves semisimplicity (modular case, hypothesis (A))

This module supplies hypothesis **(A)** of the characteristic-`p` reduction
`isIrreducible_scalarExtension_of_isSemisimple_of_finrank_intertwiningMap_eq_one`
(see `FieldIndependence/CharPReduction.lean`):

> a semisimple `k[G]`-representation `ρ`, scalar-extended along a **separable** field extension
> `K / k`, stays semisimple over `K[G]`.

The endgame consumes the specialization to `K = AlgebraicClosure k` for a **perfect** base field
`k` (a simple `k[G]`-representation is in particular semisimple, and over a perfect field the
algebraic closure is automatically separable, by `Algebra.IsAlgebraic.isSeparable_of_perfectField`).

## Mathematical content

A `k[G]`-module `M` is semisimple iff it is a direct sum of simple submodules.  Scalar extension
`K ⊗_k (-)` is an additive, `K`-linear, `G`-equivariant exact functor on finite-dimensional
representations, so it carries a direct-sum decomposition `M = ⨁ Sᵢ` to `M_K = ⨁ (Sᵢ)_K`.  A
direct sum of semisimple representations is semisimple, so the whole statement reduces to the single
atom:

* **(atom)** the scalar extension of a *simple* `k[G]`-representation along a separable extension is
  semisimple.

This atom is the genuine separability input: it can fail for an *inseparable* extension (where the
group algebra of the extended field acquires nilpotents in its action), but holds for separable
`K / k` because the endomorphism division algebra of a simple module is then a separable
`k`-algebra,
so its base change `K ⊗_k End_{k[G]}(S)` is again semisimple.  Mathlib does not (yet) contain the
"semisimple algebra ⊗ separable field = semisimple" theorem, so the atom is isolated here as the
single residual hypothesis `isSemisimpleRepresentation_scalarExtension_of_isIrreducible_separable`.
-/

noncomputable section

universe u

open scoped TensorProduct MonoidAlgebra

namespace Representation

/-! ## Base-change of submodules: spanning and stability helpers -/

section Submodule

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The base change of an iSup of `k`-submodules is contained in the iSup of the base changes.
(The reverse inclusion also holds by monotonicity; only this direction is needed.) -/
theorem baseChange_iSup_le {ι : Type*} (f : ι → Submodule k V) :
    (⨆ i, f i).baseChange K ≤ ⨆ i, (f i).baseChange K := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.iSup_induction' with
  | mem i x hx => exact Submodule.mem_iSup_of_mem i (Submodule.tmul_mem_baseChange_of_mem 1 hx)
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy

/-- The base change of a `k`-linear map carries the base change of a submodule into the base change
of its image. -/
theorem map_baseChange_le (N : Submodule k V) (f : V →ₗ[k] V) :
    (N.baseChange K).map (f.baseChange K) ≤ (N.map f).baseChange K := by
  rw [Submodule.map_le_iff_le_comap, Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.baseChange_tmul,
    TensorProduct.mk_apply]
  exact Submodule.tmul_mem_baseChange_of_mem 1 (Submodule.mem_map_of_mem hx)

/-- The canonical `K`-linear equivalence `K ⊗_k N ≃ N.baseChange K`, using that a field is flat
(so `K ⊗ (-)` preserves the injection `N ↪ V`). -/
def baseChangeEquivTensor (N : Submodule k V) : (K ⊗[k] N) ≃ₗ[K] N.baseChange K :=
  LinearEquiv.ofBijective (N.toBaseChange K)
    ⟨by
      have hinj : Function.Injective (N.subtype.baseChange K) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
      intro a b hab
      exact hinj (congrArg Subtype.val hab),
     N.toBaseChange_surjective K⟩

@[simp] theorem baseChangeEquivTensor_tmul (N : Submodule k V) (a : K) (x : N) :
    ((baseChangeEquivTensor (K := K) N) (a ⊗ₜ[k] x) : K ⊗[k] V) = a ⊗ₜ[k] (x : V) := rfl

end Submodule

/-! ## Base change of a subrepresentation -/

section Subrep

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
variable {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

private theorem scalarExtension_apply (g : G) :
    (scalarExtension (k := K) ρ) g = LinearMap.baseChange K (ρ g) := rfl

/-- The base change of a subrepresentation `σ ≤ ρ` to a subrepresentation of `scalarExtension ρ`.
The carrier is the `K`-base change `σ.toSubmodule.baseChange K`, which is `G`-stable because the
scalar-extended action is the base change of the original action. -/
def baseChangeSubrep (σ : Subrepresentation ρ) :
    Subrepresentation (scalarExtension (k := K) ρ) where
  toSubmodule := σ.toSubmodule.baseChange K
  apply_mem_toSubmodule g v hv := by
    change (LinearMap.baseChange K (ρ g)) v ∈ σ.toSubmodule.baseChange K
    have hmap : (LinearMap.baseChange K (ρ g)) v ∈
        (σ.toSubmodule.baseChange K).map ((ρ g).baseChange K) := ⟨v, hv, rfl⟩
    refine (Submodule.baseChange_mono K ?_) (map_baseChange_le σ.toSubmodule (ρ g) hmap)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact σ.apply_mem_toSubmodule g hy

@[simp] theorem baseChangeSubrep_toSubmodule (σ : Subrepresentation ρ) :
    (baseChangeSubrep (K := K) ρ σ).toSubmodule = σ.toSubmodule.baseChange K := rfl

/-- The base-changed subrepresentation `baseChangeSubrep ρ σ` is equivalent, as a representation,
to the scalar extension of the subrepresentation `σ.toRepresentation`.

The underlying `K`-linear equivalence is `baseChangeEquivTensor`, identifying `K ⊗_k σ` with the
carrier `σ.baseChange K`; it is `G`-equivariant because both actions are the base change of
`σ.toRepresentation g`. -/
def baseChangeSubrepEquiv (σ : Subrepresentation ρ) :
    (scalarExtension (k := K) σ.toRepresentation).Equiv
      (baseChangeSubrep (K := K) ρ σ).toRepresentation :=
  Representation.Equiv.mk (baseChangeEquivTensor (K := K) σ.toSubmodule)
    (by
      intro g
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a y =>
          apply Subtype.ext
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          change ((baseChangeEquivTensor (K := K) σ.toSubmodule)
              ((scalarExtension (k := K) σ.toRepresentation) g (a ⊗ₜ[k] y)) : K ⊗[k] V)
            = (scalarExtension (k := K) ρ) g
                ((baseChangeEquivTensor (K := K) σ.toSubmodule) (a ⊗ₜ[k] y) : K ⊗[k] V)
          rw [scalarExtension_apply σ.toRepresentation g, scalarExtension_apply ρ g,
            LinearMap.baseChange_tmul, baseChangeEquivTensor_tmul, baseChangeEquivTensor_tmul,
            LinearMap.baseChange_tmul]
          rfl
      | add x y hx hy =>
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_add] at hx hy ⊢
          rw [hx, hy])

end Subrep

/-! ## Transport of semisimplicity along representation equivalences -/

section Transport

variable {k : Type u} [Field k] {G : Type u} [Group G]
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The `k[G]`-linear equivalence of `asModule`s underlying a representation equivalence. -/
def Equiv.asModuleLinearEquiv {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : ρ.asModule ≃ₗ[k[G]] σ.asModule :=
  LinearEquiv.ofBijective (IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    (by
      have hcoe : (⇑(IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap) :
          ρ.asModule → σ.asModule) = (e.toLinearEquiv : V → W) := rfl
      rw [hcoe]; exact e.toLinearEquiv.bijective)

/-- Semisimplicity of a representation transports along a representation equivalence. -/
theorem isSemisimpleRepresentation_of_equiv {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) (hρ : IsSemisimpleRepresentation ρ) : IsSemisimpleRepresentation σ := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hρ ⊢
  -- `IsSemisimpleModule.congr`'s `Module` instance argument is synthesized lazily and fails to
  -- resolve `Module k[G] (asModule …)` in this position, so we capture the instances eagerly.
  letI iM : Module k[G] ρ.asModule := inferInstance
  letI iN : Module k[G] σ.asModule := inferInstance
  letI iAM : AddCommGroup ρ.asModule := inferInstance
  letI iAN : AddCommGroup σ.asModule := inferInstance
  exact @IsSemisimpleModule.congr k[G] _ ρ.asModule iAM iM σ.asModule iAN iN hρ
    e.asModuleLinearEquiv.symm

end Transport

/-! ## Descent infrastructure for the infinite separable case -/

section Helper
variable {K0 : Type u} [Field K0]
variable {G : Type u} [Group G]
variable {W : Type u} [AddCommGroup W] [Module K0 W]

/-- A semisimple representation admits, for every subrepresentation, a `G`-equivariant linear
projection onto it (corestriction of the splitting along a complement). -/
theorem exists_proj_of_subrep_of_isSemisimple
    (ρ : Representation K0 G W) [IsSemisimpleRepresentation ρ]
    (Nσ : Subrepresentation ρ) :
    ∃ p : W →ₗ[K0] W,
      (∀ m, p m ∈ Nσ.toSubmodule) ∧ (∀ m ∈ Nσ.toSubmodule, p m = m) ∧
      (∀ (g : G) (m : W), p (ρ g m) = ρ g (p m)) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_isCompl Nσ
  have hcompl : IsCompl Nσ.toSubmodule τ.toSubmodule := by
    rw [isCompl_iff] at hτ ⊢
    obtain ⟨hd, hc⟩ := hτ
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff] at hd ⊢
      have := congrArg Subrepresentation.toSubmodule hd
      simpa using this
    · rw [codisjoint_iff] at hc ⊢
      have := congrArg Subrepresentation.toSubmodule hc
      simpa using this
  set p : W →ₗ[K0] W :=
    Nσ.toSubmodule.subtype.comp (Nσ.toSubmodule.linearProjOfIsCompl τ.toSubmodule hcompl) with hp
  have hpmem : ∀ m, p m ∈ Nσ.toSubmodule := fun m =>
    (Nσ.toSubmodule.linearProjOfIsCompl τ.toSubmodule hcompl m).2
  have hpid : ∀ m ∈ Nσ.toSubmodule, p m = m := by
    intro m hm
    rw [hp]
    change ((Nσ.toSubmodule.linearProjOfIsCompl τ.toSubmodule hcompl m : W)) = m
    rw [Submodule.linearProjOfIsCompl_apply_left hcompl ⟨m, hm⟩]
  refine ⟨p, hpmem, hpid, ?_⟩
  intro g m
  have hmem : m ∈ Nσ.toSubmodule ⊔ τ.toSubmodule :=
    hcompl.codisjoint.eq_top ▸ Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hmem
  have hps : p m = s := by
    rw [hp]
    change ((Nσ.toSubmodule.linearProjOfIsCompl τ.toSubmodule hcompl m : W)) = s
    rw [← hst, map_add, Submodule.linearProjOfIsCompl_apply_left hcompl ⟨s, hs⟩,
      Submodule.linearProjOfIsCompl_apply_right hcompl ⟨t, ht⟩, add_zero]
  have hsN : ρ g s ∈ Nσ.toSubmodule := Nσ.apply_mem_toSubmodule g hs
  have htτ : ρ g t ∈ τ.toSubmodule := τ.apply_mem_toSubmodule g ht
  have hpgm : p (ρ g m) = ρ g s := by
    have hsplit : ρ g m = ρ g s + ρ g t := by rw [← hst, map_add]
    rw [hsplit, hp]
    change ((Nσ.toSubmodule.linearProjOfIsCompl τ.toSubmodule hcompl (ρ g s + ρ g t) : W)) = ρ g s
    rw [map_add, Submodule.linearProjOfIsCompl_apply_left hcompl ⟨_, hsN⟩,
      Submodule.linearProjOfIsCompl_apply_right hcompl ⟨_, htτ⟩, add_zero]
  rw [hpgm, hps]

/-- A semisimple representation admits, for every `G`-stable submodule, a `G`-equivariant linear
projection onto it. -/
theorem exists_proj_of_stable_submodule_of_isSemisimple
    (ρ : Representation K0 G W) [IsSemisimpleRepresentation ρ]
    (N0 : Submodule K0 W) (hN0 : ∀ (g : G) (m : W), m ∈ N0 → ρ g m ∈ N0) :
    ∃ p : W →ₗ[K0] W,
      (∀ m, p m ∈ N0) ∧ (∀ m ∈ N0, p m = m) ∧
      (∀ (g : G) (m : W), p (ρ g m) = ρ g (p m)) :=
  exists_proj_of_subrep_of_isSemisimple ρ
    { toSubmodule := N0, apply_mem_toSubmodule := fun g m hm => hN0 g m hm }

end Helper

section ScalarExtMul
variable {k : Type u} [Field k] {K0 : Type u} [Field K0] [Algebra k K0]
variable {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The scalar-extended action composes via the group law. -/
theorem scalarExtension_apply_mul (S : Representation k G V) (g g' : G) (m : K0 ⊗[k] V) :
    (scalarExtension (k := K0) S) g ((scalarExtension (k := K0) S) g' m)
      = (scalarExtension (k := K0) S) (g * g') m := by
  rw [map_mul]; rfl

end ScalarExtMul

section Cancel
variable {k : Type u} [Field k] {K0 : Type u} [Field K0] [Algebra k K0]
variable {K : Type u} [Field K] [Algebra k K] [Algebra K0 K] [IsScalarTower k K0 K]
variable {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The `cancelBaseChange` equivalence intertwines the iterated scalar extension with the direct
one. -/
theorem cancelBaseChange_scalarExtension_equiv (S : Representation k G V) (g : G)
    (w : K ⊗[K0] (K0 ⊗[k] V)) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k K0 K K V)
        ((scalarExtension (k := K) (scalarExtension (k := K0) S)) g w)
      = (scalarExtension (k := K) S) g
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange k K0 K K V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a u =>
      induction u using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
      | tmul b v =>
          show (TensorProduct.AlgebraTensorModule.cancelBaseChange k K0 K K V)
              (LinearMap.baseChange K (LinearMap.baseChange K0 (S g)) (a ⊗ₜ[K0] (b ⊗ₜ[k] v)))
            = LinearMap.baseChange K (S g)
                ((TensorProduct.AlgebraTensorModule.cancelBaseChange k K0 K K V)
                  (a ⊗ₜ[K0] (b ⊗ₜ[k] v)))
          rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
              TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
              TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
              LinearMap.baseChange_tmul]
      | add u1 u2 hu1 hu2 =>
          rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, hu1, hu2]
  | add w1 w2 hw1 hw2 => simp only [map_add]; rw [hw1, hw2]

end Cancel

section BaseChangeProj
variable {K0 : Type u} [Field K0] {K : Type u} [Field K] [Algebra K0 K]
variable {W : Type u} [AddCommGroup W] [Module K0 W]

/-- The base change of a map landing in `N0` lands in `N0.baseChange K`. -/
theorem baseChange_mem_baseChange (N0 : Submodule K0 W) (p : W →ₗ[K0] W)
    (hp : ∀ m, p m ∈ N0) (y : K ⊗[K0] W) : (p.baseChange K) y ∈ N0.baseChange K := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a w => rw [LinearMap.baseChange_tmul]; exact Submodule.tmul_mem_baseChange_of_mem a (hp w)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- The base change of a map that is the identity on `N0` is the identity on `N0.baseChange K`. -/
theorem baseChange_id_on_baseChange (N0 : Submodule K0 W) (p : W →ₗ[K0] W)
    (hp : ∀ m ∈ N0, p m = m) (z : K ⊗[K0] W) (hz : z ∈ N0.baseChange K) :
    (p.baseChange K) z = z := by
  rw [Submodule.baseChange_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨w, hw, rfl⟩ := hu
      rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul, hp w hw]
  | zero => rw [map_zero]
  | add a b _ _ iha ihb => rw [map_add, iha, ihb]
  | smul c a _ iha => rw [map_smul, iha]

end BaseChangeProj

section Descent
variable {k : Type u} [Field k] {K0 : Type u} [Field K0] [Algebra k K0]
variable {K : Type u} [Field K] [Algebra k K] [Algebra K0 K] [IsScalarTower k K0 K]
variable {G : Type u} [Group G] [Finite G]

/-- **Descent step over an abstract finite separable subextension `K0 / k`.**

Given a finite spanning family `gens` of a `G`-stable `K`-submodule `N` of `K ⊗_k V`, whose
coordinates (in the base-changed basis `eb.baseChange K`) all lie in the image of `algebraMap K0 K`,
and assuming `scalarExtension (k := K0) S` is semisimple, there is a `G`-equivariant `K`-linear
projection onto `N`. -/
theorem descent_step
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : Representation k G V) [IsSemisimpleRepresentation (scalarExtension (k := K0) S)]
    (N : Submodule K (K ⊗[k] V))
    (hN : ∀ (g : G) ⦃m⦄, m ∈ N → (Representation.scalarExtension (k := K) S) g m ∈ N)
    (gens : Finset (K ⊗[k] V)) (hgens : Submodule.span K (gens : Set (K ⊗[k] V)) = N)
    (eb : Module.Basis (Fin (Module.finrank k V)) k V)
    (hmem : ∀ x ∈ gens, ∀ i,
      (eb.baseChange K).repr x i ∈ (algebraMap K0 K).range) :
    ∃ π : (K ⊗[k] V) →ₗ[K] (K ⊗[k] V),
      (∀ m, π m ∈ N) ∧ (∀ m ∈ N, π m = m) ∧
      (∀ (g : G) (m : K ⊗[k] V),
        π ((Representation.scalarExtension (k := K) S) g m)
          = (Representation.scalarExtension (k := K) S) g (π m)) := by
  classical
  set EB : Module.Basis (Fin (Module.finrank k V)) K (K ⊗[k] V) := eb.baseChange K with hEB
  -- the cancelBaseChange equivalence
  let Ψ : K ⊗[K0] (K0 ⊗[k] V) ≃ₗ[K] K ⊗[k] V :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange k K0 K K V
  have hΨ_tmul : ∀ (a : K) (b : K0) (v : V),
      Ψ (a ⊗ₜ[K0] (b ⊗ₜ[k] v)) = (b • a) ⊗ₜ[k] v := fun _ _ _ => rfl
  -- chosen K0-preimage of each coordinate
  let c0 : (x : K ⊗[k] V) → x ∈ gens → Fin (Module.finrank k V) → K0 :=
    fun x hx i => Classical.choose (hmem x hx i)
  have hc0 : ∀ (x : K ⊗[k] V) (hx : x ∈ gens) (i),
      algebraMap K0 K (c0 x hx i) = EB.repr x i :=
    fun x hx i => Classical.choose_spec (hmem x hx i)
  -- lift of a generator x to K0 ⊗ V
  let lift : (x : K ⊗[k] V) → x ∈ gens → (K0 ⊗[k] V) :=
    fun x hx => ∑ i, (c0 x hx i) ⊗ₜ[k] eb i
  -- key: Ψ (1 ⊗ lift x) = x
  have key : ∀ (x : K ⊗[k] V) (hx : x ∈ gens), Ψ ((1 : K) ⊗ₜ[K0] (lift x hx)) = x := by
    intro x hx
    have hsmul1 : ∀ (c : K0), c • (1 : K) = algebraMap K0 K c := by
      intro c; rw [Algebra.smul_def, mul_one]
    have hLHS : Ψ ((1 : K) ⊗ₜ[K0] (lift x hx)) = ∑ i, EB.repr x i ⊗ₜ[k] eb i := by
      show Ψ ((1 : K) ⊗ₜ[K0] (∑ i, (c0 x hx i) ⊗ₜ[k] eb i)) = _
      rw [TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hΨ_tmul, hsmul1, hc0 x hx i]
    rw [hLHS]
    conv_rhs => rw [← EB.sum_repr x]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hEB, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  -- the G-invariant generating set for N0
  let gen0Set : Set (K0 ⊗[k] V) :=
    { y | ∃ (g : G) (x : K ⊗[k] V) (hx : x ∈ gens),
        y = (scalarExtension (k := K0) S) g (lift x hx) }
  let N0 : Submodule K0 (K0 ⊗[k] V) := Submodule.span K0 gen0Set
  -- gen0Set is G-invariant
  have hgen0_stable : ∀ (g : G) (y : K0 ⊗[k] V), y ∈ gen0Set →
      (scalarExtension (k := K0) S) g y ∈ gen0Set := by
    rintro g y ⟨g', x, hx, rfl⟩
    exact ⟨g * g', x, hx, scalarExtension_apply_mul S g g' (lift x hx)⟩
  -- N0 is G-stable
  have hN0 : ∀ (g : G) (m : K0 ⊗[k] V), m ∈ N0 →
      (scalarExtension (k := K0) S) g m ∈ N0 := by
    intro g m hm
    refine Submodule.span_induction
      (p := fun z _ => (scalarExtension (k := K0) S) g z ∈ N0) ?_ ?_ ?_ ?_ hm
    · intro y hy; exact Submodule.subset_span (hgen0_stable g y hy)
    · show (scalarExtension (k := K0) S) g 0 ∈ N0
      rw [map_zero]; exact Submodule.zero_mem _
    · intro a b _ _ iha ihb
      show (scalarExtension (k := K0) S) g (a + b) ∈ N0
      rw [map_add]; exact Submodule.add_mem _ iha ihb
    · intro c a _ iha
      show (scalarExtension (k := K0) S) g (c • a) ∈ N0
      rw [map_smul]; exact Submodule.smul_mem _ _ iha
  -- K0-projection onto N0 (G-stable submodule of the semisimple representation)
  obtain ⟨p0, hp0N, hp0id, hp0equiv⟩ :=
    exists_proj_of_stable_submodule_of_isSemisimple (scalarExtension (k := K0) S) N0 hN0
  -- baseChange p0 to K
  let bcp0 : (K ⊗[K0] (K0 ⊗[k] V)) →ₗ[K] (K ⊗[K0] (K0 ⊗[k] V)) := LinearMap.baseChange K p0
  have hbc_mem : ∀ y, bcp0 y ∈ N0.baseChange K :=
    fun y => baseChange_mem_baseChange (K := K) N0 p0 hp0N y
  have hbc_id : ∀ z ∈ N0.baseChange K, bcp0 z = z :=
    fun z hz => baseChange_id_on_baseChange (K := K) N0 p0 hp0id z hz
  -- the transported projection
  let π : (K ⊗[k] V) →ₗ[K] (K ⊗[k] V) :=
    (Ψ.toLinearMap).comp (bcp0.comp Ψ.symm.toLinearMap)
  have hπ_def : ∀ m, π m = Ψ (bcp0 (Ψ.symm m)) := fun m => rfl
  -- N = Ψ '' (N0.baseChange K)
  have hN_eq : N = (N0.baseChange K).map Ψ.toLinearMap := by
    apply le_antisymm
    · rw [← hgens, Submodule.span_le]
      intro x hx
      simp only [SetLike.mem_coe]
      rw [Submodule.mem_map]
      refine ⟨(1 : K) ⊗ₜ[K0] (lift x hx), ?_, key x hx⟩
      have hliftN0 : lift x hx ∈ N0 := Submodule.subset_span ⟨1, x, hx, by rw [map_one]; rfl⟩
      exact Submodule.tmul_mem_baseChange_of_mem 1 hliftN0
    · rw [Submodule.map_le_iff_le_comap, Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, TensorProduct.mk_apply]
      refine Submodule.span_induction
        (p := fun z _ => Ψ ((1 : K) ⊗ₜ[K0] z) ∈ N) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨g, x, hx, rfl⟩
        rw [show ((1 : K) ⊗ₜ[K0] ((scalarExtension (k := K0) S) g (lift x hx)))
            = (scalarExtension (k := K) (scalarExtension (k := K0) S)) g
                ((1 : K) ⊗ₜ[K0] (lift x hx)) from by
              show _ = LinearMap.baseChange K (LinearMap.baseChange K0 (S g)) _
              rw [LinearMap.baseChange_tmul]; rfl]
        rw [cancelBaseChange_scalarExtension_equiv, key x hx]
        exact hN g (by rw [← hgens]; exact Submodule.subset_span hx)
      · show Ψ ((1 : K) ⊗ₜ[K0] (0 : K0 ⊗[k] V)) ∈ N
        rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
      · intro a b _ _ iha ihb
        show Ψ ((1 : K) ⊗ₜ[K0] (a + b)) ∈ N
        rw [TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ iha ihb
      · intro c a _ iha
        show Ψ ((1 : K) ⊗ₜ[K0] (c • a)) ∈ N
        have hcomm : (1 : K) ⊗ₜ[K0] (c • a) = (algebraMap K0 K c) • ((1 : K) ⊗ₜ[K0] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
            Algebra.smul_def, mul_one]
        rw [hcomm, map_smul]
        exact N.smul_mem _ iha
  -- assemble the three properties of π
  refine ⟨π, ?_, ?_, ?_⟩
  · intro m
    rw [hπ_def, hN_eq, Submodule.mem_map]
    exact ⟨bcp0 (Ψ.symm m), hbc_mem (Ψ.symm m), rfl⟩
  · intro m hm
    rw [hN_eq, Submodule.mem_map] at hm
    obtain ⟨z, hz, rfl⟩ := hm
    rw [hπ_def]
    show Ψ (bcp0 (Ψ.symm (Ψ z))) = Ψ z
    rw [LinearEquiv.symm_apply_apply, hbc_id z hz]
  · intro g m
    rw [hπ_def, hπ_def]
    have hsymm : Ψ.symm ((scalarExtension (k := K) S) g m)
        = (scalarExtension (k := K) (scalarExtension (k := K0) S)) g (Ψ.symm m) := by
      apply Ψ.injective
      rw [LinearEquiv.apply_symm_apply, cancelBaseChange_scalarExtension_equiv,
        LinearEquiv.apply_symm_apply]
    rw [hsymm]
    have hbc_comm : bcp0 ((scalarExtension (k := K) (scalarExtension (k := K0) S)) g (Ψ.symm m))
        = (scalarExtension (k := K) (scalarExtension (k := K0) S)) g (bcp0 (Ψ.symm m)) := by
      show LinearMap.baseChange K p0
            (LinearMap.baseChange K (LinearMap.baseChange K0 (S g)) (Ψ.symm m))
          = LinearMap.baseChange K (LinearMap.baseChange K0 (S g))
            (LinearMap.baseChange K p0 (Ψ.symm m))
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        ← LinearMap.baseChange_comp]
      congr 2
      apply LinearMap.ext
      intro w
      simp only [LinearMap.comp_apply]
      exact hp0equiv g w
    rw [hbc_comm]
    show Ψ ((scalarExtension (k := K) (scalarExtension (k := K0) S)) g (bcp0 (Ψ.symm m))) = _
    rw [cancelBaseChange_scalarExtension_equiv]

end Descent


/-! ## The simple atom (separability input) -/

section Atom

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
variable {G : Type u} [Group G] [Finite G]

/-! **Atom (separability input).** The scalar extension of an *irreducible* `k[G]`-representation
along a separable field extension `K / k` is a semisimple `K[G]`-representation
(`isSemisimpleRepresentation_scalarExtension_of_isIrreducible_separable` below).

This is the single genuinely separable-specific fact behind the whole reduction.  Mathematically it
is the statement that the endomorphism division algebra `D = End_{k[G]}(S)` of a simple module is a
*separable* `k`-algebra, so that its base change `K ⊗_k D` is again semisimple (for an inseparable
extension this can fail).

For a **finite** separable extension the atom is now *proved* (Maschke averaging over `K / k`,
`Representation.isSemisimpleRepresentation_scalarExtension_of_isSemisimple_finite` in
`SeparableAveraging.lean`).  For a general (possibly infinite) separable extension it is obtained
from the finite case by the standard reduction to a finite subextension; that reduction is the only
remaining gap, and is purely a base-change/descent statement with **no** further separability
content (see `isSemisimpleRepresentation_scalarExtension_of_isSemisimple_infinite` below). -/

/-- **Descent-to-finite-subextension residual (the single remaining gap).**

Given a `G`-stable `K`-submodule `N` of `K ⊗_k V` (i.e. a subrepresentation of
`scalarExtension (k := K) S`), there is a `G`-equivariant `K`-linear *projection* `π` onto `N`
(`π` lands in `N`, restricts to the identity on `N`, and commutes with the `G`-action).

This is the only step of the infinite-extension reduction that is not yet formalised, and it carries
**no** separability content beyond the finite case.  The mathematical content is the standard
*descent to a finite subextension*: `N` is finite-dimensional over `K` (a subspace of the
finite-dimensional `K ⊗_k V`), hence spanned by finitely many vectors, each a finite `K`-linear
combination of the pure tensors `1 ⊗ eⱼ` for a fixed `k`-basis `(eⱼ)` of `V`.  The finitely many
`K`-coefficients occurring generate a finitely generated subextension
`K₀ := k⟮coeffs⟯ ⊆ K`, which is **finite** and separable over `k`
(`IntermediateField.finiteDimensional_adjoin` for algebraic — hence integral — separable elements).
Thus `N` is defined over `K₀`: it is the image, under the base-change identification
`K ⊗_{K₀} (K₀ ⊗_k V) ≅ K ⊗_k V` (`TensorProduct.AlgebraTensorModule.cancelBaseChange`, which is a
representation equivalence between `scalarExtension (k := K) (scalarExtension (k := K₀) S)` and
`scalarExtension (k := K) S`), of `N₀.baseChange K` for a `G`-stable `K₀`-submodule
`N₀ ⊆ K₀ ⊗_k V`.  The **finite** atom
`Representation.isSemisimpleRepresentation_scalarExtension_of_isSemisimple_finite` makes
`scalarExtension (k := K₀) S` semisimple, so `N₀` admits a `G`-equivariant `K₀`-linear projection
(`exists_kProj_of_isSemisimple`/`isCompl_of_kProj` over the finite extension `K₀ / k`);
base-changing that projection along `K₀ → K` and transporting it through the `cancelBaseChange`
identification gives the required `G`-equivariant `K`-linear projection `π` onto `N`. -/
theorem exists_Gequivariant_projection_of_separable_descent
    [Algebra.IsSeparable k K]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : Representation k G V) [IsSemisimpleRepresentation S]
    (N : Submodule K (K ⊗[k] V))
    (hN : ∀ (g : G) ⦃m⦄, m ∈ N → (Representation.scalarExtension (k := K) S) g m ∈ N) :
    ∃ π : (K ⊗[k] V) →ₗ[K] (K ⊗[k] V),
      (∀ m, π m ∈ N) ∧ (∀ m ∈ N, π m = m) ∧
      (∀ (g : G) (m : K ⊗[k] V),
        π ((Representation.scalarExtension (k := K) S) g m)
          = (Representation.scalarExtension (k := K) S) g (π m)) := by
  classical
  let eb : Module.Basis (Fin (Module.finrank k V)) k V := Module.finBasis k V
  let EB : Module.Basis (Fin (Module.finrank k V)) K (K ⊗[k] V) := eb.baseChange K
  have hNfg : N.FG := (Submodule.fg_iff_finiteDimensional N).mpr inferInstance
  obtain ⟨gens, hgens⟩ := hNfg
  -- the finite subextension generated by the coordinates of the generators
  let coeffs : Finset K := gens.biUnion (fun x => Finset.image (fun i => EB.repr x i) Finset.univ)
  let K0 : IntermediateField k K := IntermediateField.adjoin k (coeffs : Set K)
  haveI hfd : FiniteDimensional k K0 := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x _; exact Algebra.IsIntegral.isIntegral x
  haveI hsep : Algebra.IsSeparable k K0 := Algebra.isSeparable_tower_bot_of_isSeparable k K0 K
  -- the coordinates lie in K0
  have hmem0 : ∀ x ∈ gens, ∀ i, EB.repr x i ∈ K0 := by
    intro x hx i
    apply IntermediateField.subset_adjoin
    simp only [coeffs, Finset.coe_biUnion, Set.mem_iUnion, Finset.coe_image]
    exact ⟨x, hx, i, Finset.mem_univ i, rfl⟩
  -- the coordinates lie in the range of algebraMap K0 K
  have hmem : ∀ x ∈ gens, ∀ i, EB.repr x i ∈ (algebraMap K0 K).range := by
    intro x hx i
    exact ⟨⟨EB.repr x i, hmem0 x hx i⟩, rfl⟩
  -- semisimplicity over the finite separable subextension (finite atom)
  haveI : IsSemisimpleRepresentation (scalarExtension (k := K0) S) :=
    isSemisimpleRepresentation_scalarExtension_of_isSemisimple_finite S
  exact descent_step S N hN gens hgens eb hmem

/-- **Infinite-extension reduction (separability-free residual).**  Reducing the semisimplicity of
`scalarExtension (k := K) S` for a possibly *infinite* separable extension `K / k` to the **finite**
case (already proved in `SeparableAveraging.lean`,
`Representation.isSemisimpleRepresentation_scalarExtension_of_isSemisimple_finite`).

A `K[G]`-submodule of the finite-dimensional `S ⊗_k K` is finite-dimensional over `K`, hence
generated by finitely many tensors involving finitely many `k`-coefficients of `K`, so it is
defined over a finite subextension `K₀` (finite, and separable as a subextension of a separable
extension); splitting it there via the finite atom and base-changing the splitting back up to `K`
yields a complement.  This step uses **no** separability input beyond the finite case — it is a
pure descent-to-finite-subextension argument.

This theorem performs all of the lattice-theoretic packaging: it converts the existence of a
`G`-equivariant `K`-linear projection onto each subrepresentation
(`exists_Gequivariant_projection_of_separable_descent`, the single remaining residual) into a
complement via `LinearMap.isCompl_of_proj`, the kernel being a `G`-stable complementary
subrepresentation.  Hence the *only* remaining gap is the descent residual above. -/
theorem isSemisimpleRepresentation_scalarExtension_of_isSemisimple_infinite
    [Algebra.IsSeparable k K]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : Representation k G V) [IsSemisimpleRepresentation S] :
    IsSemisimpleRepresentation (Representation.scalarExtension (k := K) S) := by
  classical
  -- `IsSemisimpleRepresentation` unfolds to `ComplementedLattice (Subrepresentation _)`: produce a
  -- complement for every subrepresentation `W`.
  refine ⟨fun W => ?_⟩
  -- the descent residual: a `G`-equivariant `K`-linear projection onto `W.toSubmodule`
  obtain ⟨π, hπN, hπid, hπequiv⟩ :=
    exists_Gequivariant_projection_of_separable_descent S W.toSubmodule
      (fun g m hm => W.apply_mem_toSubmodule g hm)
  -- corestrict `π` to `W.toSubmodule`, which is the identity there, so its kernel is a complement
  let πN : (K ⊗[k] V) →ₗ[K] W.toSubmodule :=
    { toFun := fun m => ⟨π m, hπN m⟩
      map_add' := fun x y => by ext; simp [map_add]
      map_smul' := fun c x => by ext; simp [map_smul] }
  have hπN_id : ∀ x : W.toSubmodule, πN x = x := fun x => Subtype.ext (hπid x.1 x.2)
  have hcompl := LinearMap.isCompl_of_proj (p := W.toSubmodule) (f := πN) hπN_id
  -- identify `ker πN` with `ker π`
  have hkereq : LinearMap.ker πN = LinearMap.ker π := by
    ext m
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      have h' : πN m = (0 : W.toSubmodule) := h
      have := congrArg Subtype.val h'
      simpa [πN] using this
    · intro h; apply Subtype.ext; simpa [πN] using h
  rw [hkereq] at hcompl
  -- `ker π` is `G`-stable by equivariance of `π`, hence a subrepresentation
  let τ : Subrepresentation (Representation.scalarExtension (k := K) S) :=
    { toSubmodule := LinearMap.ker π
      apply_mem_toSubmodule := fun g m hm => by
        rw [LinearMap.mem_ker] at hm ⊢
        rw [hπequiv g m, hm, map_zero] }
  refine ⟨τ, ?_⟩
  -- transport `IsCompl` from the submodule lattice to the subrepresentation lattice
  rw [isCompl_iff] at hcompl ⊢
  obtain ⟨hd, hc⟩ := hcompl
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff] at hd ⊢
    apply Subrepresentation.toSubmodule_injective
    simpa using hd
  · rw [codisjoint_iff] at hc ⊢
    apply Subrepresentation.toSubmodule_injective
    simpa using hc

theorem isSemisimpleRepresentation_scalarExtension_of_isIrreducible_separable
    [Algebra.IsSeparable k K]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : Representation k G V) [Representation.IsIrreducible S] :
    IsSemisimpleRepresentation (Representation.scalarExtension (k := K) S) := by
  haveI : IsSemisimpleRepresentation S := inferInstance
  by_cases hfin : FiniteDimensional k K
  · -- finite separable case: proved by separable Maschke averaging
    exact Representation.isSemisimpleRepresentation_scalarExtension_of_isSemisimple_finite S
  · -- general separable case: reduce to a finite separable subextension.
    -- This is a base-change/descent step with no separability content beyond the finite case.
    exact isSemisimpleRepresentation_scalarExtension_of_isSemisimple_infinite (K := K) S

end Atom

/-! ## Identifying a subrepresentation module with its `asSubmodule` -/

section AsSubmodule

variable {k : Type u} [Field k] {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

set_option backward.isDefEq.respectTransparency false in
/-- The `k[G]`-linear equivalence between the module of the subrepresentation
`σ.toRepresentation` and the `k[G]`-submodule `σ.asSubmodule` of `ρ.asModule`. Both are carried
by `σ.toSubmodule`, with the same (restricted) `k[G]`-action. -/
def asModuleEquivAsSubmodule (σ : Subrepresentation ρ) :
    σ.toRepresentation.asModule ≃ₗ[k[G]] (σ.asSubmodule) where
  toFun x := ⟨(x : σ.toSubmodule).1, by
    rw [Subrepresentation.mem_asSubmodule_iff]; exact (x : σ.toSubmodule).2⟩
  invFun y := (⟨y.1, by have := y.2; rwa [Subrepresentation.mem_asSubmodule_iff] at this⟩ :
    σ.toSubmodule)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul]
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [add_smul, add_smul, AddSubmonoid.coe_add, ha, hb]
    | single g a =>
        rw [Representation.single_smul, Representation.single_smul, SetLike.val_smul]
        rfl

/-- A semisimple subrepresentation gives a semisimple `asSubmodule`. -/
theorem isSemisimpleModule_asSubmodule_of_isSemisimpleRepresentation (σ : Subrepresentation ρ)
    (h : IsSemisimpleRepresentation σ.toRepresentation) :
    IsSemisimpleModule k[G] (σ.asSubmodule) := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at h
  letI iM : Module k[G] σ.toRepresentation.asModule := inferInstance
  letI iN : Module k[G] (σ.asSubmodule) := inferInstance
  letI iAM : AddCommGroup σ.toRepresentation.asModule := inferInstance
  letI iAN : AddCommGroup (σ.asSubmodule) := inferInstance
  exact @IsSemisimpleModule.congr k[G] _ σ.toRepresentation.asModule iAM iM
    (σ.asSubmodule) iAN iN h (asModuleEquivAsSubmodule ρ σ).symm

set_option backward.isDefEq.respectTransparency false in
/-- The subrepresentation `ofSubmodule' N` attached to a simple `k[G]`-submodule `N` is
irreducible. -/
theorem irreducible_ofSubmodule' (N : Submodule k[G] ρ.asModule) (hN : IsSimpleModule k[G] N) :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' N).toRepresentation := by
  rw [irreducible_iff_isSimpleModule_asModule]
  letI iM : Module k[G] (Subrepresentation.ofSubmodule' N).toRepresentation.asModule :=
    inferInstance
  letI iN : Module k[G] N := inferInstance
  letI iAM : AddCommGroup (Subrepresentation.ofSubmodule' N).toRepresentation.asModule :=
    inferInstance
  letI iAN : AddCommGroup N := inferInstance
  exact @IsSimpleModule.congr k[G] _
    (Subrepresentation.ofSubmodule' N).toRepresentation.asModule iAM iM N iAN iN
    (asModuleEquivAsSubmodule ρ (Subrepresentation.ofSubmodule' N)) hN

set_option backward.isDefEq.respectTransparency false in
/-- **The irreducible subrepresentations of a semisimple representation span it.** -/
theorem iSup_irreducible_toSubmodule_eq_top [IsSemisimpleRepresentation ρ] :
    (⨆ i : { σ : Subrepresentation ρ // Representation.IsIrreducible σ.toRepresentation },
       i.1.toSubmodule) = ⊤ := by
  have hmod := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  have hsup := IsSemisimpleModule.sSup_simples_eq_top k[G] ρ.asModule
  rw [sSup_eq_iSup'] at hsup
  rw [eq_top_iff]
  intro x hxt
  clear hxt
  have hx : x ∈ ⨆ a : { m : Submodule k[G] ρ.asModule // IsSimpleModule k[G] m },
      (a : Submodule k[G] ρ.asModule) := hsup.ge Submodule.mem_top
  clear hmod hsup
  induction hx using Submodule.iSup_induction' with
  | mem N y hy =>
      exact Submodule.mem_iSup_of_mem
        ⟨Subrepresentation.ofSubmodule' N.1, irreducible_ofSubmodule' ρ N.1 N.2⟩
        (by simpa using hy)
  | zero => exact Submodule.zero_mem _
  | add a b _ _ iha ihb => exact Submodule.add_mem _ iha ihb

end AsSubmodule

/-! ## Main theorem: separable base change preserves semisimplicity -/

section Main

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
variable {G : Type u} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- **Separable base change preserves semisimplicity.** A semisimple `k[G]`-representation, scalar-
extended along a separable field extension `K / k`, is again semisimple over `K[G]`.

The proof writes the ambient module as the (`K[G]`-submodule) sum of the base changes of the simple
subrepresentations of `ρ`; each summand is semisimple by the simple atom together with the
base-change equivalence `baseChangeSubrepEquiv`, and they span because the simple
subrepresentations already span `ρ` and `K ⊗_k (-)` preserves spanning (`baseChange_iSup_le`,
`Submodule.baseChange_top`). -/
theorem isSemisimpleRepresentation_scalarExtension_of_isSeparable
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [hρ : IsSemisimpleRepresentation ρ] :
    IsSemisimpleRepresentation (Representation.scalarExtension (k := K) ρ) := by
  classical
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  -- index by irreducible subrepresentations of `ρ`
  set Idx := { σ : Subrepresentation ρ // Representation.IsIrreducible σ.toRepresentation }
    with hIdx
  -- the base-changed `K[G]`-submodule of `(scalarExtension ρ).asModule`
  let p : Idx → Submodule K[G] (Representation.scalarExtension (k := K) ρ).asModule :=
    fun i => (baseChangeSubrep (K := K) ρ i.1).asSubmodule
  letI iM : Module K[G] (Representation.scalarExtension (k := K) ρ).asModule := inferInstance
  letI iAM : AddCommGroup (Representation.scalarExtension (k := K) ρ).asModule := inferInstance
  refine @isSemisimpleModule_of_isSemisimpleModule_submodule' Idx K[G] _
    (Representation.scalarExtension (k := K) ρ).asModule iAM iM p (fun i => ?_) ?_
  · -- each summand is semisimple
    have hss : IsSemisimpleRepresentation
        (Representation.scalarExtension (k := K) i.1.toRepresentation) := by
      haveI := i.2
      exact isSemisimpleRepresentation_scalarExtension_of_isIrreducible_separable
        (K := K) i.1.toRepresentation
    have hssub : IsSemisimpleRepresentation (baseChangeSubrep (K := K) ρ i.1).toRepresentation :=
      isSemisimpleRepresentation_of_equiv (baseChangeSubrepEquiv (K := K) ρ i.1) hss
    exact isSemisimpleModule_asSubmodule_of_isSemisimpleRepresentation
      (Representation.scalarExtension (k := K) ρ) (baseChangeSubrep (K := K) ρ i.1) hssub
  · -- the summands span: the irreducible subrepresentations of `ρ` span `ρ`, and base change
    -- preserves spanning, so the base-changed irreducible subreps span `scalarExtension ρ`
    letI iM' : Module K[G] (Representation.scalarExtension (k := K) ρ).asModule := inferInstance
    -- every `1 ⊗ y` lies in the sum `⨆ p i`
    have hmem : ∀ y : V, ((1 : K) ⊗ₜ[k] y :
        (Representation.scalarExtension (k := K) ρ).asModule) ∈ ⨆ i, p i := by
      intro y
      have hk : y ∈ (⨆ i : Idx, i.1.toSubmodule) := by
        rw [iSup_irreducible_toSubmodule_eq_top ρ]; exact Submodule.mem_top
      induction hk using Submodule.iSup_induction' with
      | mem i z hz =>
          refine @Submodule.mem_iSup_of_mem K[G]
            (Representation.scalarExtension (k := K) ρ).asModule _ _ iM' _ _ p i ?_
          rw [Subrepresentation.mem_asSubmodule_iff]
          exact Submodule.tmul_mem_baseChange_of_mem 1 hz
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add a b _ _ iha ihb => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ iha ihb
    set P := ⨆ i, p i with hP
    -- `P` is `K`-stable and `K ⊗ V` is `K`-spanned by `1 ⊗ V`, so `P = ⊤`
    rw [eq_top_iff]
    intro z hzt
    clear hzt
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul a v =>
        have h1 : (a ⊗ₜ[k] v : (Representation.scalarExtension (k := K) ρ).asModule)
            = a • ((1 : K) ⊗ₜ[k] v :
              (Representation.scalarExtension (k := K) ρ).asModule) := by
          change a ⊗ₜ[k] v = a • ((1 : K) ⊗ₜ[k] v : K ⊗[k] V)
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h1]
        exact Submodule.smul_of_tower_mem P a (hmem v)
    | add a b ha hb => exact Submodule.add_mem _ ha hb

end Main

/-! ## Specialization to the algebraic closure of a perfect field -/

section PerfectField

variable {k : Type u} [Field k] [PerfectField k]
variable {G : Type u} [Group G] [Finite G]

/-- **Separable base change to the algebraic closure of a perfect field.** For a perfect base field
`k`, a semisimple `k[G]`-representation stays semisimple after scalar extension to the algebraic
closure `AlgebraicClosure k`. The extension `AlgebraicClosure k / k` is algebraic and `k` is
perfect, hence the extension is separable (`Algebra.IsAlgebraic.isSeparable_of_perfectField`), so
the general theorem applies.

In particular a *simple* `k[G]`-representation `S` (being semisimple) yields the hypothesis (A)
`IsSemisimpleRepresentation (scalarExtension (k := AlgebraicClosure k) S.ρ)` needed by
`CharPReduction.isIrreducible_scalarExtension_of_isSemisimple_of_finrank_intertwiningMap_eq_one`. -/
theorem isSemisimpleRepresentation_scalarExtension_algebraicClosure_of_perfectField
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [IsSemisimpleRepresentation ρ] :
    IsSemisimpleRepresentation
      (Representation.scalarExtension (k := AlgebraicClosure k) ρ) :=
  isSemisimpleRepresentation_scalarExtension_of_isSeparable ρ

end PerfectField

end Representation

import Mathlib
import LinearRepresentations_Serre_1977.Serre.RepresentationTheory.RealizableOver

/-!
# Separable Maschke averaging (finite separable case)

This module proves the genuine separability input behind
`SeparableSemisimple.isSemisimpleRepresentation_scalarExtension_of_isIrreducible_separable`,
for a **finite** separable field extension `K / k`:

> A semisimple `k[G]`-representation `S`, scalar-extended along a finite separable extension
> `K / k`, stays semisimple over `K[G]`.

The proof is **Maschke's averaging argument carried out over the separable extension `K / k`**
(instead of over the finite group `G`, which fails in characteristic `p`).  The averaging weight is
the *trace-dual Casimir element* `∑ᵢ bᵢ ⊗ b'ᵢ ∈ K ⊗_k K`, where `b` is a `k`-basis of `K` and `b'`
its dual basis for the (nondegenerate, by separability) trace form.  Its two defining properties are
proved here unconditionally for finite separable `K / k`:

* **centrality** `∑ᵢ (c·bᵢ) ⊗ b'ᵢ = ∑ᵢ bᵢ ⊗ (b'ᵢ·c)` (`sum_smul_traceDual_casimir_central`), and
* **normalisation** `∑ᵢ bᵢ·b'ᵢ = 1` (`sum_mul_traceDual_eq_one`).

Together with a `G`-equivariant `k`-linear projection (available because the base-restricted
representation `baseRestrict S` is semisimple, `isSemisimpleRepresentation_baseRestrict`), the
averaged operator is a `G`-equivariant `K`-linear projection onto any subrepresentation, which
exhibits a complement and hence semisimplicity.
-/

noncomputable section

universe u

open scoped TensorProduct MonoidAlgebra
open Algebra

namespace Representation

/-! ## The trace-dual Casimir element of a finite separable extension -/

section Casimir

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
variable [FiniteDimensional k K] [Algebra.IsSeparable k K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k K)

/-- Coordinate expansion in the basis `b` via the trace form:
`b.repr x i = Tr_{K/k}(x · (b.traceDual i))`. -/
theorem repr_eq_trace_mul_traceDual (x : K) (i : ι) :
    b.repr x i = Algebra.trace k K (x * b.traceDual i) := by
  have hbb : b = b.traceDual.traceDual := (Module.Basis.traceDual_traceDual b).symm
  rw [hbb, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
    Module.Basis.traceDual_traceDual]

/-- **Centrality of the trace-dual Casimir element.**  For every `c : K`,
`∑ᵢ (c·bᵢ) ⊗ b'ᵢ = ∑ᵢ bᵢ ⊗ (b'ᵢ·c)` in `K ⊗_k K`. -/
theorem sum_smul_traceDual_casimir_central (c : K) :
    ∑ i, (c * b i) ⊗ₜ[k] (b.traceDual i) = ∑ i, (b i) ⊗ₜ[k] (b.traceDual i * c) := by
  classical
  set b' := b.traceDual with hb'
  have hexp_b : ∀ x : K, x = ∑ j, (Algebra.trace k K (x * b' j)) • b j := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [repr_eq_trace_mul_traceDual b x j]
  have hrepr_b' : ∀ (x : K) (j : ι), b'.repr x j = Algebra.trace k K (x * b j) := by
    intro x j
    rw [hb', Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
  have hexp_b' : ∀ x : K, x = ∑ j, (Algebra.trace k K (x * b j)) • b' j := by
    intro x
    conv_lhs => rw [← b'.sum_repr x]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hrepr_b']
  have hL : ∑ i, (c * b i) ⊗ₜ[k] (b' i)
      = ∑ i, ∑ j, (Algebra.trace k K (c * b i * b' j)) • (b j ⊗ₜ[k] b' i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    conv_lhs => rw [hexp_b (c * b i)]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [TensorProduct.smul_tmul']
  have hR : ∑ i, (b i) ⊗ₜ[k] (b' i * c)
      = ∑ i, ∑ j, (Algebra.trace k K (b' i * c * b j)) • (b i ⊗ₜ[k] b' j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    conv_lhs => rw [hexp_b' (b' i * c)]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [TensorProduct.tmul_smul]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  congr 2
  ring

/-- **Normalisation of the trace-dual Casimir element.**  `∑ᵢ bᵢ · b'ᵢ = 1`. -/
theorem sum_mul_traceDual_eq_one : ∑ i, b i * b.traceDual i = 1 := by
  classical
  set b' := b.traceDual with hb'
  have hrepr_b : ∀ (x : K) (j : ι), b.repr x j = Algebra.trace k K (x * b' j) :=
    repr_eq_trace_mul_traceDual b
  have hnd := traceForm_nondegenerate k K
  rw [← sub_eq_zero]
  refine hnd.1 _ (fun y => ?_)
  rw [Algebra.traceForm_apply, sub_mul, map_sub, one_mul, Finset.sum_mul, map_sum, sub_eq_zero]
  have hstep : ∀ i, Algebra.trace k K (b i * b' i * y) = b.repr (y * b i) i := by
    intro i; rw [hrepr_b (y * b i) i]; ring_nf
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [Algebra.trace_eq_matrix_trace b y, Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']

end Casimir

/-! ## The base-restricted representation and its semisimplicity -/

section BaseRestrict

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
variable {G : Type u} [Group G]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The `k`-representation underlying `scalarExtension S` (restricting scalars `K → k`). Its
underlying space is `K ⊗_k V` with `g` acting by `id_K ⊗ S g`. -/
def baseRestrict (S : Representation k G V) : Representation k G (K ⊗[k] V) where
  toFun g := ((scalarExtension (k := K) S) g).restrictScalars k
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [Module.End.mul_apply]

@[simp] theorem baseRestrict_apply (S : Representation k G V) (g : G) (x : K ⊗[k] V) :
    (baseRestrict (K := K) S) g x = (scalarExtension (k := K) S) g x := rfl

/-- The `k[G]`-action on `(baseRestrict S).asModule` is `id_K ⊗ (k[G]-action on S.asModule)` on the
`single g t` generators. -/
theorem baseRestrict_single_smul_tmul (S : Representation k G V) (g : G) (t : k) (a : K) (v : V) :
    (MonoidAlgebra.single g t : k[G]) •
        (show (baseRestrict (K := K) S).asModule from a ⊗ₜ[k] v)
      = (show (baseRestrict (K := K) S).asModule from
          a ⊗ₜ[k] (show V from (MonoidAlgebra.single g t : k[G]) • (show S.asModule from v))) := by
  rw [single_smul, single_smul]
  show t • (baseRestrict (K := K) S) g (a ⊗ₜ[k] v) = a ⊗ₜ[k] (t • S g v)
  rw [baseRestrict_apply]
  show t • LinearMap.baseChange K (S g) (a ⊗ₜ[k] v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.tmul_smul]

set_option backward.isDefEq.respectTransparency false in
/-- **Semisimplicity of the base-restricted representation.**  If `S` is a semisimple
`k[G]`-representation and `K` has a `k`-basis indexed by `ι`, then `baseRestrict S` (the
representation of `G` on `K ⊗_k V` over `k`) is semisimple: as a `k[G]`-module it is the direct
sum, over `ι`, of copies of `S.asModule`. -/
theorem isSemisimpleRepresentation_baseRestrict
    (S : Representation k G V) [IsSemisimpleRepresentation S]
    {ι : Type*} (b : Module.Basis ι k K) :
    IsSemisimpleRepresentation (baseRestrict (K := K) S) := by
  classical
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  haveI hssS := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule S).mp ‹_›
  haveI hssfs : IsSemisimpleModule k[G] (ι →₀ S.asModule) := inferInstance
  -- the k-linear equiv K ⊗ V ≅ (ι →₀ V)
  let e0 : K ⊗[k] V ≃ₗ[k] (ι →₀ k) ⊗[k] V :=
    TensorProduct.congr b.repr (LinearEquiv.refl k V)
  let e1 : (ι →₀ k) ⊗[k] V ≃ₗ[k] (ι →₀ V) := TensorProduct.finsuppScalarLeft k V ι
  let e : (baseRestrict (K := K) S).asModule ≃ₗ[k] (ι →₀ S.asModule) := e0.trans e1
  have he_tmul : ∀ (a : K) (v : V) (i : ι),
      (e (a ⊗ₜ[k] v)) i = b.repr a i • v := by
    intro a v i
    show e1 (b.repr a ⊗ₜ[k] v) i = _
    rw [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  -- e is k[G]-linear on single generators: both sides are k-linear in x, agree on pure tensors
  have hgen : ∀ (g : G) (t : k) (x : (baseRestrict (K := K) S).asModule),
      e ((MonoidAlgebra.single g t : k[G]) • x)
        = (MonoidAlgebra.single g t : k[G]) • e x := by
    intro g t
    let L : (baseRestrict (K := K) S).asModule →ₗ[k] (ι →₀ S.asModule) :=
      (e.toLinearMap).comp (DistribSMul.toLinearMap k _ (MonoidAlgebra.single g t : k[G]))
    let R : (baseRestrict (K := K) S).asModule →ₗ[k] (ι →₀ S.asModule) :=
      (DistribSMul.toLinearMap k _ (MonoidAlgebra.single g t : k[G])).comp e.toLinearMap
    suffices h : L = R by intro x; exact LinearMap.congr_fun h x
    refine TensorProduct.ext' ?_
    intro a v
    show e ((MonoidAlgebra.single g t : k[G]) •
        (show (baseRestrict (K := K) S).asModule from a ⊗ₜ[k] v))
      = (MonoidAlgebra.single g t : k[G]) •
          e (show (baseRestrict (K := K) S).asModule from a ⊗ₜ[k] v)
    apply Finsupp.ext; intro i
    rw [baseRestrict_single_smul_tmul S g t a v, he_tmul, Finsupp.smul_apply, he_tmul]
    exact (smul_comm _ _ _)
  -- assemble the k[G]-linear equiv
  let E : (baseRestrict (K := K) S).asModule ≃ₗ[k[G]] (ι →₀ S.asModule) :=
    { e with
      map_smul' := by
        intro r x
        show e (r • x) = r • e x
        induction r using MonoidAlgebra.induction_linear generalizing x with
        | zero => rw [zero_smul, map_zero, zero_smul]
        | add r s hr hs => rw [add_smul, add_smul, map_add, hr, hs]
        | single g t => exact hgen g t x }
  exact IsSemisimpleModule.congr E

end BaseRestrict

/-! ## The averaged projection and the finite separable atom -/

section Averaging

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
variable [FiniteDimensional k K] [Algebra.IsSeparable k K]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

variable (S : Representation k G V)

/-- The `K`-action on `K ⊗_k V = (scalarExtension S).asModule` commutes with the `G`-action: scalar
multiplication by `c : K` is `G`-equivariant for `scalarExtension S`. -/
theorem scalarExtension_smul_comm (g : G) (c : K) (m : K ⊗[k] V) :
    (scalarExtension (k := K) S) g (c • m) = c • (scalarExtension (k := K) S) g m := by
  exact map_smul ((scalarExtension (k := K) S) g) c m

/-- Given a `G`-equivariant `k`-linear projection `p` onto a `K`-stable, `G`-stable subspace `N` of
`K ⊗_k V`, the trace-dual average is a `K`-linear `G`-equivariant projection onto `N`.

We package the conclusion as: `N` has a complement among the subrepresentations of
`scalarExtension S`. -/
theorem isCompl_of_kProj
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k K)
    (N : Submodule K (K ⊗[k] V))
    (p : (K ⊗[k] V) →ₗ[k] (K ⊗[k] V))
    (hpN : ∀ m, p m ∈ N)
    (hpid : ∀ m ∈ N, p m = m)
    (hpequiv : ∀ (g : G) (m : K ⊗[k] V),
      p ((scalarExtension (k := K) S) g m) = (scalarExtension (k := K) S) g (p m)) :
    ∃ q : Submodule K (K ⊗[k] V),
      (∀ g, ∀ m ∈ q, (scalarExtension (k := K) S) g m ∈ q) ∧ IsCompl N q := by
  classical
  set b' := b.traceDual with hb'
  -- the averaged k-linear endomorphism
  let avgₖ : (K ⊗[k] V) →ₗ[k] (K ⊗[k] V) :=
    ∑ i, (DistribSMul.toLinearMap k _ (b i)).comp
      (p.comp (DistribSMul.toLinearMap k _ (b' i)))
  have havg_apply : ∀ m, avgₖ m = ∑ i, (b i) • p ((b' i) • m) := by
    intro m
    simp only [avgₖ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      DistribSMul.toLinearMap_apply]
  -- K-linearity of avgₖ, via centrality of the trace-dual Casimir
  have havg_Ksmul : ∀ (c : K) (m : K ⊗[k] V), avgₖ (c • m) = c • avgₖ m := by
    intro c m
    -- the k-bilinear evaluation K ⊗_k K → (K⊗V), x ⊗ y ↦ x • p (y • m)
    let Φ : K ⊗[k] K →ₗ[k] (K ⊗[k] V) :=
      TensorProduct.lift
        { toFun := fun x =>
            { toFun := fun y => x • p (y • m)
              map_add' := fun y₁ y₂ => by rw [add_smul, map_add, smul_add]
              map_smul' := fun a y => by
                simp only [RingHom.id_apply]
                rw [smul_assoc, map_smul, smul_comm x a] }
          map_add' := fun x₁ x₂ => by ext y; simp [add_smul]
          map_smul' := fun a x => by ext y; simp [smul_assoc] }
    have hΦ_tmul : ∀ (x y : K), Φ (x ⊗ₜ[k] y) = x • p (y • m) := fun x y => rfl
    have hkey := sum_smul_traceDual_casimir_central b c
    have := congrArg Φ hkey
    rw [map_sum, map_sum] at this
    simp only [hΦ_tmul] at this
    rw [havg_apply, havg_apply]
    -- LHS: avgₖ (c•m) = Σ b_i • p (b'_i • c • m) = Σ b_i • p ((b'_i c) • m)
    -- RHS: c • avgₖ m = Σ (c b_i) • p (b'_i • m)
    calc ∑ i, (b i) • p ((b' i) • c • m)
        = ∑ i, (b i) • p ((b' i * c) • m) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [smul_smul]
      _ = ∑ i, (c * b i) • p ((b' i) • m) := this.symm
      _ = c • ∑ i, (b i) • p ((b' i) • m) := by
          rw [Finset.smul_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); rw [smul_smul]
  -- avgₖ lands in N
  have havg_memN : ∀ m, avgₖ m ∈ N := by
    intro m
    rw [havg_apply]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    exact N.smul_mem _ (hpN _)
  -- avgₖ is the identity on N (uses ∑ b_i b'_i = 1)
  have havg_idN : ∀ m ∈ N, avgₖ m = m := by
    intro m hm
    rw [havg_apply]
    have hstep : ∀ i ∈ Finset.univ, (b i) • p ((b' i) • m) = (b i) • ((b' i) • m) := by
      intro i _
      rw [hpid ((b' i) • m) (N.smul_mem _ hm)]
    rw [Finset.sum_congr rfl hstep]
    have : ∑ i, (b i) • ((b' i) • m) = (∑ i, b i * b' i) • m := by
      rw [Finset.sum_smul]; refine Finset.sum_congr rfl (fun i _ => ?_); rw [smul_smul]
    rw [this, sum_mul_traceDual_eq_one b, one_smul]
  -- avgₖ is G-equivariant
  have havg_equiv : ∀ (g : G) (m : K ⊗[k] V),
      avgₖ ((scalarExtension (k := K) S) g m) = (scalarExtension (k := K) S) g (avgₖ m) := by
    intro g m
    rw [havg_apply, havg_apply, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← scalarExtension_smul_comm S g (b' i), hpequiv g, scalarExtension_smul_comm S g (b i)]
  -- upgrade avgₖ to a K-linear idempotent endomorphism
  let avg : (K ⊗[k] V) →ₗ[K] (K ⊗[k] V) :=
    { toFun := avgₖ
      map_add' := avgₖ.map_add
      map_smul' := fun c m => by simp only [RingHom.id_apply]; exact havg_Ksmul c m }
  have havg_avg : ∀ m, avg m = avgₖ m := fun m => rfl
  -- the complement is the kernel of avg (a K-submodule, G-stable)
  refine ⟨LinearMap.ker avg, ?_, ?_⟩
  · -- ker avg is G-stable
    intro g m hm
    rw [LinearMap.mem_ker] at hm ⊢
    rw [havg_avg, havg_equiv, ← havg_avg, hm, map_zero]
  · -- IsCompl N (ker avg): avg is a projection onto N
    have hproj : ∀ x : N, avg x = x := fun x => havg_idN x.1 x.2
    have hrange : ∀ m, avg m ∈ N := havg_memN
    -- N = range of avg restricted; use isCompl_of_proj on the corestriction
    let avgN : (K ⊗[k] V) →ₗ[K] N :=
      { toFun := fun m => ⟨avg m, hrange m⟩
        map_add' := fun x y => by ext; simp [map_add]
        map_smul' := fun c x => by ext; simp [map_smul] }
    have havgN_id : ∀ x : N, avgN x = x := by
      intro x; apply Subtype.ext; exact hproj x
    have hcompl := LinearMap.isCompl_of_proj (p := N) (f := avgN) havgN_id
    -- ker avgN = ker avg
    have hkereq : LinearMap.ker avgN = LinearMap.ker avg := by
      ext m
      simp only [LinearMap.mem_ker]
      constructor
      · intro h
        have h' : avgN m = (0 : N) := h
        have := congrArg (Subtype.val) h'
        simpa [avgN] using this
      · intro h; apply Subtype.ext; simpa [avgN] using h
    rwa [hkereq] at hcompl

/-- A `k`-linear `G`-equivariant projection onto a `G`-stable `K`-submodule `N`, produced from the
semisimplicity of `baseRestrict S`: `N.restrictScalars k` is a subrepresentation of
`baseRestrict S`,
hence has a complementary subrepresentation, and the associated linear projection is `k`-linear and
`G`-equivariant. -/
theorem exists_kProj_of_isSemisimple [IsSemisimpleRepresentation S]
    {ι : Type*} (b : Module.Basis ι k K)
    (N : Submodule K (K ⊗[k] V))
    (hN : ∀ (g : G) ⦃m⦄, m ∈ N → (scalarExtension (k := K) S) g m ∈ N) :
    ∃ p : (K ⊗[k] V) →ₗ[k] (K ⊗[k] V),
      (∀ m, p m ∈ N) ∧ (∀ m ∈ N, p m = m) ∧
      (∀ (g : G) (m : K ⊗[k] V),
        p ((scalarExtension (k := K) S) g m) = (scalarExtension (k := K) S) g (p m)) := by
  classical
  haveI := isSemisimpleRepresentation_baseRestrict (K := K) S b
  -- N as a subrepresentation of baseRestrict S
  let Nσ : Subrepresentation (baseRestrict (K := K) S) :=
    { toSubmodule := N.restrictScalars k
      apply_mem_toSubmodule := fun g m hm => hN g hm }
  -- complement subrepresentation
  obtain ⟨τ, hτ⟩ := exists_isCompl Nσ
  have hcompl : IsCompl (N.restrictScalars k) τ.toSubmodule := by
    have h1 : Disjoint (N.restrictScalars k) τ.toSubmodule := by
      have := hτ.1
      rw [disjoint_iff] at this ⊢
      have h2 := congrArg Subrepresentation.toSubmodule this
      simpa [Nσ] using h2
    have h2 : Codisjoint (N.restrictScalars k) τ.toSubmodule := by
      have := hτ.2
      rw [codisjoint_iff] at this ⊢
      have h2 := congrArg Subrepresentation.toSubmodule this
      simpa [Nσ] using h2
    exact ⟨h1, h2⟩
  set p : (K ⊗[k] V) →ₗ[k] (K ⊗[k] V) :=
    (N.restrictScalars k).subtype.comp
      ((N.restrictScalars k).linearProjOfIsCompl τ.toSubmodule hcompl) with hp
  have hpmem : ∀ m, p m ∈ N := by
    intro m
    have : p m ∈ N.restrictScalars k :=
      ((N.restrictScalars k).linearProjOfIsCompl τ.toSubmodule hcompl m).2
    rwa [Submodule.restrictScalars_mem] at this
  have hpid : ∀ m ∈ N, p m = m := by
    intro m hm
    have hm' : m ∈ N.restrictScalars k := by rwa [Submodule.restrictScalars_mem]
    rw [hp]
    change ((N.restrictScalars k).linearProjOfIsCompl τ.toSubmodule hcompl m : K ⊗[k] V) = m
    rw [Submodule.linearProjOfIsCompl_apply_left hcompl ⟨m, hm'⟩]
  refine ⟨p, hpmem, hpid, ?_⟩
  -- G-equivariance
  intro g m
  -- decompose m = s + t with s ∈ N, t ∈ τ; p maps via this decomposition
  have hmem : m ∈ N.restrictScalars k ⊔ τ.toSubmodule :=
    hcompl.codisjoint.eq_top ▸ Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hmem
  -- p m = s
  have hps : p m = s := by
    rw [hp]
    change ((N.restrictScalars k).linearProjOfIsCompl τ.toSubmodule hcompl m : K ⊗[k] V) = s
    rw [← hst, map_add, Submodule.linearProjOfIsCompl_apply_left hcompl ⟨s, hs⟩,
      Submodule.linearProjOfIsCompl_apply_right hcompl ⟨t, ht⟩, add_zero]
  -- scalarExtension g m = (scalarExtension g s) + (scalarExtension g t), with the summands in N, τ
  have hsN : (scalarExtension (k := K) S) g s ∈ N :=
    hN g (by rwa [Submodule.restrictScalars_mem] at hs)
  have htτ : (scalarExtension (k := K) S) g t ∈ τ.toSubmodule :=
    τ.apply_mem_toSubmodule g ht
  have hpgm : p ((scalarExtension (k := K) S) g m) = (scalarExtension (k := K) S) g s := by
    have hsplit : (scalarExtension (k := K) S) g m
        = (scalarExtension (k := K) S) g s + (scalarExtension (k := K) S) g t := by
      rw [← hst, map_add]
    rw [hsplit, hp]
    change ((N.restrictScalars k).linearProjOfIsCompl τ.toSubmodule hcompl
        ((scalarExtension (k := K) S) g s + (scalarExtension (k := K) S) g t) : K ⊗[k] V)
      = (scalarExtension (k := K) S) g s
    rw [map_add,
      Submodule.linearProjOfIsCompl_apply_left hcompl
        ⟨_, by rwa [Submodule.restrictScalars_mem]⟩,
      Submodule.linearProjOfIsCompl_apply_right hcompl ⟨_, htτ⟩, add_zero]
  rw [hpgm, hps]

/-- **Finite separable atom.** A semisimple `k[G]`-representation, scalar-extended along a *finite*
separable field extension `K / k`, stays semisimple over `K[G]`.

This is Maschke's averaging argument carried out over the separable extension `K / k`: for each
subrepresentation `σ` we produce a `G`-equivariant `k`-linear projection onto `σ` (using
`exists_kProj_of_isSemisimple`, which rests on the semisimplicity of `baseRestrict S`), then average
it with the trace-dual Casimir weight (`isCompl_of_kProj`) to obtain a `G`-equivariant `K`-linear
projection, hence a complement.  The complemented lattice of subrepresentations is exactly
semisimplicity. -/
theorem isSemisimpleRepresentation_scalarExtension_of_isSemisimple_finite
    [IsSemisimpleRepresentation S] :
    IsSemisimpleRepresentation (scalarExtension (k := K) S) := by
  classical
  -- a finite k-basis of K
  let b : Module.Basis (Fin (Module.finrank k K)) k K := Module.finBasis k K
  -- `IsSemisimpleRepresentation` is `ComplementedLattice (Subrepresentation _)`
  refine ⟨fun σ => ?_⟩
  -- σ.toSubmodule is a G-stable K-submodule of K ⊗ V
  obtain ⟨p, hpN, hpid, hpequiv⟩ :=
    exists_kProj_of_isSemisimple S b σ.toSubmodule
      (fun g m hm => σ.apply_mem_toSubmodule g hm)
  obtain ⟨q, hqG, hcompl⟩ := isCompl_of_kProj S b σ.toSubmodule p hpN hpid hpequiv
  -- package q as a subrepresentation, complementary to σ
  let τ : Subrepresentation (scalarExtension (k := K) S) :=
    { toSubmodule := q
      apply_mem_toSubmodule := fun g m hm => hqG g m hm }
  refine ⟨τ, ?_⟩
  rw [isCompl_iff] at hcompl ⊢
  obtain ⟨hd, hc⟩ := hcompl
  constructor
  · rw [disjoint_iff] at hd ⊢
    apply Subrepresentation.toSubmodule_injective
    simpa using hd
  · rw [codisjoint_iff] at hc ⊢
    apply Subrepresentation.toSubmodule_injective
    simpa using hc

end Averaging

end Representation

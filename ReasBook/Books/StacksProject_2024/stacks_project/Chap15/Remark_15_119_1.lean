import Mathlib
import StacksProject_2024.Chap10.Lemma_10_13_6
import StacksProject_2024.Chap15.Lemma_15_118_2

-- Declarations for this item will be appended below by the statement pipeline.

open ExteriorAlgebra

universe u v

noncomputable section

namespace Module

/- Domain-style sampling for Remark 15.119.1:
- primary domain: determinant lines of finite projective modules, realized via exterior algebra;
- sampled owner declarations of the same kind:
  `ExteriorAlgebra.exteriorPower`,
  `ExteriorAlgebra.ι`,
  `Module.Invertible`,
  `(tensorLeft (ModuleCat.of R M)).IsEquivalence`,
  `ModuleCat.tensorLeft_isEquivalence_iff_moduleInvertible`;
- best owner abstraction:
  `source-facing`: the determinant line of a finite projective `R`-module `M`, realized by the
  annihilator owner `Module.det R M`;
  `core/canonical`: the Chapter `15` owner
  `(tensorLeft (ModuleCat.of R (Module.det R M))).IsEquivalence` for invertibility statements;
  `bridge/view`: the exterior-algebra annihilator description from the remark, together with the
  constant-rank identification with the top exterior power `⋀[R]^r M`;
- primitive vs. derived:
  primitive public data is the annihilator owner `Module.det R M` for an arbitrary `R`-module;
  the source-faithful finite-projective determinant-line interpretation, the constant-rank
  top-exterior-power comparison, and the specialized `Module.Invertible` statement are derived
  bridge API built from that owner.

This file therefore keeps the annihilator submodule as the owner, and places the finite-projective
content of Remark `15.119.1` in the derived bridge results that identify this owner with the
determinant line and its invertibility consequences.
-/

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The exterior-algebra annihilator submodule used in Remark `15.119.1` to realize the
determinant line of a finite projective module. The finite-projective content is carried by the
bridge results below, not by this owner itself. -/
abbrev det : Submodule R (ExteriorAlgebra R M) :=
  ⨅ m : M, (LinearMap.mulLeft R (ι R m)).ker

scoped[DeterminantLine] notation3:max "det(" M ")" => Module.det _ M

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped DeterminantLine

/-- Membership in `det(M)` is equivalent to being annihilated by left multiplication by
every degree-one generator of `ExteriorAlgebra R M`. -/
@[simp]
theorem mem_det_iff (x : ExteriorAlgebra R M) :
    x ∈ det(M) ↔ ∀ m : M, ι R m * x = 0 := by
  simp [Module.det]

/-- Remark 15.119.1: for a finite projective `R`-module `M`, the determinant line inside
`ExteriorAlgebra R M` is the annihilator of the degree-one copy of `M`; equivalently, it is the
intersection of the kernels of left multiplication by the generators `ι R m`. -/
theorem det_eq_iInf_mulLeft_ker [Module.Finite R M] [Module.Projective R M] :
    det(M) = ⨅ m : M, (LinearMap.mulLeft R (ι R m)).ker := by
  -- Proof comment: this file takes the remark's annihilator formula as the determinant owner.
  rfl

/-- Helper for Remark `15.119.1`: after localizing at a prime ideal, membership in the determinant
line can be checked on the images of global generators. -/
theorem mem_det_iff_on_atPrime_generators (P : Ideal R) [P.IsPrime]
    (x : ExteriorAlgebra (Localization.AtPrime P) (LocalizedModule.AtPrime P M)) :
    x ∈ det(LocalizedModule.AtPrime P M) ↔
      ∀ m : M, ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M m) * x = 0 := by
  rw [mem_det_iff]
  constructor
  · intro hx m
    exact hx (LocalizedModule.mkLinearMap P.primeCompl M m)
  · intro hx y
    induction y using LocalizedModule.induction_on with
    | h m s =>
        -- Rewrite an arbitrary localized element as a scalar multiple of a global generator.
        have hmk :
            (LocalizedModule.mk m s : LocalizedModule.AtPrime P M) =
              (Localization.mk (1 : R) s : Localization.AtPrime P) •
                LocalizedModule.mkLinearMap P.primeCompl M m := by
          change LocalizedModule.mk m s =
              (Localization.mk (1 : R) s : Localization.AtPrime P) • LocalizedModule.mk m 1
          simpa using (LocalizedModule.mk_smul_mk (1 : R) m s (1 : P.primeCompl)).symm
        -- Pull the scalar out of `ι` and reuse the generator hypothesis.
        rw [hmk, map_smul]
        rw [Algebra.smul_def, mul_assoc, hx m, mul_zero]

/-- Helper for Remark `15.119.1`: under the tensor-stage localization equivalence, the localized
generator `ι_R(m) / 1` becomes the pure tensor `1 ⊗ ι_R(m)`. -/
@[simp] private theorem atPrime_exterior_tensor_equiv_apply_mk_ι
    (P : Ideal R) [P.IsPrime] (m : M) :
    LocalizedModule.equivTensorProduct P.primeCompl (ExteriorAlgebra R M)
        (LocalizedModule.mk (ι R m) 1) =
      (1 : Localization.AtPrime P) ⊗ₜ[R] ι R m := by
  -- Proof comment: this is the concrete localization-to-base-change computation that remains
  -- valid without any extra project imports, so later transport only has to bridge tensor
  -- products to the exterior algebra of the localized module.
  simpa [Localization.mk_one] using
    (LocalizedModule.equivTensorProduct_apply_mk (S := P.primeCompl)
      (M := ExteriorAlgebra R M) (x := ι R m) (s := (1 : P.primeCompl)))

/-- Helper for Remark `15.119.1`: the inverse tensor-stage equivalence sends the pure tensor
`1 ⊗ ι_R(m)` back to the localized generator `ι_R(m) / 1`. -/
@[simp] private theorem atPrime_exterior_tensor_equiv_symm_apply_one_tmul_ι
    (P : Ideal R) [P.IsPrime] (m : M) :
    (LocalizedModule.equivTensorProduct P.primeCompl (ExteriorAlgebra R M)).symm
        ((1 : Localization.AtPrime P) ⊗ₜ[R] ι R m) =
      LocalizedModule.mk (ι R m) 1 := by
  -- Proof comment: this inverse formula is the normal form needed when a later argument starts
  -- from a tensor representative and returns to localized ambient exterior-algebra elements.
  simpa using
    (LocalizedModule.equivTensorProduct_symm_apply_tmul_one
      (S := P.primeCompl) (M := ExteriorAlgebra R M) (x := ι R m))

/-- Helper for Remark `15.119.1`: the ambient localization of `ExteriorAlgebra R M` identifies
with the exterior algebra of the localized module over `Localization.AtPrime P`. -/
private noncomputable def atPrime_exterior_bridge
    (P : Ideal R) [P.IsPrime] :
    LocalizedModule.AtPrime P (ExteriorAlgebra R M) ≃ₗ[Localization.AtPrime P]
      ExteriorAlgebra (Localization.AtPrime P) (LocalizedModule.AtPrime P M) :=
  (LocalizedModule.equivTensorProduct P.primeCompl (ExteriorAlgebra R M)).trans
    (_root_.localizedExteriorAlgebraEquiv
      (R := R) (M := M) (S := P.primeCompl)).symm.toLinearEquiv

/-- Helper for Remark `15.119.1`: under the ambient at-prime bridge, the localized generator
`ι_R(m) / 1` becomes the localized exterior generator `ι(m / 1)`. -/
@[simp] private theorem atPrime_exterior_bridge_apply_mk_ι
    (P : Ideal R) [P.IsPrime] (m : M) :
    atPrime_exterior_bridge (R := R) (M := M) P (LocalizedModule.mk (ι R m) 1) =
      ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M m) := by
  -- Proof comment: compare both sides after applying `localizedExteriorAlgebraEquiv`, where the
  -- bridge is definitionally the inverse equivalence composed with `equivTensorProduct`.
  apply (_root_.localizedExteriorAlgebraEquiv (R := R) (M := M) (S := P.primeCompl)).injective
  -- Proof comment: both images are the same tensor-stage generator `1 ⊗ ι_R(m)`.
  simpa [atPrime_exterior_bridge, atPrime_exterior_tensor_equiv_apply_mk_ι, LinearMap.baseChange_tmul]
    using (_root_.localizedExteriorAlgebraEquiv_apply_ι (S := P.primeCompl)
      (M := M) (x := LocalizedModule.mkLinearMap P.primeCompl M m)).symm

/-- Helper for Remark `15.119.1`: under the ambient at-prime bridge, localized left
multiplication by `ι_R(m)` becomes left multiplication by the localized generator `ι(m / 1)`. -/
private theorem atPrime_exterior_bridge_mulLeft_ι
    (P : Ideal R) [P.IsPrime] (m : M) :
    (atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap.comp
        (LocalizedModule.map P.primeCompl (LinearMap.mulLeft R (ι R m))) =
      (LinearMap.mulLeft (Localization.AtPrime P)
          (ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M m))).comp
        (atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap := by
  let F := (atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap.comp
    (LocalizedModule.map P.primeCompl (LinearMap.mulLeft R (ι R m)))
  let G := (LinearMap.mulLeft (Localization.AtPrime P)
      (ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M m))).comp
    (atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap
  ext x
  induction x using LocalizedModule.induction_on with
  | h y s =>
      have hmk_one :
          F (LocalizedModule.mk (M := ExteriorAlgebra R M) y 1) =
            G (LocalizedModule.mk (M := ExteriorAlgebra R M) y 1) := by
        -- Proof comment: on denominator-`1` generators, both composites become multiplication by
        -- the same tensor element `(1 ⊗ ι_R(m))` after applying `localizedExteriorAlgebraEquiv`.
        apply (_root_.localizedExteriorAlgebraEquiv (R := R) (M := M) (S := P.primeCompl)).injective
        simp [F, G, atPrime_exterior_bridge, LocalizedModule.map_mk,
          LocalizedModule.equivTensorProduct_apply_mk, LinearMap.baseChange_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Localization.mk_one]
      have hmk :
          (LocalizedModule.mk y s : LocalizedModule.AtPrime P (ExteriorAlgebra R M)) =
            (Localization.mk (1 : R) s : Localization.AtPrime P) •
              LocalizedModule.mk y 1 := by
        -- Proof comment: rewrite an arbitrary localization class as a scalar multiple of a
        -- denominator-`1` generator so the denominator-free comparison applies.
        change LocalizedModule.mk y s =
            (Localization.mk (1 : R) s : Localization.AtPrime P) • LocalizedModule.mk y 1
        simpa using (LocalizedModule.mk_smul_mk (1 : R) y s (1 : P.primeCompl)).symm
      have hFmk :
          F (LocalizedModule.mk y s) =
            (Localization.mk (1 : R) s : Localization.AtPrime P) • F (LocalizedModule.mk y 1) := by
        calc
          F (LocalizedModule.mk y s) =
              F ((Localization.mk (1 : R) s : Localization.AtPrime P) • LocalizedModule.mk y 1) := by
                rw [hmk]
          _ = (Localization.mk (1 : R) s : Localization.AtPrime P) • F (LocalizedModule.mk y 1) := by
                simp [F]
      have hGmk :
          G (LocalizedModule.mk y s) =
            (Localization.mk (1 : R) s : Localization.AtPrime P) • G (LocalizedModule.mk y 1) := by
        calc
          G (LocalizedModule.mk y s) =
              G ((Localization.mk (1 : R) s : Localization.AtPrime P) • LocalizedModule.mk y 1) := by
                rw [hmk]
          _ = (Localization.mk (1 : R) s : Localization.AtPrime P) • G (LocalizedModule.mk y 1) := by
                simp [G]
      -- Proof comment: the denominator-`1` comparison propagates to arbitrary denominators by
      -- linearity over the localized coefficient ring.
      calc
        F (LocalizedModule.mk y s) =
            (Localization.mk (1 : R) s : Localization.AtPrime P) • F (LocalizedModule.mk y 1) := hFmk
        _ = (Localization.mk (1 : R) s : Localization.AtPrime P) • G (LocalizedModule.mk y 1) := by
            rw [hmk_one]
        _ = G (LocalizedModule.mk y s) := hGmk.symm

/-- Helper for Remark `15.119.1`: under the ambient at-prime bridge, denominator-`1`
`ιMulti` generators transport to the corresponding localized `ιMulti` generators. -/
@[simp] private theorem atPrime_exterior_bridge_apply_mk_ιMulti
    (P : Ideal R) [P.IsPrime] :
    ∀ n : ℕ, ∀ v : Fin n → M,
      atPrime_exterior_bridge (R := R) (M := M) P
        (LocalizedModule.mk (ExteriorAlgebra.ιMulti R n v) 1) =
          ExteriorAlgebra.ιMulti (Localization.AtPrime P) n
            (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i)) := by
  intro n
  induction n with
  | zero =>
      intro v
      -- Proof comment: the degree-zero generator is the unit, and the bridge preserves that
      -- unit after passing through the tensor-stage equivalence.
      apply (_root_.localizedExteriorAlgebraEquiv (R := R) (M := M) (S := P.primeCompl)).injective
      simpa [atPrime_exterior_bridge, LocalizedModule.equivTensorProduct_apply_mk,
        Localization.mk_one, Algebra.TensorProduct.one_def]
  | succ n ih =>
      intro v
      have htail :
          (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M ((Matrix.vecTail v) i)) =
            Matrix.vecTail (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i)) := by
        -- Proof comment: the localized family commutes definitionally with the `vecTail`
        -- operation used in the recursive `ιMulti` formula.
        ext i
        rfl
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      -- Proof comment: reduce the successor case to the already-proved transport of localized
      -- left multiplication by a degree-one generator, then invoke the induction hypothesis.
      calc
        atPrime_exterior_bridge (R := R) (M := M) P
            (LocalizedModule.mk
              ((ι R (v 0)) * ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) 1)
            = (LinearMap.mulLeft (Localization.AtPrime P)
                (ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M (v 0))))
                (atPrime_exterior_bridge (R := R) (M := M) P
                  (LocalizedModule.mk (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) 1)) := by
              simpa [LinearMap.comp_apply, LocalizedModule.map_mk] using
                LinearMap.congr_fun
                  (atPrime_exterior_bridge_mulLeft_ι (R := R) (M := M) P (v 0))
                  (LocalizedModule.mk (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) 1)
        _ = (ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M (v 0))) *
              ExteriorAlgebra.ιMulti (Localization.AtPrime P) n
                (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M ((Matrix.vecTail v) i)) := by
              rw [ih (Matrix.vecTail v)]
              rfl
        _ = (ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M (v 0))) *
              ExteriorAlgebra.ιMulti (Localization.AtPrime P) n
                (Matrix.vecTail (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i))) := by
              rw [htail]
        _ = ExteriorAlgebra.ιMulti (Localization.AtPrime P) (n + 1)
              (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i)) := by
              simpa using
                (ExteriorAlgebra.ιMulti_succ_apply
                  (R := Localization.AtPrime P)
                  (v := fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i))).symm

/-- Helper for Remark `15.119.1`: a denominator-`1` `ιMulti` generator already belongs to the
localized image of the global top exterior power. -/
private theorem mk_ιMulti_mem_localized_topExteriorPower
    (P : Ideal R) [P.IsPrime] (r : ℕ) (v : Fin r → M) :
    (LocalizedModule.mk (ExteriorAlgebra.ιMulti R r v) 1 :
        LocalizedModule.AtPrime P (ExteriorAlgebra R M)) ∈
      Submodule.localized' (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))
        (⋀[R]^r M : Submodule R (ExteriorAlgebra R M)) := by
  -- Proof comment: the generator already lies in the global fixed-degree piece, so its
  -- denominator-`1` localization lies in the localized submodule by `mem_localized'`.
  rw [Submodule.mem_localized']
  refine ⟨ExteriorAlgebra.ιMulti R r v, ?_, 1, ?_⟩
  · exact ExteriorAlgebra.ιMulti_range R r ⟨v, rfl⟩
  · simp [LocalizedModule.mkLinearMap_apply]

/-- Helper for Remark `15.119.1`: after applying the ambient at-prime bridge, a denominator-`1`
`ιMulti` generator lies in the localized top exterior power. -/
private theorem atPrime_exterior_bridge_apply_mk_ιMulti_mem_topExteriorPower
    (P : Ideal R) [P.IsPrime] (r : ℕ) (v : Fin r → M) :
    atPrime_exterior_bridge (R := R) (M := M) P
        (LocalizedModule.mk (ExteriorAlgebra.ιMulti R r v) 1) ∈
      (⋀[Localization.AtPrime P]^r (LocalizedModule.AtPrime P M) :
        Submodule (Localization.AtPrime P)
          (ExteriorAlgebra (Localization.AtPrime P) (LocalizedModule.AtPrime P M))) := by
  -- Proof comment: compute the bridge on the explicit `ιMulti` generator and then use the
  -- standard fixed-degree membership theorem on the localized side.
  simpa using
    (ExteriorAlgebra.ιMulti_range (Localization.AtPrime P) r
      ⟨fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i), rfl⟩)

/-- Helper for Remark `15.119.1`: if a finite family spans `M`, then membership in `det(M)` can
be checked on that family alone. -/
private theorem mem_det_iff_of_span_eq_top {n : ℕ} (v : Fin n → M)
    (hv : Submodule.span R (Set.range v) = ⊤) (x : ExteriorAlgebra R M) :
    x ∈ det(M) ↔ ∀ i : Fin n, ι R (v i) * x = 0 := by
  rw [mem_det_iff]
  constructor
  · intro hx i
    exact hx (v i)
  · intro hx m
    have hm : m ∈ Submodule.span R (Set.range v) := by
      simpa [hv] using (show m ∈ (⊤ : Submodule R M) from Submodule.mem_top)
    -- Proof comment: because `ι` is linear, vanishing on a spanning family propagates to all of
    -- `M` by span induction.
    refine Submodule.span_induction
      (s := Set.range v)
      (p := fun y _ => ι R y * x = 0)
      ?_ ?_ ?_ ?_ hm
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hx i
    · simp
    · intro y z hy hz hy' hz'
      simp [map_add, add_mul, hy', hz']
    · intro a y hy hy'
      simp [map_smul, hy']

/-- Helper for Remark `15.119.1`: if a finite family spans `M`, then `det(M)` is the
intersection of the kernels of left multiplication by the corresponding degree-one generators. -/
private theorem det_eq_iInf_mulLeft_ker_of_span_eq_top {n : ℕ} (v : Fin n → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    det(M) = ⨅ i : Fin n, (LinearMap.mulLeft R (ι R (v i))).ker := by
  ext x
  rw [mem_det_iff_of_span_eq_top (R := R) (M := M) v hv x]
  simp [LinearMap.mem_ker]

/-- Helper for Remark `15.119.1`: the images of global generators span the localization of `M`
at a prime ideal. -/
private theorem atPrime_generator_range_span_top
    (P : Ideal R) [P.IsPrime] :
    Submodule.span (Localization.AtPrime P)
      (Set.range (LocalizedModule.mkLinearMap P.primeCompl M)) = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  induction x using LocalizedModule.induction_on with
  | h m s =>
      have hmem :
          LocalizedModule.mkLinearMap P.primeCompl M m ∈
            Submodule.span (Localization.AtPrime P)
              (Set.range (LocalizedModule.mkLinearMap P.primeCompl M)) := by
        exact Submodule.subset_span ⟨m, rfl⟩
      have hmk :
          (LocalizedModule.mk m s : LocalizedModule.AtPrime P M) =
            (Localization.mk (1 : R) s : Localization.AtPrime P) •
              LocalizedModule.mkLinearMap P.primeCompl M m := by
        -- Proof comment: every localized class is a scalar multiple of a denominator-`1`
        -- generator coming from `M`.
        change LocalizedModule.mk m s =
            (Localization.mk (1 : R) s : Localization.AtPrime P) • LocalizedModule.mk m 1
        simpa using (LocalizedModule.mk_smul_mk (1 : R) m s (1 : P.primeCompl)).symm
      rw [hmk]
      exact Submodule.smul_mem _ _ hmem

/-- Helper for Remark `15.119.1`: localization commutes with finite intersections indexed by
`Fin n`. -/
private theorem localized'_iInf_fin {N : Type*} [AddCommGroup N] [Module R N]
    (P : Ideal R) [P.IsPrime] :
    ∀ {n : ℕ} (K : Fin n → Submodule R N),
      (⨅ i, K i).localized' (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl N) =
      ⨅ i, (K i).localized' (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl N) := by
  intro n
  induction n with
  | zero =>
      intro K
      rw [show (⨅ i : Fin 0, K i) = ⊤ by simp, Submodule.localized'_top]
      rw [show (⨅ i : Fin 0,
          (K i).localized' (Localization.AtPrime P) P.primeCompl
            (LocalizedModule.mkLinearMap P.primeCompl N)) = ⊤ by simp]
  | succ n ih =>
      intro K
      have hiInf :
          (⨅ i : Fin (n + 1), K i) = K 0 ⊓ ⨅ i : Fin n, K i.succ := by
        ext x
        simp [Fin.forall_fin_succ]
      have hiInf' :
          (⨅ i : Fin (n + 1),
              (K i).localized' (Localization.AtPrime P) P.primeCompl
                (LocalizedModule.mkLinearMap P.primeCompl N)) =
            (K 0).localized' (Localization.AtPrime P) P.primeCompl
                (LocalizedModule.mkLinearMap P.primeCompl N) ⊓
              ⨅ i : Fin n,
                (K i.succ).localized' (Localization.AtPrime P) P.primeCompl
                  (LocalizedModule.mkLinearMap P.primeCompl N) := by
        ext x
        simp [Fin.forall_fin_succ]
      -- Proof comment: rewrite the finite intersection into head-plus-tail form and use the
      -- induction hypothesis on the tail.
      rw [hiInf, Submodule.localized'_inf, ih, hiInf']

/-- Helper for Remark `15.119.1`: a linear equivalence carries a finite intersection of submodules
to the corresponding finite intersection of their images. -/
private theorem map_iInf_fin {A : Type*} [CommRing A]
    {B : Type*} [AddCommGroup B] [Module A B]
    {C : Type*} [AddCommGroup C] [Module A C]
    (e : B ≃ₗ[A] C) :
    ∀ {n : ℕ} (K : Fin n → Submodule A B),
      Submodule.map e.toLinearMap (⨅ i, K i) =
        ⨅ i, Submodule.map e.toLinearMap (K i) := by
  intro n
  induction n with
  | zero =>
      intro K
      ext x
      simp
  | succ n ih =>
      intro K
      have hiInf :
          (⨅ i : Fin (n + 1), K i) = K 0 ⊓ ⨅ i : Fin n, K i.succ := by
        ext x
        simp [Fin.forall_fin_succ]
      have hiInf' :
          (⨅ i : Fin (n + 1), Submodule.map e.toLinearMap (K i)) =
            Submodule.map e.toLinearMap (K 0) ⊓
              ⨅ i : Fin n, Submodule.map e.toLinearMap (K i.succ) := by
        ext x
        simp [Fin.forall_fin_succ]
      -- Proof comment: finite intersections are preserved because `Submodule.map` preserves
      -- binary infima along injective linear maps.
      rw [hiInf, Submodule.map_inf _ e.injective, ih, hiInf']

/-- Helper for Remark `15.119.1`: if a finite family spans `M`, then its denominator-`1` images
span the localization of `M` at a prime ideal. -/
private theorem atPrime_generator_family_span_top_of_span_eq_top
    (P : Ideal R) [P.IsPrime] {n : ℕ} (v : Fin n → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span (Localization.AtPrime P)
      (Set.range (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i))) = ⊤ := by
  have hloc := congrArg
    (fun N : Submodule R M =>
      N.localized' (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M)) hv
  -- Proof comment: localizing the global spanning relation replaces each generator by its
  -- denominator-`1` image and turns the localized top module into `⊤`.
  calc
    Submodule.span (Localization.AtPrime P)
        (Set.range (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i))) =
      Submodule.span (Localization.AtPrime P)
        ((fun a ↦ LocalizedModule.mk a 1) '' Set.range v) := by
          congr 1
          ext x
          constructor
          · rintro ⟨i, rfl⟩
            exact ⟨v i, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
            exact ⟨i, rfl⟩
    _ = ⊤ := by
          simpa [Submodule.localized'_span] using hloc

/-- Helper for Remark `15.119.1`: after transporting denominator-`1` global `ιMulti` generators
through the at-prime bridge, one gets exactly the local `ιMulti` generators built from images of
global vectors. -/
private theorem atPrime_exterior_bridge_ιMulti_image_eq
    (P : Ideal R) [P.IsPrime] (r : ℕ) :
    (atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap ''
      (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M) ''
        Set.range (ExteriorAlgebra.ιMulti R r)) =
    ExteriorAlgebra.ιMulti (Localization.AtPrime P) r ''
      {a | Set.range a ⊆ Set.range (LocalizedModule.mkLinearMap P.primeCompl M)} := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, ⟨v, rfl⟩, rfl⟩, rfl⟩
    refine ⟨fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i), ?_, ?_⟩
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      exact ⟨v i, rfl⟩
    · simpa using
        atPrime_exterior_bridge_apply_mk_ιMulti (R := R) (M := M) P r v
  · intro hx
    rcases hx with ⟨a, ha, rfl⟩
    classical
    have hpre :
        ∀ i : Fin r, ∃ m : M, LocalizedModule.mkLinearMap P.primeCompl M m = a i := by
      intro i
      exact ha (Set.mem_range_self i)
    choose v hv using hpre
    have hfun :
        (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i)) = a := by
      ext i
      exact hv i
    refine ⟨LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)
        (ExteriorAlgebra.ιMulti R r v), ?_, ?_⟩
    · exact ⟨ExteriorAlgebra.ιMulti R r v, ⟨v, rfl⟩, rfl⟩
    · -- Proof comment: choose preimages of the local family coordinatewise and transport the
      -- resulting denominator-`1` global generator through the bridge.
      calc
        atPrime_exterior_bridge (R := R) (M := M) P
            (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)
              (ExteriorAlgebra.ιMulti R r v)) =
          ExteriorAlgebra.ιMulti (Localization.AtPrime P) r
            (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i)) := by
              simpa using
                atPrime_exterior_bridge_apply_mk_ιMulti (R := R) (M := M) P r v
        _ = ExteriorAlgebra.ιMulti (Localization.AtPrime P) r a := by
              rw [hfun]

/-- Helper for Remark `15.119.1`: transporting the localized global top exterior power through
the at-prime bridge gives the local top exterior power. -/
private theorem atPrime_exterior_bridge_map_topExteriorPower
    (P : Ideal R) [P.IsPrime] (r : ℕ) :
    Submodule.map (atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap
      (((⋀[R]^r M : Submodule R (ExteriorAlgebra R M)).localized'
        (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)))) =
      (⋀[Localization.AtPrime P]^r (LocalizedModule.AtPrime P M) :
        Submodule (Localization.AtPrime P)
          (ExteriorAlgebra (Localization.AtPrime P) (LocalizedModule.AtPrime P M))) := by
  calc
    Submodule.map (atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap
        (((⋀[R]^r M : Submodule R (ExteriorAlgebra R M)).localized'
          (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)))) =
      Submodule.span (Localization.AtPrime P)
        ((atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap ''
          (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M) ''
            Set.range (ExteriorAlgebra.ιMulti R r))) := by
          -- Proof comment: rewrite the global top exterior power as the span of its `ιMulti`
          -- generators, then localize and transport that spanning set.
          rw [show (⋀[R]^r M : Submodule R (ExteriorAlgebra R M)) =
              Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R r)) by
                simpa using
                  (ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (n := r) (M := M)).symm,
            Submodule.localized'_span, Submodule.map_span]
    _ = Submodule.span (Localization.AtPrime P)
        (ExteriorAlgebra.ιMulti (Localization.AtPrime P) r ''
          {a | Set.range a ⊆ Set.range (LocalizedModule.mkLinearMap P.primeCompl M)}) := by
          rw [atPrime_exterior_bridge_ιMulti_image_eq (R := R) (M := M) P r]
    _ = (⋀[Localization.AtPrime P]^r (LocalizedModule.AtPrime P M) :
          Submodule (Localization.AtPrime P)
            (ExteriorAlgebra (Localization.AtPrime P) (LocalizedModule.AtPrime P M))) := by
          simpa using
            (exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top
              (R := Localization.AtPrime P) (n := r)
              (M := LocalizedModule.AtPrime P M)
              (s := Set.range (LocalizedModule.mkLinearMap P.primeCompl M))
              (atPrime_generator_range_span_top (R := R) (M := M) P))

/-- Helper for Remark `15.119.1`: a linear equivalence transports the kernel of a map to the
kernel of any conjugate map. -/
private theorem map_ker_eq_of_intertwine
    {A : Type*} [CommRing A]
    {B : Type*} [AddCommGroup B] [Module A B]
    {C : Type*} [AddCommGroup C] [Module A C]
    (e : B ≃ₗ[A] C) (f : B →ₗ[A] B) (g : C →ₗ[A] C)
    (h : e.toLinearMap.comp f = g.comp e.toLinearMap) :
    Submodule.map e.toLinearMap (LinearMap.ker f) = LinearMap.ker g := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change f x = 0 at hx
    change g (e x) = 0
    simpa [LinearMap.comp_apply, hx] using (LinearMap.congr_fun h x).symm
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    change g y = 0 at hy
    change f (e.symm y) = 0
    apply e.injective
    simpa [LinearMap.comp_apply, hy] using LinearMap.congr_fun h (e.symm y)

/-- Helper for Remark `15.119.1`: transporting the localized determinant line through the
at-prime bridge identifies it with the determinant line of the localized module, provided one has
fixed a finite spanning family of the original module. -/
private theorem atPrime_exterior_bridge_map_det_of_span_eq_top
    (P : Ideal R) [P.IsPrime] {n : ℕ} (v : Fin n → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.map (atPrime_exterior_bridge (R := R) (M := M) P).toLinearMap
      (((det(M)).localized' (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)))) =
      det(LocalizedModule.AtPrime P M) := by
  let e := atPrime_exterior_bridge (R := R) (M := M) P
  have hspanLocal :
      Submodule.span (Localization.AtPrime P)
        (Set.range (fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i))) = ⊤ :=
    atPrime_generator_family_span_top_of_span_eq_top (R := R) (M := M) P v hv
  calc
    Submodule.map e.toLinearMap
        (((det(M)).localized' (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)))) =
      Submodule.map e.toLinearMap
        (⨅ i : Fin n,
          ((LinearMap.mulLeft R (ι R (v i))).ker).localized'
            (Localization.AtPrime P) P.primeCompl
            (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))) := by
          -- Proof comment: replace the global determinant line by the finite intersection of
          -- kernels coming from the chosen spanning family before localizing.
          rw [det_eq_iInf_mulLeft_ker_of_span_eq_top (R := R) (M := M) v hv,
            localized'_iInf_fin (R := R) (N := ExteriorAlgebra R M) P]
    _ = ⨅ i : Fin n,
        Submodule.map e.toLinearMap
          (((LinearMap.mulLeft R (ι R (v i))).ker).localized'
            (Localization.AtPrime P) P.primeCompl
            (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))) := by
          rw [map_iInf_fin e]
    _ = ⨅ i : Fin n,
        (LinearMap.mulLeft (Localization.AtPrime P)
          (ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M (v i)))).ker := by
          apply iInf_congr
          intro i
          have hker :
              ((LinearMap.mulLeft R (ι R (v i))).ker).localized'
                  (Localization.AtPrime P) P.primeCompl
                  (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)) =
                LinearMap.ker
                  (LocalizedModule.map P.primeCompl
                    (LinearMap.mulLeft R (ι R (v i)))) := by
            -- Proof comment: localization commutes with kernels for the localized left
            -- multiplication map.
            simpa using
              (LinearMap.localized'_ker_eq_ker_localizedMap
                (S := Localization.AtPrime P) (p := P.primeCompl)
                (f := LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))
                (f' := LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))
                (g := LinearMap.mulLeft R (ι R (v i))))
          rw [hker]
          exact map_ker_eq_of_intertwine e
            (LocalizedModule.map P.primeCompl (LinearMap.mulLeft R (ι R (v i))))
            (LinearMap.mulLeft (Localization.AtPrime P)
              (ι (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M (v i))))
            (atPrime_exterior_bridge_mulLeft_ι (R := R) (M := M) P (v i))
    _ = det(LocalizedModule.AtPrime P M) := by
          rw [(det_eq_iInf_mulLeft_ker_of_span_eq_top
            (R := Localization.AtPrime P) (M := LocalizedModule.AtPrime P M)
            (v := fun i ↦ LocalizedModule.mkLinearMap P.primeCompl M (v i))
            hspanLocal).symm]

section

variable [Module.Finite R M] [Module.Projective R M]

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: in the finite free case, the full wedge basis vector is
annihilated by every degree-one generator, hence lies in the determinant line. -/
-- Proof sketch: rewrite an arbitrary generator `ι m` in the chosen basis, then use the
-- singleton-times-top-wedge multiplication rule to show each basis summand kills the top wedge.
private theorem basis_univ_mem_det
    {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M) :
    b.ExteriorAlgebra (Finset.univ : Finset I) ∈ det(M) := by
  let n := Fintype.card I
  let topIndex : Set.powersetCard I n := ⟨Finset.univ, by simp [n]⟩
  rw [mem_det_iff]
  intro m
  -- Rewrite an arbitrary generator using the basis and kill each basis term separately.
  have hm :
      ι R m = ∑ i, b.repr m i • ι R (b i) := by
    have hsum : ι R m = ι R (∑ i, b.repr m i • b i) :=
      congrArg (ι R) (b.sum_repr m).symm
    have hmap :
        ι R (∑ i, b.repr m i • b i) = ∑ i, ι R (b.repr m i • b i) := by
      simpa using (_root_.map_sum (ι R) (fun i ↦ b.repr m i • b i) Finset.univ)
    calc
      ι R m = ι R (∑ i, b.repr m i • b i) := hsum
      _ = ∑ i, ι R (b.repr m i • b i) := hmap
      _ = ∑ i, b.repr m i • ι R (b i) := by simp
  rw [hm, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  let singletonIndex : Set.powersetCard I 1 := ⟨{i}, by simp⟩
  have hindex : (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofSingleton i)) 0 = i := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact Finset.orderEmbOfFin_singleton i 0
  have hι :
      ι R (b i) = b.ExteriorAlgebra ({i} : Finset I) := by
    symm
    simpa [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, hindex] using
      (ExteriorAlgebra.basis_apply_powersetCard (b := b) (m := 1)
        (s := Set.powersetCard.ofSingleton i))
  have hmul :
      ι R (b i) * b.ExteriorAlgebra (Finset.univ : Finset I) = 0 := by
    -- The singleton basis vector intersects the top-degree basis vector, so their product is zero.
    simpa [n, singletonIndex, topIndex, hι] using
      (ExteriorAlgebra.basis_mul_of_not_disjoint (b := b) (m := 1) (n := n)
        (s := singletonIndex) (t := topIndex) (by
          simp [singletonIndex, topIndex]))
  simp [hmul]

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: in the finite free case, the span of the full wedge basis vector
already lies in the determinant line. This packages the stable half of the free-model argument. -/
-- Proof sketch: the determinant line is a submodule, so once the top wedge basis vector is in it,
-- the span of that single generator is contained in it as well.
private theorem span_basis_univ_le_det
    {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M) :
    Submodule.span R {b.ExteriorAlgebra (Finset.univ : Finset I)} ≤ det(M) := by
  exact Submodule.span_le.2 fun x hx ↦ by
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact basis_univ_mem_det (R := R) (M := M) b

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: the top-degree basis vector of the exterior algebra basis agrees
with the degree-one generator `ι (b i)` for a singleton subset. -/
-- Proof sketch: evaluate the exterior-algebra basis on the singleton subset and unfold the
-- `ιMulti` description of that basis vector.
private theorem basis_singleton_eq_ι
    {I : Type*} [Finite I] [LinearOrder I] (b : Basis I R M) (i : I) :
    b.ExteriorAlgebra ({i} : Finset I) = ι R (b i) := by
  let _ := Fintype.ofFinite I
  let singletonIndex : Set.powersetCard I 1 := ⟨{i}, by simp⟩
  have hindex : (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofSingleton i)) 0 = i := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact Finset.orderEmbOfFin_singleton i 0
  simpa [singletonIndex, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply, hindex] using
    (ExteriorAlgebra.basis_apply_powersetCard (b := b) (m := 1)
      (s := Set.powersetCard.ofSingleton i))

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: for a finite free module, the top exterior power is generated by
the full wedge of any basis. -/
-- Proof sketch: the basis of the top exterior power is indexed by `Set.powersetCard I |I|`, and
-- that index type is a singleton because the only `|I|`-element finite subset of `I` is `univ`.
private theorem topExteriorPower_eq_span_basis_univ
    {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M) :
    (⋀[R]^(Fintype.card I) M : Submodule R (ExteriorAlgebra R M)) =
      Submodule.span R {b.ExteriorAlgebra (Finset.univ : Finset I)} := by
  let n := Fintype.card I
  let topIndex : Set.powersetCard I n := ⟨Finset.univ, by simp [n]⟩
  let B : Basis (Set.powersetCard I n) R ↥(⋀[R]^n M) := b.exteriorPower n
  have hsub : Subsingleton (Set.powersetCard I n) := by
    refine ⟨fun s t ↦ ?_⟩
    have hs_univ : (s : Finset I) = Finset.univ := by
      apply (Finset.card_eq_iff_eq_univ (s := (s : Finset I))).mp
      simpa [n] using s.2
    have ht_univ : (t : Finset I) = Finset.univ := by
      apply (Finset.card_eq_iff_eq_univ (s := (t : Finset I))).mp
      simpa [n] using t.2
    apply Subtype.ext
    simpa [hs_univ, ht_univ]
  have hrange :
      Set.range (fun s : Set.powersetCard I n ↦ B s) = {B topIndex} := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      have hs : s = topIndex := Subsingleton.elim _ _
      simp [hs]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨topIndex, rfl⟩
  have htop : (⊤ : Submodule R ↥(⋀[R]^n M)) = Submodule.span R {B topIndex} := by
    rw [← B.span_eq, hrange]
  have hcoe_top :
      Set.range (fun s : Set.powersetCard I n ↦ ((B s : ↥(⋀[R]^n M)) : ExteriorAlgebra R M)) =
        {(((B topIndex : ↥(⋀[R]^n M)) : ExteriorAlgebra R M))} := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      have hs : s = topIndex := Subsingleton.elim _ _
      simp [hs]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨topIndex, rfl⟩
  calc
    (⋀[R]^n M : Submodule R (ExteriorAlgebra R M)) = Submodule.map (⋀[R]^n M).subtype ⊤ := by
      rw [Submodule.map_subtype_top]
    _ = Submodule.map (⋀[R]^n M).subtype (Submodule.span R {B topIndex}) := by
      rw [htop]
    _ = Submodule.span R ((↑(⋀[R]^n M).subtype) '' {B topIndex}) := by
      rw [Submodule.map_span]
    _ = Submodule.span R {b.ExteriorAlgebra (Finset.univ : Finset I)} := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases Set.mem_singleton_iff.mp hy with rfl
        have htopBasis :
            (((B topIndex : ↥(⋀[R]^n M)) : ExteriorAlgebra R M)) =
              b.ExteriorAlgebra (Finset.univ : Finset I) := by
          simpa [B, topIndex, n] using
            (ExteriorAlgebra.basis_eq_coe_basis (b := b) (m := n) (s := topIndex)).symm
        simp [htopBasis]
      · intro hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        refine ⟨B topIndex, ?_, ?_⟩
        · simp
        · have htopBasis :
              (((B topIndex : ↥(⋀[R]^n M)) : ExteriorAlgebra R M)) =
                b.ExteriorAlgebra (Finset.univ : Finset I) := by
            simpa [B, topIndex, n] using
              (ExteriorAlgebra.basis_eq_coe_basis (b := b) (m := n) (s := topIndex)).symm
          simpa [htopBasis]

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: in the finite free case, every determinant-line element has zero
coefficient on every proper-subset exterior basis vector. -/
-- Proof sketch: pick `i ∉ s`, multiply the exterior-basis expansion of `x` by `ι (b i)`, and
-- read the coefficient of the basis vector indexed by `insert i s`; all other summands vanish,
-- while the surviving `s`-summand is a unit multiple of the desired coefficient.
private theorem coeff_eq_zero_of_mem_det_of_ne_univ
    {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M)
    {x : ExteriorAlgebra R M} (hx : x ∈ det(M)) {s : Finset I} (hs : s ≠ Finset.univ) :
    b.ExteriorAlgebra.equivFun x s = 0 := by
  let B : Basis (Finset I) R (ExteriorAlgebra R M) := b.ExteriorAlgebra
  have hs' : ∃ i : I, i ∉ s := by
    by_contra hs'
    apply hs
    refine Finset.eq_univ_iff_forall.mpr ?_
    intro i
    by_contra hi
    exact hs' ⟨i, hi⟩
  obtain ⟨i, his⟩ := hs'
  let u : Finset I := insert i s
  have hz : ι R (b i) * x = 0 := (mem_det_iff (R := R) (M := M) x).1 hx (b i)
  have hcoeffZero : B.equivFun (ι R (b i) * x) u = 0 := by
    simp [hz, B, u]
  have hxsum := B.sum_equivFun x
  rw [← hxsum, Finset.mul_sum] at hcoeffZero
  rw [map_sum] at hcoeffZero
  have hsingleton : ι R (b i) = B ({i} : Finset I) := by
    simpa [B] using (basis_singleton_eq_ι (R := R) (M := M) b i).symm
  have hcoeff_basis_ne : ∀ {t : Finset I}, t ≠ s → B.equivFun (ι R (b i) * B t) u = 0 := by
    intro t hts
    by_cases hit : i ∈ t
    · let singletonIndex : Set.powersetCard I 1 := ⟨{i}, by simp⟩
      let tIndex : Set.powersetCard I t.card := ⟨t, by simp⟩
      have hnotdisj' : ¬ Disjoint (↑singletonIndex : Finset I) (↑tIndex : Finset I) := by
        simpa [singletonIndex, tIndex, hit]
      have hmul : B ({i} : Finset I) * B t = 0 := by
        simpa [B, singletonIndex, tIndex] using
          (ExteriorAlgebra.basis_mul_of_not_disjoint (b := b) (m := 1) (n := t.card)
            (s := singletonIndex) (t := tIndex) hnotdisj')
      simpa [hsingleton, hmul]
    · let singletonIndex : Set.powersetCard I 1 := ⟨{i}, by simp⟩
      let tIndex : Set.powersetCard I t.card := ⟨t, by simp⟩
      have hdisj' : Disjoint (↑singletonIndex : Finset I) (↑tIndex : Finset I) := by
        simpa [singletonIndex, tIndex, hit]
      have hmul : B ({i} : Finset I) * B t =
          Equiv.Perm.sign (Set.powersetCard.permOfDisjoint hdisj') • B (insert i t) := by
        simpa [B, singletonIndex, tIndex] using
          (ExteriorAlgebra.basis_mul_of_disjoint (b := b) (m := 1) (n := t.card)
            (s := singletonIndex) (t := tIndex) hdisj')
      have hne : insert i t ≠ u := by
        intro hEq
        apply hts
        have := congrArg (fun A : Finset I ↦ A.erase i) hEq
        simpa [u, hit, his] using this
      rw [hsingleton, hmul]
      simp [B, hne]
  have hterm_repr : ∀ t : Finset I,
      (B.repr x) t * (B.repr ((ι R (b i) * B t))) u =
        if t = s then B.equivFun x s * (B.equivFun (ι R (b i) * B s) u) else 0 := by
    intro t
    by_cases hts : t = s
    · subst hts
      simp [B]
    · have hinner : B.equivFun (ι R (b i) * B t) u = 0 := hcoeff_basis_ne hts
      have hinner' : (B.repr ((ι R (b i) * B t))) u = 0 := by
        simpa [Module.Basis.equivFun_apply] using hinner
      simp [hts, B, hinner']
  have hcoeffZero_repr :
      ∑ t : Finset I, (B.repr x) t * (B.repr ((ι R (b i) * B t))) u = 0 := by
    simpa [Module.Basis.equivFun_apply] using hcoeffZero
  have hcoeffZero' :
      ∑ t : Finset I,
        (if t = s then B.equivFun x s * (B.equivFun (ι R (b i) * B s) u) else 0) = 0 := by
    calc
      ∑ t : Finset I,
          (if t = s then B.equivFun x s * (B.equivFun (ι R (b i) * B s) u) else 0) =
            ∑ t : Finset I, (B.repr x) t * (B.repr ((ι R (b i) * B t))) u := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              symm
              exact hterm_repr t
      _ = 0 := hcoeffZero_repr
  have hmain_unit : IsUnit (B.equivFun (ι R (b i) * B s) u) := by
    let singletonIndex : Set.powersetCard I 1 := ⟨{i}, by simp⟩
    let sIndex : Set.powersetCard I s.card := ⟨s, by simp⟩
    have hdisj' : Disjoint (↑singletonIndex : Finset I) (↑sIndex : Finset I) := by
      simpa [singletonIndex, sIndex, his]
    have hmul : B ({i} : Finset I) * B s =
        Equiv.Perm.sign (Set.powersetCard.permOfDisjoint hdisj') • B u := by
      simpa [B, u, singletonIndex, sIndex] using
        (ExteriorAlgebra.basis_mul_of_disjoint (b := b) (m := 1) (n := s.card)
          (s := singletonIndex) (t := sIndex) hdisj')
    rw [← hsingleton] at hmul
    have hu : B.equivFun (ι R (b i) * B s) u =
        Equiv.Perm.sign (Set.powersetCard.permOfDisjoint hdisj') • (1 : R) := by
      rw [hmul]
      simp [B, u]
    rw [hu]
    simpa using Units.isUnit (Equiv.Perm.sign (Set.powersetCard.permOfDisjoint hdisj'))
  have hsum_single :
      ∑ t : Finset I,
        (if t = s then B.equivFun x s * (B.equivFun (ι R (b i) * B s) u) else 0) =
          B.equivFun x s * (B.equivFun (ι R (b i) * B s) u) := by
    simpa using
      (Finset.sum_ite_eq' (s := Finset.univ) (a := s)
        (b := fun _ : Finset I ↦ B.equivFun x s * (B.equivFun (ι R (b i) * B s) u)))
  have hmulzero : B.equivFun x s * B.equivFun (ι R (b i) * B s) u = 0 := by
    rw [← hsum_single]
    exact hcoeffZero'
  rcases hmain_unit with ⟨ucoeff, hucoeff⟩
  rw [← hucoeff] at hmulzero
  have hcancel := congrArg (fun z : R ↦ z * ↑ucoeff⁻¹) hmulzero
  simpa [B, mul_assoc] using hcancel

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: in the finite free case, the determinant line equals the top
exterior power. This upgrades the stable span inclusion to the full free-model equality. -/
-- Proof sketch: the top exterior power is the span of the full wedge basis vector, which already
-- lies in `det(M)`; conversely, the coefficient-killing lemma forces every determinant-line
-- element to be a scalar multiple of that top wedge basis vector.
private theorem det_eq_topExteriorPower_of_basis
    {I : Type*} [Fintype I] [LinearOrder I] (b : Basis I R M) :
    det(M) = (⋀[R]^(Fintype.card I) M : Submodule R (ExteriorAlgebra R M)) := by
  rw [topExteriorPower_eq_span_basis_univ (R := R) (M := M) b]
  refine le_antisymm ?_ (span_basis_univ_le_det (R := R) (M := M) b)
  intro x hx
  rw [Submodule.mem_span_singleton]
  refine ⟨(b.ExteriorAlgebra).equivFun x Finset.univ, ?_⟩
  -- Expand in the exterior basis and kill all proper-subset coefficients using `det(M)`.
  calc
    (b.ExteriorAlgebra).equivFun x Finset.univ • b.ExteriorAlgebra (Finset.univ : Finset I) =
        ∑ t : Finset I, (b.ExteriorAlgebra).equivFun x t • b.ExteriorAlgebra t := by
          symm
          refine Finset.sum_eq_single_of_mem (Finset.univ : Finset I) (Finset.mem_univ _) ?_
          intro t _ hne
          simp [coeff_eq_zero_of_mem_det_of_ne_univ (R := R) (M := M) b hx hne]
    _ = x := (b.ExteriorAlgebra).sum_equivFun x

/-- Helper for Remark `15.119.1`: the top exterior power of a free rank-`r` module is a free
rank-one module. -/
-- Proof comment: the basis `b.exteriorPower r` is indexed by `Set.powersetCard (Fin r) r`, and
-- that index type is a singleton because the only `r`-element subset of `Fin r` is `univ`.
private theorem topExteriorPower_linearEquiv_fin_one_of_basis
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N] {r : ℕ}
    (b : Basis (Fin r) A N) :
    Nonempty ((⋀[A]^r N : Submodule A (ExteriorAlgebra A N)) ≃ₗ[A] (Fin 1 → A)) := by
  let ι : Type := Set.powersetCard (Fin r) r
  let B : Basis ι A ↥(⋀[A]^r N) := b.exteriorPower r
  have hsub : Subsingleton ι := by
    refine ⟨fun s t ↦ ?_⟩
    have hs_univ : (s : Finset (Fin r)) = Finset.univ := by
      apply (Finset.card_eq_iff_eq_univ (s := (s : Finset (Fin r)))).mp
      simpa using s.2
    have ht_univ : (t : Finset (Fin r)) = Finset.univ := by
      apply (Finset.card_eq_iff_eq_univ (s := (t : Finset (Fin r)))).mp
      simpa using t.2
    apply Subtype.ext
    simpa [hs_univ, ht_univ]
  letI : Unique ι :=
    ⟨⟨Finset.univ, by simp⟩, fun s ↦ hsub.elim s ⟨Finset.univ, by simp⟩⟩
  -- Proof comment: identify the top exterior power with functions on its singleton basis index,
  -- then transport that singleton function space to `Fin 1 → A`.
  let eFun : (ι → A) ≃ₗ[A] (Fin 1 → A) :=
    (LinearEquiv.funCongrLeft A A (Equiv.ofUnique ι (Fin 1))).symm
  exact ⟨B.equivFun.trans eFun⟩

/-- Helper for Remark `15.119.1`: for any finite basis, the determinant line is a free rank-one
module. -/
-- Proof comment: first identify `det(N)` with the top exterior power using the chosen basis,
-- then reindex that basis by `Fin` so the previously established rank-one trivialization applies.
private theorem det_linearEquiv_fin_one_of_basis
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Projective A N]
    {I : Type*} [Finite I] [LinearOrder I] (b : Basis I A N) :
    Nonempty (Module.det A N ≃ₗ[A] (Fin 1 → A)) := by
  let _ := Fintype.ofFinite I
  let bFin : Basis (Fin (Fintype.card I)) A N := b.reindex (Fintype.equivFin I)
  have hdet :
      Module.det A N = (⋀[A]^(Fintype.card I) N : Submodule A (ExteriorAlgebra A N)) := by
    simpa using (det_eq_topExteriorPower_of_basis (R := A) (M := N) (I := I) b)
  rcases topExteriorPower_linearEquiv_fin_one_of_basis (A := A) (N := N) bFin with ⟨eTop⟩
  exact ⟨(LinearEquiv.ofEq _ _ hdet).trans eTop⟩

/-- Helper for Remark `15.119.1`: in the finite free case, the determinant line is invertible. -/
-- Proof comment: rewrite the determinant line as the top exterior power, trivialize that top
-- exterior power by the rank-one basis above, and transport the canonical invertible structure on
-- the ring module across the resulting linear equivalence.
private theorem det_moduleInvertible_of_basis
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Projective A N] {r : ℕ}
    (b : Basis (Fin r) A N) :
    Module.Invertible A (Module.det A N) := by
  have hdet :
      Module.det A N = (⋀[A]^r N : Submodule A (ExteriorAlgebra A N)) := by
    simpa using
      (det_eq_topExteriorPower_of_basis
        (R := A) (M := N) (I := Fin r) b)
  rcases topExteriorPower_linearEquiv_fin_one_of_basis (A := A) (N := N) b with ⟨eTop⟩
  let eDet : Module.det A N ≃ₗ[A] (Fin 1 → A) :=
    (LinearEquiv.ofEq _ _ hdet).trans eTop
  let eRing : Module.det A N ≃ₗ[A] A :=
    eDet.trans (LinearEquiv.funUnique (Fin 1) A A)
  letI : Module.Invertible A A := inferInstance
  exact Module.Invertible.congr eRing.symm

/-- Helper for Remark `15.119.1`: in the finite free local model, the determinant-line contraction
map is bijective. -/
-- Proof comment: the owner predicate `Module.Invertible` is defined exactly so that bijectivity of
-- `contractLeft` is its computational avatar.
private theorem det_contractLeft_bijective_of_basis
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Projective A N] {r : ℕ}
    (b : Basis (Fin r) A N) :
    Function.Bijective (contractLeft A (Module.det A N)) := by
  letI : Module.Invertible A (Module.det A N) :=
    det_moduleInvertible_of_basis (A := A) (N := N) b
  simpa using (Module.Invertible.bijective (R := A) (M := Module.det A N))

/-- Helper for Remark `15.119.1`: at a maximal ideal, the localized determinant line agrees with
the localized top exterior power. -/
private theorem localized_det_eq_localized_topExteriorPower_at_maximal
    (r : ℕ) (hM : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r)
    (P : Ideal R) [P.IsMaximal] :
    (det(M)).localized' (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)) =
      ((⋀[R]^r M : Submodule R (ExteriorAlgebra R M))).localized'
        (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)) := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let e := atPrime_exterior_bridge (R := R) (M := M) P
  let _ : Module.Flat (Localization.AtPrime P) (LocalizedModule.AtPrime P M) := inferInstance
  let _ : Module.Free (Localization.AtPrime P) (LocalizedModule.AtPrime P M) :=
    Module.free_of_flat_of_isLocalRing
  let p : PrimeSpectrum R := ⟨P, inferInstance⟩
  have hp :
      Module.finrank (Localization.AtPrime P) (LocalizedModule.AtPrime P M) =
        Module.rankAtStalk M p := by
    calc
      Module.finrank (Localization.AtPrime P) (LocalizedModule.AtPrime P M) =
          Module.finrank (Localization.AtPrime P)
            (TensorProduct R (Localization.AtPrime P) M) := by
              simpa using (LocalizedModule.equivTensorProduct P.primeCompl M).finrank_eq
      _ = Module.rankAtStalk M p := (Module.rankAtStalk_eq_finrank_tensorProduct (M := M) p).symm
  have hfinrank :
      Module.finrank (Localization.AtPrime P) (LocalizedModule.AtPrime P M) = r := by
    -- Proof comment: the constant stalk-rank hypothesis gives the exact size of a finite basis of
    -- the localized module over the local ring `R_P`.
    calc
      Module.finrank (Localization.AtPrime P) (LocalizedModule.AtPrime P M) =
          Module.rankAtStalk M p := hp
      _ = r := hM p
  let b : Basis (Fin r) (Localization.AtPrime P) (LocalizedModule.AtPrime P M) :=
    Module.finBasisOfFinrankEq (Localization.AtPrime P) (LocalizedModule.AtPrime P M) hfinrank
  have hlocal :
      det(LocalizedModule.AtPrime P M) =
        (⋀[Localization.AtPrime P]^r (LocalizedModule.AtPrime P M) :
          Submodule (Localization.AtPrime P)
            (ExteriorAlgebra (Localization.AtPrime P) (LocalizedModule.AtPrime P M))) :=
    by
      simpa using
        (det_eq_topExteriorPower_of_basis
          (R := Localization.AtPrime P) (M := LocalizedModule.AtPrime P M)
          (I := Fin r) b)
  -- Proof comment: after transporting both localized global submodules through the bridge, the
  -- comparison is exactly the free local model proved by `det_eq_topExteriorPower_of_basis`.
  apply (Submodule.map_injective_of_injective e.injective)
  calc
    Submodule.map e.toLinearMap
        ((det(M)).localized' (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))) =
      det(LocalizedModule.AtPrime P M) :=
        atPrime_exterior_bridge_map_det_of_span_eq_top (R := R) (M := M) P v hv
    _ = (⋀[Localization.AtPrime P]^r (LocalizedModule.AtPrime P M) :
          Submodule (Localization.AtPrime P)
            (ExteriorAlgebra (Localization.AtPrime P) (LocalizedModule.AtPrime P M))) := hlocal
    _ = Submodule.map e.toLinearMap
        (((⋀[R]^r M : Submodule R (ExteriorAlgebra R M)).localized'
          (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)))) :=
        (atPrime_exterior_bridge_map_topExteriorPower (R := R) (M := M) P r).symm

/-- Helper for Remark `15.119.1`: the explicit localized owner of the determinant line obtained
from `Submodule.toLocalized'` is canonically the same localized module as
`LocalizedModule.AtPrime P (det(M))`. -/
private noncomputable abbrev atPrime_det_localized_owner_linear_equiv
    (P : Ideal R) [P.IsPrime] :
    ((Module.det R M).localized' (Localization.AtPrime P) P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))) ≃ₗ[Localization.AtPrime P]
      LocalizedModule.AtPrime P ↥(Module.det R M) :=
  let κ :
      ↥(Module.det R M) →ₗ[R]
        (Module.det R M).localized' (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M)) :=
    Submodule.toLocalized' (Localization.AtPrime P) P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))
      (Module.det R M)
  letI : IsLocalizedModule P.primeCompl κ := inferInstance
  -- Proof comment: compare the explicit `localized'` owner with the canonical localized module
  -- before transporting it through the ambient exterior-algebra bridge.
  (IsLocalizedModule.linearEquiv P.primeCompl κ
    (LocalizedModule.mkLinearMap P.primeCompl ↥(Module.det R M))).extendScalarsOfIsLocalization
      P.primeCompl (Localization.AtPrime P)

/-- Helper for Remark `15.119.1`: once a finite spanning family of `M` is fixed, the localized
global determinant line identifies with the determinant line of the localized module. -/
private noncomputable abbrev atPrime_det_localized_linearEquiv
    (P : Ideal R) [P.IsPrime] {n : ℕ} (v : Fin n → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    LocalizedModule.AtPrime P ↥(Module.det R M) ≃ₗ[Localization.AtPrime P]
      ↥(Module.det (Localization.AtPrime P) (LocalizedModule.AtPrime P M)) :=
  -- Proof comment: first replace the explicit `localized'` owner by the canonical localized
  -- determinant module, then apply the already-proved ambient at-prime determinant comparison.
    (atPrime_det_localized_owner_linear_equiv (R := R) (M := M) P).symm.trans <|
    (atPrime_exterior_bridge (R := R) (M := M) P).ofSubmodules _ _
      (atPrime_exterior_bridge_map_det_of_span_eq_top (R := R) (M := M) P v hv)

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: for a general submonoid localization, the tensor-stage
equivalence sends the denominator-`1` exterior generator to the corresponding pure tensor. -/
@[simp] private theorem localized_exterior_tensor_equiv_apply_mk_ι
    (S : Submonoid R) (m : M) :
    LocalizedModule.equivTensorProduct S (ExteriorAlgebra R M)
        (LocalizedModule.mk (ι R m) 1) =
      (1 : Localization S) ⊗ₜ[R] ι R m := by
  -- Proof comment: this is the denominator-`1` normal form needed for every later transport
  -- through the ambient localization bridge.
  simpa [Localization.mk_one] using
    (LocalizedModule.equivTensorProduct_apply_mk (S := S)
      (M := ExteriorAlgebra R M) (x := ι R m) (s := (1 : S)))

/-- Helper for Remark `15.119.1`: localizing the ambient exterior algebra at `S` identifies it
with the exterior algebra of the localized module. -/
private noncomputable def localized_exterior_bridge
    (S : Submonoid R) :
    LocalizedModule S (ExteriorAlgebra R M) ≃ₗ[Localization S]
      ExteriorAlgebra (Localization S) (LocalizedModule S M) :=
  (LocalizedModule.equivTensorProduct S (ExteriorAlgebra R M)).trans
    (_root_.localizedExteriorAlgebraEquiv
      (R := R) (M := M) (S := S)).symm.toLinearEquiv

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: under the general localization bridge, the denominator-`1`
global exterior generator becomes the localized exterior generator. -/
@[simp] private theorem localized_exterior_bridge_apply_mk_ι
    (S : Submonoid R) (m : M) :
    localized_exterior_bridge (R := R) (M := M) S (LocalizedModule.mk (ι R m) 1) =
      ι (Localization S) (LocalizedModule.mkLinearMap S M m) := by
  -- Proof comment: both sides become the same pure tensor after applying
  -- `localizedExteriorAlgebraEquiv`.
  apply (_root_.localizedExteriorAlgebraEquiv (R := R) (M := M) (S := S)).injective
  simpa [localized_exterior_bridge, localized_exterior_tensor_equiv_apply_mk_ι,
      LinearMap.baseChange_tmul] using
    (_root_.localizedExteriorAlgebraEquiv_apply_ι (S := S)
      (M := M) (x := LocalizedModule.mkLinearMap S M m)).symm

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: under the general localization bridge, localized left
multiplication by `ι_R(m)` becomes left multiplication by the localized generator. -/
private theorem localized_exterior_bridge_mulLeft_ι
    (S : Submonoid R) (m : M) :
    (localized_exterior_bridge (R := R) (M := M) S).toLinearMap.comp
        (LocalizedModule.map S (LinearMap.mulLeft R (ι R m))) =
      (LinearMap.mulLeft (Localization S)
          (ι (Localization S) (LocalizedModule.mkLinearMap S M m))).comp
        (localized_exterior_bridge (R := R) (M := M) S).toLinearMap := by
  let F := (localized_exterior_bridge (R := R) (M := M) S).toLinearMap.comp
    (LocalizedModule.map S (LinearMap.mulLeft R (ι R m)))
  let G := (LinearMap.mulLeft (Localization S)
      (ι (Localization S) (LocalizedModule.mkLinearMap S M m))).comp
    (localized_exterior_bridge (R := R) (M := M) S).toLinearMap
  ext x
  induction x using LocalizedModule.induction_on with
  | h y s =>
      have hmk_one :
          F (LocalizedModule.mk (M := ExteriorAlgebra R M) y 1) =
            G (LocalizedModule.mk (M := ExteriorAlgebra R M) y 1) := by
        -- Proof comment: denominator-`1` representatives are enough because every localized
        -- class is a localized scalar multiple of one.
        apply (_root_.localizedExteriorAlgebraEquiv (R := R) (M := M) (S := S)).injective
        simp [F, G, localized_exterior_bridge, LocalizedModule.map_mk,
          LocalizedModule.equivTensorProduct_apply_mk, LinearMap.baseChange_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Localization.mk_one]
      have hmk :
          (LocalizedModule.mk y s : LocalizedModule S (ExteriorAlgebra R M)) =
            (Localization.mk (1 : R) s : Localization S) •
              LocalizedModule.mk y 1 := by
        -- Proof comment: rewrite an arbitrary denominator as a scalar so the denominator-`1`
        -- calculation applies unchanged.
        change LocalizedModule.mk y s =
            (Localization.mk (1 : R) s : Localization S) • LocalizedModule.mk y 1
        simpa using (LocalizedModule.mk_smul_mk (1 : R) y s (1 : S)).symm
      have hFmk :
          F (LocalizedModule.mk y s) =
            (Localization.mk (1 : R) s : Localization S) • F (LocalizedModule.mk y 1) := by
        calc
          F (LocalizedModule.mk y s) =
              F ((Localization.mk (1 : R) s : Localization S) • LocalizedModule.mk y 1) := by
                rw [hmk]
          _ = (Localization.mk (1 : R) s : Localization S) • F (LocalizedModule.mk y 1) := by
                simp [F]
      have hGmk :
          G (LocalizedModule.mk y s) =
            (Localization.mk (1 : R) s : Localization S) • G (LocalizedModule.mk y 1) := by
        calc
          G (LocalizedModule.mk y s) =
              G ((Localization.mk (1 : R) s : Localization S) • LocalizedModule.mk y 1) := by
                rw [hmk]
          _ = (Localization.mk (1 : R) s : Localization S) • G (LocalizedModule.mk y 1) := by
                simp [G]
      -- Proof comment: linearity over `Localization S` propagates the denominator-`1`
      -- comparison to all localized representatives.
      calc
        F (LocalizedModule.mk y s) =
            (Localization.mk (1 : R) s : Localization S) • F (LocalizedModule.mk y 1) := hFmk
        _ = (Localization.mk (1 : R) s : Localization S) • G (LocalizedModule.mk y 1) := by
            rw [hmk_one]
        _ = G (LocalizedModule.mk y s) := hGmk.symm

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: denominator-`1` `ιMulti` generators transport through the
general localization bridge to the corresponding localized `ιMulti` generators. -/
@[simp] private theorem localized_exterior_bridge_apply_mk_ιMulti
    (S : Submonoid R) :
    ∀ n : ℕ, ∀ v : Fin n → M,
      localized_exterior_bridge (R := R) (M := M) S
        (LocalizedModule.mk (ExteriorAlgebra.ιMulti R n v) 1) =
          ExteriorAlgebra.ιMulti (Localization S) n
            (fun i ↦ LocalizedModule.mkLinearMap S M (v i)) := by
  intro n
  induction n with
  | zero =>
      intro v
      -- Proof comment: the degree-zero generator is the unit, which the bridge preserves.
      apply (_root_.localizedExteriorAlgebraEquiv (R := R) (M := M) (S := S)).injective
      simpa [localized_exterior_bridge, LocalizedModule.equivTensorProduct_apply_mk,
        Localization.mk_one, Algebra.TensorProduct.one_def]
  | succ n ih =>
      intro v
      have htail :
          (fun i ↦ LocalizedModule.mkLinearMap S M ((Matrix.vecTail v) i)) =
            Matrix.vecTail (fun i ↦ LocalizedModule.mkLinearMap S M (v i)) := by
        -- Proof comment: localization commutes definitionally with the tail family.
        ext i
        rfl
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      -- Proof comment: reduce the successor case to the already-proved transport of localized
      -- left multiplication by the head generator.
      calc
        localized_exterior_bridge (R := R) (M := M) S
            (LocalizedModule.mk
              ((ι R (v 0)) * ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) 1) =
          (LinearMap.mulLeft (Localization S)
              (ι (Localization S) (LocalizedModule.mkLinearMap S M (v 0))))
            (localized_exterior_bridge (R := R) (M := M) S
              (LocalizedModule.mk (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) 1)) := by
              simpa [LinearMap.comp_apply, LocalizedModule.map_mk] using
                LinearMap.congr_fun
                  (localized_exterior_bridge_mulLeft_ι (R := R) (M := M) S (v 0))
                  (LocalizedModule.mk (ExteriorAlgebra.ιMulti R n (Matrix.vecTail v)) 1)
        _ = (ι (Localization S) (LocalizedModule.mkLinearMap S M (v 0))) *
              ExteriorAlgebra.ιMulti (Localization S) n
                (fun i ↦ LocalizedModule.mkLinearMap S M ((Matrix.vecTail v) i)) := by
              rw [ih (Matrix.vecTail v)]
              rfl
        _ = (ι (Localization S) (LocalizedModule.mkLinearMap S M (v 0))) *
              ExteriorAlgebra.ιMulti (Localization S) n
                (Matrix.vecTail (fun i ↦ LocalizedModule.mkLinearMap S M (v i))) := by
              rw [htail]
        _ = ExteriorAlgebra.ιMulti (Localization S) (n + 1)
              (fun i ↦ LocalizedModule.mkLinearMap S M (v i)) := by
              simpa using
                (ExteriorAlgebra.ιMulti_succ_apply
                  (R := Localization S)
                  (v := fun i ↦ LocalizedModule.mkLinearMap S M (v i))).symm

/-- Helper for Remark `15.119.1`: localization commutes with finite intersections indexed by
`Fin n` for an arbitrary submonoid localization. -/
private theorem localized'_iInf_fin_submonoid {N : Type*} [AddCommGroup N] [Module R N]
    (S : Submonoid R) :
    ∀ {n : ℕ} (K : Fin n → Submodule R N),
      (⨅ i, K i).localized' (Localization S) S
        (LocalizedModule.mkLinearMap S N) =
      ⨅ i, (K i).localized' (Localization S) S
        (LocalizedModule.mkLinearMap S N) := by
  intro n
  induction n with
  | zero =>
      intro K
      rw [show (⨅ i : Fin 0, K i) = ⊤ by simp, Submodule.localized'_top]
      rw [show (⨅ i : Fin 0,
          (K i).localized' (Localization S) S
            (LocalizedModule.mkLinearMap S N)) = ⊤ by simp]
  | succ n ih =>
      intro K
      have hiInf :
          (⨅ i : Fin (n + 1), K i) = K 0 ⊓ ⨅ i : Fin n, K i.succ := by
        ext x
        simp [Fin.forall_fin_succ]
      have hiInf' :
          (⨅ i : Fin (n + 1),
              (K i).localized' (Localization S) S
                (LocalizedModule.mkLinearMap S N)) =
            (K 0).localized' (Localization S) S
                (LocalizedModule.mkLinearMap S N) ⊓
              ⨅ i : Fin n,
                (K i.succ).localized' (Localization S) S
                  (LocalizedModule.mkLinearMap S N) := by
        ext x
        simp [Fin.forall_fin_succ]
      -- Proof comment: rewrite the finite intersection into head-plus-tail form before
      -- localizing.
      rw [hiInf, Submodule.localized'_inf, ih, hiInf']

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: if a finite family spans `M`, then its denominator-`1` images
span the localization of `M` at any submonoid `S`. -/
private theorem localized_generator_family_span_top_of_span_eq_top
    (S : Submonoid R) {n : ℕ} (v : Fin n → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span (Localization S)
      (Set.range (fun i ↦ LocalizedModule.mkLinearMap S M (v i))) = ⊤ := by
  have hloc := congrArg
    (fun N : Submodule R M =>
      N.localized' (Localization S) S (LocalizedModule.mkLinearMap S M)) hv
  -- Proof comment: localizing the global spanning relation replaces each generator by its
  -- denominator-`1` image and turns the localized top module into `⊤`.
  calc
    Submodule.span (Localization S)
        (Set.range (fun i ↦ LocalizedModule.mkLinearMap S M (v i))) =
      Submodule.span (Localization S)
        ((fun a ↦ LocalizedModule.mk a 1) '' Set.range v) := by
          congr 1
          ext x
          constructor
          · rintro ⟨i, rfl⟩
            exact ⟨v i, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
            exact ⟨i, rfl⟩
    _ = ⊤ := by
          simpa [Submodule.localized'_span] using hloc

omit [Module.Finite R M] [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: once a finite spanning family is fixed, transporting the
localized global determinant line through the general localization bridge gives the determinant
line of the localized module. -/
private theorem localized_exterior_bridge_map_det_of_span_eq_top
    (S : Submonoid R) {n : ℕ} (v : Fin n → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.map (localized_exterior_bridge (R := R) (M := M) S).toLinearMap
      (((det(M)).localized' (Localization S) S
        (LocalizedModule.mkLinearMap S (ExteriorAlgebra R M)))) =
      det(LocalizedModule S M) := by
  let e := localized_exterior_bridge (R := R) (M := M) S
  have hspanLocal :
      Submodule.span (Localization S)
        (Set.range (fun i ↦ LocalizedModule.mkLinearMap S M (v i))) = ⊤ :=
    localized_generator_family_span_top_of_span_eq_top (R := R) (M := M) S v hv
  calc
    Submodule.map e.toLinearMap
        (((det(M)).localized' (Localization S) S
          (LocalizedModule.mkLinearMap S (ExteriorAlgebra R M)))) =
      Submodule.map e.toLinearMap
        (⨅ i : Fin n,
          ((LinearMap.mulLeft R (ι R (v i))).ker).localized'
            (Localization S) S
            (LocalizedModule.mkLinearMap S (ExteriorAlgebra R M))) := by
          -- Proof comment: replace the determinant line by the finite intersection of kernels
          -- coming from the chosen spanning family before localizing.
          rw [det_eq_iInf_mulLeft_ker_of_span_eq_top (R := R) (M := M) v hv,
            localized'_iInf_fin_submonoid (R := R) (N := ExteriorAlgebra R M) S]
    _ = ⨅ i : Fin n,
        Submodule.map e.toLinearMap
          (((LinearMap.mulLeft R (ι R (v i))).ker).localized'
            (Localization S) S
            (LocalizedModule.mkLinearMap S (ExteriorAlgebra R M))) := by
          rw [map_iInf_fin e]
    _ = ⨅ i : Fin n,
        (LinearMap.mulLeft (Localization S)
          (ι (Localization S) (LocalizedModule.mkLinearMap S M (v i)))).ker := by
          apply iInf_congr
          intro i
          have hker :
              ((LinearMap.mulLeft R (ι R (v i))).ker).localized'
                  (Localization S) S
                  (LocalizedModule.mkLinearMap S (ExteriorAlgebra R M)) =
                LinearMap.ker
                  (LocalizedModule.map S
                    (LinearMap.mulLeft R (ι R (v i)))) := by
            -- Proof comment: localization commutes with kernels for the localized left
            -- multiplication map.
            simpa using
              (LinearMap.localized'_ker_eq_ker_localizedMap
                (S := Localization S) (p := S)
                (f := LocalizedModule.mkLinearMap S (ExteriorAlgebra R M))
                (f' := LocalizedModule.mkLinearMap S (ExteriorAlgebra R M))
                (g := LinearMap.mulLeft R (ι R (v i))))
          rw [hker]
          exact map_ker_eq_of_intertwine e
            (LocalizedModule.map S (LinearMap.mulLeft R (ι R (v i))))
            (LinearMap.mulLeft (Localization S)
              (ι (Localization S) (LocalizedModule.mkLinearMap S M (v i))))
            (localized_exterior_bridge_mulLeft_ι (R := R) (M := M) S (v i))
    _ = det(LocalizedModule S M) := by
          rw [(det_eq_iInf_mulLeft_ker_of_span_eq_top
            (R := Localization S) (M := LocalizedModule S M)
            (v := fun i ↦ LocalizedModule.mkLinearMap S M (v i))
            hspanLocal).symm]

/-- Helper for Remark `15.119.1`: the explicit localized determinant owner obtained from
`Submodule.toLocalized'` is canonically equivalent to the canonical localized module
`LocalizedModule S (det(M))`. -/
private noncomputable abbrev localized_det_localized_owner_linear_equiv
    (S : Submonoid R) :
    ((Module.det R M).localized' (Localization S) S
      (LocalizedModule.mkLinearMap S (ExteriorAlgebra R M))) ≃ₗ[Localization S]
      LocalizedModule S ↥(Module.det R M) :=
  let κ :
      ↥(Module.det R M) →ₗ[R]
        (Module.det R M).localized' (Localization S) S
          (LocalizedModule.mkLinearMap S (ExteriorAlgebra R M)) :=
    Submodule.toLocalized' (Localization S) S
      (LocalizedModule.mkLinearMap S (ExteriorAlgebra R M))
      (Module.det R M)
  letI : IsLocalizedModule S κ := inferInstance
  -- Proof comment: isolate the owner-level transport from the explicit `localized'` submodule to
  -- the canonical localized determinant module before using the ambient bridge.
  (IsLocalizedModule.linearEquiv S κ
    (LocalizedModule.mkLinearMap S ↥(Module.det R M))).extendScalarsOfIsLocalization
      S (Localization S)

/-- Helper for Remark `15.119.1`: localizing the determinant-line owner at a principal open
`D(f)` identifies it with the determinant-line owner of the localized module. -/
private noncomputable abbrev away_det_localized_linearEquiv
    (f : R) :
    LocalizedModule.Away f ↥(Module.det R M) ≃ₗ[Localization.Away f]
      ↥(Module.det (Localization.Away f) (LocalizedModule.Away f M)) :=
  let hfinite := Module.Finite.exists_fin (R := R) (M := M)
  let v := Classical.choose (Classical.choose_spec hfinite)
  let hv := Classical.choose_spec (Classical.choose_spec hfinite)
  -- Proof comment: first replace the explicit localized owner by the canonical localized module,
  -- then transport it through the ambient exterior-algebra localization bridge.
  (localized_det_localized_owner_linear_equiv (R := R) (M := M) (Submonoid.powers f)).symm.trans <|
    (localized_exterior_bridge (R := R) (M := M) (Submonoid.powers f)).ofSubmodules _ _
      (localized_exterior_bridge_map_det_of_span_eq_top (R := R) (M := M)
        (Submonoid.powers f) v hv)

omit [Module.Projective R M] in
/-- Helper for Remark `15.119.1`: on a standard-open cover piece where `M` is finite free, the
localized determinant line is free of rank `1`. -/
-- Proof comment: choose a finite basis of the localized module, trivialize its local determinant
-- line by the basis-independent helper above, and isolate the remaining work to transporting the
-- global annihilator owner through localization.
private theorem away_det_linearEquiv_fin_one_of_cover_piece
    (f : R)
    [Module.Free (Localization.Away f) (LocalizedModule.Away f M)]
    [Module.Finite (Localization.Away f) (LocalizedModule.Away f M)] :
    Nonempty (LocalizedModule.Away f (Module.det R M) ≃ₗ[Localization.Away f]
      (Fin 1 → Localization.Away f)) := by
  classical
  rcases subsingleton_or_nontrivial (Localization.Away f) with hA | hA
  · letI : Subsingleton (Localization.Away f) := hA
    letI : Subsingleton (LocalizedModule.Away f (Module.det R M)) :=
      Module.subsingleton (Localization.Away f) (LocalizedModule.Away f (Module.det R M))
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · letI : Nontrivial (Localization.Away f) := hA
    let b :
        Basis (Module.Free.ChooseBasisIndex (Localization.Away f) (LocalizedModule.Away f M))
          (Localization.Away f) (LocalizedModule.Away f M) :=
      Module.Free.chooseBasis (Localization.Away f) (LocalizedModule.Away f M)
    letI :
        Finite (Module.Free.ChooseBasisIndex (Localization.Away f) (LocalizedModule.Away f M)) :=
      Module.Finite.finite_basis b
    let bFin :
        Basis (Fin (Fintype.card
          (Module.Free.ChooseBasisIndex (Localization.Away f) (LocalizedModule.Away f M))))
          (Localization.Away f) (LocalizedModule.Away f M) :=
      b.reindex (Fintype.equivFin
        (Module.Free.ChooseBasisIndex (Localization.Away f) (LocalizedModule.Away f M)))
    rcases det_linearEquiv_fin_one_of_basis
        (A := Localization.Away f) (N := LocalizedModule.Away f M) bFin with ⟨eLocal⟩
    -- Proof comment: the away-local determinant bridge lands exactly in the local determinant
    -- line, so the local rank-one trivialization closes the argument immediately.
    exact ⟨(away_det_localized_linearEquiv (R := R) (M := M) f).trans eLocal⟩

/-- Helper for Remark `15.119.1`: the determinant line of a finite projective module is finite
locally free of rank `1`. -/
-- Proof comment: finite projective modules are finite locally free on a standard-open cover, and
-- the previous lemma reduces each cover piece for `det(M)` to the single away-local determinant
-- comparison still isolated above.
private theorem det_finiteLocallyFreeOfRank_one :
    Module.FiniteLocallyFreeOfRank R (Module.det R M) 1 := by
  letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  letI : Module.Flat R M := Module.Flat.of_projective (R := R) (M := M)
  letI : Module.FiniteLocallyFree R M :=
    Module.finiteLocallyFree_of_finitePresentation_of_flat (R := R) (M := M)
  obtain ⟨s, hs_span, hs_triv⟩ :=
    Module.FiniteLocallyFree.exists_standardOpen_cover (R := R) (M := M)
  refine ⟨s, hs_span, ?_⟩
  intro f hf
  rcases hs_triv f hf with ⟨hfree, hfinite⟩
  letI : Module.Free (Localization.Away f) (LocalizedModule.Away f M) := hfree
  letI : Module.Finite (Localization.Away f) (LocalizedModule.Away f M) := hfinite
  exact away_det_linearEquiv_fin_one_of_cover_piece (R := R) (M := M) f

/-- Under a constant rank hypothesis, the determinant line agrees with the top exterior power
inside `ExteriorAlgebra R M`. This presents the exterior-algebra annihilator owner as the
standard top-exterior-power model under stronger assumptions. -/
theorem det_eq_topExteriorPower_of_rankAtStalk_eq (r : ℕ)
    (hM : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) :
    det(M) = ⋀[R]^r M := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  -- Proof comment: the determinant-line owner can already be normalized against a finite spanning
  -- family; the remaining work is the maximal-localization comparison isolated below.
  have hdet_fin :
      det(M) = ⨅ i : Fin n, (LinearMap.mulLeft R (ι R (v i))).ker :=
    det_eq_iInf_mulLeft_ker_of_span_eq_top (R := R) (M := M) v hv
  let _ := hdet_fin
  refine Submodule.eq_of_localization_maximal
    (Rₚ := fun P => Localization.AtPrime P)
    (Mₚ := fun P => LocalizedModule.AtPrime P (ExteriorAlgebra R M))
    (f := fun P => LocalizedModule.mkLinearMap P.primeCompl (ExteriorAlgebra R M))
    ?_
  intro P _
  exact localized_det_eq_localized_topExteriorPower_at_maximal
    (R := R) (M := M) r hM P

/-- The determinant line of a finite projective module is invertible as an `R`-module. Via
Definition `15.118.1`, this is equivalent to the Chapter `15` tensor-left invertibility owner. -/
instance det_invertible : Module.Invertible R (Module.det R M) :=
  by
    -- Route correction: stop localizing `contractLeft` itself. Instead, prove `det(M)` is finite
    -- locally free of rank `1` on the same standard-open cover as `M`, then invoke Lemma 15.118.2.
    letI : Module.FiniteLocallyFreeOfRank R (Module.det R M) 1 :=
      det_finiteLocallyFreeOfRank_one (R := R) (M := M)
    simpa using ModuleCat.moduleInvertible_of_finiteLocallyFreeOfRank_one
      (R := R) (M := ModuleCat.of R (Module.det R M))

end

end Module

end

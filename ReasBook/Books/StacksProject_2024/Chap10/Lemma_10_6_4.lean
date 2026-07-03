import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.FiniteType

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Algebra.FiniteType R S]

namespace Module.FinitePresentation

open scoped TensorProduct

/- Domain-style sampling:
- primary domain: finite presentation of modules under change of scalars along a finite-type
  algebra map;
- sampled owner declarations:
  `Module.FinitePresentation`,
  `Module.Finite.of_restrictScalars_finite`,
  `Algebra.FiniteType.of_restrictScalars_finiteType`,
  `Module.FinitePresentation.trans`;
- best owner abstraction: `Module.FinitePresentation`;
- primitive data: an `S`-module structure on `M`, finite presentation of `M` over `R`, and the
  finite-type algebra map `R → S`;
- derived API: finite presentation of `M` over `S`, and downstream equivalences such as
  `Lemma_10_36_23` obtained by combining this bridge with `Module.FinitePresentation.trans`.

Source/core/bridge triage:
- `source-facing`: the scalar-restriction permanence statement below for finitely presented
  modules;
- `core/canonical`: the owner predicates `Module.FinitePresentation` and `Algebra.FiniteType`;
- `bridge/view`: this theorem upgrades the base-ring finite-presentation hypothesis to the
  algebra-ring finite-presentation conclusion. There is no upstream exact theorem with this
  interface, so the chapter keeps this bridge theorem instead of replacing it by a recall item.
-/
/-
Proof sketch: finite type means the `S`-action on `M` is controlled by finitely many algebra
generators of `S` over `R`. Inside `Hom_R(M, -)`, the condition that an `R`-linear map is
`S`-linear is therefore cut out by finitely many commutation equalities. Since `M` is finitely
presented over `R`, these finite equalizer conditions preserve filtered colimits, which upgrades
the `R`-finite-presentation owner to `Module.FinitePresentation S M`.
-/
variable (R)

/-- Lemma 10.6.4 (0561): if `R → S` is of finite type and an `S`-module `M` is finitely
presented over `R`, then `M` is finitely presented over `S`. -/
theorem of_restrictScalars_finiteType [Module.FinitePresentation R M] :
    Module.FinitePresentation S M := by
  -- Follow the source proof through the canonical action map `S ⊗[R] M → M`.
  let μ : (S ⊗[R] M) →ₗ[S] M :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.restrictScalarsₗ R S M M S ∘ₗ LinearMap.lsmul S M)
  -- The action map is always surjective: `m` is the image of `1 ⊗ m`.
  have hμ_surj : Function.Surjective μ := by
    intro m
    refine ⟨1 ⊗ₜ[R] m, ?_⟩
    simp [μ]
  have hker_fg : (LinearMap.ker μ).FG := by
    classical
    obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := S)
    obtain ⟨σ, hσ, _⟩ := (inferInstance : Module.FinitePresentation R M)
    let rel : t × σ → S ⊗[R] M := fun p ↦
      ((p.1 : S) ⊗ₜ[R] (p.2 : M)) - 1 ⊗ₜ[R] ((p.1 : S) • (p.2 : M))
    let K : Submodule S (S ⊗[R] M) := Submodule.span S (Set.range rel)
    -- Each algebra generator acts on every module element through the finite relation family.
    have hgen : ∀ a ∈ t, ∀ m : M, a ⊗ₜ[R] m - 1 ⊗ₜ[R] (a • m) ∈ K := by
      intro a ha m
      let δ : M →ₗ[R] S ⊗[R] M :=
        TensorProduct.mk R S M a -
          (TensorProduct.mk R S M 1).comp
            (LinearMap.restrictScalarsₗ R S M M S (LinearMap.lsmul S M a))
      have htop : (⊤ : Submodule R M) ≤ Submodule.comap δ (K.restrictScalars R) := by
        rw [← hσ, Submodule.span_le]
        intro x hx
        change δ x ∈ K
        apply Submodule.subset_span
        exact ⟨(⟨a, ha⟩, ⟨x, hx⟩), rfl⟩
      exact htop trivial
    -- Route correction: instead of pushing directly on arbitrary tensors, first close the
    -- source-faithful adjoin step for the action relations and then run tensor induction.
    have hrel_adjoin : ∀ a : S, a ∈ Algebra.adjoin R (t : Set S) →
        ∀ m : M, a ⊗ₜ[R] m - 1 ⊗ₜ[R] (a • m) ∈ K := by
      intro a ha
      refine Algebra.adjoin_induction
        (fun x hx m ↦ hgen x hx m)
        (fun r m ↦ by
          -- Scalars from `R` already act through the tensor-product balancing relation.
          have : (algebraMap R S r) ⊗ₜ[R] m - 1 ⊗ₜ[R] ((algebraMap R S r) • m) = 0 := by
            simp [Algebra.smul_def, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
          rw [this]
          exact Submodule.zero_mem K)
        (fun x y hx hy hxK hyK m ↦ by
          -- Addition is handled by adding the two already-known relations.
          have hdecomp :
              (x + y) ⊗ₜ[R] m - 1 ⊗ₜ[R] ((x + y) • m) =
                (x ⊗ₜ[R] m - 1 ⊗ₜ[R] (x • m)) + (y ⊗ₜ[R] m - 1 ⊗ₜ[R] (y • m)) := by
            simp [sub_eq_add_neg, TensorProduct.add_tmul, TensorProduct.tmul_add, add_smul,
              add_assoc, add_left_comm, add_comm]
          rw [hdecomp]
          exact K.add_mem (hxK m) (hyK m))
        (fun x y hx hy hxK hyK m ↦ by
          -- Multiplication lowers to the relation for `y` plus the relation for `x` on `y • m`.
          have hy' : x • (y ⊗ₜ[R] m - 1 ⊗ₜ[R] (y • m)) ∈ K :=
            K.smul_mem x (hyK m)
          have hx' : x ⊗ₜ[R] (y • m) - 1 ⊗ₜ[R] (x • (y • m)) ∈ K :=
            hxK (y • m)
          have hdecomp :
              (x * y) ⊗ₜ[R] m - 1 ⊗ₜ[R] ((x * y) • m) =
                x • (y ⊗ₜ[R] m - 1 ⊗ₜ[R] (y • m)) +
                  (x ⊗ₜ[R] (y • m) - 1 ⊗ₜ[R] (x • (y • m))) := by
            simp [sub_eq_add_neg, TensorProduct.smul_tmul', mul_smul,
              add_assoc, add_left_comm, add_comm]
          rw [hdecomp]
          exact K.add_mem hy' hx')
        ha
    have hrel_all : ∀ a m, a ⊗ₜ[R] m - 1 ⊗ₜ[R] (a • m) ∈ K := by
      intro a m
      have ha_top : a ∈ (⊤ : Subalgebra R S) := by simp
      have ha_adjoin : a ∈ Algebra.adjoin R (t : Set S) := by
        simp [ht] at ha_top ⊢
      exact hrel_adjoin a ha_adjoin m
    have hK_le_ker : K ≤ LinearMap.ker μ := by
      -- Every chosen relation is killed by the action map `μ`.
      refine Submodule.span_le.2 ?_
      rintro _ ⟨p, rfl⟩
      change μ (rel p) = 0
      simp [μ, rel]
    have hker_le_K : LinearMap.ker μ ≤ K := by
      -- Any tensor is congruent modulo `K` to `1 ⊗ μ x`, so kernel elements lie in `K`.
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hreduce : x - 1 ⊗ₜ[R] μ x ∈ K := by
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp [μ]
        · intro a m
          simpa [μ] using hrel_all a m
        · intro x y hxK hyK
          have hdecomp :
              (x + y) - 1 ⊗ₜ[R] μ (x + y) =
                (x - 1 ⊗ₜ[R] μ x) + (y - 1 ⊗ₜ[R] μ y) := by
            simp [sub_eq_add_neg, map_add, TensorProduct.tmul_add,
              add_assoc, add_left_comm, add_comm]
          rw [hdecomp]
          exact K.add_mem hxK hyK
      simpa [hx] using hreduce
    have hker_eq : LinearMap.ker μ = K :=
      le_antisymm hker_le_K hK_le_ker
    rw [hker_eq]
    exact Submodule.fg_span (Set.finite_range rel)
  let _ : Module.FinitePresentation S (S ⊗[R] M) := inferInstance
  exact Module.finitePresentation_of_surjective μ hμ_surj hker_fg

end Module.FinitePresentation

end

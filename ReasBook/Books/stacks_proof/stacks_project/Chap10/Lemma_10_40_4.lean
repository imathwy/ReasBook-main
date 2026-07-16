import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-
Domain triage: this file lies in the commutative-algebra domain of annihilators under flat base
change. The `source-facing` textbook content is the annihilator comparison in Lemma 10.40.4. The
owner abstractions are the canonical mathlib/project declarations `Ideal.torsionOf`,
`Module.annihilator`, and `Ideal.mapInfTopHom`; the file should derive its finite-intersection step
from that owner map rather than keep a parallel local ideal-map API. Primitive data are only the
flat algebra structure and the module. Derived API consists of the two public annihilator theorems
below. -/

namespace Ideal

private noncomputable def quotientTensorSingletonEquiv
    (m : M) :
    (S ⧸ Ideal.map (algebraMap R S) (torsionOf R M m)) ≃ₗ[S]
      S ∙ ((1 : S) ⊗ₜ[R] m) :=
  let I := torsionOf R M m
  let e₁ : (S ⧸ Ideal.map (algebraMap R S) I) ≃ₗ[S] S ⊗[R] (R ⧸ I) :=
    Ideal.qoutMapEquivTensorQout S
  let e₂ : S ⊗[R] (R ⧸ I) ≃ₗ[S] S ⊗[R] ↥(R ∙ m) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (Ideal.quotTorsionOfEquivSpanSingleton R M m)
  let e₃ : S ⊗[R] ↥(R ∙ m) ≃ₗ[S] (R ∙ m).baseChange S :=
    Submodule.toBaseChange.toLinearEquiv S (R ∙ m)
  let e₄ : (R ∙ m).baseChange S ≃ₗ[S] S ∙ ((1 : S) ⊗ₜ[R] m) :=
    LinearEquiv.ofEq ((R ∙ m).baseChange S) (S ∙ ((1 : S) ⊗ₜ[R] m))
      (by
        change (Submodule.span R ({m} : Set M)).baseChange S =
          S ∙ ((1 : S) ⊗ₜ[R] m)
        rw [Submodule.baseChange_span]
        congr
        ext x
        simp)
  e₁.trans <| e₂.trans <| e₃.trans e₄

/-- Lemma 10.40.4 (Tag 07T8): for a flat ring map `R → S`, extending the annihilator ideal of
`m : M` agrees with the annihilator ideal of the base-changed element `1 ⊗ₜ[R] m`
in `S ⊗[R] M`.

This is the canonical Lean form of the first assertion in the textbook lemma, using
`Ideal.torsionOf` for the annihilator of an element. -/
-- Proof sketch: consider the exact sequence
-- `0 → Ideal.torsionOf R M m → R → M` sending `r` to `r • m`, tensor it with `S`, and identify
-- the kernel of `S → S ⊗[R] M` sending `s` to `s • (1 ⊗ₜ[R] m)` with
-- `Ideal.torsionOf S (S ⊗[R] M) (1 ⊗ₜ[R] m)`.
@[stacks 07T8 "element-annihilator assertion"]
theorem map_torsionOf_eq_torsionOf_baseChange_of_flat
    (m : M) :
    map (algebraMap R S) (torsionOf R M m) =
      torsionOf S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] m) := by
  let e :
      (S ⧸ map (algebraMap R S) (torsionOf R M m)) ≃ₗ[S]
        S ∙ ((1 : S) ⊗ₜ[R] m) :=
    quotientTensorSingletonEquiv m
  have hq :
      Module.annihilator S (S ⧸ map (algebraMap R S) (torsionOf R M m)) =
        map (algebraMap R S) (torsionOf R M m) :=
    annihilator_quotient
  rw [← hq, e.annihilator_eq]
  simpa [torsionOf] using
    (Submodule.annihilator_span_singleton ((1 : S) ⊗ₜ[R] m))

end Ideal

namespace Module

/-- Canonical Lean form of the finite-module assertion in Lemma 10.40.4: if `M` is finite over
`R`, then extending `annihilator R M` along a flat map `R → S` agrees with the annihilator of the
base-changed module `S ⊗[R] M`. -/
-- Proof sketch: choose finitely many generators of `M`, express both annihilators as
-- intersections of the annihilators of those generators, apply
-- `Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat` termwise, and then use Lemma 10.39.2 to
-- move extension of ideals across the finite intersection.
@[stacks 07T8 "finite-module assertion"]
theorem map_annihilator_eq_annihilator_baseChange_of_flat [Module.Finite R M] :
    Ideal.map (algebraMap R S) (annihilator R M) =
      annihilator S (S ⊗[R] M) := by
  have hsFinite : ∃ n : ℕ, ∃ s : Fin n → M, Submodule.span R (Set.range s) = ⊤ :=
    Module.Finite.exists_fin
  obtain ⟨n, s, hs⟩ := hsFinite
  have hsTensor : Submodule.span S (Set.range fun i : Fin n ↦ (1 : S) ⊗ₜ[R] s i) = ⊤ := by
    rw [← Submodule.baseChange_top, ← hs, Submodule.baseChange_span]
    congr
    ext x
    simp
  have hann :
      annihilator R M = ⨅ i : Fin n, Ideal.torsionOf R M (s i) := by
    rw [← Submodule.annihilator_top, ← hs, Submodule.annihilator_span]
    ext r
    simp [Ideal.torsionOf, Set.mem_range]
  have hbase :
      annihilator S (S ⊗[R] M) =
        ⨅ i : Fin n, Ideal.torsionOf S (S ⊗[R] M) ((1 : S) ⊗ₜ[R] s i) := by
    rw [← Submodule.annihilator_top, ← hsTensor, Submodule.annihilator_span]
    ext r
    simp [Ideal.torsionOf, Set.mem_range]
  rw [hann, hbase]
  rw [show Ideal.map (algebraMap R S) (⨅ i, Ideal.torsionOf R M (s i)) =
      ⨅ i, Ideal.map (algebraMap R S) (Ideal.torsionOf R M (s i)) by
        simpa [Finset.inf_eq_iInf] using
          map_finset_inf Ideal.mapInfTopHom Finset.univ
            (fun i ↦ Ideal.torsionOf R M (s i))]
  ext x
  simp [Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat]

end Module

end

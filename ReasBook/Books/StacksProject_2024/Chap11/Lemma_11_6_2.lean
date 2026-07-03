import Mathlib
import StacksProject_2024.Chap11.Theorem_11_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open ConjAct

variable {k : Type u} [Field k]
variable {A : CSA.{u, v} k}

/- Domain-style sampling for Lemma 11.6.2:
- primary domain: inner automorphisms of finite central simple algebras, obtained from the
  canonical conjugation action of units;
- sampled owner declarations:
  `CSA.algHom_inner_conjugate`,
  `MulSemiringAction.toAlgEquiv`,
  `ConjAct.toConjAct`,
  `ConjAct.toConjAct_smul`;
- best owner abstraction: the core/canonical owner is the conjugation automorphism
  `MulSemiringAction.toAlgEquiv k A (toConjAct x)` of a finite central simple algebra `A`;
- primitive data: `A : CSA k` and `σ : A ≃ₐ[k] A`;
- derived API: the source-facing pointwise inner formula and its matrix-algebra specialization.

Source/core/bridge triage:
- `source-facing`: the pointwise formula saying every automorphism is conjugation by a unit;
- `core/canonical`: equality of algebra automorphisms with
  `MulSemiringAction.toAlgEquiv k A (toConjAct x)`;
- `bridge/view`: evaluating that equality at an element `a : A`. -/

-- Proof sketch: apply the Skolem-Noether conjugacy theorem of the previous item to the two
-- `k`-algebra homomorphisms `σ.toAlgHom` and `AlgHom.id k A`; the returned unit conjugates the
-- identity map to `σ`, hence `σ` is exactly the canonical conjugation algebra equivalence attached
-- to that unit.
theorem algEquiv_inner_conjugate (σ : A ≃ₐ[k] A) :
    ∃ x : Aˣ, σ = MulSemiringAction.toAlgEquiv k A (toConjAct x) := by
  rcases A.algHom_inner_conjugate σ.toAlgHom (AlgHom.id k A) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  ext a
  simpa [AlgHom.comp_apply] using DFunLike.congr_fun hx a

-- Proof sketch: specialize the canonical automorphism-level conjugacy statement above and evaluate
-- the resulting equality at each element of `A`.
/-- Lemma 11.6.2: any `k`-algebra automorphism of a finite central simple `k`-algebra is inner. -/
theorem algEquiv_isInner_of_finite_central_simple (σ : A ≃ₐ[k] A) :
    ∃ x : Aˣ, ∀ a : A, σ a = ↑x * a * ↑(x⁻¹) := by
  rcases algEquiv_inner_conjugate σ with ⟨x, rfl⟩
  exact ⟨x, fun a ↦ by simp [ConjAct.units_smul_def]⟩

-- Proof sketch: specialize the general finite-central-simple statement to the matrix algebra
-- `Matrix (Fin n) (Fin n) k`, using the standard mathlib instances showing that this algebra is
-- finite-dimensional, central, and simple over the field `k`.
/-- Every `k`-algebra automorphism of a full matrix algebra over a field is inner. -/
theorem matrix_algEquiv_isInner (n : ℕ)
    (σ : Matrix (Fin n) (Fin n) k ≃ₐ[k] Matrix (Fin n) (Fin n) k) :
    ∃ x : (Matrix (Fin n) (Fin n) k)ˣ,
      ∀ M : Matrix (Fin n) (Fin n) k,
        σ M = (x : Matrix (Fin n) (Fin n) k) * M * (↑(x⁻¹) : Matrix (Fin n) (Fin n) k) := by
  cases n with
  | zero =>
      refine ⟨1, fun M ↦ ?_⟩
      exact Subsingleton.elim _ _
  | succ n =>
      let A : CSA.{u, u} k := .mk (AlgCat.of k (Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      change A ≃ₐ[k] A at σ
      simpa [A] using algEquiv_isInner_of_finite_central_simple σ

end

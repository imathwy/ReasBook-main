import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

/-
Domain sampling for this item:
* primary domain: polynomial factorization over a commutative ring at a chosen root;
* sampled owner declarations: `mul_divByMonic_eq_iff_isRoot`, `dvd_iff_isRoot`, `monic_X_sub_C`, and
  `Monic.of_mul_monic_left`;
* layer triage:
  - `source-facing`: the textbook existential factorization statement;
  - `core/canonical`: the canonical quotient-factorization owner
    `mul_divByMonic_eq_iff_isRoot`;
  - `bridge/view`: the monicity of the canonical quotient `P /ₘ (X - C α)`, derived from
    `Monic.of_mul_monic_left`.
* owner decision: keep the textbook existential theorem as the public source-facing item and derive
  it directly from the canonical `Polynomial` quotient factorization at a root rather than choosing
  an arbitrary divisibility witness.
-/

/-- Lemma 15.21.1: a monic polynomial `P` over a commutative ring with root `α` factors as
`(X - C α) * Q` for some monic polynomial `Q`. -/
@[stacks 052Z]
theorem exists_monic_factor_of_isRoot {R : Type u} [CommRing R] (P : R[X]) (hP : P.Monic)
    {α : R} (hα : P.IsRoot α) :
    ∃ Q : R[X], Q.Monic ∧ P = (X - C α) * Q := by
  refine ⟨P /ₘ (X - C α), (monic_X_sub_C α).of_mul_monic_left ?_, ?_⟩
  · simpa [mul_divByMonic_eq_iff_isRoot.mpr hα] using hP
  exact (mul_divByMonic_eq_iff_isRoot.mpr hα).symm

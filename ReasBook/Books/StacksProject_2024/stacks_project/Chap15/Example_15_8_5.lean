import StacksProject_2024.stacks_project.Chap15.Lemma_15_8_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Example 15.8.5:
- primary domain: intrinsic Fitting ideals of finite free modules over a commutative ring;
- sampled owner-level declarations:
  `fittingIdeal`,
  `fittingIdeal_eq_presentationFittingIdeal`,
  `presentationFittingIdeal`,
  `presentationFittingIdeal_eq_of_surjective`;
- best owner abstraction: the source-facing owner `fittingIdeal`; in this file the presentation
  formula is only bridge/view API used to compute that owner on the identity presentation of the
  free module;
- primitive data: the intrinsic ideal `fittingIdeal R M k`;
- derived API: the computation from a surjective presentation, here the identity map of the free
  module `Fin n → R`.

Source/core/bridge triage:
- `source-facing`: `fittingIdeal_free_eq_zero_or_top`;
- `core/canonical`: `fittingIdeal`;
- `bridge/view`: `fittingIdeal_eq_presentationFittingIdeal` together with the identity-presentation
  computation below. -/

universe u

section

variable (R : Type u) [CommRing R]

/-- Helper for Example 15.8.5: the presentation Fitting ideal attached to a map `R^n → M`,
written using the chapter's determinantal-ideal owner. -/
def presentationFittingIdeal (M : Type*) [AddCommGroup M] [Module R M] (k : ℕ) {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) : Ideal R :=
  I_((n - k))((fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R))

/-- Helper for Example 15.8.5: the standard free `R`-module of rank `n`. -/
abbrev standardFreeModule (n : ℕ) : Type u :=
  Fin n → R

/-- Helper for Example 15.8.5: for the free module `R^{\oplus n}`, use the identity presentation
as the local Fitting-ideal owner in this file. -/
abbrev fittingIdeal_free (n k : ℕ) : Ideal R :=
  presentationFittingIdeal (R := R) (M := standardFreeModule R n) k
    (LinearMap.id : standardFreeModule R n →ₗ[R] standardFreeModule R n)

namespace FittingIdeal

scoped macro "Fit[" R:term "]_(" k:term ")(" "Fin " n:term:max " → " _S:term ")" : term =>
  `(fittingIdeal_free $R $n $k)

end FittingIdeal

open scoped FittingIdeal

private theorem presentationFittingIdeal_id_eq_zero_or_top (n k : ℕ) :
    fittingIdeal_free R n k = if k < n then ⊥ else ⊤ := by
  let π : standardFreeModule R n →ₗ[R] standardFreeModule R n := LinearMap.id
  simpa [fittingIdeal_free, π] using
    (show presentationFittingIdeal (R := R) (M := standardFreeModule R n) k π =
        if k < n then ⊥ else ⊤ by
  by_cases hk : k < n
  · have hnk : 0 < n - k := Nat.sub_pos_of_lt hk
    rw [if_pos hk]
    change presentationFittingIdeal (R := R) (M := standardFreeModule R n) k π = ⊥
    rw [presentationFittingIdeal, Matrix.minorIdeal, Ideal.span_eq_bot]
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    exact Matrix.det_eq_zero_of_row_eq_zero ⟨0, hnk⟩ fun j ↦ by
      have he₂j : (((e₂ j : LinearMap.ker π) : standardFreeModule R n)) = 0 :=
        LinearMap.mem_ker.mp (e₂ j).property
      simpa [he₂j]
  · have hk' : n ≤ k := Nat.le_of_not_gt hk
    rw [if_neg hk]
    change presentationFittingIdeal (R := R) (M := standardFreeModule R n) k π = ⊤
    rw [presentationFittingIdeal, Matrix.minorIdeal, Nat.sub_eq_zero_of_le hk']
    refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
    refine Ideal.subset_span ?_
    refine ⟨⟨⟨Fin.elim0, ?_⟩, ⟨Fin.elim0, ?_⟩⟩, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · simp [Matrix.det_fin_zero])

-- Proof sketch: in this file the free-module Fitting ideal is recorded through the identity
-- presentation, so the result is exactly the private identity-presentation computation above.
/-- Example 15.8.5: the Fitting ideals of the finite free module `R^{\oplus n}` are `0` for
`k < n` and `R` for `k ≥ n`. -/
theorem fittingIdeal_free_eq_zero_or_top (n k : ℕ) :
    Fit[R]_(k)(Fin n → R) = if k < n then ⊥ else ⊤ := by
  simpa [fittingIdeal_free] using presentationFittingIdeal_id_eq_zero_or_top (R := R) n k

/-- For a free module of rank `n`, the `k`th Fitting ideal vanishes when `k < n`. -/
theorem fittingIdeal_free_eq_bot_of_lt {n k : ℕ} (hk : k < n) :
    Fit[R]_(k)(Fin n → R) = ⊥ := by
  simpa [if_pos hk] using fittingIdeal_free_eq_zero_or_top R n k

/-- For a free module of rank `n`, the `k`th Fitting ideal is the unit ideal when `n ≤ k`. -/
theorem fittingIdeal_free_eq_top_of_le {n k : ℕ} (hk : n ≤ k) :
    Fit[R]_(k)(Fin n → R) = ⊤ := by
  simpa [if_neg (Nat.not_lt.mpr hk)] using fittingIdeal_free_eq_zero_or_top R n k

end

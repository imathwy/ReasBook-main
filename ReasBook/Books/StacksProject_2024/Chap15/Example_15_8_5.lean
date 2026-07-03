import stacks_project.Chap15.Definition_15_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FittingIdeal

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

private theorem presentationFittingIdeal_id_eq_zero_or_top (n k : ℕ) :
    presentationFittingIdeal R (Fin n → R) k
        (LinearMap.id : (Fin n → R) →ₗ[R] (Fin n → R)) =
      if k < n then ⊥ else ⊤ := by
  let π : (Fin n → R) →ₗ[R] (Fin n → R) := LinearMap.id
  by_cases hk : k < n
  · have hnk : 0 < n - k := Nat.sub_pos_of_lt hk
    rw [if_pos hk]
    change presentationFittingIdeal R (Fin n → R) k π = ⊥
    rw [presentationFittingIdeal, Matrix.minorIdeal, Ideal.span_eq_bot]
    rintro _ ⟨⟨e₁, e₂⟩, rfl⟩
    let i : Fin (n - k) := ⟨0, hnk⟩
    exact Matrix.det_eq_zero_of_row_eq_zero i fun j ↦ by
      have he₂j : (((e₂ j : LinearMap.ker π) : Fin n → R)) = 0 :=
        LinearMap.mem_ker.mp (e₂ j).property
      simpa [he₂j]
  · have hk' : n ≤ k := Nat.le_of_not_gt hk
    rw [if_neg hk]
    change presentationFittingIdeal R (Fin n → R) k π = ⊤
    rw [presentationFittingIdeal, Matrix.minorIdeal, Nat.sub_eq_zero_of_le hk']
    refine Ideal.eq_top_of_isUnit_mem _ ?_ isUnit_one
    have hmem :
        (1 : R) ∈
          Set.range
            (fun p :
              (Fin 0 ↪ Fin n) × (Fin 0 ↪ LinearMap.ker π) ↦
                Matrix.det
                  (Matrix.submatrix
                    (fun i x ↦ x.1 i : Matrix (Fin n) (LinearMap.ker π) R) p.1 p.2)) := by
      let e₁ : Fin 0 ↪ Fin n := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
      let e₂ : Fin 0 ↪ LinearMap.ker π := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
      refine ⟨⟨e₁, e₂⟩, ?_⟩
      simp [e₁, e₂, Matrix.det_fin_zero]
    exact Ideal.subset_span hmem

-- Proof sketch: apply `fittingIdeal_eq_presentationFittingIdeal` to the identity presentation
-- `(Fin n → R) →ₗ[R] (Fin n → R)`, then evaluate the resulting presentation ideal using the
-- private identity-presentation computation above.
/-- Example 15.8.5: the Fitting ideals of the finite free module `R^{\oplus n}` are `0` for
`k < n` and `R` for `k ≥ n`. -/
theorem fittingIdeal_free_eq_zero_or_top (n k : ℕ) :
    Fit[R]_(k)(Fin n → R) = if k < n then ⊥ else ⊤ := by
  rw [fittingIdeal_eq_presentationFittingIdeal R (Fin n → R) k
      (LinearMap.id : (Fin n → R) →ₗ[R] (Fin n → R)) Function.surjective_id]
  simpa using presentationFittingIdeal_id_eq_zero_or_top R n k

/-- For a free module of rank `n`, the `k`th Fitting ideal vanishes when `k < n`. -/
theorem fittingIdeal_free_eq_bot_of_lt {n k : ℕ} (hk : k < n) :
    Fit[R]_(k)(Fin n → R) = ⊥ := by
  simpa [if_pos hk] using fittingIdeal_free_eq_zero_or_top R n k

/-- For a free module of rank `n`, the `k`th Fitting ideal is the unit ideal when `n ≤ k`. -/
theorem fittingIdeal_free_eq_top_of_le {n k : ℕ} (hk : n ≤ k) :
    Fit[R]_(k)(Fin n → R) = ⊤ := by
  simpa [if_neg (Nat.not_lt.mpr hk)] using fittingIdeal_free_eq_zero_or_top R n k

end

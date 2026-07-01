import Mathlib.Tactic.Recall
import stacks_project.Chap15.Definition_15_8_3
import stacks_project.Chap15.Lemma_15_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FittingIdeal

/-
Domain-style sampling for Example 15.8.6:
- primary domain: Fitting ideals of finite modules, especially quotient modules and direct sums;
- sampled owner-level declarations:
  `fittingIdeal`,
  `fittingIdeal_zero_quotient`,
  `fittingIdeal_zero_directSum`,
  `fittingIdeal_directSum`;
- best owner abstraction: the source-facing owner is `fittingIdeal`, and the quotient/direct-sum
  examples should reuse that owner directly;
- primitive data: the intrinsic ideal `fittingIdeal R M k`;
- derived API: the quotient and direct-sum formulas supplied by `Lemma 15.8.4`.

Source/core/bridge triage:
- `source-facing`: the three example computations of `fittingIdeal`;
- `core/canonical`: `fittingIdeal`;
- `bridge/view`: `fittingIdeal_zero_quotient` and `fittingIdeal_directSum`. -/

universe u

section

variable {R : Type u} [CommRing R]

private theorem fittingIdeal_one_quotient_eq_top (I : Ideal R) :
    Fit[R]_(1)(R ⧸ I) = ⊤ := by
  let π : (Fin 1 → R) →ₗ[R] R ⧸ I :=
    (Ideal.Quotient.mkₐ R I).toLinearMap.comp (LinearEquiv.funUnique (Fin 1) R R).toLinearMap
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨(LinearEquiv.funUnique (Fin 1) R R).symm r, ?_⟩
    simp [π]
  exact fittingIdeal_eq_top_of_exists_surjective_fin 1 ⟨π, hπ⟩

/- Example 15.8.6 (1): the zeroth Fitting ideal of the quotient module `R ⧸ I` is `I`. -/
recall fittingIdeal_zero_quotient

/-- Example 15.8.6 (2): the zeroth Fitting ideal of `R ⧸ I ⊕ R ⧸ J` is the product ideal `IJ`. -/
theorem fittingIdeal_zero_quotient_directSum (I J : Ideal R) :
    Fit[R]_(0)((R ⧸ I) × (R ⧸ J)) = I * J := by
  have h :
      Fit[R]_(0)((R ⧸ I) × (R ⧸ J)) = Fit[R]_(0)(R ⧸ I) * Fit[R]_(0)(R ⧸ J) :=
    fittingIdeal_zero_directSum
  simpa [fittingIdeal_zero_quotient] using h

/-- Example 15.8.6 (3): the first Fitting ideal of `R ⧸ I ⊕ R ⧸ J` is the sum ideal `I + J`. -/
theorem fittingIdeal_one_quotient_directSum (I J : Ideal R) :
    Fit[R]_(1)((R ⧸ I) × (R ⧸ J)) = I + J := by
  have h :
      Fit[R]_(1)((R ⧸ I) × (R ⧸ J)) =
        Finset.sum (Finset.antidiagonal 1) fun p ↦
          Fit[R]_(p.1)(R ⧸ I) * Fit[R]_(p.2)(R ⧸ J) :=
    fittingIdeal_directSum 1
  rw [h]
  norm_num [Finset.antidiagonal]
  rw [fittingIdeal_zero_quotient I,
    fittingIdeal_zero_quotient J,
    fittingIdeal_one_quotient_eq_top I,
    fittingIdeal_one_quotient_eq_top J]
  simp

end

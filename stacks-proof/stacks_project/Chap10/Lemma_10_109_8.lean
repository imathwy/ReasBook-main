import Mathlib
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian

universe u v

section

variable {R : Type u} [Ring R]

/-- Having projective dimension at most `n` is equivalent to vanishing of all higher `Ext`
groups above degree `n`. -/
-- Proof sketch: unfold `HasProjectiveDimensionLE M n` as
-- `HasProjectiveDimensionLT M (n + 1)` and rewrite with
-- `hasProjectiveDimensionLT_iff`.
theorem hasProjectiveDimensionLE_iff_ext_eq_zero_of_ge
    (M : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveDimensionLE M n ↔
      ∀ (N : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i → ∀ e : Ext M N i, e = 0 := by
  constructor
  · intro hM N i hi e
    letI : HasProjectiveDimensionLT M (n + 1) := hM
    exact Ext.eq_zero_of_hasProjectiveDimensionLT e (n + 1) hi
  · intro h
    rw [HasProjectiveDimensionLE, hasProjectiveDimensionLT_iff]
    intro i hi N e
    exact h N i hi e

/-- Having projective dimension at most `n` is equivalent to vanishing of `Ext^{n+1}(M, N)` for
every `R`-module `N`. -/
-- Proof sketch: one direction is the degree `n + 1` case of higher Ext-vanishing. For the
-- converse, use `hasProjectiveDimensionLT_of_enoughInjectives` in `ModuleCat R`, observing that
-- vanishing of all classes in degree `n + 1` makes each `Ext^{n+1}(M, N)` a subsingleton.
theorem hasProjectiveDimensionLE_iff_ext_eq_zero_at_succ
    (M : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveDimensionLE M n ↔
      ∀ N : ModuleCat.{max u v} R, ∀ e : Ext M N (n + 1), e = 0 := by
  constructor
  · intro hM N e
    letI : HasProjectiveDimensionLT M (n + 1) := hM
    exact Ext.eq_zero_of_hasProjectiveDimensionLT e (n + 1) (by rfl)
  · intro h
    exact hasProjectiveDimensionLT_of_enoughInjectives M (n + 1) fun N ↦
      ⟨fun e₁ e₂ ↦ by rw [h N e₁, h N e₂]⟩

/-- Lemma 10.109.8: for an `R`-module `M` and `n ≥ 0`, the following are equivalent:
`M` has projective dimension at most `n`, `Ext^i_R(M, N) = 0` for every `R`-module `N` and
every `i ≥ n + 1`, and `Ext^{n + 1}_R(M, N) = 0` for every `R`-module `N`. -/
-- Proof sketch: combine `hasProjectiveDimensionLE_iff_ext_eq_zero_of_ge` and
-- `hasProjectiveDimensionLE_iff_ext_eq_zero_at_succ`, then package the three pairwise
-- equivalent clauses as a `List.TFAE`.
theorem moduleCat_projectiveDimensionLE_ext_vanishing_tfae
    (M : ModuleCat.{max u v} R) (n : ℕ) :
    List.TFAE [
      HasProjectiveDimensionLE M n,
      ∀ (N : ModuleCat.{max u v} R) (i : ℕ), n + 1 ≤ i → ∀ e : Ext M N i, e = 0,
      ∀ N : ModuleCat.{max u v} R, ∀ e : Ext M N (n + 1), e = 0
    ] := by
  tfae_have 1 ↔ 2 := hasProjectiveDimensionLE_iff_ext_eq_zero_of_ge M n
  tfae_have 1 ↔ 3 := hasProjectiveDimensionLE_iff_ext_eq_zero_at_succ M n
  tfae_finish

end

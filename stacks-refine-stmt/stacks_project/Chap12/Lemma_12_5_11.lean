import Mathlib

noncomputable section

open CategoryTheory Limits ZeroObject ComposableArrows

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}

/-- Lemma 12.5.11 (1): a commutative square in an abelian category is cartesian if and only if
the sequence `0 ⟶ W ⟶ X ⊞ Y ⟶ Z` with maps `(g, f)` and `(k, -h)` is exact. -/
theorem isPullback_iff_exact_biproduct_sequence
    (sq : CommSq g f k h) :
    IsPullback g f k h ↔ (mk₃ (0 : 0 ⟶ W) sq.shortComplex'.f sq.shortComplex'.g).Exact := by
  constructor
  · intro hsq
    let S : ShortComplex C := .mk (0 : 0 ⟶ W) sq.shortComplex'.f
      (by simpa using (show (0 : 0 ⟶ W) ≫ sq.shortComplex'.f = 0 from zero_comp))
    have h₀ : (mk₂ (0 : 0 ⟶ W) sq.shortComplex'.f).Exact := by
      change S.toComposableArrows.Exact
      rw [← S.exact_iff_exact_toComposableArrows]
      exact (S.exact_iff_mono (by rfl)).2 hsq.mono_shortComplex'_f
    have hδ₀ : (mk₃ (0 : 0 ⟶ W) sq.shortComplex'.f sq.shortComplex'.g).δ₀.Exact := by
      simpa [ComposableArrows.δ₀, ShortComplex.toComposableArrows] using
        hsq.exact_shortComplex'.exact_toComposableArrows
    exact ComposableArrows.exact_of_δ₀ h₀ hδ₀
  · intro hExact
    have hsplit := (ComposableArrows.exact_iff_δ₀
      (mk₃ (0 : 0 ⟶ W) sq.shortComplex'.f sq.shortComplex'.g)).1 hExact
    let S : ShortComplex C := .mk (0 : 0 ⟶ W) sq.shortComplex'.f
      (by simpa using (show (0 : 0 ⟶ W) ≫ sq.shortComplex'.f = 0 from zero_comp))
    have hmono' : Mono sq.shortComplex'.f := by
      exact (S.exact_iff_mono (by rfl)).1 <| by
        rw [S.exact_iff_exact_toComposableArrows]
        change (mk₂ (0 : 0 ⟶ W) sq.shortComplex'.f).Exact
        exact hsplit.1
    have hexact' : sq.shortComplex'.Exact := by
      rw [sq.shortComplex'.exact_iff_exact_toComposableArrows]
      simpa [ComposableArrows.δ₀, ShortComplex.toComposableArrows] using hsplit.2
    refine IsPullback.of_isLimit ((sq.isLimitEquivIsLimitKernelFork).symm ?_)
    exact ((sq.shortComplex').exact_and_mono_f_iff_f_is_kernel.mp ⟨hexact', hmono'⟩).some
/-- Lemma 12.5.11 (2): a commutative square in an abelian category is cocartesian if and only if
the sequence `W ⟶ X ⊞ Y ⟶ Z ⟶ 0` with maps `(g, -f)` and `(k, h)` is exact. -/
theorem isPushout_iff_exact_biproduct_sequence
    (sq : CommSq g f k h) :
    IsPushout g f k h ↔ (mk₃ sq.shortComplex.f sq.shortComplex.g (0 : Z ⟶ 0)).Exact := by
  let zToZero := (0 : Z ⟶ 0)
  constructor
  · intro hsq
    have hδlast :
        (mk₃ sq.shortComplex.f sq.shortComplex.g zToZero).δlast.Exact := by
      refine ComposableArrows.exact₂_mk _ ?_ ?_
      · change sq.shortComplex.f ≫ sq.shortComplex.g = 0
        exact sq.shortComplex.zero
      simpa [ComposableArrows.δlast, zToZero, ShortComplex.toComposableArrows] using
        hsq.exact_shortComplex
    let S : ShortComplex C := .mk sq.shortComplex.g zToZero
      (by simpa [zToZero] using (show sq.shortComplex.g ≫ (0 : Z ⟶ 0) = 0 from comp_zero))
    have h₂ : (mk₂ sq.shortComplex.g zToZero).Exact := by
      change S.toComposableArrows.Exact
      rw [← S.exact_iff_exact_toComposableArrows]
      exact (S.exact_iff_epi (by rfl)).2 hsq.epi_shortComplex_g
    exact ComposableArrows.exact_of_δlast (mk₃ sq.shortComplex.f sq.shortComplex.g zToZero)
      hδlast h₂
  · intro hExact
    have hsplit := (ComposableArrows.exact_iff_δlast
      (mk₃ sq.shortComplex.f sq.shortComplex.g zToZero)).1 hExact
    let S : ShortComplex C := .mk sq.shortComplex.g zToZero
      (by simpa [zToZero] using (show sq.shortComplex.g ≫ (0 : Z ⟶ 0) = 0 from comp_zero))
    have hexact : sq.shortComplex.Exact := by
      simpa [ComposableArrows.δlast, zToZero, ShortComplex.toComposableArrows] using
        (ComposableArrows.exact₂_iff
          ((mk₃ sq.shortComplex.f sq.shortComplex.g zToZero).δlast) hsplit.1.toIsComplex).1
          hsplit.1
    have hepι : Epi sq.shortComplex.g := by
      exact (S.exact_iff_epi (by rfl)).1 <| by
        rw [S.exact_iff_exact_toComposableArrows]
        change (mk₂ sq.shortComplex.g zToZero).Exact
        exact hsplit.2
    refine IsPushout.of_isColimit ((sq.isColimitEquivIsColimitCokernelCofork).symm ?_)
    exact ((sq.shortComplex).exact_and_epi_g_iff_g_is_cokernel.mp ⟨hexact, hepι⟩).some

end CategoryTheory

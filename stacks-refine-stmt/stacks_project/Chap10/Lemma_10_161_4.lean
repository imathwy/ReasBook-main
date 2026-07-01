import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Definition_10_161_1

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-
Domain triage: this file is in the commutative algebra of the `N-1` and `N-2` conditions under a
finite principal-open cover.

Owner abstractions sampled for this item:
- `IsN1Ring` and `IsN2Ring`, the source-facing owners from `Definition_10_161_1`;
- `isN1Ring_of_isLocalization` and `isN2Ring_of_isLocalization`, the localization-stability
  bridge theorems from `Lemma_10_161_3`;
- `Module.Finite.of_localizationSpan_finite`, the canonical finite-module descent theorem over a
  principal-open cover from `Lemma_10_23_2`.

Primitive data are the finite cover `s`, the unit-ideal hypothesis `hs`, and the domain hypotheses
for the chosen localizations. The localized `N-1` / `N-2` conditions are source-facing
assumptions. The finite-normalization statements and localization identifications are derived API
internal to the proofs, so this file should reuse the owners above directly rather than introducing
parallel local wrappers.
-/

/- Lemma 10.161.4, the `N-1` clause, is exactly the owner definition `IsN1Ring`: the forward
direction is `IsN1Ring.integralClosure_finite`, and the reverse direction is `IsN1Ring.mk`. -/
recall IsN1Ring.integralClosure_finite
recall IsN1Ring.mk

/- Lemma 10.161.4, the `N-2` clause, is exactly the owner definition `IsN2Ring`: the forward
direction is `IsN2Ring.integralClosure_finite`, and the reverse direction is `IsN2Ring.mk`. -/
recall IsN2Ring.integralClosure_finite
recall IsN2Ring.mk

variable (s : Finset R)

-- Proof sketch: use the local `N-1` assumptions together with `isN1Ring_of_isLocalization` to
-- place the canonical normalization owner on each principal localization, transport that
-- finiteness statement across `IsLocalization.integralClosure`, and descend finiteness of the
-- global normalization via `Module.Finite.of_localizationSpan_finite`.
/-- Lemma 10.161.4 (1): if the elements of `s` generate the unit ideal and each localization
`R_f` is `N-1`, then `R` is `N-1`. -/
theorem isN1Ring_of_isN1Ring_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, let _ : IsDomain (Localization.Away f.1) := hdom f
      IsN1Ring (Localization.Away f.1)) :
    IsN1Ring R := sorry

-- Proof sketch: for a finite extension `L / FractionRing R`, apply the localized owner theorem
-- `isN2Ring_of_isLocalization` to each principal localization, identify the localization of
-- `integralClosure R L` with the local integral closure via `IsLocalization.integralClosure`, and
-- descend finiteness back to `R` using `Module.Finite.of_localizationSpan_finite`.
/-- Lemma 10.161.4 (2): if the elements of `s` generate the unit ideal and each localization
`R_f` is `N-2`, then `R` is `N-2`. -/
theorem isN2Ring_of_isN2Ring_localizationAway
    (hs : Ideal.span (s : Set R) = ⊤)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, let _ : IsDomain (Localization.Away f.1) := hdom f
      IsN2Ring (Localization.Away f.1)) :
    IsN2Ring R := sorry

end

import Mathlib
import StacksProject_2024.Chap15.Definition_15_3_1
import StacksProject_2024.Chap16.Definition_16_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

local notation:max "A[" a "]" => Localization.Away a

/- Domain-style sampling for local smoothness criteria in finitely presented commutative algebra:
* primary domain: standard smooth localizations, Kähler differentials, and the Chapter 16
  predicates `IsElementaryStandard` and `IsStrictlyStandard`;
* sampled owner declarations:
  `Algebra.IsStandardSmooth`,
  `IsStandardSmooth.smooth`,
  `IsStandardSmooth.free_kaehlerDifferential`,
  `Module.StablyFree`;
* best owner abstraction:
  `Algebra.IsStandardSmooth` and `Smooth` are the canonical owners for the localized algebra
  `A[a]`, while `Module.StablyFree` is the chapter owner for the stable-freeness clause on
  `Ω[A[a]⁄R]`; the predicates `IsElementaryStandard` and `IsStrictlyStandard` remain the
  source-facing conditions on `a`;
* primitive vs. derived:
  the primitive source-facing data are only the two Chapter 16 predicates on `a`. Standard
  smoothness and smoothness of `A[a]`, together with freeness or stable freeness of `Ω[A[a]⁄R]`,
  are derived owner-level consequences and should be stated directly through those owners rather
  than repackaged in a local wrapper.

Source/core/bridge triage:
* `source-facing`: the six conditions in Stacks Lemma 16.3.7 on a single element `a : A`;
* `core/canonical`: `Algebra.IsStandardSmooth`, `Smooth`, `Module.Free`, and `Module.StablyFree`
  for the localized algebra and its Kähler differentials;
* `bridge/view`: the Chapter 16 predicates `IsElementaryStandard` and `IsStrictlyStandard`
  translate presentation-level Jacobian conditions into those canonical owner conclusions.
-/

-- Proof sketch for Lemma 16.3.7 (a), implication `(4) ⇒ (3)`: this is the direct source-facing
-- conjunction of the canonical owner consequences
-- `IsStandardSmooth.free_kaehlerDifferential` and `[IsStandardSmooth R A_a] : Smooth R A_a`.
/-- Lemma 16.3.7 (a), implication `(4) ⇒ (3)`: if `A_a` is standard smooth over `R`, then `A_a`
is smooth over `R` and its module of Kähler differentials is free. -/
theorem standardSmoothAway_implies_freeKaehler
    (a : A) (h : IsStandardSmooth R A[a]) :
    Smooth R A[a] ∧ Module.Free A[a] Ω[A[a]⁄R] := by
  let _ : IsStandardSmooth R A[a] := h
  exact ⟨inferInstance, inferInstance⟩

-- Proof sketch for Lemma 16.3.7 (a), implication `(3) ⇒ (2)`: this is the direct owner-level
-- upgrade from `Module.Free` to `Module.StablyFree`, via the canonical instance
-- `Module.stablyFree_of_free`, together with the unchanged smoothness hypothesis.
/-- Lemma 16.3.7 (a), implication `(3) ⇒ (2)`: if `A_a` is smooth over `R` and `Ω[(A_a)/R]` is
free, then `A_a` is smooth over `R` and `Ω[(A_a)/R]` is stably free. -/
theorem freeKaehlerAway_implies_stablyFreeKaehler
    (a : A) (hsmooth : Smooth R A[a]) (hfree : Module.Free A[a] Ω[A[a]⁄R]) :
    Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R] := by
  let _ : Module.Free A[a] Ω[A[a]⁄R] := hfree
  exact ⟨hsmooth, inferInstance⟩

-- Proof sketch for Lemma 16.3.7 (a), implication `(2) ⇒ (1)`: this is the tautological
-- projection from condition `(2)` to its smoothness component.
/-- Lemma 16.3.7 (a), implication `(2) ⇒ (1)`: condition `(2)` implies that `A_a` is smooth over
`R`. -/
theorem stablyFreeKaehlerAway_implies_smooth
    (a : A) (h : Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R]) :
    Smooth R A[a] := h.1

-- Proof sketch for Lemma 16.3.7 (b), implication `(6) ⇒ (5)`: an elementary standard element is,
-- by definition, a special case of a strictly standard element using a single leading Jacobian
-- determinant.
/-- Lemma 16.3.7 (b), implication `(6) ⇒ (5)`: every elementary standard element of `A` over `R`
is strictly standard. -/
theorem isElementaryStandard_implies_isStrictlyStandard
    (a : A) (h : IsElementaryStandard R a) :
    IsStrictlyStandard R a := sorry

-- Proof sketch for Lemma 16.3.7 (c), implication `(6) ⇒ (4)`: starting from an elementary
-- standard presentation, adjoin an inverse to the chosen Jacobian determinant and rewrite the
-- localization as a standard smooth presentation.
/-- Lemma 16.3.7 (c), implication `(6) ⇒ (4)`: if `a` is elementary standard in `A` over `R`,
then the localization `A_a` is standard smooth over `R`. -/
theorem isElementaryStandard_implies_standardSmoothAway
    (a : A) (h : IsElementaryStandard R a) :
    IsStandardSmooth R A[a] := sorry

-- Proof sketch for Lemma 16.3.7 (d), implication `(5) ⇒ (2)`: a strictly standard presentation
-- gives a smooth localization, and the conormal sequence shows that `Ω[(A_a)/R]` is a direct
-- summand of a finite free module, hence stably free.
/-- Lemma 16.3.7 (d), implication `(5) ⇒ (2)`: if `a` is strictly standard in `A` over `R`, then
`A_a` is smooth over `R` and `Ω[(A_a)/R]` is stably free. -/
theorem isStrictlyStandard_implies_stablyFreeKaehlerAway
    (a : A) (h : IsStrictlyStandard R a) :
    Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R] := sorry

section

variable [FinitePresentation R A]

-- Proof sketch for Lemma 16.3.7 (e): choose a finite presentation of `A` over `R`, stabilize the
-- conormal module so it becomes free after adjoining dummy variables, and then use the Jacobian
-- criterion to obtain that all sufficiently large powers of `a` are strictly standard.
/-- Lemma 16.3.7 (e): if condition `(2)` holds, then there exists `e0` such that every power
`a^e` with `e ≥ e0` is strictly standard in `A` over `R`. -/
theorem stablyFreeKaehlerAway_eventually_strictlyStandard_pow
    (a : A) (hsmooth : Smooth R A[a]) (hstablyFree : Module.StablyFree A[a] Ω[A[a]⁄R]) :
    ∃ e0 : ℕ, ∀ e : ℕ, e0 ≤ e → IsStrictlyStandard R (a ^ e) := sorry

-- Proof sketch for Lemma 16.3.7 (f): from a standard smooth presentation of `A_a`, clear
-- denominators in the chosen generators and defining equations to descend to a presentation of
-- `A`; for all sufficiently large powers of `a`, the Jacobian determinant and tail
-- ideal-membership conditions then witness elementary standardness.
/-- Lemma 16.3.7 (f): if condition `(4)` holds, then there exists `e0` such that every power
`a^e` with `e ≥ e0` is elementary standard in `A` over `R`. -/
theorem standardSmoothAway_eventually_elementaryStandard_pow
    (a : A) (h : IsStandardSmooth R A[a]) :
    ∃ e0 : ℕ, ∀ e : ℕ, e0 ≤ e → IsElementaryStandard R (a ^ e) := sorry

end

end

end Algebra

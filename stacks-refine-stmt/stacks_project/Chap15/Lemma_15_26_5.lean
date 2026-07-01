import Mathlib
import stacks_project.Chap10.Definition_10_17_1
import stacks_project.Chap10.Definition_10_78_1
import stacks_project.Chap15.Definition_15_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open scoped AffineBlowupChart PrimeSpectrum

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

variable [Module.Finite R M]
variable {f : R} {r : ℕ}

/-
Domain-style sampling pass for Lemma 15.26.5.

Primary domain: commutative algebra of affine blowups, strict transforms, and finite locally free
modules.

Sampled owner declarations:
* `affineBlowupStrictTransform` from `Chap15/Definition_15_26_1.lean`;
* `fittingIdealAffineBlowupStrictTransform_finiteLocallyFreeOfRank` from
  `Chap15/Lemma_15_26_4.lean`;
* `Module.FiniteLocallyFreeOfRank` from `Chap10/Definition_10_78_1.lean`;
* `V(-)` from `Chap10/Definition_10_17_1.lean` as the source-facing closed-subset notation on
  `Spec R`.

Owner abstraction: the intrinsic owners are the ideal `I`, its closed subset
`V((I : Set R))`, the affine blowup charts `R[I / a]`, and the strict
transform `affineBlowupStrictTransform I a M`. The previous local structure in this file was only
a one-off package of three logical clauses and did not carry new mathematical data, so the public
statement should expose those clauses directly rather than through a parallel wrapper.

Primitive data: the ideal `I` and its chart elements `a : I`.
Derived API: finite generation of `I`, equality of closed loci with `(f)`, and the finite locally
free rank condition on each strict transform chart.

Source/core/bridge triage:
* `source-facing`: the existential blowup-ideal statement below;
* `core/canonical`: `V((I : Set R))`, `R[I / a]`, `affineBlowupStrictTransform I a M`, and
  `Module.FiniteLocallyFreeOfRank`;
* `bridge/view`: Lemma `15.26.4`, which supplies the chartwise finite-locally-free conclusion once
  the ideal choice is made.
-/

-- Proof sketch: replace `M` by a finitely presented module that agrees with it after inverting
-- `f`, choose the ideal `I = f * Fit_r(M)` in the finitely presented case, and apply the
-- Fitting-ideal criterion for finite locally free modules on each affine blowup chart after
-- quotienting by the `a`-power torsion.
/-- Lemma 15.26.5: if `M` becomes finite locally free of rank `r` after inverting `f`, then there
exists a finitely generated ideal `I` with `V(f) = V(I)` such that every affine blowup chart
`R[I/a]` makes the strict transform of `M` finite locally free of rank `r`. -/
theorem exists_blowupIdeal_with_strictTransform_finiteLocallyFreeOfRank
    (hMf : Module.FiniteLocallyFreeOfRank (Localization.Away f) (LocalizedModule.Away f M) r) :
    ∃ I : Ideal R,
      I.FG ∧
      V(({f} : Set R)) = V((I : Set R)) ∧
      ∀ a : I, Module.FiniteLocallyFreeOfRank R[I / a]
        (affineBlowupStrictTransform I a M) r :=
  sorry

end

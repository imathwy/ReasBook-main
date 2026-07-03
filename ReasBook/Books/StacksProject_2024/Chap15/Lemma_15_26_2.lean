import Mathlib
import StacksProject_2024.Chap10.Lemma_10_70_3
import StacksProject_2024.Chap10.Lemma_10_70_12
import StacksProject_2024.Chap15.Definition_15_26_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w x

open scoped AffineBlowupChart

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
variable {S : Type w} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type x} [AddCommGroup M] [Module S M] [Module.Finite S M]

noncomputable local instance instModuleAffineBlowupApproximationStage
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) :
    Module R[I / a.1]
      (affineBlowupStrictTransform
        (Ideal.map (algebraMap R S) I) (mappedIdealElement I a.1) M) :=
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a.1
  Module.compHom _ <| algebraMap (R[I / a.1]) (S[J / b])

/-
Domain-style sampling pass for Lemma 15.26.2.

Primary domain: affine blowup strict transforms in commutative algebra over a local domain.

Sampled owner declarations:
* `R[I / a]` from `Chap10/Definition_10_70_1.lean`;
* `IsAffineBlowupApproximation` from `Chap10/Lemma_10_70_12.lean`;
* `mappedIdealElement` from `Chap10/Lemma_10_70_3.lean`;
* `affineBlowupStrictTransform` from `Chap15/Definition_15_26_1.lean`.

Owner abstraction: the source-facing strict transform algebra of `S` on `R[I/a]` is the affine
blowup chart `S[Ideal.map (algebraMap R S) I / mappedIdealElement I a.1]`, and the source-facing
strict transform of `M` is the Chapter 15 owner
`affineBlowupStrictTransform (Ideal.map (algebraMap R S) I) (mappedIdealElement I a.1) M`.
Primitive data are the ideal `I`, the chosen nonzero `a ∈ I`, and the induced ideal map
`Ideal.map (algebraMap R S) I`; flatness and finite-presentation conditions are derived API.

Source/core/bridge triage:
* `source-facing`: the existence theorem returning a blowup chart approximation together with the
  flatness and finite-presentation properties of its strict transform algebra and module;
* `core/canonical`: `IsAffineBlowupApproximation`, the strict transform algebra owner
  `S[Ideal.map (algebraMap R S) I / mappedIdealElement I a.1]`, and the strict transform module
  owner
  `affineBlowupStrictTransform (Ideal.map (algebraMap R S) I) (mappedIdealElement I a.1) M`;
* `bridge/view`: `mappedIdealElement` and `tensorToAffineBlowupAlgebra` from
  `Lemma_10_70_3.lean`.
-/

-- Proof sketch: approximate the dominating valuation ring `A` by affine blowup charts as in
-- Lemma `10.70.12`, reduce to the polynomial-algebra case by presenting `S` as a quotient of a
-- polynomial ring, and then use the valuation-ring flatness and finite-presentation results from
-- Lemmas `15.22.10`, `15.25.6`, and the limit-flatness descent statement `10.168.1 (3)` to find a
-- stage where both strict transforms have the required properties.
/-- Lemma 15.26.2: for every valuation ring `A ⊆ K` dominating the local domain `R`, there exists
an affine blowup chart `R' = R[I/a]` with nonzero `a ∈ I ⊆ maximalIdeal R` and nonzero special
fibre such that, writing `J = Ideal.map (algebraMap R S) I`, `b` for the image of `a` in `J`, and
`B = S[J/b]`, the strict transform algebra `B` is flat and finitely presented over `R'`, while
the strict transform module `affineBlowupStrictTransform J b M` is flat over `R'` and finitely
presented over `B`. -/
theorem exists_affineBlowup_with_flat_finitelyPresented_strictTransforms
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) :
    ∃ (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }),
      let R' := R[I / a.1]
      let J : Ideal S := Ideal.map (algebraMap R S) I
      let b : J := mappedIdealElement I a.1
      let B := S[J / b]
      let T := affineBlowupStrictTransform J b M
      IsAffineBlowupApproximation A I a ∧
        Module.Flat R' B ∧
        Algebra.FinitePresentation R' B ∧
        Module.Flat R' T ∧
        Module.FinitePresentation B T :=
  sorry

end

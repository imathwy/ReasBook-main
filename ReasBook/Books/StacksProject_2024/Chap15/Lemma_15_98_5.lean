import stacks_project.Chap15.Lemma_15_92_14
import stacks_project.Chap15.Lemma_15_98_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open DerivedModuleTower
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "F" => idealPowerQuotientRingSystem I

/- Domain-style sampling:
- primary domain: derived inverse limits of ideal-power quotient towers in `D(A)`, together with
  the chapter bridge owner for stagewise restriction/base change and the derived-completeness owner;
- sampled owner declarations:
  `IdealPowerQuotientDerivedTower`,
  `stageRestrictionToBaseTower`,
  `stageDerivedBaseChange`,
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing ideal-power quotient tower owner
  `IdealPowerQuotientDerivedTower I` from `Lemma_15_98_4`, with derived completeness coming from
  `Definition_15_92_4`;
- primitive data: the tower `T : IdealPowerQuotientDerivedTower I` and the chosen derived limit
  `K` of the canonical fixed-base inverse system `stageRestrictionToBaseTower F A T`;
- derived API: the canonical fixed-base tower owner
  `stageRestrictionToBaseTower` and the upstream stagewise base-change owner
  `stageDerivedBaseChange (idealPowerQuotientRingSystem I) T n`, and the predicate
  `K.IsDerivedCompleteWithRespectTo I`.

Source/core/bridge triage:
- `source-facing`: the two statements of Lemma `15.98.5`;
- `core/canonical`: `CategoryTheory.IsDerivedLimit` and
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: `stageRestrictionToBaseTower F A`,
  `stageDerivedBaseChange (idealPowerQuotientRingSystem I) T n`, and the quotient-stage
  base-change object `K ⊗[A]^L[A ⧸ I ^ (n + 1)]`, reused directly from
  `Lemma_15_98_4`. -/

-- Proof sketch: restrict the tower `K_n` from `D(A / I^(n+1))` to `D(A)`. On stage `n`, the
-- ideal power `I^(n+1)` acts trivially, so for every `f ∈ I` a sufficiently large power of `f`
-- kills the `n`th stage. Apply Lemma `15.92.14` to the resulting inverse system in `D(A)`.
/-- Lemma 15.98.5 (1): let `A` be a ring, let `I ⊆ A` be an ideal, and let `K` be a
chosen derived limit of a compatible tower `K_n ∈ D(A / I^(n+1))` viewed over `A`. Then `K` is
derived complete with respect to `I`. Here stage `0` corresponds to the textbook object `K_1`. -/
theorem derivedLimit_of_idealPowerQuotientTower_isDerivedComplete
    (T : IdealPowerQuotientDerivedTower I) (K : DMod)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    : K.IsDerivedCompleteWithRespectTo I := sorry

section

variable [IsNoetherianRing A]

-- Proof sketch: choose bounded-above flat representatives for the stages using the bounded-above
-- hypothesis on `K_1` and the nilpotent lifting statement of Lemma `15.76.3`, then represent the
-- derived limit by the termwise inverse limit complex. Tensoring this bounded-above flat complex
-- with `A / I^(n+1)` commutes with the inverse limit and stabilizes at stage `n`, giving the
-- desired identification with `K_n`.
/-- Lemma 15.98.5 (2): let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and let `K` be a
chosen derived limit of a compatible tower `K_n ∈ D(A / I^(n+1))` whose stagewise derived
reductions `K_{n+1} \otimes_{A / I^(n+2)}^{\mathbf L} A / I^(n+1)` identify with `K_n`. If the
first stage `K_1` is bounded above, then the derived base change of `K` to each quotient
`A / I^(n+1)` recovers `K_n`. Here stage `0` corresponds to the textbook object `K_1`. -/
theorem idealPowerQuotientBaseChange_isomorphic_of_boundedAbove_derivedLimit
    (T : IdealPowerQuotientDerivedTower I) (K : DMod)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁_bounded : ∃ b : ℤ, (T.obj 0).IsLE b)
    (hstageBaseChange :
      ∀ n : ℕ,
        IsIsomorphic
          (T.obj (n + 1) ⊗[A ⧸ I ^ (n + 2)]^L[A ⧸ I ^ (n + 1)])
          (T.obj n)) :
    ∀ n : ℕ, IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) := sorry

end

end

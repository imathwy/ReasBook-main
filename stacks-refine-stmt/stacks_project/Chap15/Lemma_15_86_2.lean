import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Definition_10_134_1
import stacks_project.Chap15.Lemma_15_33_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

noncomputable section

universe u x y

/- Domain triage:
* primary domain: underived base change for presentationwise naive cotangent complexes and their
  degree `-1` and `0` homology in commutative algebra;
* sampled owner declarations:
  - `Presentation.baseChange`,
  - `Presentation.baseChangeFromBaseChange`,
  - `Extension.naiveCotangentChainComplex`,
  - `Extension.CotangentSpace.map_comp_cotangentComplex`,
  - `tensor_presentation_cotangent_h1_to_h1_cotangent`,
  - `KaehlerDifferential.tensorKaehlerEquivBase`;
* best owner abstraction: the source-facing owner is the comparison chain map between the
  canonical two-term complexes
  `P.toExtension.baseChange.naiveCotangentChainComplex` and
  `(P.baseChange R').toExtension.naiveCotangentChainComplex`; the owner-level public comparison on
  `H^{-1}` is the canonical composite
  `H1Cotangent.baseChangeComparison R R' S`,
  `S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R' S'`,
  the degree `0` owner is already the canonical equivalence
  `KaehlerDifferential.tensorKaehlerEquivBase R R' S`;
* primitive data: the ring maps `R → S`, `R → R'`, and the chosen presentation `P`;
* derived API: the source-facing surjectivity theorem for the explicit presentation-level
  `H^{-1}` comparison composite, the owner-level comparison
  `H1Cotangent.baseChangeComparison R R' S` and its surjectivity statement, and direct reuse of
  `KaehlerDifferential.tensorKaehlerEquivBase` for degree `0`.

Source/core/bridge triage:
* `source-facing`: the comparison `NL(P/R) ⊗[S] S' → NL(P.baseChange R'/R')` for a chosen
  presentation `P`;
* `core/canonical`: `Presentation.baseChange`, `Presentation.baseChangeFromBaseChange`,
  `Extension.naiveCotangentChainComplex`, `H1Cotangent.baseChangeComparison`, and
  `KaehlerDifferential.tensorKaehlerEquivBase`;
* `bridge/view`: the explicit presentation-level composite of
  `tensor_presentation_cotangent_h1_to_h1_cotangent`,
  `H1Cotangent.map`, and `equivH1Cotangent.symm` used in the surjectivity theorem below.
-/

section

variable {R S R' : Type u}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable {ι : Type x} {σ : Type y}

local notation "S'" => R' ⊗[R] S

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.H1Cotangent

variable (R R' S)

/- The canonical owner-level base-change map
`S' ⊗[S] H¹(L_{S/R}) → H¹(L_{S'/R'})`. -/
noncomputable abbrev baseChangeComparison :
    S' ⊗[S] H1Cotangent R S →ₗ[S'] H1Cotangent R' S' :=
  (map R R' S' S').comp (LinearMap.liftBaseChange S' (map R R S S'))

/- Lemma 15.86.2 (in particular): the canonical owner-level base-change map
`S' ⊗[S] H¹(L_{S/R}) → H¹(L_{S'/R'})` is surjective. -/
theorem baseChangeComparison_surjective
    :
    Function.Surjective (baseChangeComparison R R' S) := sorry

end Algebra.H1Cotangent

namespace Algebra.Presentation

/-- Lemma 15.86.2: for a chosen presentation `P` of `S` over `R`, the comparison
`NL(P/R) ⊗[S] S' → NL(P.baseChange R'/R')`
is surjective on `H^{-1}`. This is the source-facing presentation-level comparison whose target is
identified with `H1Cotangent R' S'` via the canonical presentation equivalence. -/
theorem naiveCotangentBaseChangeH1Comparison_surjective
    (P : Presentation R S ι σ) :
    Function.Surjective
      (((P.baseChange R').toGenerators.equivH1Cotangent.symm).toLinearMap ∘ₗ
        H1Cotangent.map R R' S' S' ∘ₗ
          tensor_presentation_cotangent_h1_to_h1_cotangent S' P.toGenerators) := sorry

end Algebra.Presentation

/- The degree `0` part of Lemma 15.86.2 is the canonical Kähler-differential base-change
equivalence, i.e. the degree-`0` comparison for the owner chain map
`Extension.naiveCotangentChainMap (P.baseChangeFromBaseChange R')`. -/
recall KaehlerDifferential.tensorKaehlerEquivBase

end

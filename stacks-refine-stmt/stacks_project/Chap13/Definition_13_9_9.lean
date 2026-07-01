import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C]
variable (S : ShortComplex (CochainComplex C ℤ))

/- Source/core/bridge triage for Definition 13.9.9:
- primary domain: termwise split exact sequences of cochain complexes and the induced connecting
  morphism and associated triangle.
- inspected declarations in this domain:
  `ShortComplex.map`,
  `HomologicalComplex.eval`,
  `ShortComplex.Splitting`,
  `ShortComplex.Splitting.shortExact`,
  `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.triangleOfDegreewiseSplit`,
  `CochainComplex.trianglehOfDegreewiseSplit`.
- best owner abstraction: the source-facing notion is a short complex
  `S : ShortComplex (CochainComplex C ℤ)` whose evaluation in each degree,
  `S.map (eval C (up ℤ) n)`, admits a splitting, expressed canonically as the existence property
  `∀ n : ℤ, Nonempty ((S.map (eval C (up ℤ) n)).Splitting)`. This direct `ShortComplex.map` view
  is the owner-level way the mathlib degreewise-split constructions are stated, so no parallel
  chapter alias is needed here. After choosing a witness
  `σ : ∀ n : ℤ, (S.map (eval C (up ℤ) n)).Splitting`, mathlib derives the connecting morphism
  `CochainComplex.homOfDegreewiseSplit S σ` and the associated triangle
  `CochainComplex.triangleOfDegreewiseSplit S σ`. Passing this triangle to the homotopy category
  gives the bridge/view `CochainComplex.trianglehOfDegreewiseSplit S σ`.
- layer:
  `source-facing`: the short complex `S` together with degreewise splitness as an existence
    property;
  `core/canonical`: `ShortComplex`, degreewise `ShortComplex.Splitting`,
    `CochainComplex.homOfDegreewiseSplit`, and `CochainComplex.triangleOfDegreewiseSplit`;
  `bridge/view`: `CochainComplex.trianglehOfDegreewiseSplit`.
- primitive data: exactly the short complex `S` and the degreewise splitness condition
  `∀ n : ℤ, Nonempty ((S.map (eval C (up ℤ) n)).Splitting)`.
- derived API: after choosing a splitting family `σ`, one gets
  exactness in each degree from `ShortComplex.Splitting.shortExact` when `C` has a zero object,
  `CochainComplex.homOfDegreewiseSplit S σ`,
  `CochainComplex.triangleOfDegreewiseSplit S σ`, and its homotopy-category image
  `CochainComplex.trianglehOfDegreewiseSplit S σ`. The dependence on that choice is handled
  separately in Lemma 13.9.10.
-/

/- Definition 13.9.9: a termwise split exact sequence of cochain complexes is a short complex
whose degreewise short complex in each degree admits a splitting. -/
#check (∀ n : ℤ, Nonempty ((S.map (eval C (up ℤ) n)).Splitting))

/- Companion recall: a chosen splitting in one degree is the canonical owner
`ShortComplex.Splitting`. -/
recall ShortComplex.Splitting

section

variable [HasZeroObject C]

/- Companion recall: when `C` has a zero object, exactness in each degree is derived from a
chosen splitting via
`ShortComplex.Splitting.shortExact`; it is not extra primitive data in Definition 13.9.9. -/
recall ShortComplex.Splitting.shortExact

end

section

variable (σ : ∀ n : ℤ, (S.map (eval C (up ℤ) n)).Splitting)

/- Companion check: after choosing a degreewise splitting family `σ`, mathlib constructs the
canonical connecting morphism `CochainComplex.homOfDegreewiseSplit S σ :
S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧`. The independence of this choice is deferred to Lemma 13.9.10. -/
recall CochainComplex.homOfDegreewiseSplit

/- Companion check: the associated triangle of cochain complexes is the canonical owner
`CochainComplex.triangleOfDegreewiseSplit S σ`. -/
recall CochainComplex.triangleOfDegreewiseSplit

/- Downstream bridge check: applying the quotient functor from cochain complexes to the homotopy
category sends `CochainComplex.triangleOfDegreewiseSplit S σ` to
`CochainComplex.trianglehOfDegreewiseSplit S σ`, used in Definition 13.10.1. -/
recall CochainComplex.trianglehOfDegreewiseSplit

end

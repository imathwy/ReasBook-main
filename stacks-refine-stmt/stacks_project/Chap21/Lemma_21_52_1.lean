import Mathlib
import stacks_project.Chap13.Lemma_13_35_7
import Mathlib.CategoryTheory.Retract
import stacks_project.Chap13.Definition_13_37_1
import stacks_project.Chap13.Remark_13_35_5

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{v} A]
variable [IsGrothendieckAbelian.{w} A]

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.52.1:
- primary domain: compact objects in Grothendieck abelian categories and their bounded-complex
  representatives in the derived category, with generation data expressed through the canonical
  separator API for object properties;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `CategoryTheory.ObjectProperty.IsSeparating`,
  `CategoryTheory.ObjectProperty.isSeparating_iff_epi`,
  `CategoryTheory.ObjectProperty.coproductFrom`,
  `CategoryTheory.isCompactObject_iff`,
  `CategoryTheory.additiveClosure`,
  `CochainComplex.IsStrictlyGE`,
  `CochainComplex.IsStrictlyLE`,
  `CategoryTheory.Retract`;
- best owner abstraction: the compactness owner `IsCompactObject`, applied both to the compact
  derived object `K` and to the generators `E ∈ S`, together with the separating owner
  `ObjectProperty.IsSeparating` for the generating family, the canonical bounded-support owners on
  a chosen cochain representative, and the direct-summand owner `Retract` for the bounded-complex
  conclusion;
- primitive-vs-derived split: the primitive source data are the separating property of the object
  property `fun Y : A ↦ Y ∈ S` and the compactness of each generator in `A`; the concrete
  epimorphic-coproduct presentation is derived from `ObjectProperty.isSeparating_iff_epi`, while
  the boundedness and termwise additive-closure condition are carried by `CochainComplex` support
  owners and the retract data are derived from the canonical owner `Retract`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that every compact object of `D(A)` is a direct summand of
  an object represented by a bounded complex with terms finite direct sums of generators;
- `core/canonical`: `CategoryTheory.IsCompactObject`,
  `CategoryTheory.ObjectProperty.IsSeparating`, and `CategoryTheory.Retract`;
- `bridge/view`: the Chapter 13 owner `CategoryTheory.additiveClosure`, which records the
  finite-coproduct closure of the generator set up to isomorphism, together with the chosen
  cochain-complex representative `P` of the retract target `DerivedCategory.Q.obj P`.
-/

-- Proof sketch: apply the Stacks argument using compactness of `K` to force bounded-above
-- truncation, resolve `K` by a bounded-above complex of coproducts of elements of `S`, factor the
-- identity through a bounded subcomplex, and then shrink the remaining infinite summands one
-- degree at a time until each term is a finite coproduct of elements of `S`. The resulting
-- bounded complex yields an object of `D(A)` admitting `K` as a retract.
/-- Lemma 21.52.1: if `A` is a Grothendieck abelian category and `S` is a set of objects such
that every object of `A` is a quotient of a direct sum of elements of `S`, while every
`E ∈ S` is compact in `A`, then every compact object of `D(A)` is a direct summand of an object
represented by a bounded complex whose terms are finite direct sums of elements of `S`. -/
theorem compactObject_isRetract_of_finiteCoproductComplex_of_generatingSet
    (S : Set A) {K : DerivedCategory A} (hK : IsCompactObject K)
    (hgen : ObjectProperty.IsSeparating (fun Y : A ↦ Y ∈ S))
    (hsmall : ∀ ⦃E : A⦄, E ∈ S → IsCompactObject E) :
    ∃ (P : CochainComplex A ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧
        P.IsStrictlyLE b ∧
          (∀ i : Set.Icc a b, (additiveClosure fun Y : A ↦ Y ∈ S) (P.X i.1)) ∧
            Nonempty (Retract K (DerivedCategory.Q.obj P)) := sorry

end

end CategoryTheory.IsGrothendieckAbelian

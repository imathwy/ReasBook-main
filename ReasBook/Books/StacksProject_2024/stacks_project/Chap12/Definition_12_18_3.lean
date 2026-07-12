import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape

namespace HomologicalComplex₂

scoped[HomologicalComplex₂] notation:max "Tot(" K ")" => HomologicalComplex₂.total K (up ℤ)

end HomologicalComplex₂

open scoped HomologicalComplex₂

section

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) [A.HasTotal (up ℤ)]

/- Domain-style sampling for Definition 12.18.3:
- primary domain: total complexes of cohomological double complexes;
- sampled owner declarations:
  `HomologicalComplex₂.HasTotal`,
  `HomologicalComplex₂.total`,
  `HomologicalComplex₂.total_d`,
  `HomologicalComplex₂.totalFunctor`;
- source/core/bridge triage:
  `source-facing`: the simple complex `sA^• = Tot(A^{•, •})` attached to a cohomological double
    complex;
  `core/canonical`: `HomologicalComplex₂.total`;
  `bridge/view`: the differential formula `HomologicalComplex₂.total_d`.

Primitive data are the bicomplex objects and horizontal/vertical differentials already packaged by
`HomologicalComplex₂`. The existence predicate `HomologicalComplex₂.HasTotal` and the total
complex `HomologicalComplex₂.total` are derived owner API, so this file should recall those
canonical declarations directly rather than introduce a chapter-local `simpleComplex` alias or
wrapper.
-/

/- Companion recall: the finiteness/existence predicate needed to form the total complex of a
double complex is the canonical owner `HomologicalComplex₂.HasTotal`. -/
recall HomologicalComplex₂.HasTotal

/- Source-facing notation: in Chapter 12, the simple complex attached to a cohomological
bicomplex `A` is written `Tot(A)`. -/
#check Tot(A)

/- Definition 12.18.3: for a cohomological double complex `A`, the associated simple complex
`sA^• = Tot(A^{•, •})` is the canonical owner construction `HomologicalComplex₂.total`,
specialized in the Stacks setting to total degree shape `up ℤ`. -/
recall HomologicalComplex₂.total

/- Companion recall: the differential on the total complex is the canonical sum of the horizontal
and signed vertical parts, recorded by the owner lemma `HomologicalComplex₂.total_d`. -/
recall HomologicalComplex₂.total_d

end

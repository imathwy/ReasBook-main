import Mathlib
import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap15.Lemma_15_69_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Algebra

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: the naive cotangent complex `NL_{B/A}` in `D(B)` and its smooth/formally smooth
  Ext-vanishing criteria;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the source-facing Chapter 10 owner for `NL_{B/A}` in `D(B)`;
  - `Generators.self`, the canonical self-presentation `A[B] ↠ B`;
  - `Extension.naiveCotangentChainComplex`, the chapter owner for the two-term naive cotangent
    complex of a presentation;
  - `derivedExtToModuleFunctor`, the Chapter 15 owner for the degree-`1` derived `Ext`
    functorial test;
  - `Algebra.formallySmooth_tfae_presentation_section_conormal_sequence_projective`, the
    presentation-independent formal smoothness criterion.
* best owner abstraction: the primitive data for this remark are only the algebra map `A → B`,
  whose source-facing derived owner is `NL_{B/A} = naiveCotangent A B`. The chosen
  self-presentation and its two-term representative are bridge data internal to that owner. The
  smoothness and formal smoothness criteria are derived API and should be stated for `NL_{B/A}`,
  using the canonical vanishing condition `IsZero (derivedExtToModuleFunctor (naiveCotangentObject
  A B) 1)` rather than a local wrapper predicate, and not for its raw representative.
* layer triage:
  - `source-facing`: the criterion in terms of `Ext^1_B(NL_{B/A}, N)`;
  - `core/canonical`: `naiveCotangent A B`;
  - `bridge/view`: the derived-category realization
    `DerivedCategory.Q.obj
      (((Generators.self A B).toExtension.naiveCotangentChainComplex).extend embeddingDownNat)`.

Primitive data are only the algebra map and the canonical owner `NL_{B/A}`. The derived `Ext`
vanishing condition and the smooth/formally smooth criteria are already owned upstream and are
reused directly here. -/

-- Proof sketch: combine the canonical criterion `Algebra.smooth_iff`, which rewrites smoothness
-- as finite presentation plus formal smoothness, with the degree-`1` derived `Ext`-vanishing
-- criterion `IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1)` applied to the
-- canonical owner `NL_{B/A}`, and with Proposition `10.138.8`, which identifies formal
-- smoothness with
-- vanishing of `H¹(L_{B/A})` together with projectivity of `Ω[B⁄A]`.
/-- Remark 15.85.2 (1): an `A`-algebra `B` is smooth if and only if it is of finite presentation
and `Ext^1_B(NL_{B/A}, N)` vanishes for every `B`-module `N`. -/
theorem smooth_iff_finitePresentation_and_naiveCotangent_ext1_vanishes :
    Smooth A B ↔
      FinitePresentation A B ∧
        IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1) := sorry

-- Proof sketch: apply Lemma `15.85.1` to the canonical owner `NL_{B/A}`,
-- whose only nonzero cohomology groups are `H^{-1}(NL_{B/A}) = H1Cotangent A B` and
-- `H^0(NL_{B/A}) = Ω[B⁄A]`, and then rewrite the resulting condition using Proposition
-- `10.138.8`, i.e. `Algebra.formallySmooth_iff`.
/-- Remark 15.85.2 (2): an `A`-algebra `B` is formally smooth if and only if
`Ext^1_B(NL_{B/A}, N)` vanishes for every `B`-module `N`. -/
theorem formallySmooth_iff_naiveCotangent_ext1_vanishes :
    FormallySmooth A B ↔
      IsZero (derivedExtToModuleFunctor (naiveCotangentObject A B) 1) := sorry

end

end Algebra

import Mathlib
import stacks_project.Chap13.Lemma_13_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape Limits

universe u

noncomputable section

variable {R : Type u} [CommRing R]

section

variable (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)

/- Domain-style sampling:
- primary domain: bounded-above acyclic cochain complexes of `R`-modules, together with reduction
  modulo `I` and the owner retract-stability/direct-summand condition on the allowed termwise
  module class;
- sampled owner declarations:
  `CochainComplex.MinusWithTermsIn`,
  `ObjectProperty.map`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`,
  `HomologicalComplex.Acyclic`,
  `ObjectProperty.IsStableUnderRetracts`;
- best owner abstraction: the bounded-above termwise-`PClass` owner
  `CochainComplex.MinusWithTermsIn PClass`, the reduced owner
  `CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`, the canonical retract-stability owner
  `PClass.IsStableUnderRetracts` for the source direct-summand condition, and the reduction
  owner on cochain complexes `ReduceModI.mapHomologicalComplex (up ℤ)`;
- primitive data: the lifted complex `P : CochainComplex.MinusWithTermsIn PClass` and the target
  reduced complex `E : CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`;
- derived API: the acyclicity of the underlying cochain complexes of `P` and `E`, and the
  existence of a reduction isomorphism
  `((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ (E : CpxRI)`.

Source/core/bridge triage:
- `source-facing`: the existence statement of Lemma `15.76.1`;
- `core/canonical`: `CochainComplex.MinusWithTermsIn PClass`, `HomologicalComplex.Acyclic`, and
  the reduction/base-change owners `ReduceModI`, `ReduceModI.mapHomologicalComplex (up ℤ)`,
  together with the chapter owner `PClass.IsStableUnderRetracts`;
- `bridge/view`: the comparison isomorphism
  `e : ((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ (E : CpxRI)`. -/

-- Proof sketch: start above the top nonzero degree of `E` and descend inductively. At each step,
-- split the already constructed acyclic tail into cycles and boundaries, use the retract-stability
-- owner `PClass.IsStableUnderRetracts` for the source direct-summand condition to keep the cycle
-- objects inside `PClass`, lift the next differential from a projective module, and then upgrade
-- surjectivity modulo `I` to actual surjectivity by hypothesis.
/-- Lemma 15.76.1: under the stated projectivity, retract-stability (equivalently, direct-summand
closure in the module category), and surjectivity-modulo-`I` hypotheses on a class `PClass` of
`R`-modules, every bounded-above acyclic complex of
`(R ⧸ I)`-modules whose terms are reductions of objects of `PClass` lifts to a bounded-above
acyclic complex of `R`-modules with terms in `PClass`. -/
theorem exists_boundedAbove_acyclic_lift_of_module_class
    (PClass : ObjectProperty ModR)
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex.MinusWithTermsIn
      (PClass.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))))
    (hacyclic : (E : CpxRI).Acyclic) :
    ∃ (P : CochainComplex.MinusWithTermsIn PClass)
      (e :
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex (up ℤ)).obj
          (P : CpxR) ≅ (E : CpxRI)),
      (P : CpxR).Acyclic := sorry

end

end

import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_76_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "DModRI" => DerivedCategory ModRI
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
variable (PClass : ObjectProperty ModR)
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "PClassModI" => (PClass.map ReduceModI)

/- Domain-style sampling:
- primary domain: bounded-above derived representatives of module complexes, together with
  reduction modulo an ideal;
- sampled owner declarations:
  `CochainComplex.MinusWithTermsIn`,
  `ObjectProperty.IsClosedUnderBinaryCoproducts`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`;
- best owner abstraction: the chosen bounded-above cochain complex with terms in `PClass`
  `P : CochainComplex.MinusWithTermsIn PClass`, together with the chapter owners
  `PClass.IsClosedUnderBinaryCoproducts` and `PClass.IsStableUnderRetracts` for the direct-sum and
  direct-summand conditions; representation / reduction remain direct isomorphism data on that
  owner object, and the reduced complex is already owned by
  `CochainComplex.MinusWithTermsIn (PClass.map ReduceModI)`;
- primitive data: `P : CochainComplex.MinusWithTermsIn PClass`, an isomorphism
  `K ≅ DerivedCategory.Q.obj (P : CpxR)`, and the reduced owner
  `E : CochainComplex.MinusWithTermsIn PClassModI`;
- derived API: the bounded-above condition and termwise membership of `E`, plus existential
  theorems asserting that such a representative or lift exists.

Source/core/bridge triage:
- `source-facing`: existence of a bounded-above `PClass`-complex representing `K`, and of one whose
  reduction modulo `I` is a prescribed complex `E`;
- `core/canonical`: the chosen complex `P` together with owner-style predicates on `P`;
- `bridge/view`: the termwise reduction condition
  `((ReduceModI).mapHomologicalComplex (up ℤ)).obj (P : CpxR) ≅ E`. -/

-- Proof sketch: choose a bounded-above `PClass`-representative of `K`, identify its derived
-- reduction modulo `I` with the termwise scalar extension to `R ⧸ I`, compare that complex with
-- the underlying complex of the owner `E` in `D(R ⧸ I)`, and then lift the resulting acyclic cone
-- by the previous lifting lemma. The cokernel complex of the lifted map gives the desired
-- representative of `K` with prescribed reduction.
/-- Lemma 15.76.2: let `R` be a ring, let `I ⊆ R` be an ideal, and let `PClass` be a class of
`R`-modules satisfying the projectivity, direct-sum closure, retract-stability/direct-summand
closure, and surjectivity-modulo-`I` hypotheses. If `E^•` is a bounded-above complex of
`R/I`-modules representing `K ⊗_R^{\mathbf L} R/I`, and if `K` admits a bounded-above
representative with terms in `PClass`, then there exists a bounded-above complex `P^•` with terms
in `PClass` which represents `K` in `D(R)` and whose reduction modulo `I` is isomorphic to
`E^•`. -/
theorem exists_boundedAbove_representative_lifting_derivedReduction
    (hprojective : ∀ ⦃P : ModR⦄, PClass P → Projective P)
    [PClass.IsClosedUnderBinaryCoproducts]
    [PClass.IsStableUnderRetracts]
    (hsurj : ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
      PClass P₁ → PClass P₂ →
      Function.Surjective ((ReduceModI.map f).hom) →
      Function.Surjective f.hom)
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn PClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hKrep : ∃ P : CochainComplex.MinusWithTermsIn PClass,
      K ≅ DerivedCategory.Q.obj (P : CpxR)) :
    ∃ P : CochainComplex.MinusWithTermsIn PClass,
      (K ≅ DerivedCategory.Q.obj (P : CpxR)) ×
        (ReduceModI.mapHomologicalComplex (ComplexShape.up ℤ)).obj (P : CpxR) ≅ (E : CpxRI) := sorry

end

end CategoryTheory

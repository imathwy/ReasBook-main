import Mathlib
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_76_2

noncomputable section

open CategoryTheory
open ComplexShape
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "FiniteProjectiveClass" => finiteProjectiveModuleProperty R
local notation "FiniteProjectiveClassModI" => finiteProjectiveModuleProperty (R ⧸ I)
local notation "ReduceCpx" =>
  (Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ))

/- Domain-style sampling:
- primary domain: lifting bounded-above finite-projective derived representatives across reduction
  modulo a henselian ideal;
- sampled owner declarations:
  `finiteProjectiveModuleProperty`,
  `exists_finiteProjective_lift_of_henselianRing`,
  `CochainComplex.MinusWithTermsIn`,
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.extendScalars`;
- best owner abstraction: the chosen representative should remain a bounded-above owner complex
  `P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass`, while the quotient-side input should
  use the canonical owner `CochainComplex.MinusWithTermsIn FiniteProjectiveClassModI`; the bridge
  from quotient-side finite projectives to reduction data for `Lemma 15.76.2` is proof-only, via
  `exists_finiteProjective_lift_of_henselianRing`; pseudo-coherence remains on the derived object
  `K`;
- primitive data: the quotient-side bounded-above finite-projective complex `E`, the lifted
  bounded-above finite-projective representative `P`, and the comparison data in `D(R)` and after
  reduction modulo `I`;
- derived API: the existence of such representatives, recorded by the explicit comparison
  isomorphisms supplied by the owner theorem
  `exists_boundedAbove_representative_lifting_derivedReduction`; since those isomorphisms are
  genuine data rather than propositions, the source-facing statement below exposes them as
  explicit existential binders together with the termwise freeness consequence.

Source/core/bridge triage:
- `source-facing`: the lifting-existence statement of Lemma `15.76.9`;
- `core/canonical`: `finiteProjectiveModuleProperty`, `CochainComplex.MinusWithTermsIn`, and
  `K.IsPseudoCoherent`;
- `bridge/view`: the explicit comparison isomorphisms
  `K ≅ DerivedCategory.Q.obj (P : CpxR)` and
  `(ReduceCpx).obj (P : CpxR) ≅ (E : CpxRI)`. -/

-- Proof sketch: apply Lemma `15.76.2` with `PClass` equal to the class of finite projective
-- `R`-modules. The henselian-pair hypothesis and Lemma `15.13.1` lift each finite projective
-- `R/I`-term of `E`, Nakayama's lemma supplies the surjectivity condition via Lemma `15.3.5`, and
-- pseudo-coherence gives a bounded-above finite-projective representative of `K` by Lemma
-- `15.65.5`.
/-- Lemma 15.76.9: let `R` be a commutative ring, let `I ⊆ R` be an ideal, let `E^•` be a
bounded-above cochain complex of finite projective `R/I`-modules, and let `K` be an object of
`D(R)`. Assume `K \otimes_R^{\mathbf L} R/I` is represented by `E^•`, `K` is pseudo-coherent, and
`(R, I)` is a henselian pair. Then there exists a bounded-above cochain complex of finite
projective `R`-modules representing `K` whose reduction modulo `I` is isomorphic to `E^•`;
moreover, if `E^i` is free, then the lifted term `P^i` is free. -/
theorem exists_boundedAbove_finiteProjective_representative_lifting_derivedReduction
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn FiniteProjectiveClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hK : K.IsPseudoCoherent) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
      ∃ eK : K ≅ DerivedCategory.Q.obj (P : CpxR),
        ∃ eE : (ReduceCpx).obj (P : CpxR) ≅ (E : CpxRI),
        ∀ i : ℤ, Module.Free (R ⧸ I) ((E : CpxRI).X i) → Module.Free R ((P : CpxR).X i) := sorry

end

end CategoryTheory

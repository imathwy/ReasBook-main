import Mathlib
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Definition_15_3_1
import stacks_project.Chap15.Lemma_15_76_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "FiniteStablyFreeClass" => finiteStablyFreeModuleProperty R
local notation "FiniteStablyFreeClassModI" => finiteStablyFreeModuleProperty (R ⧸ I)

/- Domain-style sampling:
- primary domain: lifting bounded-above finite stably free derived representatives across
  reduction modulo an ideal inside the Jacobson radical;
- sampled owner declarations:
  `finiteStablyFreeModuleProperty`,
  `CochainComplex.MinusWithTermsIn`,
  `DerivedCategory.IsPseudoCoherent`,
  `exists_boundedAbove_representative_lifting_derivedReduction`,
  `Module.StablyFree`;
- best owner abstraction: the chosen representative should remain a bounded-above owner complex
  `P : CochainComplex.MinusWithTermsIn FiniteStablyFreeClass`, while the quotient-side input
  should use the direct owner `CochainComplex.MinusWithTermsIn FiniteStablyFreeClassModI`; the
  reduction comparison remains a bridge from `P` to `E`, and pseudo-coherence remains on the
  derived object `K`;
- primitive data: the quotient-side and source-side bounded-above finite-stably-free complexes
  `E` and `P`, together with the comparison isomorphisms in `D(R)` and after reduction modulo `I`;
- derived API: the existence of such a lift, plus the termwise freeness consequence.

Source/core/bridge triage:
- `source-facing`: the lifting existence statement of Lemma `15.76.5`;
- `core/canonical`: `finiteStablyFreeModuleProperty`, `CochainComplex.MinusWithTermsIn`,
  `K.IsPseudoCoherent`, and the owner predicates `Module.Finite` / `Module.StablyFree`;
- `bridge/view`: the reduction comparison
  `((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I))
      (ComplexShape.up ℤ)).obj (P : CpxR) ≅ (E : CpxRI))`. -/

-- Proof sketch: apply Lemma `15.76.2` with `PClass` equal to the class of finite stably free
-- `R`-modules. The closure conditions come from Lemma `15.3.2`, lifting termwise reductions comes
-- from Lemma `15.3.3`, the pseudo-coherent hypothesis provides a bounded-above finite free
-- representative of `K`, and Lemma `15.3.5` upgrades the lifted terms to free ones whenever the
-- corresponding term of `E` is free.
/-- Lemma 15.76.5: let `R` be a commutative ring, let `I ⊆ R` be an ideal, let `E^•` be a
bounded-above complex of finite stably free `R/I`-modules, and let `K` be an object of `D(R)`.
Assume `K \otimes_R^{\mathbf L} R/I` is represented by `E^•`, `K` is pseudo-coherent, and
`I ⊆ \operatorname{Jac}(R)` (equivalently, every element of `1 + I` is invertible). Then there
exists a bounded-above complex `P^•` of finite stably free `R`-modules representing `K` whose
reduction modulo `I` is isomorphic to `E^•`; moreover, if `E^i` is free, then `P^i` is free. -/
theorem exists_boundedAbove_finiteStablyFree_representative_lifting_derivedReduction
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn FiniteStablyFreeClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hK : K.IsPseudoCoherent)
    (hI : I ≤ Ring.jacobson R) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteStablyFreeClass,
      ∃ eK : K ≅ DerivedCategory.Q.obj (P : CpxR),
        ∃ eE :
          ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I))
              (ComplexShape.up ℤ)).obj (P : CpxR)) ≅ (E : CpxRI),
          ∀ i : ℤ, Module.Free (R ⧸ I) ((E : CpxRI).X i) → Module.Free R ((P : CpxR).X i) := sorry

end

end CategoryTheory

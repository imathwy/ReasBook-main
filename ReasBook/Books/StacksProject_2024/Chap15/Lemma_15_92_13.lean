import Mathlib
import stacks_project.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory
open scoped DerivedInternalHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.13:
- primary domain: derived completion and derived internal Hom in `D(A)`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  `DerivedCategory.toDerivedCompletion`,
  `DerivedCategory.extendedAlternatingCechDerivedObject`,
  `CategoryTheory.derivedInternalHomTensorIso`;
- best owner abstraction:
  `source-facing`: compatibility of derived completion with `RHom_A(K, -)` and the induced map
    from `K ⟶ K^∧`;
  `core/canonical`: the derived-completion reflector `derivedCompletionOf I hI` and its unit
    `toDerivedCompletion I hI`;
  `bridge/view`: the explicit Čech-model object from Lemma `15.92.10`, which realizes the same
    completion functor for a chosen generating family but should not remain the public owner here.
- primitive data: the ideal `I`, the finite-generation witness `hI : I.FG`, the chosen derived
  internal-Hom owner `H : MonoidalClosed DMod`, and the objects `K`, `L`;
- derived API: any explicit chosen generators and the Čech-model presentation of completion. -/

-- Proof sketch: choose the canonical derived-completion reflector from Remark `15.92.11`, whose
-- explicit Čech-model realization is supplied by Lemma `15.92.10`. Then apply the
-- tensor-Hom currying comparison from Lemma `15.74.1` together with the symmetry of derived tensor
-- product to identify
-- `RHom_A(\check C(f), RHom_A(K, L))` with `RHom_A(K, RHom_A(\check C(f), L))`.
/-- Lemma 15.92.13 (1): for a ring `A`, a finitely generated ideal `I`, and derived
`A`-complexes `K` and `L`, the derived completion of `R\mathrm{Hom}_A(K, L)` is canonically
isomorphic to `R\mathrm{Hom}_A(K, L^\wedge)`. -/
theorem derivedCompletionOf_derivedInternalHom_isIsomorphic
    (I : Ideal A) (hI : I.FG) (H : MonoidalClosed DMod)
    (K L : DMod) :
    IsIsomorphic
      ((RHom[H](K, L))^∧[I, hI])
      (RHom[H](K, L^∧[I, hI])) := sorry

-- Proof sketch: the canonical morphism `K ⟶ K^\wedge` supplied by the adjunction from
-- Remark `15.92.11` induces a morphism
-- `RHom_A(K^\wedge, L^\wedge) ⟶ RHom_A(K, L^\wedge)`. Since `L^\wedge` is already derived
-- complete, the universal property of derived completion makes this morphism an isomorphism.
/-- Lemma 15.92.13 (2): for a ring `A`, a finitely generated ideal `I`, and derived
`A`-complexes `K` and `L`, the canonical map `K ⟶ K^\wedge` induces an isomorphism
`R\mathrm{Hom}_A(K^\wedge, L^\wedge) \to R\mathrm{Hom}_A(K, L^\wedge)`. -/
theorem derivedInternalHom_toDerivedCompletion_isIso
    (I : Ideal A) (hI : I.FG) (H : MonoidalClosed DMod)
    (K L : DMod) :
    IsIso
      (derivedInternalHomMap H (toDerivedCompletion I hI K)
        (𝟙 (L^∧[I, hI]))) := sorry

end

end CategoryTheory

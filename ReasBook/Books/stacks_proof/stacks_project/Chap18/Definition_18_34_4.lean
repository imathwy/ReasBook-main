import Mathlib
import stacks_proof.stacks_project.Chap18.Lemma_18_34_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
variable (F : ringedSiteModuleCategory J O₂)
variable (k : ℕ)

/- Domain-style sampling for Definition 18.34.4:
- primary domain: principal-parts sheaves on a ringed site, defined via the functor of
  differential operators of bounded order;
- sampled owner declarations:
  `Functor.CorepresentableBy`,
  `differentialOperatorsFunctor`,
  `exists_principal_parts_of_order`,
  `principalParts_representsDifferentialOperators`;
- best owner abstraction: the specialized canonical owner
  `(differentialOperatorsFunctor φ F k).CorepresentableBy`.

Primitive-vs-derived split:
- primitive data here: none beyond the already defined differential-operator functor
  `differentialOperatorsFunctor φ F k`;
- derived API: existence of a corepresenting sheaf from `exists_principal_parts_of_order`, plus
  the universal differential operator and factorization API from Lemma `18.34.3`.

Source/core/bridge triage:
- `source-facing`: the phrase “`P` is a module of principal parts of order `k` of `F` relative
  to `φ`”;
- `core/canonical`: `(differentialOperatorsFunctor φ F k).CorepresentableBy`;
- `bridge/view`: `principalPartsDifferentialOperator` and
  `principalParts_representsDifferentialOperators`.

This numbered definition is recall-only, so the file should use the fixed-object corepresenting
owner directly and not introduce a parallel predicate or wrapper declaration.
-/
/- Definition 18.34.4: an `O₂`-module sheaf `P` is a module of principal parts of order `k` of
`F` relative to `φ : O₁ ⟶ O₂` precisely when it corepresents the functor of order-`k`
differential operators out of `F`. -/
#check (differentialOperatorsFunctor φ F k).CorepresentableBy

end

end SheafOfModules.RingedSite

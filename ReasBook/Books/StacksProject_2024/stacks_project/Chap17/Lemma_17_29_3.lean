import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Lemma_18_34_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- Domain triage:
- primary domain: principal-parts representability for differential operators between sheaves of
  modules on the opens site of a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.differentialOperatorsFunctor`,
  `SheafOfModules.RingedSite.exists_principal_parts_of_order`,
  `Functor.IsCorepresentable`;
- best owner abstraction: the generic site-level existence theorem
  `SheafOfModules.RingedSite.exists_principal_parts_of_order`, specialized to the opens site;
- primitive data here: none beyond the generic site-level differential-operator functor
  `SheafOfModules.RingedSite.differentialOperatorsFunctor`;
- derived API: the opens-site source-facing reading of the generic existence theorem.

Source/core/bridge triage:
- `source-facing`: Lemma 17.29.3 for sheaves on a topological space;
- `core/canonical`: `SheafOfModules.RingedSite.exists_principal_parts_of_order`;
- `bridge/view`: specialization from an arbitrary ringed site to the opens site of `X`.

This item adds no new mathematics beyond the generic site-level owner, so it should be a direct
canonical recall rather than a duplicate local functor and existence theorem. -/

/- Lemma 17.29.3: for a morphism `varphi : 𝒪₁ ⟶ 𝒪₂` of sheaves of commutative rings on a
topological space, an `𝒪₂`-module sheaf `ℱ`, and `k : ℕ`, the existence of a sheaf of principal
parts corepresenting order-`k` differential operators out of `ℱ` is exactly the opens-site
specialization of `SheafOfModules.RingedSite.exists_principal_parts_of_order`. -/
recall SheafOfModules.RingedSite.exists_principal_parts_of_order

end

import Mathlib
import stacks_project.Chap12.Lemma_12_10_3
import stacks_project.Chap13.Lemma_13_17_1
import stacks_project.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

/- Domain-style sampling:
- primary domain: object properties on `ModuleCat A` and the generic derived-category owner
  `derivedCategoryCohomologyInProperty`;
- sampled owner-side declarations:
  `ObjectProperty.IsWeakSerreClass`,
  `ObjectProperty.weakSerreSubcategory_inclusion_exact`,
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategory.derivedCompleteObjectProperty`,
  `ModuleCat.derivedCompleteObjectProperty`;
- best owner abstraction: the object-property owners
  `ModuleCat.derivedCompleteObjectProperty I` and
  `DerivedCategory.derivedCompleteObjectProperty I`;
- primitive data: the module and derived derived-complete predicates from
  `Definition_15_92_4`;
- derived API: the weak-Serre structure on the module owner and the identification of the
  derived owner with the generic cohomology-in-property owner.

Layer triage:
- `source-facing`: derived-complete modules and derived-complete objects with respect to `I`;
- `core/canonical`: `ModuleCat.derivedCompleteObjectProperty I`,
  `DerivedCategory.derivedCompleteObjectProperty I`, and
  `derivedCategoryCohomologyInProperty`;
- `bridge/view`: the pointwise iff restatement below, derived from the owner-level equality. -/

-- Proof sketch: Lemma 15.92.1 identifies derived completeness with vanishing of
-- `Ext^n_A(A_f, -)` for every `f ∈ I`; the associated long exact sequences show closure under
-- kernels, cokernels, and extensions, and Lemma 12.10.3 packages these closures into the weak
-- Serre structure.
/-- Lemma 15.92.6: the derived complete `A`-modules with respect to `I` form a weak Serre
subcategory of `Mod_A`. -/
theorem derivedCompleteObjectProperty_isWeakSerreClass :
    IsWeakSerreClass (ModuleCat.derivedCompleteObjectProperty I) := sorry

namespace DerivedCategory

local notation "DMod" => DerivedCategory (ModuleCat A)

-- Proof sketch: use Lemma 15.92.1 to pass between derived completeness of a complex and the
-- vanishing criterion after localizing at each `f ∈ I`. The long exact cohomology sequences show
-- that this criterion holds degreewise on the cohomology modules of `K`.
/-- The derived-complete owner on `D(A)` is exactly the generic cohomology-in-property owner
attached to derived-complete modules. -/
theorem derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty :
    DerivedCategory.derivedCompleteObjectProperty I =
      derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) := by
  ext K
  sorry

/-- Companion pointwise restatement of
`derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty`. -/
theorem isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty
    (K : DMod) :
    K.IsDerivedCompleteWithRespectTo I ↔
      derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) K := by
  change DerivedCategory.derivedCompleteObjectProperty I K ↔
    derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) K
  exact
    (congrArg (fun P : ObjectProperty DMod ↦ P K)
      (derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty I)).to_iff


end DerivedCategory

end

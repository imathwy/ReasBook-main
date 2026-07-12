import Mathlib
import StacksProject_2024.Chap13.Definition_13_37_1
import StacksProject_2024.Chap18.«18_19_2_1»
import StacksProject_2024.Chap18.Lemma_18_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)

/-- Helper for Lemma 18.30.4: the represented additive Hom functor from `j_{U!}\mathcal O_U`. -/
private abbrev localizedStructureModuleExtensionByZeroHomFunctor :
    ringedSiteModuleCategory J 𝒪 ⥤ AddCommGrpCat :=
  preadditiveCoyoneda.obj (op (j![𝒪, U]))

/-- Helper for Lemma 18.30.4: the additive group of sections over `U`, viewed as a functor. -/
private abbrev moduleSectionsAsAddCommGrp :
    ringedSiteModuleCategory J 𝒪 ⥤ AddCommGrpCat :=
  SheafOfModules.evaluation (ringSheaf J 𝒪) (op U) ⋙
    forget₂ (ModuleCat ((ringSheaf J 𝒪).1.obj (op U))) AddCommGrpCat

/- Domain-style sampling for Lemma 18.30.4:
- primary domain: sheaves of modules on a ringed site, the standard summands
  `j_{U!}\mathcal O_U`, and compactness of the represented additive Hom-functor;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `localizedStructureModuleExtensionByZero`,
  `localizedStructureModuleExtensionByZero_homEquiv`,
  `quasiCompactObject_module_evaluation_preserves_direct_sums`,
  `preadditiveCoyoneda.obj`;
- best owner abstraction: the earlier-project owner for the mathematics
  “`Hom(K, -)` preserves direct sums” is `CategoryTheory.IsCompactObject K`, so this file should
  expose quasi-compactness of `j_{U!}\mathcal O_U` through
  `IsCompactObject (localizedStructureModuleExtensionByZero 𝒪 U)`, with the source-facing sections
  comparison carried by
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U`;
- primitive-vs-derived split: the primitive data are only the ringed site `(C, J, 𝒪)`, the object
  `U`, and the quasi-compactness hypothesis on `U`; compactness and the represented additive
  Hom-functor preserving direct sums are derived from the owner
  `localizedStructureModuleExtensionByZero 𝒪 U`, the compactness predicate
  `CategoryTheory.IsCompactObject`, and the bridge
  `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that `j_{U!}\mathcal O_U` is compact, equivalently that
  `Hom_\mathcal O(j_{U!}\mathcal O_U, -)` preserves direct sums for quasi-compact `U`;
- `core/canonical`: `CategoryTheory.IsCompactObject (localizedStructureModuleExtensionByZero 𝒪 U)`;
- `bridge/view`: the comparison `localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U` and the
  evaluation-preserves-direct-sums theorem
  `quasiCompactObject_module_evaluation_preserves_direct_sums`.

This file should therefore state the lemma directly as compactness of `j_{U!}\mathcal O_U`,
deriving the represented-Hom direct-sum preservation surface through the existing
`IsCompactObject` instance and the sections comparison
`localizedStructureModuleExtensionByZero_homEquiv`. -/

-- Proof sketch: identify `Hom_\mathcal O(j_{U!}\mathcal O_U, -)` with the sections functor
-- `\mathcal F ↦ \mathcal F(U)` via `localizedStructureModuleExtensionByZero_homEquiv`, then apply
-- the quasi-compact direct-sum preservation statement for sections from Lemma `18.30.3`. The
-- represented additive Hom-functor preserving direct sums is then recovered from the compactness
-- instance attached to `IsCompactObject`.
/-- Helper for Lemma 18.30.4: `localizedStructureModuleExtensionByZero_homEquiv` is natural in
the target module sheaf. -/
private theorem localizedStructureModuleExtensionByZeroHomEquivNaturality
    {ℱ 𝒢 : ringedSiteModuleCategory J 𝒪}
    (β : j![𝒪, U] ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β) := by
  -- The owner equivalence is defined by target-functorial constructions, so target naturality is
  -- definitional.
  rfl

/-- Helper for Lemma 18.30.4: the owner equivalence preserves addition on morphisms. -/
private theorem localizedStructureModuleExtensionByZeroHomEquivMapAdd
    (ℱ : ringedSiteModuleCategory J 𝒪)
    (α β : j![𝒪, U] ⟶ ℱ) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ (α + β) =
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ α +
        localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β := by
  -- Addition is respected definitionally by the additive owner equivalence.
  rfl

/-- Helper for Lemma 18.30.4: the Hom-evaluation comparison upgrades to an additive equivalence on
each target sheaf. -/
private noncomputable def localizedStructureModuleExtensionByZeroHomAddEquiv
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    (localizedStructureModuleExtensionByZeroHomFunctor (J := J) (𝒪 := 𝒪) (U := U)).obj ℱ ≃+
      ((moduleSectionsAsAddCommGrp (J := J) (𝒪 := 𝒪) (U := U)).obj ℱ) where
  toFun := localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ
  invFun := (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ).symm
  left_inv := Equiv.symm_apply_apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ)
  right_inv := Equiv.apply_symm_apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ)
  map_add' := localizedStructureModuleExtensionByZeroHomEquivMapAdd (J := J) (𝒪 := 𝒪)
    (U := U) (ℱ := ℱ)

/-- Helper for Lemma 18.30.4: each component of the represented-Hom functor is additively
identified with sections over the same object. -/
private noncomputable def localizedStructureModuleExtensionByZeroPreadditiveCoyonedaIsoEvaluationComponent
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    (localizedStructureModuleExtensionByZeroHomFunctor (J := J) (𝒪 := 𝒪) (U := U)).obj ℱ ≅
      ((moduleSectionsAsAddCommGrp (J := J) (𝒪 := 𝒪) (U := U)).obj ℱ) :=
  -- Use the canonical additive-equivalence-to-isomorphism bridge instead of reproving the inverse
  -- identities componentwise.
  (localizedStructureModuleExtensionByZeroHomAddEquiv (J := J) (𝒪 := 𝒪) (U := U) ℱ).toAddCommGrpIso

/-- Helper for Lemma 18.30.4: the Hom-evaluation comparison is natural as a morphism of additive
functors. -/
private theorem localizedStructureModuleExtensionByZeroPreadditiveCoyonedaIsoEvaluationNaturality
    {ℱ 𝒢 : ringedSiteModuleCategory J 𝒪} (α : ℱ ⟶ 𝒢) :
    (localizedStructureModuleExtensionByZeroHomFunctor (J := J) (𝒪 := 𝒪) (U := U)).map α ≫
        (localizedStructureModuleExtensionByZeroPreadditiveCoyonedaIsoEvaluationComponent (J := J)
          (𝒪 := 𝒪) (U := U) 𝒢).hom =
      (localizedStructureModuleExtensionByZeroPreadditiveCoyonedaIsoEvaluationComponent (J := J)
        (𝒪 := 𝒪) (U := U) ℱ).hom ≫
        ((moduleSectionsAsAddCommGrp (J := J) (𝒪 := 𝒪) (U := U)).map α) := by
  -- Route correction: compare the two additive morphisms on an element `β`; after unfolding the
  -- component map, this is exactly the owner equivalence naturality.
  ext β
  exact localizedStructureModuleExtensionByZeroHomEquivNaturality (J := J) (𝒪 := 𝒪) (U := U)
    (β := β) (α := α)

/-- Helper for Lemma 18.30.4: represented Hom from `j_{U!}\mathcal O_U` is naturally identified
with evaluation at `U`. -/
private noncomputable def localizedStructureModuleExtensionByZeroPreadditiveCoyonedaIsoEvaluation
    :
    localizedStructureModuleExtensionByZeroHomFunctor (J := J) (𝒪 := 𝒪) (U := U) ≅
      moduleSectionsAsAddCommGrp (J := J) (𝒪 := 𝒪) (U := U) :=
  NatIso.ofComponents
    (localizedStructureModuleExtensionByZeroPreadditiveCoyonedaIsoEvaluationComponent (J := J)
      (𝒪 := 𝒪) (U := U))
    (localizedStructureModuleExtensionByZeroPreadditiveCoyonedaIsoEvaluationNaturality (J := J)
      (𝒪 := 𝒪) (U := U))

/-- Helper for Lemma 18.30.4: quasi-compactness of `U` makes the represented Hom functor preserve
`Discrete I`-coproducts. -/
private theorem localizedStructureModuleExtensionByZeroPreservesDiscreteCoproducts
    (hU : J.QuasiCompactObject U) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      (localizedStructureModuleExtensionByZeroHomFunctor (J := J) (𝒪 := 𝒪) (U := U)) := by
  -- Route correction: instead of unfolding `j_!`, transport the existing direct-sum preservation
  -- theorem for evaluation across the Hom-evaluation natural isomorphism.
  let e := localizedStructureModuleExtensionByZeroPreadditiveCoyonedaIsoEvaluation (J := J)
    (𝒪 := 𝒪) (U := U)
  let _ :
      PreservesColimitsOfShape (Discrete I)
        (moduleSectionsAsAddCommGrp (J := J) (𝒪 := 𝒪) (U := U)) :=
    quasiCompactObject_module_sections_preserves_direct_sums (J := J) (𝒪 := ringSheaf J 𝒪)
      (W := U) hU I
  exact CategoryTheory.Limits.preservesColimitsOfShape_of_natIso e.symm

/-- Lemma 18.30.4: if `U` is quasi-compact in a ringed site `(\mathcal C, \mathcal O)`, then
`j_{U!}\mathcal O_U` is a compact object of `Mod(\mathcal O)`. -/
theorem localizedStructureModuleExtensionByZero_isCompactObject
    (hU : J.QuasiCompactObject U) :
    IsCompactObject (j![𝒪, U]) := by
  -- Compactness asks for preservation of each `Discrete I`-coproduct shape by the represented
  -- additive Hom functor.
  refine ⟨fun I ↦ ?_⟩
  -- The previous helper already transported this preservation statement from evaluation at `U`.
  exact localizedStructureModuleExtensionByZeroPreservesDiscreteCoproducts (J := J)
    (𝒪 := 𝒪) (U := U) hU I

end SheafOfModules.RingedSite

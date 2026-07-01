import Mathlib
import stacks_project.Chap20.«20_54_2_1»
import stacks_project.Chap21.Lemma_21_20_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

universe u v

namespace RingedSite

/- Domain-style sampling for Lemma 21.50.1:
- primary domain: projection-formula morphisms in monoidal derived categories of module sheaves on
  ringed sites;
- sampled declarations:
  `RingedSite.Hom.localizedRestriction`,
  `RingedSite.Hom.ModuleDerived`,
  `CategoryTheory.projectionFormulaMorphism`,
  `SheafOfModules.RingedSite.DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: the general ringed-site perfectness owner
    `RingedSite.DerivedCategory.IsPerfect` and the resulting `IsIso` statement for the canonical
    projection-formula morphism;
  `core/canonical`: `CategoryTheory.projectionFormulaMorphism` together with the ringed-site
    derived category `RingedSite.Hom.ModuleDerived`;
  `bridge/view`: the Chapter 21 commutative-ringed-site owner
    `SheafOfModules.RingedSite.DerivedCategory.IsPerfect`, which matches the same mathematical
    notion under stronger commutativity hypotheses but does not cover arbitrary `RingCat`-valued
    ringed sites;
- primitive data: the local strictly perfect model criterion for a representative complex and the
  resulting derived perfectness predicate on `RingedSite.Hom.ModuleDerived`;
- derived API: the perfectness owner `RingedSite.DerivedCategory.IsPerfect` and the theorem
  `projectionFormulaMorphism_isIso_of_isPerfect`. -/

section Perfectness

variable {X : RingedSite.{u, v}}

private abbrev ModuleComplex (X : RingedSite.{u, v}) :=
  CochainComplex (RingedSite.Hom.ModuleCat X) ℤ

private def isStrictlyPerfectComplex
    {Z : RingedSite.{u, v}} (E : ModuleComplex Z) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, ∃ I : Type (max u v), Finite I ∧
      Nonempty (Retract (E.X i)
        (SheafOfModules.free.{max u v} I : RingedSite.Hom.ModuleCat Z))

variable [∀ U : X, (RingedSite.Hom.localizedRestriction X U).PreservesZeroMorphisms]

private abbrev localizedRestrictionComplex (U : X) :
    ModuleComplex X ⥤ ModuleComplex (X.localization U) :=
  show ModuleComplex X ⥤ ModuleComplex (X.localization U) from
    (RingedSite.Hom.localizedRestriction X U).mapHomologicalComplex (ComplexShape.up ℤ)

private def isPerfectComplex
    (E : ModuleComplex X) : Prop :=
  ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ E' : ModuleComplex (X.localization I.Y),
      ∃ α : E' ⟶ (localizedRestrictionComplex I.Y).obj E,
        isStrictlyPerfectComplex E' ∧ QuasiIso α

namespace DerivedCategory

/-- An object of `D(\mathcal O_X)` on a ringed site is perfect if it is represented by a complex
whose localizations are quasi-isomorphic to strictly perfect complexes. -/
def IsPerfect (K : RingedSite.Hom.ModuleDerived X) : Prop :=
  ∃ E : ModuleComplex X,
    ∃ α : DerivedCategory.Q.obj E ⟶ K,
      isPerfectComplex E ∧ IsIso α

end DerivedCategory

end Perfectness

end RingedSite

namespace RingedSite.Hom

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [∀ U : Y, (localizedRestriction Y U).PreservesZeroMorphisms]
variable [MonoidalCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]

variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

variable
  (pullbackTensorComparison :
    ∀ (K L : ModuleDerived Y),
      ((modulePullbackDerived f).obj (((curriedTensor (ModuleDerived Y)).obj L).obj K)) ≅
        (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj L)).obj
          ((modulePullbackDerived f).obj K)))

-- Proof sketch: the statement is local on the target ringed topos, so for a perfect object `K`
-- one works on a cover where `K` is represented by a strictly perfect complex. The projection
-- formula is immediate for finite free summands and stable under finite direct sums, summands, and
-- stupid truncations, reducing to the case `K = \mathcal O_{\mathcal D}[n]`.
/-- Lemma 21.50.1: for a morphism of ringed topoi formalized by the ringed-site morphism `f`, if
`K` is a perfect object of `D(\mathcal O_\mathcal D)`, then the canonical projection-formula
morphism
`K \otimes_{\mathcal O_\mathcal D}^{\mathbf L} Rf_* E ⟶
  Rf_*(Lf^* K \otimes_{\mathcal O_\mathcal C}^{\mathbf L} E)`
is an isomorphism in `D(\mathcal O_\mathcal D)`. -/
theorem projectionFormulaMorphism_isIso_of_isPerfect
    (E : ModuleDerived X) (K : ModuleDerived Y)
    (hK : DerivedCategory.IsPerfect K) :
    IsIso
      (projectionFormulaMorphism
        (modulePullbackDerived f)
        (modulePushforwardDerived f)
        adj
        (fun A B ↦ pullbackTensorComparison B A)
        E
        K) := sorry

end

end RingedSite.Hom

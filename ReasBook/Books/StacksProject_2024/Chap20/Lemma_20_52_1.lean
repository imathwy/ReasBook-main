import StacksProject_2024.Chap20.Lemma_20_34_4
import StacksProject_2024.Chap21.Lemma_21_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.52.1:
- primary domain: `\mathcal O_X`-modules on a ringed space, their global sections, and the finite
  projective/full-subcategory owner on the module side;
- sampled owner declarations:
  `(RingedSpace.Modules X)`,
  `globalSectionsRing`,
  `moduleGlobalSectionsFunctor`,
  `CategoryTheory.finiteFreeRetractModuleProperty`,
  `CategoryTheory.finiteFreeRetractModuleCat`,
  `CategoryTheory.finiteFreeRetractModules_equiv_finiteProjectiveModules`;
- best owner abstraction: the generic ringed-site owner
  `CategoryTheory.finiteFreeRetractModuleCat`, specialized to `X.ringCatSheaf`, whose inclusion still
  comes from the owner
  property `CategoryTheory.finiteFreeRetractModuleProperty X.ringCatSheaf`, together with the
  chapter-level global-sections owner `moduleGlobalSectionsFunctor X`;
- primitive data: an object of the finite-free-retract full subcategory of `(RingedSpace.Modules X)`;
- derived API: the lifted global-sections functor on the full subcategory and the source-facing
  equivalence statement for that specific functor.

Source/core/bridge triage:
- `source-facing`: Lemma 20.52.1, formulated for the global-sections functor on a ringed space;
- `core/canonical`: `(RingedSpace.Modules X)`, `globalSectionsRing`, `moduleGlobalSectionsFunctor`, and
  `CategoryTheory.finiteFreeRetractModuleCat`;
- `bridge/view`: the lifted functor below from the finite-free-retract full subcategory to
  `FiniteProjectiveModuleCat (globalSectionsRing X)`.

The local finite-free-retract predicate and the local ringed-space wrappers for `\mathcal O_X`-
modules/global sections would duplicate owner declarations already present earlier in the project,
so this file reuses those owners directly. The source category of the bridge functor below is the
owner alias `CategoryTheory.finiteFreeRetractModuleCat`, specialized to `X.ringCatSheaf`, while the
actual inclusion functor
still comes from the owner property `CategoryTheory.finiteFreeRetractModuleProperty X.ringCatSheaf`. -/

variable {X : RingedSpace.{u}}

private abbrev finiteFreeRetractModuleSubcategory (X : RingedSpace.{u}) :=
  finiteFreeRetractModuleCat X.ringCatSheaf

-- Proof sketch: if `ℱ` is a retract of a finite free sheaf `\mathcal O_X^{\oplus I}`, then taking
-- global sections exhibits `Γ(X, ℱ)` as a retract of the finite free `Γ(X, \mathcal O_X)`-module
-- `R^{\oplus I}`. A retract of a finite free module is projective, and finite generation is
-- inherited from the finite free ambient module.
/-- Global sections send a direct summand of a finite free `\mathcal O_X`-module to a finite
projective module over `Γ(X, \mathcal O_X)`. -/
theorem moduleGlobalSections_mem_finiteProjectiveModuleProperty
    (ℱ : finiteFreeRetractModuleSubcategory X) :
    finiteProjectiveModuleProperty (globalSectionsRing X)
      ((moduleGlobalSectionsFunctor X).obj ℱ.obj) :=
  sorry

/-- The global-sections functor restricted to `\mathcal O_X`-modules that are direct summands of
finite free module sheaves. -/
abbrev finiteFreeRetractGlobalSectionsFunctor (X : RingedSpace.{u}) :
    finiteFreeRetractModuleSubcategory X ⥤
      FiniteProjectiveModuleCat (globalSectionsRing X) :=
  (finiteProjectiveModuleProperty (globalSectionsRing X)).lift
    ((finiteFreeRetractModuleProperty X.ringCatSheaf).ι ⋙
      moduleGlobalSectionsFunctor X)
    (fun ℱ ↦ moduleGlobalSections_mem_finiteProjectiveModuleProperty ℱ)

-- Proof sketch: the functor is global sections. On objects, a retract of a finite free
-- `\mathcal O_X`-module goes to a retract of a finite free `Γ(X, \mathcal O_X)`-module, hence to
-- a finite projective module. Conversely, Lemma `17.10.5` associates to a finite projective
-- `Γ(X, \mathcal O_X)`-module a sheaf of `\mathcal O_X`-modules; because finite projective
-- modules are retracts of finite free modules, this associated sheaf lands in the designated full
-- subcategory. The adjunction from Lemma `17.10.5` then provides the inverse hom-set comparison.
/-- Lemma 20.52.1: if `R = Γ(X, \mathcal O_X)`, then the global-sections functor identifies the
full subcategory of `\mathcal O_X`-modules that are direct summands of finite free modules with
the full subcategory of finite projective `R`-modules. -/
theorem finiteFreeRetractGlobalSectionsFunctor_isEquivalence
    (X : RingedSpace.{u}) :
    Functor.IsEquivalence (finiteFreeRetractGlobalSectionsFunctor X) :=
  sorry

end AlgebraicGeometry.RingedSpace

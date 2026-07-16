import Mathlib
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_21
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_22
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_3
import StacksProject_2024.stacks_project.Chap20.Bounded_below_derived_sections_at_open
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core

open CategoryTheory
open CategoryTheory.CohomologicalDeltaFunctor
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => X.Modules
local notation "ΓModX" => ModuleCat (globalSectionsRing X)

/- Domain-style sampling for the global-sections cohomological `δ`-functor:
- primary domain: the long exact cohomology sequence on `\mathcal O_X`-modules obtained from the
  canonical short-exact-sequence boundary `singleδ` after applying derived global sections;
- sampled owner declarations:
  `moduleDerivedGlobalSections`,
  `ShortComplex.ShortExact.singleδ`,
  `DeltaFunctor.postcomposeExactFunctor`,
  `DeltaFunctor.toCohomologicalDeltaFunctor`,
  `moduleCohomologyAtOpen`;
- best owner abstraction:
  `source-facing`: the Chapter 20 cohomological `δ`-functor on `X.Modules` computing
    `H^p(X, -)`;
  `core/canonical`: `moduleDerivedGlobalSections`, `ShortComplex.ShortExact.singleδ`,
    `DeltaFunctor.postcomposeExactFunctor`, and
    `DeltaFunctor.toCohomologicalDeltaFunctor`;
  `bridge/view`: the bounded-below global-sections owner used only to prove the degree-`-1`
    vanishing input, and the degreewise identification with
    `moduleCohomologyAtOpen (⊤ : Opens X.carrier)`.
- primitive vs. derived:
  primitive data are just the ringed space `X` and the canonical global-sections functor on
  `X.Modules`;
  the connecting maps and degreewise cohomology owners are derived API and should be exposed
  through the cohomological `δ`-functor owner below rather than redefined locally downstream. -/

private instance moduleDerivedGlobalSections_commShift :
    (moduleDerivedGlobalSections X).CommShift ℤ := by
  sorry

private instance moduleDerivedGlobalSections_isTriangulated :
    (moduleDerivedGlobalSections X).IsTriangulated := by
  sorry

private abbrev singleToDerivedDeltaFunctor :
    DeltaFunctor ModX (DerivedCategory ModX) where
  toFunctor := DerivedCategory.singleFunctor ModX 0
  additive := inferInstance
  δ := fun {_} hS ↦ hS.singleδ
  map_distinguished := fun {_} hS ↦ hS.singleTriangle_distinguished
  δ_naturality := fun {_ _} hS hT φ ↦ by
    refine CommSq.mk ?_
    simpa using
      (ShortComplex.ShortExact.singleTriangle.map (h₁ := hS) (h₂ := hT) φ).comm₃.symm

private abbrev globalSectionsDeltaFunctor :
    DeltaFunctor ModX (DerivedCategory ΓModX) :=
  singleToDerivedDeltaFunctor.postcomposeExactFunctor
    (moduleDerivedGlobalSections X)

private theorem globalSectionsDeltaFunctor_hneg
    (ℳ : ModX) :
    CategoryTheory.Limits.IsZero
      (((DerivedCategory.homologyFunctor ΓModX 0).shift (-1)).obj
      (globalSectionsDeltaFunctor (X := X).obj ℳ)) := by
  sorry

/-- The Chapter 20 cohomological `δ`-functor on `\mathcal O_X`-modules obtained by applying
derived global sections to the canonical boundary morphism `singleδ` of a short exact sequence. -/
abbrev globalCohomologyDeltaFunctor (X : RingedSpace.{u}) :
    CohomologicalDeltaFunctor X.Modules (ModuleCat (globalSectionsRing X)) :=
  globalSectionsDeltaFunctor.toCohomologicalDeltaFunctor
    (DerivedCategory.homologyFunctor (ModuleCat (globalSectionsRing X)) 0)
    (globalSectionsDeltaFunctor_hneg (X := X))

/-- The degree-`p` branch of `globalCohomologyDeltaFunctor X` computes the canonical top-open
module cohomology owner `moduleCohomologyAtOpen (⊤ : Opens X.carrier)`. -/
theorem globalCohomologyDegree_obj_eq_moduleCohomologyAtOpen
    (X : RingedSpace.{u}) (ℱ : X.Modules) (p : ℕ) :
    ((globalCohomologyDeltaFunctor X p).obj).obj ℱ =
      moduleCohomologyAtOpen (⊤ : Opens X.carrier) ℱ p := by
  sorry

end AlgebraicGeometry.RingedSpace

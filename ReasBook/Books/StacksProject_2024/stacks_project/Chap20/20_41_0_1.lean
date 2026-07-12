import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import StacksProject_2024.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex.HomComplex
open CochainComplex.HomComplex.CohomologyClass
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {U : Opens X.carrier}

local notation "ModU" => openSubspaceModuleCategory X U

/- Domain-style sampling for 20.41.0.1:
- primary domain: cohomology of Hom complexes and morphisms in the homotopy category of cochain
  complexes of `𝒪_U`-modules;
- sampled owner declarations:
  `openSubspaceModuleCategory`,
  `moduleRestrictionToOpen`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`,
  `stacks_project/Chap15/15_72_0_1.lean`;
- best owner abstraction: the canonical owner layer is the Hom-complex cohomology-class API,
  instantiated in the Chapter 20 open-subspace module category
  `openSubspaceModuleCategory X U`;
- primitive data vs derived API:
  the primitive inputs are the ambient category `openSubspaceModuleCategory X U`, the complexes
  `L`, `M`, and the degree `n`; the displayed equivalence is already the derived upstream composite
  `(homologyAddEquiv L M n).trans homAddEquiv`;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(Γ(U, Hom^•(L^•, M^•))) ≃ Hom_{K(𝒪_U)}(L^•, M^•⟦n⟧)`;
  `core/canonical`: `ModU`,
  `homologyAddEquiv`, and `homAddEquiv`;
  `bridge/view`: the direct composite equivalence below.

This file therefore targets the `bridge/view` layer. Since mathlib names the two canonical owner
equivalences but not their composite, the correct local surface is a thin named alias whose body is
exactly the direct canonical composite below, with no extra wrapper API.
-/

variable (L M : CochainComplex ModU ℤ) (n : ℤ)

/-- 20.41.0.1: the degree-`n` homology of the Hom complex on `U` identifies with morphisms
`L ⟶ M⟦n⟧` in the homotopy category. This is the direct canonical composite of the standard
homology-to-cohomology-class equivalence with the standard cohomology-class-to-homotopy-morphism
equivalence. -/
abbrev openSubspaceHomComplexHomologyToHomotopyHomAddEquiv :
    (CochainComplex.HomComplex L M).homology n ≃+
      ((HomotopyCategory.quotient ModU _).obj L ⟶
        (HomotopyCategory.quotient ModU _).obj (M⟦n⟧)) :=
  -- Expose the canonical upstream bridge as the named item declaration.
  (homologyAddEquiv L M n).trans homAddEquiv

end

end AlgebraicGeometry.RingedSpace

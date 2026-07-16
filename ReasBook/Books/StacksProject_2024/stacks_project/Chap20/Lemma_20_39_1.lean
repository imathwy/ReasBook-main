import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core
import StacksProject_2024.stacks_project.Chap15.Lemma_15_94_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpaceDerivedGlobalSections

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.39.1:
- primary domain: principal derived-completion comparison diagrams specialized to derived global
  sections on a ringed space;
- sampled owner declarations:
  `globalSectionsRing X`,
  `moduleGlobalSectionsFunctor X`,
  `moduleDerivedGlobalSections X`,
  `principalDerivedCompletion_cohomology_has_comparison_diagram`;
  completion is then expressed with the chapter notation `K^∧[I, hI]`.
- best owner abstraction:
  `source-facing`: the ringed-space specialization with `K = RΓ(X, E)` for
    `E ∈ D(𝒪_X)`;
  `core/canonical`: `globalSectionsRing X`, `moduleGlobalSectionsFunctor X`,
  `moduleDerivedGlobalSections X`, `principalDerivedCompletion_cohomology_has_comparison_diagram`,
  and the chapter completion notation `K^∧[I, hI]`;
  `bridge/view`: the specialization of the Chapter 15 principal derived-completion comparison
    theorem along the Chapter 20 owner `moduleDerivedGlobalSections X`.
- primitive vs. derived:
  primitive data are the ringed space `X`, the global section `f`, and the derived object
  `E : DerivedCategory (RingedSpace.Modules X)`;
  the quotient/torsion towers, the completed object
  `(RΓ(X, E))^∧[(f), principalIdeal_fg f]`, and the comparison diagram are derived API.

Source/core/bridge triage:
- `source-facing`: Lemma 20.39.1, read as the comparison diagram for the cohomology of
  `RΓ(X, E)` and the completed object `(RΓ(X, E))^∧[(f), principalIdeal_fg f]`;
- `core/canonical`: `globalSectionsRing X`, `moduleDerivedGlobalSections X`,
  `principalDerivedCompletion_cohomology_has_comparison_diagram`, and `K^∧[I, hI]`;
- `bridge/view`: the global-sections specialization of the Chapter 15 comparison theorem.

This file should therefore remain a `bridge/view` recall item: it specializes the Chapter 15
comparison diagram to the canonical derived global-sections construction and the global sections
ring `Γ(X, 𝒪_X)`, and exposes the completed derived-global-sections object through the
chapter completion notation, without introducing a second local theorem shell.
-/

variable (f : globalSectionsRing X) (E : DerivedCategory (RingedSpace.Modules X)) (p : ℤ)

/- Lemma 20.39.1: this is the Chapter 15 principal derived-completion comparison diagram
specialized to the ringed-space global-sections ring `Γ(X, 𝒪_X)` and the derived global sections
object `RΓ(X, E)`. -/
#check
  (principalDerivedCompletion_cohomology_has_comparison_diagram f ((RΓ(X)).obj E) p)

end

end AlgebraicGeometry.RingedSpace

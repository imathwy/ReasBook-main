import Mathlib
import stacks_project.Chap13.Definition_13_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CochainComplex

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-
Domain-style sampling:
- primary domain: bounded-below injective resolutions of cochain complexes;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectiveResolution.injective`,
  `CochainComplex.InjectiveResolution.quasiIso`,
  `CategoryTheory.HomotopyResolutionFunctor`;
- best owner abstraction: `CochainComplex.InjectiveResolution` already owns the chosen resolving
  complex, comparison map, bounded-below structure, and termwise-injective/quasi-isomorphism API
  for a single bounded-below complex;
- primitive data here: only the objectwise assignment `K ↦ InjectiveResolution K`;
- derived API here: the chosen complex, the comparison map, and the basic resolution facts, all of
  which should be read directly from the owner `InjectiveResolution` instead of being re-exported
  under parallel local names.

Source/core/bridge triage:
- `source-facing`: `ResolutionFunctorOne` is the Stacks-definition objectwise choice of bounded-
  below injective resolutions;
- `core/canonical`: `CochainComplex.InjectiveResolution` is the project owner for the data of a
  chosen injective resolution of one complex;
- `bridge/view`: later files build the homotopy-category realization from this objectwise choice.
-/
/-- Definition 13.23.2: a resolution functor 1 on an abelian category assigns to each
bounded-below cochain complex `K : Plus 𝒜` a chosen bounded-below injective resolution of
`K`, namely an element of the canonical owner `InjectiveResolution K.obj`. -/
abbrev ResolutionFunctorOne :=
  (K : Plus 𝒜) → InjectiveResolution K.obj

end CochainComplex

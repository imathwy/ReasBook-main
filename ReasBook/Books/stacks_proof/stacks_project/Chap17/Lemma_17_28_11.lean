import StacksProject_2024.Chap18.Lemma_18_33_9

open CategoryTheory
open TopCat
open scoped RelativeDerivation

universe u

section

variable {X : TopCat.{u}}
variable {O₁ O₂ A : TopCat.Sheaf CommRingCat.{u} X}
variable (φ : O₁ ⟶ O₂) (α : O₁ ⟶ A) (π : A ⟶ O₂)

/- Domain-style sampling for Lemma 17.28.11:
- primary domain: square-zero extensions of sheaves of commutative rings on a fixed topological
  space, their intrinsic kernel ideal sheaves, restriction of scalars along a chosen section, and
  relative derivations into that kernel;
- sampled owner declarations:
  `IsAlgebraSection`,
  `kernelIdealSheaf`,
  `kernelIdealSheafModule`,
  `existsUnique_derivation_of_algebraSection`;
- best owner abstraction: the generic-site owner API from `Chap18/Lemma_18_33_9`, specialized to
  the site `Opens.grothendieckTopology X`;
- primitive data: only the structure maps `φ : O₁ ⟶ O₂`, `α : O₁ ⟶ A`, and `π : A ⟶ O₂`;
- derived API: compatible algebra sections, the intrinsic kernel ideal sheaf and its descended
  `O₂`-module structure, the perturbation predicate, and the two existence/uniqueness theorems.

Source/core/bridge triage:
- `core/canonical`: the general-site declarations from `Chap18/Lemma_18_33_9`;
- `bridge/view`: this file is only the specialization from an arbitrary site to the site of opens
  of a topological space.

This file therefore reuses the generic-site owner directly instead of redeclaring a second
topological-space-specific API with the same mathematical content. -/

/- Companion recall: the compatible-section predicate and the intrinsic kernel constructions used
in Lemma 17.28.11 are already owned by the generic-site API and specialize directly to
`TopCat.Sheaf`. -/
#check IsAlgebraSection φ α π
#check kernelIdealSheaf π
#check KernelSquareZero π
#check kernelIdealSheafModule π
#check IsSectionPerturbation φ π

/- Companion recall: perturbing a fixed compatible section by a derivation into the intrinsic
kernel ideal is already the generic-site theorem specialized to `TopCat.Sheaf`. -/
#check existsUnique_algebraSection_of_derivation φ α π

/- Lemma 17.28.11: on a topological space, the uniqueness of the derivation measuring the
difference between two compatible algebra sections is exactly the specialization of the generic-site
theorem `existsUnique_derivation_of_algebraSection`. -/
#check existsUnique_derivation_of_algebraSection φ α π

end

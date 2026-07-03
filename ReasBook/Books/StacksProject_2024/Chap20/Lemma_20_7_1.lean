import Mathlib
import StacksProject_2024.Chap20.Lemma_20_13_6
import StacksProject_2024.Chap20.Lemma_20_32_1
import StacksProject_2024.Chap20.Lemma_20_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.7.1:
- primary domain: restriction of sheaves of modules to an open subspace of a ringed space and the
  induced comparison on sheaf cohomology;
- sampled owner declarations:
  `moduleSheafExtensionByZeroAdjunction`,
  `moduleSheafExtensionByZeroFromOpen_exact`,
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`,
  `openHypercohomology_isomorphic_restricted`;
- best owner abstraction: the restriction/extension-by-zero adjunction together with the ambient
  hypercohomology comparison on the open subspace;
- primitive data: a ringed space `X`, an open subset `U`, and a module sheaf `ℱ : (RingedSpace.Modules X)`;
- derived API: preservation of injective objects under restriction to `U`, and the degree-`p`
  cohomology comparison between sections over `U` and global sections of `ℱ|_U`.

Source/core/bridge triage:
- `source-facing`: the two textbook statements about restricting injective `\mathcal O_X`-modules
  and comparing cohomology on `U` with cohomology of the restricted module on `X|_U`;
- `core/canonical`: `moduleSheafExtensionByZeroAdjunction`,
  `moduleSheafExtensionByZeroFromOpen_exact`,
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`, and
  `openHypercohomology_isomorphic_restricted`;
- `bridge/view`: this file, which should remain a thin specialization to ordinary sheaf
  cohomology of a single `\mathcal O_X`-module rather than rebuilding the adjunction or derived
  comparison APIs locally. -/

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

/-- Lemma 20.7.1 (1): restriction of `\mathcal O_X`-modules to an open subspace preserves
injective objects, so an injective `\mathcal O_X`-module restricts to an injective
`\mathcal O_U`-module. -/
-- Proof sketch: by Lemma `6.31.8`, restriction to `U` is right adjoint to extension by zero
-- along the open immersion `j : U ↪ X`; the left adjoint is exact by Lemma `20.32.1`, hence it
-- preserves monomorphisms, and the standard adjunction criterion shows that the right adjoint
-- preserves injective objects.
instance moduleRestrictionToOpen_preservesInjectiveObjects :
    (moduleRestrictionToOpen X U).PreservesInjectiveObjects := by
  letI : PreservesFiniteLimits (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)) :=
    ((CategoryTheory.exactFunctor_iff (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X))).mp
      (moduleSheafExtensionByZeroFromOpen_exact (X := X) U)).1
  letI : (moduleSheafExtensionByZeroFromOpen U (RingedSpace.ringCatSheaf X)).PreservesMonomorphisms :=
    inferInstance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleSheafExtensionByZeroAdjunction U (RingedSpace.ringCatSheaf X))

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology U) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u})]

/-- Lemma 20.7.1 (2): for a sheaf of `\mathcal O_X`-modules `\mathcal F`, the cohomology of the
open subspace `U` computed on `X` is canonically isomorphic to the cohomology of the restricted
`\mathcal O_U`-module `\mathcal F|_U`. -/
-- Proof sketch: this is the single-sheaf source-facing specialization of the canonical
-- hypercohomology comparison `openHypercohomology_isomorphic_restricted` from Lemma `20.32.2`.
-- On a module sheaf concentrated in degree `0`, both sides compute the same degree-`p`
-- cohomology groups as the textbook statement.
theorem ringedSpaceModuleCohomologyOnOpen_isomorphic_to_restricted
    (ℱ : (RingedSpace.Modules X)) (p : ℕ) :
    IsIsomorphic ((moduleUnderlyingSheaf ℱ).H' p U)
      (((SheafOfModules.toSheaf
          ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))).obj
          ((moduleRestrictionToOpen X U).obj ℱ)).H' p (⊤ : Opens U)) := sorry

end AlgebraicGeometry.RingedSpace

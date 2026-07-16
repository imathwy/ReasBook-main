import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [MonoidalCategory X.Modules]

local notation "ModX" =>
  SheafOfModules.RingedSite.ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf

/-
Domain-style sampling for Lemma 17.16.3:
- primary domain: tensoring sheaves of modules on a ringed space on the right, viewed as an
  endofunctor of the ambient module category and measured by the canonical exactness owners;
- inspected owner declarations:
  `moduleTensorMap`,
  `sheafModuleTensorRightFunctor`,
  `rightExactFunctor`,
  `rightExactFunctor_iff`;
- best owner abstraction: the chapter/project owner for right tensoring is the site-level functor
  `sheafModuleTensorRightFunctor`, specialized to the opens-site ringed space
  `(RingedSpace.ringCatSheaf X)`;
- primitive data: only the fixed right tensor factor `𝒢 : RingedSpace.Modules X`;
- derived API: the right-exactness statement for that owner functor.

Source/core/bridge triage:
- `source-facing`: tensoring an exact sequence
  `\mathcal F_1 \to \mathcal F_2 \to \mathcal F_3 \to 0` on the right by `\mathcal G` preserves
  exactness and the terminal epimorphism;
- `core/canonical`: `sheafModuleTensorRightFunctor` together with the owner predicate
  `rightExactFunctor`;
- `bridge/view`: the ringed-space specialization from sheaves of modules on a ringed site to
  `(RingedSpace.Modules X)`.

Primitive-vs-derived check:
- the local Chapter 17 wrappers `moduleTensorRightMap` and `moduleTensorRightFunctor` were exact
  interface copies of the Chapter 18 owners `moduleTensorMap` and
  `sheafModuleTensorRightFunctor`;
- this file should therefore expose the source-facing result directly through the canonical owner
  instead of keeping a parallel wrapper API.
-/

-- Proof sketch: the Stacks lemma is exactly the right-exactness of the canonical tensor-right
-- endofunctor on `Mod(\mathcal O_X)`.
/-- Lemma 17.16.3: tensoring `\mathcal O_X`-modules on a ringed space on the right by a fixed
`\mathcal O_X`-module is right exact. -/
theorem moduleTensor_rightExact
    (𝒢 : ModX) :
    rightExactFunctor ModX ModX (sheafModuleTensorRightFunctor 𝒢) := by
  -- Proof comment: unfold to the canonical `tensorRight` owner and apply the exactness criterion
  -- directly to its finite-colimit preservation instance.
  change rightExactFunctor ModX ModX (tensorRight 𝒢)
  exact (rightExactFunctor_iff (tensorRight 𝒢)).mpr inferInstance

end AlgebraicGeometry.RingedSpace

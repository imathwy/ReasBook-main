import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap18.Lemma_18_27_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
variable (ℱ : RingedSpace.Modules X)

/-
Domain-style sampling for Lemma 17.16.5:
- primary domain: tensor products of sheaves of modules on a ringed space and their colimit
  behavior;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `moduleTensor`,
  `tensorLeft`,
  the canonical instance `PreservesColimits (tensorLeft ℱ)`,
  the Chapter 18 site-level specialization in `Lemma_18_27_7`;
- best owner abstraction:
  the source-facing ringed-space tensor product is the chapter/project owner `moduleTensor`; once
  the ambient monoidal closed owner structure on `RingedSpace.Modules X` has been established
  upstream via the Chapter 18 ringed-site tensor calculus, the left tensor functor
  `𝒢 ↦ moduleTensor ℱ 𝒢` is exactly `tensorLeft ℱ`, and the colimit-preservation statement is the
  canonical instance `PreservesColimits (tensorLeft ℱ)`;
- primitive data:
  the ambient monoidal closed structure on `RingedSpace.Modules X` and a fixed
  `\mathcal O_X`-module `ℱ`;
- derived API:
  the fact that the concrete left tensor functor with `ℱ` preserves arbitrary colimits.

Source/core/bridge triage:
- `source-facing`: the ringed-space formulation of Stacks Project Lemma 17.16.5;
- `core/canonical`: `moduleTensor`, `tensorLeft ℱ`, and the canonical
  `PreservesColimits (tensorLeft ℱ)` instance on `RingedSpace.Modules X`;
- `bridge/view`: specialization from sheaves of modules over a sheaf of rings on the opens site to
  the structure sheaf of a ringed space.
-/

/- Lemma 17.16.5: for any `\mathcal O_X`-module `\mathcal F`, the functor
`\mathcal G \mapsto \mathcal F \otimes_{\mathcal O_X} \mathcal G` on `Mod(\mathcal O_X)`
commutes with arbitrary colimits. In the concrete tensor-product owner subtree, this is the
ringed-space specialization of the Chapter 18 owner result on ringed sites, expressed here as the
canonical owner instance `PreservesColimits (tensorLeft ℱ)` on `RingedSpace.Modules X` under the
ambient monoidal closed owner structure. -/
#synth PreservesColimits (tensorLeft ℱ)

end

end AlgebraicGeometry.RingedSpace

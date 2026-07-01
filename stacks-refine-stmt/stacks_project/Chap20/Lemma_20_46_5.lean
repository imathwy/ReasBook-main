import Mathlib
import stacks_project.Chap20.Lemma_20_47_9
import stacks_project.Chap21.Lemma_21_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ℰ ℱ 𝒢 : (RingedSpace.Modules X)}

/- Domain-style sampling for Lemma 20.46.5:
- primary domain: sheaves of `\mathcal O_X`-modules on a ringed space, with local lifting against
  epimorphisms from a source sheaf that is a direct summand of a finite free module sheaf;
- sampled owner declarations:
  `(RingedSpace.Modules X)`,
  `CategoryTheory.finiteFreeRetractModuleProperty`,
  `SheafOfModules.RingedSite.exists_cover_lift_of_epi_of_retract_finiteFree`,
  `moduleSheafRestrictionToOpen`;
- best owner abstraction: the generic ringed-site owner
  `CategoryTheory.finiteFreeRetractModuleProperty`, specialized here to the underlying sheaf of
  rings `X.ringCatSheaf`;
- primitive data: the morphisms `f : ℰ ⟶ ℱ` and `p : 𝒢 ⟶ ℱ`, the epimorphism structure on `p`,
  and the finite-free-retract owner hypothesis on `ℰ`;
- derived API: the local lift on restrictions to an open neighborhood of each point.

Source/core/bridge triage:
- `source-facing`: this local lifting theorem;
- `core/canonical`: `(RingedSpace.Modules X)`,
  `CategoryTheory.finiteFreeRetractModuleProperty`, and `moduleSheafRestrictionToOpen`;
- `bridge/view`: the ringed-site covering-lift theorem
  `SheafOfModules.RingedSite.exists_cover_lift_of_epi_of_retract_finiteFree`, whose specialization
  at the top open yields this pointwise neighborhood statement.

This file should therefore keep the source-facing lemma and reuse the project owner directly,
rather than keeping a second local predicate for the same finite-free-retract condition. -/

-- Proof sketch: choose a finite free sheaf `\mathcal O_X^{\oplus I}` of which `ℰ` is a retract.
-- Since `p` is surjective, the images in `ℱ` of the finitely many basis sections admit local lifts
-- to `𝒢` near any chosen point. These local lifts assemble to a lift from the finite free sheaf,
-- and composing with the retraction data yields a local lift from `ℰ`.
/-- Lemma 20.46.5: if `\mathcal E` is a direct summand of a finite free `\mathcal O_X`-module and
`p : \mathcal G \to \mathcal F` is surjective, then every morphism `\mathcal E \to \mathcal F`
locally lifts through `p`. -/
theorem exists_open_neighborhood_lift_of_epi_of_retract_finiteFree
    (f : ℰ ⟶ ℱ) (p : 𝒢 ⟶ ℱ) [Epi p]
    (hℰ : finiteFreeRetractModuleProperty X.ringCatSheaf ℰ)
    (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U)
      (l : (moduleSheafRestrictionToOpen U).obj ℰ ⟶ (moduleSheafRestrictionToOpen U).obj 𝒢),
      l ≫ (moduleSheafRestrictionToOpen U).map p = (moduleSheafRestrictionToOpen U).map f := sorry

end AlgebraicGeometry.RingedSpace

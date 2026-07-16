import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap06.Definition_6_27_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_26_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.27.3:
- primary domain: stalk/skyscraper adjunctions for sheaves on topological spaces and their
  ringed-space module refinements;
- sampled owner declarations:
  `stalkSkyscraperSheafAdjunction`,
  `AlgebraicGeometry.pointInclusion`,
  `RingedSpace.Hom.pullbackStalkIso`,
  `AlgebraicGeometry.pointModuleSheaf_homEquivTop`,
  `AlgebraicGeometry.skyscraperModuleSheaf`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: `stalkSkyscraperSheafAdjunction` on the sheaf side, and the canonical
  pullback/pushforward adjunction for `pointInclusion x` on the module side, with the
  source-facing stalk module exposed through the bundled owner
  `RingedSpace.stalkModuleCat` and the point-pullback stalk comparison
  `pullbackStalkIso (pointInclusion x)`;
- source/core/bridge triage:
  `source-facing`: the Stacks bijections `Mor(ℱ_x, A) ≃ Mor(ℱ, i_{x, *} A)` for ordinary sheaves
    and for `\mathcal O_X`-modules;
  `core/canonical`: `stalkSkyscraperSheafAdjunction` and
    `SheafOfModules.pullbackPushforwardAdjunction
      (RingedSpace.Hom.toRingCatSheafHom (pointInclusion x))`;
  `bridge/view`: the source-facing stalk-module owner `RingedSpace.stalkModuleCat`, together with
    the specialization of the canonical adjunction to `pointInclusion x`.

Primitive data are only the point and the target value/module. The sheaf adjunction is already
owned canonically by `stalkSkyscraperSheafAdjunction`, and the module statement should be exposed
through the public stalk-module owner, the one-point bridge `TopCat.Presheaf.Γgerm`,
`pullbackStalkIso (pointInclusion x)`, `pointModuleSheaf_homEquivTop`, and direct reuse of the
point-inclusion adjunction, rather than by introducing a parallel local Hom-equivalence wrapper.
-/

/- Lemma 6.27.3: let `X` be a topological space and let `x : X` be a point. Then the functors
`ℱ ↦ ℱ_x` and `A ↦ i_{x, *} A` are adjoint. The canonical mathlib declaration is the generic
adjunction `stalkSkyscraperSheafAdjunction`; specializing to sheaves of sets recovers the
Stacks-style bijection `Mor_Sets(ℱ_x, A) ≃ Mor_Sh(X)(ℱ, i_{x, *} A)`. -/
recall stalkSkyscraperSheafAdjunction

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}}
variable (x : X) (ℱ : X.Modules)
variable (M : ModuleCat (X.presheaf.stalk x))

/- Lemma 6.27.3, `\mathcal O_X`-module half, owner form: for the point inclusion
`i_x : ({x}, \mathcal O_{X, x}) \to (X, \mathcal O_X)`, the canonical adjunction
`i_x^* ⊣ i_{x, *}` on module sheaves is the specialization of
`SheafOfModules.pullbackPushforwardAdjunction` to `pointInclusion x`. The source-facing stalk
module wording is obtained from this owner equivalence by the already established one-point
bridges `RingedSpace.stalkModuleCat`, `pullbackStalkIso (pointInclusion x)`,
`pointModuleSheaf_homEquivTop`, and `pointModuleSheaf_objTopIso`, so no extra local Hom-equivalence
wrapper should remain in the public API. -/
recall SheafOfModules.pullbackPushforwardAdjunction

#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (toRingCatSheafHom (pointInclusion x))).homEquiv ℱ (pointModuleSheaf x M)) :
    (((pointInclusion x)^*).obj ℱ ⟶ pointModuleSheaf x M) ≃
      (ℱ ⟶ skyscraperModuleSheaf x M))

/- Lemma 6.27.3, source-facing stalk-module form: the owner adjunction above induces the
canonical bijection
`Mor_{\mathcal O_{X, x}}(\mathcal F_x, M) ≃ Mor_{\mathcal O_X}(\mathcal F, i_{x, *} M)`,
where the left-hand side is expressed through the chapter owner `RingedSpace.stalkModuleCat`. -/
#check
  (by
    sorry :
      (RingedSpace.stalkModuleCat ℱ x ⟶ M) ≃ (ℱ ⟶ skyscraperModuleSheaf x M))

end

end AlgebraicGeometry

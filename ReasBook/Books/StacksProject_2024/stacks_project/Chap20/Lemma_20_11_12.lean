import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»
import StacksProject_2024.stacks_project.Chap21.Lemma_21_12_5

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.11.12:
- primary domain: objectwise sheaf cohomology and the canonical product comparison map on a site;
- sampled owner declarations:
  `moduleUnderlyingSheaf`,
  `sheafProductCohomologyMap_isIso_degree_zero`,
  `sheafProductCohomologyMap_injective_degree_one`,
  `piComparison`;
- best owner abstraction: the Chapter 20 bridge `moduleUnderlyingSheaf X` from
  `𝒪_X`-modules to additive sheaves, together with the Chapter 21 sheaf-level owner
  theorems for product cohomology;
- primitive data: an open subset `U` and a family of additive sheaves on `X.carrier`;
- derived API here: the ringed-space specialization obtained by applying the Chapter 21 owner
  theorems to the underlying additive sheaf family `((moduleUnderlyingSheaf X).obj ∘ ℱ)`.

Source/core/bridge triage:
- `source-facing`: the ringed-space wording for products of `𝒪_X`-modules;
- `core/canonical`: `sheafProductCohomologyMap_isIso_degree_zero` and
  `sheafProductCohomologyMap_injective_degree_one`;
- `bridge/view`: the chapter owner
  `moduleUnderlyingSheaf X : X.Modules ⥤ X.carrier.Sheaf AddCommGrpCat`.

This file therefore should not introduce new ringed-space theorem names. Its role is only to
recall the sheaf owner theorems and record the direct ringed-space specialization through the
canonical underlying-sheaf bridge `moduleUnderlyingSheaf X`.
-/

/- Lemma 20.11.12 is the ringed-space specialization of the Chapter 21 owner theorems on the
canonical product comparison map in sheaf cohomology. -/
recall sheafProductCohomologyMap_isIso_degree_zero
recall sheafProductCohomologyMap_injective_degree_one

section

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable (U : Opens X.carrier) {I : Type u} (ℱ : I → X.Modules)

local notation "JX" => Opens.grothendieckTopology X.carrier

/-- Internal helper: the family of underlying additive sheaves attached to a family of
`𝒪_X`-modules. -/
private abbrev moduleUnderlyingSheafFamily :
    I → X.carrier.Sheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf X).obj ∘ ℱ

/-- Internal helper: cohomology of additive sheaves on `X` in degree `p`, evaluated at `U`. -/
private abbrev moduleCohomologyAtOpenFunctor (p : ℕ) :
    X.carrier.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Sheaf.cohomologyPresheafFunctor JX p ⋙
    (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/- Source-facing specialization of Lemma 20.11.12 (1): apply the sheaf-level owner theorem to the
family of underlying additive sheaves of the `𝒪_X`-modules `ℱ i`. -/
#check (sheafProductCohomologyMap_isIso_degree_zero U (moduleUnderlyingSheafFamily ℱ) :
  IsIso
    (piComparison (moduleCohomologyAtOpenFunctor U 0) (moduleUnderlyingSheafFamily ℱ)))

/- Source-facing specialization of Lemma 20.11.12 (2): the same specialization in degree `1`
gives injectivity of the canonical product comparison map. -/
#check (sheafProductCohomologyMap_injective_degree_one U (moduleUnderlyingSheafFamily ℱ) :
  Function.Injective
    (piComparison (moduleCohomologyAtOpenFunctor U 1) (moduleUnderlyingSheafFamily ℱ)))

end

end AlgebraicGeometry.RingedSpace

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import StacksProject_2024.Chap17.Lemma_17_25_10
import StacksProject_2024.Chap18.Lemma_18_30_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry Opposite TopCat TopologicalSpace

noncomputable section

universe w u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.3.5:
- primary domain: coproducts of `\mathcal O_X`-modules and sections over quasi-compact opens of a
  ringed space;
- inspected owner declarations:
  `SheafOfModules.evaluation`,
  `Limits.sigmaComparison`,
  `quasiCompactObject_module_evaluation_preserves_direct_sums`;
- best owner abstraction: the ambient owner is the structure-sheaf module category
  `SheafOfModules.{max u w} (RingedSpace.ringCatSheaf X)`, while the comparison map is the canonical
  `sigmaComparison` for the evaluation functor on `U`;
- primitive data: a ringed space `X`, an open subset `U`, and a family
  `ℱ : I → SheafOfModules.{max u w} (RingedSpace.ringCatSheaf X)` with universe-polymorphic index type `I`;
- derived API: the compactness specialization identifying the direct sum of sections with the
  sections of the coproduct sheaf.

Source/core/bridge triage:
- `source-facing`: the canonical morphism `⨁ Γ(U, ℱ i) ⟶ Γ(U, ⨁ ℱ i)` from the Stacks item;
- `core/canonical`: `SheafOfModules.{max u w} (RingedSpace.ringCatSheaf X)`,
  `SheafOfModules.evaluation`, and `sigmaComparison`;
- `bridge/view`: the passage from `IsCompact (U : Set X)` to preservation of coproducts by
  sections over `U`. -/

variable {X : RingedSpace.{u}} {I : Type w}

local notation "𝒪X" => X.ringCatSheaf
local notation "ModX" => RingedSpace.Modules X

private theorem quasiCompactObject_of_isCompact (U : Opens X) (hU : IsCompact (U : Set X)) :
    (Opens.grothendieckTopology X).QuasiCompactObject U := by
  sorry

-- Proof sketch: Chapter 18 gives the owner-level statement that evaluation on a quasi-compact
-- open preserves direct sums in `SheafOfModules`. The canonical comparison map for the coproduct
-- is therefore an isomorphism.
/-- Lemma 17.3.5: for a quasi-compact open `U`, the canonical comparison map
`⨁ Γ(U, ℱ i) ⟶ Γ(U, ⨁ ℱ)` is an isomorphism. -/
lemma ringedSpaceModule_sigmaComparison_isIso_of_isCompact
    (ℱ : I → ModX) [HasCoproduct ℱ]
    (U : Opens X)
    [HasCoproduct (fun b ↦ (SheafOfModules.evaluation 𝒪X (op U)).obj (ℱ b))]
    (hU : IsCompact (U : Set X)) :
    IsIso (sigmaComparison (SheafOfModules.evaluation 𝒪X (op U)) ℱ) := by
  let _ : PreservesColimit (Discrete.functor ℱ) (SheafOfModules.evaluation 𝒪X (op U)) := by
    let _ : PreservesColimitsOfShape (Discrete I) (SheafOfModules.evaluation 𝒪X (op U)) :=
      quasiCompactObject_module_evaluation_preserves_direct_sums 𝒪X U
        (quasiCompactObject_of_isCompact U hU) I
    infer_instance
  infer_instance

end AlgebraicGeometry.RingedSpace

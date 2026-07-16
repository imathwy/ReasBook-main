import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_31_8
import StacksProject_2024.stacks_project.Chap06.Lemma_6_31_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.12:
- primary domain: extension by zero for sheaves of modules on a ringed space, together with
  fully-faithfulness and essential-image detection by vanishing stalks outside an open subset;
- sampled owner declarations:
  `openSubsetModuleSheafExtensionByZeroAdjunction`,
  `openSubsetModuleSheafExtensionByZero_eq_moduleSheafExtensionByZeroFromOpen`,
  `openSubspaceModuleSheafExtensionByZero_unitIso`,
  `openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem`,
  `openSubsetSheafExtensionByInitialObject_essImage_iff_stalk_isZero_of_not_mem`;
- owner abstraction: the source-facing adjunction owner
  `openSubsetModuleSheafExtensionByZeroAdjunction`, obtained in `Lemma_6_31_8` from the canonical
  chosen adjoint `moduleSheafExtensionByZeroAdjunction`, together with the abelian essential-image
  criterion from `Lemma_6_31_10`;
- primitive data: the ringed space `X`, the open subset `U`, the canonical extension-by-zero
  functor on module sheaves, and the underlying-additive-sheaf functor
  `SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)`;
- derived API: full faithfulness of the module extension-by-zero functor and the module-valued
  zero-stalk essential-image criterion, with the additive criterion used only as an internal
  bridge.

Source/core/bridge triage:
- `source-facing`: the Stacks-project module-sheaf statements in parts (1) and (2);
- `core/canonical`: the explicit `j_! ⊣ j^{-1}` owner from `Lemma_6_31_8` and the abelian owner
  criterion from `Lemma_6_31_10`;
- `bridge/view`: this file’s passage from module-valued stalks to underlying additive stalks via
  `SheafOfModules.toSheaf`.

This file should therefore keep the source-facing module-sheaf statements as the public API: no
new wrapper owner is needed, and the additive-stalk criterion should appear only internally in the
proof of part (2).
-/

section

variable {X : RingedSpace}

local notation "𝒪X" => RingedSpace.ringCatSheaf X

-- Proof sketch: the explicit extension-by-zero functor agrees with the usual left adjoint to
-- restriction along the open immersion `j : U ↪ X`, and the unit `id ⟶ j⁻¹ j_!` is an
-- isomorphism on module sheaves over `U`; hence `j_!` is fully faithful.
/-- Lemma 6.31.12 (1): for a ringed space `(X, \mathcal{O}_X)` and an open subspace `j : U ↪ X`,
the canonical extension-by-zero functor
`j_! : \textit{Mod}(\mathcal{O}|_U) \to \textit{Mod}(\mathcal{O})`
is fully faithful. -/
instance openSubsetModuleSheafExtensionByZero_fullyFaithful
    (U : Opens X.carrier) :
    (openSubsetModuleSheafExtensionByZero U 𝒪X).FullyFaithful := by
  sorry

-- Proof sketch: an extended module has zero stalks outside `U` by the explicit construction;
-- conversely, if a module sheaf on `X` has zero stalks off `U`, then the canonical counit
-- `j_! j⁻¹ 𝒢 ⟶ 𝒢` is an isomorphism on stalks, so `𝒢` belongs to the essential image.
/-- Lemma 6.31.12 (2): a sheaf of `\mathcal{O}_X`-modules on `X` lies in the essential image of
the canonical extension-by-zero functor from `U` if and only if all of its stalks at points of
`X \setminus U` are zero. -/
theorem openSubsetModuleSheafExtensionByZero_essImage_iff_stalk_isZero_of_not_mem
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) :
    (openSubsetModuleSheafExtensionByZero U 𝒪X).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X.carrier) →
        IsZero
          (ModuleCat.of ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk 𝒢.val.presheaf x)) := by
  sorry

end

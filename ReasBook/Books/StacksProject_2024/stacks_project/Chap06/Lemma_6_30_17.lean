import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap06.Lemma_6_30_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable {BX : Set (Opens X)} {BY : Set (Opens Y)}
variable (ℱ : SheafOfModules ((RingedSpace.ringCatSheaf X)))
variable (𝒢 : SheafOfModules ((RingedSpace.ringCatSheaf Y)))

local notation "BasisOpenX" => ObjectProperty.FullSubcategory fun U : Opens X ↦ U ∈ BX
local notation "BasisOpenY" => ObjectProperty.FullSubcategory fun V : Opens Y ↦ V ∈ BY

/-
Domain-style sampling for Lemma 6.30.17:
- primary domain: pushforward of sheaves of modules on a morphism of ringed spaces, expressed via
  basis-indexed section families on the underlying sheaves of abelian groups;
- sampled owner declarations:
  `RingedSpace.Hom.pushforward`,
  `RingedSpace.Hom.toRingCatSheafHom`,
  `BasisContinuousMapSectionFamily`,
  `existsUnique_pushforward_hom_of_basis_section_family`,
  `SheafOfModules.toSheaf`;
- owner abstraction: the canonical target owner is `(f _*).obj ℱ`,
  while the source-facing basis data are already owned by
  `BasisContinuousMapSectionFamily f.hom.base BX BY`;
- primitive data: the only extra primitive input beyond the basis family is the
  `\mathcal O_Y(V)`-linearity condition on sections;
- derived API: the unique module morphism whose underlying sheaf morphism recovers the given basis
  family on basis opens.

Source/core/bridge triage:
- `source-facing`: the basis-pair family `η` and its linearity condition;
- `core/canonical`: the module pushforward owner `(f _*).obj ℱ`;
- `bridge/view`: `SheafOfModules.toSheaf`, used only to compare the source family with the
  underlying sheaf morphism of the resulting module map.
-/

-- Proof sketch: forget the module structure to obtain a compatible basis-indexed family of maps
-- of sheaves of abelian groups, apply Lemma `6.30.16` to extend it uniquely to the underlying
-- pushforward morphism, and then use the pointwise linearity hypothesis to view the resulting
-- morphism as a morphism of sheaves of modules.
/-- Lemma 6.30.17: a compatible family of `\mathcal O_Y(V)`-linear maps
`\mathcal G(V) → \mathcal F(U)` for basis opens `V ∈ BY`, `U ∈ BX`, and `U ⊆ f⁻¹(V)` comes from
exactly one morphism of sheaves of `\mathcal O_Y`-modules `𝒢 ⟶ f_* ℱ`, and on basis opens it
recovers the given maps after restricting from `f⁻¹(V)` to `U`. -/
theorem existsUnique_module_pushforward_hom_of_basis_pair_sections
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (η :
      BasisContinuousMapSectionFamily f.hom.base BX BY
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).obj 𝒢)
        ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ℱ))
    (hη :
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj)
        (r : ((RingedSpace.ringCatSheaf Y)).obj.obj (op V.obj)) (s : 𝒢.val.obj (op V.obj)),
        (show ℱ.val.obj (op U.obj) from η.app U V hUV (r • s)) =
          (((RingedSpace.Hom.toRingCatSheafHom f).hom.app (op V.obj) ≫
              ((RingedSpace.ringCatSheaf X)).obj.map (homOfLE hUV).op) r) •
            (show ℱ.val.obj (op U.obj) from η.app U V hUV s)) :
    ∃! φ : 𝒢 ⟶ (f _*).obj ℱ,
      ∀ (U : BasisOpenX) (V : BasisOpenY)
        (hUV : U.obj ≤ (Opens.map f.hom.base).obj V.obj),
        (((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf Y))).map φ).hom.app (op V.obj)) ≫
            ℱ.val.presheaf.map (homOfLE hUV).op =
          η.app U V hUV := sorry

end AlgebraicGeometry

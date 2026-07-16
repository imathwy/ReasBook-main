import Mathlib
import StacksProject_2024.stacks_project.Chap06.Lemma_6_30_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits

universe w v u

section

variable {C : Type v} [Category.{w} C]
variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (BX : Set (Opens X)) (BY : Set (Opens Y))
variable (𝒢 : TopCat.Sheaf C Y) (ℱ : TopCat.Sheaf C X)

-- The ambient inclusion of opens underlying a morphism in a basis-open full subcategory.
private theorem basisOpenHomLE {Z : TopCat.{u}} {B : Set (Opens Z)}
    {U V : BasisOpen B} (i : U ⟶ V) :
    U.obj ≤ V.obj :=
  i.hom.le

/- Domain-style sampling for Lemma 6.30.16:
- primary domain: basis-indexed pushforward morphisms of sheaves, with source-facing section data
  on basis opens of both `X` and `Y`;
- sampled owner declarations:
  `BasisOpen`,
  `basisOpenInclusion`,
  `Functor.sheafPushforwardContinuous`,
  `existsUnique_pushforward_hom_of_basis_restriction`;
- best owner abstraction: the canonical owner of the resulting map is the pushforward morphism
  `𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ`, while the basis-indexed section family is source-facing
  input data and the induced morphism between basis restrictions is derived API;
- primitive data: the section components `app` together with naturality in the source basis open
  and the target basis open;
- derived API: under the basis-restriction equivalences from Lemma `6.30.14`, such a family
  determines a unique morphism `𝒢 ⟶ f_* ℱ`.

Source/core/bridge triage:
- `source-facing`: `BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ`;
- `core/canonical`: `𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ`;
- `bridge/view`: the morphism between the basis restrictions of `𝒢` and `f_* ℱ` obtained from the
  section family via the basis-site equivalence.
-/
/-- A family of section morphisms on basis opens of `Y` and `X` over a continuous map `f`,
compatible with restriction in both variables. -/
structure BasisContinuousMapSectionFamily where
  app (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj) :
    𝒢.presheaf.obj (op V.obj) ⟶ ℱ.presheaf.obj (op U.obj)
  source_naturality {U U' : BasisOpen BX} (i : U' ⟶ U) {V : BasisOpen BY}
      (h : U.obj ≤ (Opens.map f).obj V.obj) :
    app U V h ≫ ℱ.presheaf.map (homOfLE (basisOpenHomLE i)).op =
      app U' V ((basisOpenHomLE i).trans h)
  target_naturality {U : BasisOpen BX} {V V' : BasisOpen BY} (j : V ⟶ V')
      (h : U.obj ≤ (Opens.map f).obj V.obj) :
    𝒢.presheaf.map (homOfLE (basisOpenHomLE j)).op ≫ app U V h =
      app U V'
        (h.trans ((Opens.map f).map (homOfLE (basisOpenHomLE j))).le)

-- Proof sketch: for each basis open `V` of `Y`, the `U`-naturality makes the family
-- `φ.app _ V _` into a compatible basis restriction datum on the open `f⁻¹(V)` of `X`, so the
-- basis-site equivalence on `X` yields a unique section map `𝒢(V) ⟶ ℱ(f⁻¹(V))` in `C`. The
-- `V`-naturality then assembles these maps into a morphism between the basis restrictions of `𝒢`
-- and `f_* ℱ` on `BY`, and Lemma `6.30.14` upgrades that canonical basis-restriction morphism to
-- a unique global morphism `𝒢 ⟶ f_* ℱ`.
/-- Lemma 6.30.16: a family of morphisms `𝒢(V) ⟶ ℱ(U)` given for basis opens `V` of `Y` and `U`
of `X` with `U ⊆ f⁻¹(V)` (equivalently `f(U) ⊆ V`), and compatible with restriction in both
variables, comes from a unique morphism `𝒢 ⟶ f_* ℱ` recovering the given maps after restricting
from `f⁻¹(V)` to `U`. -/
theorem existsUnique_pushforward_hom_of_basis_section_family
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion BX).op) C]
    [∀ V : (Opens Y)ᵒᵖ, HasLimitsOfShape (StructuredArrow V (basisOpenInclusion BY).op) C]
    (φ : BasisContinuousMapSectionFamily f BX BY 𝒢 ℱ) :
    ∃! Φ : 𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ,
      ∀ (U : BasisOpen BX) (V : BasisOpen BY) (h : U.obj ≤ (Opens.map f).obj V.obj),
        Φ.hom.app (op V.obj) ≫ ℱ.presheaf.map (homOfLE h).op = φ.app U V h := sorry

end

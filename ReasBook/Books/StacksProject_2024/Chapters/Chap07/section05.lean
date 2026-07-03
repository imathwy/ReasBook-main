import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_5_1 (from Chap07) -/
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-
Domain-style sampling for Lemma 7.5.1:
- primary domain: filtered/cofiltered criteria for structured-arrow categories
- owner declarations reused here:
  `HasSpanCocones`,
  `HasEqualizers`,
  `RepresentablyFlat` as the stronger owner from later Chapter 7 results
- target layer: `source-facing` bridge. The lemma does not supply the stronger owner
  `RepresentablyFlat u`; it only proves that `(StructuredArrow V u)ᵒᵖ` satisfies the two explicit
  hypotheses used in Chapter 4, Lemma 4.19.8.

Primitive data are the pullback/equalizer hypotheses on `C` and the corresponding preservation
hypotheses on `u`. Both the `HasSpanCocones` half and the postcomposition-equalizer half are
derived owner API, so the textbook conjunction below is kept only as a thin source-facing bridge.
-/

/-- Helper for Lemma 7.5.1: in the opposite of a category with equalizers, every parallel pair
becomes equal after postcomposition with the opposite of an equalizer map. -/
private theorem op_postcomposition_equalizers_of_hasEqualizers
    (I : Type u₁) [Category.{v₁} I] [HasEqualizers I] :
    ∀ ⦃X Y : Iᵒᵖ⦄ (f g : X ⟶ Y), ∃ (Z : Iᵒᵖ) (h : Y ⟶ Z), f ≫ h = g ≫ h := by
  -- Take the opposite of the equalizer in `I`; this is the required postcomposition equalizer.
  intro X Y f g
  refine ⟨Opposite.op (equalizer f.unop g.unop), (equalizer.ι f.unop g.unop).op, ?_⟩
  -- The equalizer identity in `I` turns into the desired equality after applying `op`.
  simpa using congrArg Quiver.Hom.op (equalizer.condition f.unop g.unop)

/-- Lemma 7.5.1: if `C` has fibre products and equalizers and `u` commutes with them, then the
opposite structured-arrow category `(StructuredArrow V u)ᵒᵖ`, which is the category
`(𝓘_V^u)ᵒᵖ` from the text, satisfies the two hypotheses of Categories, Lemma 4.19.8. -/
theorem structuredArrow_op_has_span_cocones_and_postcomposition_equalizers
    (u : C ⥤ D) (V : D)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    HasSpanCocones (StructuredArrow V u)ᵒᵖ ∧
      (∀ ⦃X Y : (StructuredArrow V u)ᵒᵖ⦄ (f g : X ⟶ Y),
        ∃ (Z : (StructuredArrow V u)ᵒᵖ) (h : Y ⟶ Z), f ≫ h = g ≫ h) := by
  -- The equalizer half of the textbook argument is supplied by the induced equalizers in the
  -- structured-arrow category.
  let _ : HasEqualizers (StructuredArrow V u) := inferInstance
  -- The pullback half gives span cocones on the opposite category, and the helper above packages
  -- the dual equalizer argument exactly as in the source proof.
  exact ⟨inferInstance, op_postcomposition_equalizers_of_hasEqualizers (StructuredArrow V u)⟩

end CategoryTheory

/-! ### Lemma_7_5_2 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-
Domain-style sampling for Lemma 7.5.2:
- primary domain: representably flat functors and the filtered/cofiltered structured-arrow
  categories they induce
- core/canonical owner: `RepresentablyFlat`
- relevant owner declarations:
  `representablyFlat_of_terminal_and_pullbacks`,
  `RepresentablyFlat.cofiltered`,
  `isFiltered_of_isCofiltered_op`
- target layer below: `source-facing` bridge from the explicit terminal-object and pullback
  hypotheses in the text to the filtered opposite structured-arrow category `(StructuredArrow V u)ᵒᵖ`

Primitive data are the explicit terminal object and pullback-preservation hypotheses. The
cofilteredness of `StructuredArrow V u` is derived owner API coming from `RepresentablyFlat`, and
`RepresentablyFlat` is already produced upstream in the chapter by the source-facing bridge
`representablyFlat_of_terminal_and_pullbacks`. This file should therefore remain a thin
bridge/view theorem over that owner abstraction.
-/

/-- Lemma 7.5.2 in textbook form: under the same hypotheses, the opposite structured-arrow
category `(StructuredArrow V u)ᵒᵖ`, i.e. `(𝓘^u_V)ᵒᵖ`, is filtered. -/
theorem structuredArrow_op_isFiltered_of_terminal_and_pullbacks
    (u : C ⥤ D) (V : D) (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    IsFiltered (StructuredArrow V u)ᵒᵖ := by
  let _ : RepresentablyFlat u := representablyFlat_of_terminal_and_pullbacks u X hX huX
  exact isFiltered_of_isCofiltered_op (StructuredArrow V u)ᵒᵖ

end CategoryTheory

/-! ### Lemma_7_5_3 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Functor

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling:
- primary domain: presheaf left Kan extensions and their units;
- sampled owner API:
  `Functor.leftKanExtensionUnit`,
  `HasLeftKanExtension`,
  `Functor.lanAdjunction`,
  nearby chapter analogue `Lemma_7_19_1` for the right Kan extension counit;
- source-facing: Lemma 7.5.3 records the canonical evaluation map and its compatibility with
  restriction maps;
- core/canonical: `Functor.leftKanExtensionUnit`;
- bridge/view: the component at `U` and the naturality equation for `f : U' ⟶ U`.

Primitive data are `u`, `ℱ`, and the existence of the left Kan extension along `u.op`. The
component map and its restriction compatibility are derived API from the unit natural
transformation, so this file should expose that owner projection directly rather than a parallel
local definition.
-/

/- Lemma 7.5.3: for a presheaf `ℱ` on `C` and `u : C ⥤ D`, the canonical map
`ℱ(U) ⟶ {}_p u \mathcal F (u(U))` is the component at `U` of the left Kan extension unit
`u.op.leftKanExtensionUnit ℱ`. -/
recall Functor.leftKanExtensionUnit

variable (u : C ⥤ D) (ℱ : Cᵒᵖ ⥤ Type w) [HasLeftKanExtension u.op ℱ]
variable {U U' : C} (f : U' ⟶ U)

/- The source-facing map of Lemma 7.5.3 is the `U`-component of that unit. -/
#check ((u.op.leftKanExtensionUnit ℱ).app (op U) :
    ℱ.obj (op U) ⟶ (u.op.leftKanExtension ℱ).obj (op (u.obj U)))

/- The restriction-map compatibility in Lemma 7.5.3 is exactly the naturality of the unit:
for `f : U' ⟶ U`, this is `(u.op.leftKanExtensionUnit ℱ).naturality f.op`. -/
#check ((u.op.leftKanExtensionUnit ℱ).naturality f.op :
    ℱ.map f.op ≫ (u.op.leftKanExtensionUnit ℱ).app (op U') =
      (u.op.leftKanExtensionUnit ℱ).app (op U) ≫
        (u.op.leftKanExtension ℱ).map (u.map f).op)

end CategoryTheory

/-! ### Lemma_7_5_4 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Functor

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)
variable [∀ ℱ : Presheaf C, u.op.HasLeftKanExtension ℱ]

/- Domain-style sampling:
- primary domain: presheaf Kan-extension adjunctions;
- sampled owner API:
  `Functor.lanAdjunction`,
  `Adjunction.homEquiv`,
  `Functor.leftKanExtensionUnit`,
  and the chapter-level owner-form recall in `Remark_7_5_5`;
- source/core/bridge triage:
  `source-facing`: the hom-set identification attached to presheaf pullback and pushforward;
  `core/canonical`: the adjunction `Functor.lanAdjunction`;
  `bridge/view`: the specialization of `Adjunction.homEquiv` to set-valued presheaves.

Primitive data are the functor `u` and the existence of left Kan extensions along `u.op`. The
hom-set equivalence is derived API from the owner adjunction, so this file should recall that
owner directly and keep the specialized hom-set bijection only as the thin source-facing bridge.
-/

variable (ℱ : Presheaf C) (𝒢 : Presheaf D)

/- Lemma 7.5.4, owner form: on set-valued presheaves the lower shriek `uₚ`, realized as the left
Kan extension along `u.op`, is left adjoint to pullback `u^p`. This is exactly the canonical
specialized adjunction `u.op.lanAdjunction (Type w)`. -/
#check (u.op.lanAdjunction (Type w) :
  u.op.lan ⊣ (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj u.op)

/- Lemma 7.5.4: the functor `uₚ` on presheaves, realized as left Kan extension along `u.op`, is
left adjoint to the pullback functor `u^p`, realized as precomposition by `u.op`; equivalently,
this adjunction gives the bifunctorial identification
`Mor_{PSh(D)}(uₚ ℱ, 𝒢) ≃ Mor_{PSh(C)}(ℱ, u^p 𝒢)`. This is the canonical hom-set equivalence
coming from `u.op.lanAdjunction (Type w)`, i.e. the presheaf specialization of
`Adjunction.homEquiv`. -/
#check (((u.op.lanAdjunction (Type w)).homEquiv ℱ 𝒢) :
    ((u.op.lan).obj ℱ ⟶ 𝒢) ≃ (ℱ ⟶ u.op ⋙ 𝒢))

end CategoryTheory

/-! ### Remark_7_5_5 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Functor

universe uC vC uD vD uA vA

section

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {A : Type uA} [Category.{vA} A]
variable (u : C ⥤ D)
variable [∀ F : Cᵒᵖ ⥤ A, u.op.HasLeftKanExtension F]

/- Domain-style sampling:
- primary domain: category-theoretic presheaf Kan extensions and their adjunctions;
- sampled owner API:
  `Functor.lanAdjunction`,
  `HasLeftKanExtension`,
  `whiskeringLeft`;
- source-facing: Remark 7.5.5 identifies the presheaf pullback functor
  `(whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op` with a functor admitting the canonical left adjoint
  `u.op.lan`;
- core/canonical: the Kan-extension adjunction `Functor.lanAdjunction`;
- bridge/view: the presheaf specialization obtained by applying that owner theorem to `u.op`.

Primitive data are the functor `u` and the hypothesis that the needed pointwise left Kan
extensions along `u.op` exist; the canonical owner itself only needs the resulting left Kan
extensions. The adjunction itself is derived API owned upstream by
`Functor.lanAdjunction`, so this file should use its presheaf specialization directly rather than
keep a parallel local wrapper or a less specific generic recall.
-/

/- Remark 7.5.5: if every diagram `I_Y ⥤ A` has the colimits needed to form the pointwise left
Kan extension along `u.op`, then on `A`-valued presheaves the pullback functor
`u^p = (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op` has the usual left adjoint
`u_p = u.op.lan`; in Lean this is exactly the specialized adjunction
`u.op.lanAdjunction A`. -/
#check (u.op.lanAdjunction A :
  u.op.lan ⊣ (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj u.op)

end

/-! ### Lemma_7_5_6 (from Chap07) -/
universe v u₁ u₂

namespace CategoryTheory

open Opposite Functor

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable (u : C ⥤ D) (U : C)

/- Domain-style sampling:
- primary domain: presheaf left Kan extensions of representables along `u.op`;
- sampled owner API:
  `Functor.leftKanExtensionUnique`,
  `Functor.leftKanExtensionUnit`,
  `CategoryTheory.yonedaMap`,
  the mathlib instance `(yoneda.obj (u.obj U)).IsLeftKanExtension (yonedaMap u U)`;
- source-facing: Lemma 7.5.6 says the pushforward of the representable presheaf `h_U` is
  canonically represented by `u.obj U`;
- core/canonical: the chosen left Kan extension `u.op.leftKanExtension (yoneda.obj U)` and its
  unit;
- bridge/view: specialize the canonical uniqueness isomorphism for left Kan extensions to the
  upstream Yoneda left-extension datum.

Primitive data are only `u` and `U`. The representability isomorphism is derived API from the
owner theorem `Functor.leftKanExtensionUnique`, after supplying the canonical local existence
witness coming from `(yoneda.obj (u.obj U)).IsLeftKanExtension (yonedaMap u U)`. This keeps the
file at the intended bridge/view layer and avoids any parallel local owner declaration.
-/

/- Lemma 7.5.6: for a functor `u : C ⥤ D` and an object `U : C`, the pushforward presheaf
`u_p h_U` is canonically represented by `u.obj U`; in mathlib terms, the chosen left Kan
extension of `yoneda.obj U` along `u.op` is canonically isomorphic to `yoneda.obj (u.obj U)`.
This is the direct specialization of `leftKanExtensionUnique` to the upstream left Kan extension
datum `yonedaMap u U`. -/
recall Functor.leftKanExtensionUnique

#check
  (by
    letI : u.op.HasLeftKanExtension (yoneda.obj U) :=
      HasLeftKanExtension.mk (yoneda.obj (u.obj U)) (yonedaMap u U)
    exact
      (Functor.leftKanExtensionUnique (u.op.leftKanExtension (yoneda.obj U))
        (u.op.leftKanExtensionUnit (yoneda.obj U))
        (yoneda.obj (u.obj U))
        (yonedaMap u U) :
          u.op.leftKanExtension (yoneda.obj U) ≅ yoneda.obj (u.obj U)))

end CategoryTheory

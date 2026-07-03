import Mathlib
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_4_8_1 (from Chap04) -/
universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {F G H : Cᵒᵖ ⥤ Type w}

/- Domain-style sampling for Lemma 4.8.1:
- primary domain: pullbacks in functor categories, specialized to set-valued presheaves
  `Cᵒᵖ ⥤ Type w`;
- sampled owner declarations:
  `pullbackObjIso`,
  `pullbackObjIso_hom_comp_fst`,
  `pullbackObjIso_hom_comp_snd`,
  `pullbackObjIso_inv_comp_fst`;
- best owner abstraction: the canonical objectwise pullback comparison isomorphism
  `pullbackObjIso a b X`;
- primitive data: only the natural transformations `a : F ⟶ G` and `b : H ⟶ G`;
- derived API: the projection comparison lemmas such as `pullbackObjIso_hom_comp_fst`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that fibre products of set-valued presheaves exist and
  are computed objectwise;
- `core/canonical`: mathlib's owner declaration `pullbackObjIso`;
- `bridge/view`: the projection identities, here recalled via `pullbackObjIso_hom_comp_fst`.

There is no local primitive wrapper to keep: the correct refinement is direct recall of the
canonical mathlib owner and its derived projection lemma. -/

/- Lemma 4.8.1: for set-valued presheaves `F, G, H : Cᵒᵖ ⥤ Type w` and natural transformations
`a : F ⟶ G`, `b : H ⟶ G`, the fibre product presheaf is computed objectwise. The canonical
mathlib statement is the objectwise pullback isomorphism `pullbackObjIso a b X`. -/
recall pullbackObjIso

/- The first projection of the objectwise pullback agrees with evaluation of the presheaf pullback
projection; this is exactly `pullbackObjIso_hom_comp_fst`. -/
recall pullbackObjIso_hom_comp_fst

end CategoryTheory.Limits

/-! ### Definition_4_8_2 (from Chap04) -/
universe v u

namespace CategoryTheory

open Opposite Limits
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]
variable {F G : Presheaf C}

/- Source/core/bridge triage for Definition 4.8.2:
- domain-style sampling in the presheaf-representability owner layer:
  `Functor.relativelyRepresentable`,
  `yoneda.relativelyRepresentable`,
  `Functor.IsRepresentable.mk'`,
  `Limits.pullbackObjIso`;
- target layer: canonical recall of the owner `yoneda.relativelyRepresentable`, plus the
  source-facing bridge to representability of fibre products with Yoneda sections;
- core/canonical background: the generic owner `Functor.relativelyRepresentable`, specialized here
  to the Yoneda embedding;
- source-facing sections are maps `ξ : h[U] ⟶ G`, while `yonedaEquiv` remains an internal proof
  bridge to the elementwise view `ξ.app (op U) (𝟙 U) : G.obj (op U)`;
- primitive data: only the presheaf morphism `a : F ⟶ G`;
- derived API: representability of the Yoneda pullbacks of `a`.
-/

/- The generic owner for relative representability of a morphism with respect to a functor is
the canonical definition `Functor.relativelyRepresentable`. -/
recall Functor.relativelyRepresentable

/- Definition 4.8.2: a morphism `a : F ⟶ G` of presheaves is representable, or equivalently `F`
is relatively representable over `G`, precisely when it is relatively representable with respect
to the Yoneda embedding. -/
#check yoneda.relativelyRepresentable

/-- Relative representability of a presheaf morphism is equivalent to representability of each
pullback along a Yoneda section. -/
-- Proof sketch: unfold `Functor.relativelyRepresentable` for a section `ξ : h[U] ⟶ G` and identify
-- the resulting pullback object in the presheaf category with the fibre product presheaf
-- `h[U] ×[G] F`.
theorem relativelyRepresentable_iff_isRepresentable_pullback_yoneda (a : F ⟶ G) :
    yoneda.relativelyRepresentable a ↔
      ∀ (U : C) (ξ : h[U] ⟶ G), (pullback a ξ).IsRepresentable := by
  constructor
  · intro ha U ξ
    -- The chosen represented pullback square already identifies a Yoneda object with the
    -- categorical pullback presheaf.
    exact Functor.IsRepresentable.mk' ((ha.isPullback ξ).isoPullback)
  · intro h U ξ
    letI : (pullback a ξ).IsRepresentable := h U ξ
    let snd : (pullback a ξ).reprX ⟶ U :=
      yoneda.preimage ((pullback a ξ).reprW.hom ≫ pullback.snd a ξ)
    -- Route correction: transport the canonical pullback square of `pullback a ξ` across the
    -- representing isomorphism, and only then extract the underlying map to `U`.
    refine ⟨(pullback a ξ).reprX, snd, (pullback a ξ).reprW.hom ≫ pullback.fst a ξ, ?_⟩
    have hpb : IsPullback ((pullback a ξ).reprW.hom ≫ pullback.fst a ξ)
        ((pullback a ξ).reprW.hom ≫ pullback.snd a ξ) a ξ := by
      simpa using
        (IsPullback.of_hasPullback a ξ).of_iso' ((pullback a ξ).reprW)
          (Iso.refl F) (Iso.refl (h[U])) (Iso.refl G)
          (by simp) (by simp) (by simp) (by simp)
    simpa [snd] using hpb

end CategoryTheory

/-! ### Lemma_4_8_3 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {F G : Presheaf C}

/- Source/core/bridge triage for Lemma 4.8.3:
- source-facing statement: a representable morphism of presheaves with representable codomain has
  representable domain;
- domain-style sampling in the presheaf representability owner layer:
  `yoneda.relativelyRepresentable`,
  `Functor.IsRepresentable`,
  `Functor.reprW`,
  `isRepresentable_of_natIso`;
- core/canonical owners: `yoneda.relativelyRepresentable` and `Functor.IsRepresentable`, with the
  latter recalled in `Definition_4_3_6`;
- bridge/view: specialize relative representability to the canonical Yoneda presentation
  `G.reprW.hom : yoneda.obj G.reprX ⟶ G`;
- primitive data: the morphism `a`, the witness `ha`, and the explicit representability proof
  `hG : G.IsRepresentable`;
- derived API: the induced isomorphism `yoneda.obj (ha.pullback G.reprW.hom) ≅ F`, obtained from
  `ha.fst G.reprW.hom`, is fed to the canonical stability theorem `isRepresentable_of_natIso`.
-/
/-- Lemma 4.8.3: if `a : F ⟶ G` is a representable morphism of presheaves of sets on `C` and
`G` is representable, then `F` is representable. -/
-- Proof sketch: choose a Yoneda presentation `yoneda.obj (G.reprX) ≅ G`. Relative
-- representability of `a` applied to the canonical map `yoneda.obj (G.reprX) ⟶ G` yields a
-- pullback square with top-left corner again of the form `yoneda.obj X`. Since the right vertical
-- map is an isomorphism, the left vertical map is an isomorphism as well, so `F` is representable.
theorem isRepresentable_of_relativelyRepresentable_of_isRepresentable_codomain
    (a : F ⟶ G) (ha : yoneda.relativelyRepresentable a) (hG : G.IsRepresentable) :
    F.IsRepresentable := by
  letI : G.IsRepresentable := hG
  -- Specialize relative representability to the canonical Yoneda presentation of `G`.
  letI : IsIso (ha.fst G.reprW.hom) := (ha.isPullback G.reprW.hom).isIso_fst_of_isIso
  -- Transport representability across the resulting Yoneda isomorphism onto `F`.
  exact isRepresentable_of_natIso (yoneda.obj (ha.pullback G.reprW.hom))
    (asIso (ha.fst G.reprW.hom))

end CategoryTheory

/-! ### Lemma_4_8_4 (from Chap04) -/
universe v u

namespace CategoryTheory

open Opposite Limits Functor.relativelyRepresentable
open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasPullbacks C]

/-
Source/core/bridge triage for Lemma 4.8.4:
- domain-style sampling in the presheaf representability layer:
  `Functor.relativelyRepresentable.diag_iff`,
  `yoneda.relativelyRepresentable`,
  `Limits.pullback`,
  `relativelyRepresentable_iff_isRepresentable_pullback_yoneda`,
  `yoneda.obj`;
- source-facing owner: `presheaf_diagonal_representability_tfae`;
- core/canonical owner: `Functor.relativelyRepresentable.diag_iff`;
- bridge/view API: specialize the owner-level diagonal criterion to Yoneda sections
  `ξ : h[U] ⟶ F`, then translate relative representability of each section to representability of
  the associated pullback by Definition 4.8.2.
- primitive data: only the presheaf `F`;
- derived API: relative representability of `diag F`, relative representability of each Yoneda
  section, and representability of the associated Yoneda pullbacks.
-/

/-- Helper for Lemma 4.8.4: the diagonal of a presheaf is relatively representable exactly when
every Yoneda section is relatively representable. -/
lemma diag_relativelyRepresentable_iff_forall_yoneda_section (F : Presheaf.{v} C) :
    yoneda.relativelyRepresentable (diag F) ↔
      ∀ (U : C) (ξ : h[U] ⟶ F), yoneda.relativelyRepresentable ξ := by
  -- This is the owner-level diagonal criterion specialized to presheaves.
  simpa using
    (diag_iff :
      yoneda.relativelyRepresentable (diag F) ↔
        ∀ ⦃U : C⦄ (ξ : yoneda.obj U ⟶ F), yoneda.relativelyRepresentable ξ)

omit [HasBinaryProducts C] [HasPullbacks C] in
/-- Helper for Lemma 4.8.4: a Yoneda section is relatively representable exactly when all of its
Yoneda pullbacks are representable. -/
lemma yoneda_section_relativelyRepresentable_iff_forall_pullback_isRepresentable
    {F : Presheaf.{v} C} {U : C} (ξ : h[U] ⟶ F) :
    yoneda.relativelyRepresentable ξ ↔
      ∀ (V : C) (ξ' : h[V] ⟶ F), (pullback ξ ξ').IsRepresentable := by
  -- This is Definition 4.8.2 in the special case of a section from a representable presheaf.
  simpa using relativelyRepresentable_iff_isRepresentable_pullback_yoneda ξ

/-- Lemma 4.8.4: for a presheaf `F` on a category with binary products and pullbacks, the
relative representability of the diagonal `Δ : F ⟶ F × F`, the relative representability of every
section `h_U ⟶ F`, and the representability of every fibre product `h_U ×[F] h_V` cut out by two
sections are equivalent. -/
theorem presheaf_diagonal_representability_tfae (F : Presheaf.{v} C) :
    [yoneda.relativelyRepresentable (diag F),
      ∀ (U : C) (ξ : h[U] ⟶ F), yoneda.relativelyRepresentable ξ,
      ∀ (U V : C) (ξ : h[U] ⟶ F) (ξ' : h[V] ⟶ F), (pullback ξ ξ').IsRepresentable].TFAE := by
  -- First package the diagonal criterion as the representability of every Yoneda section.
  tfae_have 1 ↔ 2 := by
    simpa using diag_relativelyRepresentable_iff_forall_yoneda_section F
  -- Next translate each relatively representable section into representable Yoneda pullbacks.
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h U V ξ ξ'
      exact (yoneda_section_relativelyRepresentable_iff_forall_pullback_isRepresentable ξ).1
        (h U ξ) V ξ'
    · intro h U ξ
      exact (yoneda_section_relativelyRepresentable_iff_forall_pullback_isRepresentable ξ).2
        (fun V ξ' ↦ h U V ξ ξ')
  -- The two equivalences assemble into the required TFAE statement.
  tfae_finish

end CategoryTheory

import Mathlib
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_45_1 (from Chap07) -/
universe w v u

namespace CategoryTheory

open Limits
open scoped TerminalPresheaf

variable {C : Type u} [Category.{v} C]
variable (ℱ : Presheaf C)

/-
Domain-style sampling for Definition 7.45.1:
- primary domain: set-valued presheaves and their global sections;
- sampled owner API:
  `Presheaf`,
  `Functor.sectionsEquivHom`,
  `Functor.sections`,
  `Functor.isTerminalConst`,
  `Types.isTerminalPUnit`;
- best owner abstraction: `Functor.sections` is the canonical owner of global sections for a
  `Type`-valued presheaf, and the source formula
  `Γ(\mathcal C, \mathcal F) = \operatorname{Mor}_{PSh(\mathcal C)}(*, \mathcal F)` is its
  canonical bridge `Functor.sectionsEquivHom`;
- primitive data: only the presheaf `ℱ : Presheaf C`;
- derived API: the realization of the terminal presheaf as the constant singleton-valued presheaf
  and the induced equivalence from sections to morphisms out of that terminal object, now exposed
  by the source-facing notation `*ₚ[C]`;

Source/core/bridge triage:
- `source-facing`: the formula identifying global sections with morphisms from the terminal
  presheaf;
- `core/canonical`: `Functor.sections`;
- `bridge/view`: `Functor.sectionsEquivHom`, together with `Functor.isTerminalConst` for the
  singleton-valued terminal presheaf `*ₚ[C]`.

Accordingly this definition item is a bridge/view recall around the canonical owner
`Functor.sections`, not a new owner declaration.
-/
/-
Definition 7.45.1 (Stacks, tag `06UN`): for a presheaf of sets `ℱ : Presheaf C`, the source
formula
`Γ(\mathcal C, \mathcal F) = \operatorname{Mor}_{PSh(\mathcal C)}(*, \mathcal F)` is the
`PUnit` specialization of the canonical bridge `Functor.sectionsEquivHom`.
-/
recall Functor.sectionsEquivHom

/- Companion check: the singleton-valued terminal presheaf `*ₚ[C]` is terminal in
`Presheaf C`. -/
#check
  (Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit :
    IsTerminal *ₚ[C])

/- Source-facing specialization: global sections of `ℱ` identify with morphisms from the terminal
singleton-valued presheaf `*ₚ[C]` to `ℱ`. -/
#check
  (show ℱ.sections ≃ (*ₚ[C] ⟶ ℱ) from ℱ.sectionsEquivHom PUnit)

end CategoryTheory

/-! ### Lemma_7_45_2 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.GrothendieckTopology

open scoped SheafifiedRepresentable
open scoped TerminalSheaf

attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

variable {J}
variable {U V : C} (a b : V ⟶ U)

/- Domain-style sampling for Lemma 7.45.2:
- primary domain: global sections of sheaves of types, viewed through Hom-sets out of the
  sheafified representables `h[U]^#[J]` and the terminal sheaf;
- sampled owner API:
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`,
  `Sheaf.ΓObjEquivHom`,
  `Sheaf.ΓRes`,
  `Cofork.IsColimit.homIso`;
- best owner abstraction: apply `Hom(-, ℱ)` to the source-facing coequalizer
  `h[V]^#[J] ⇉ h[U]^#[J] ⟶ 1` and then identify the resulting Hom-sets by the canonical
  sheafified-Yoneda and global-sections equivalences;
- primitive data: the coequalizer cofork in `Sheaf J (Type (max u v))`;
- derived API: the equalizer cone on `Γ(C, ℱ) ⟶ ℱ(U) ⇉ ℱ(V)`.

Source/core/bridge triage:
- `source-facing`: the public equalizer statement on global sections;
- `core/canonical`: `uliftSheafifiedRepresentableHomEquiv`, `Sheaf.ΓRes`, and
  `Cofork.IsColimit.homIso`;
- `bridge/view`: the local comparison between morphisms from the constant singleton sheaf and
  the chosen terminal singleton sheaf `*[J]`.

Accordingly the public theorem below stays source-facing, while the proof reuses the owner-level
Hom equivalences rather than introducing a parallel coequalizer/equalizer API. -/

-- Proof sketch: the explicit terminal singleton sheaf is terminal, so the two composites agree by
-- uniqueness of morphisms into a terminal object.
private theorem sheafifiedRepresentable_to_terminalSheaf_condition :
    J.sheafifiedRepresentableMap a ≫ (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ =
      J.sheafifiedRepresentableMap b ≫ (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ := by
  simp

-- Proof sketch: the chosen terminal singleton sheaf is canonically the constant singleton sheaf
-- after sheafification, so the owner equivalence `Sheaf.ΓObjEquivHom` specializes to morphisms
-- from this terminal sheaf.
private noncomputable def constantSheafPUnitIsoTerminalSheaf :
    (constantSheaf J (Type (max u v))).obj PUnit.{(max u v) + 1} ≅
      *[J] := by
  simpa [constantSheaf, Sheaf.terminal] using (sheafificationIso (*[J])).symm

private noncomputable def globalSectionsEquivTerminalSheafHom
    (ℱ : Sheaf J (Type (max u v))) :
    (Sheaf.Γ J (Type (max u v))).obj ℱ ≃ (*[J] ⟶ ℱ) :=
  (Sheaf.ΓObjEquivHom J ℱ PUnit.{(max u v) + 1}).trans
    ((constantSheafPUnitIsoTerminalSheaf).homCongr (Iso.refl ℱ))

-- Proof sketch: after transporting along the sheafification adjunction, the unique map from
-- `h_U^#` to the terminal singleton sheaf is sent by
-- `uliftSheafifiedRepresentableHomEquiv` to `PUnit.unit`, so composition with `τ` evaluates to
-- `τ.app (op U) ()`.
private theorem sheafifiedRepresentableHomEquiv_terminalSheaf_comp
    (ℱ : Sheaf J (Type (max u v))) (W : C) (τ : *[J] ⟶ ℱ) :
    J.uliftSheafifiedRepresentableHomEquiv ℱ W
        ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ τ) =
      τ.hom.app (op W) PUnit.unit := by
  calc
    CategoryTheory.uliftYonedaEquiv
        (((sheafificationAdjunction J (Type (max u v))).homEquiv
            (CategoryTheory.uliftYoneda.{max u v}.obj W) ℱ)
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ τ)) =
      τ.hom.app (op W)
        (J.uliftSheafifiedRepresentableHomEquiv *[J] W
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _)) := by
            simpa using
              (J.uliftSheafifiedRepresentableHomEquiv_comp
                ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from (h[W]^#[J])) τ)
    _ = τ.hom.app (op W) PUnit.unit := by
      simp [GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv, Sheaf.terminal]

-- Proof sketch: the owner equivalence `Sheaf.ΓObjEquivHom` sends a global section to the induced
-- morphism from the constant singleton sheaf, and evaluating that morphism at the unique element
-- recovers the usual restriction map `ΓRes`.
private theorem globalSectionsEquivTerminalSheafHom_app_eq_res
    (ℱ : Sheaf J (Type (max u v))) (W : C)
    (x : (Sheaf.Γ J (Type (max u v))).obj ℱ) :
    ((globalSectionsEquivTerminalSheafHom ℱ x).hom.app (op W) PUnit.unit) =
      Sheaf.ΓRes ℱ (op W) x := by
  have h := congr_fun
    (congr_app
      (Sheaf.ΓHomEquiv_naturality_left_symm
        (show PUnit.{(max u v) + 1} ⟶ (Sheaf.Γ J (Type (max u v))).obj ℱ from
          (Equiv.funUnique PUnit _).symm x)
        (𝟙 _))
      (op W))
    PUnit.unit
  simpa [globalSectionsEquivTerminalSheafHom, constantSheafPUnitIsoTerminalSheaf,
    Sheaf.ΓObjEquivHom, Sheaf.ΓRes, Sheaf.coneΓ] using h

private theorem sheafifiedRepresentableHomEquiv_globalSection_comp
    (ℱ : Sheaf J (Type (max u v))) (W : C)
    (x : (Sheaf.Γ J (Type (max u v))).obj ℱ) :
    J.uliftSheafifiedRepresentableHomEquiv ℱ W
        ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫
          globalSectionsEquivTerminalSheafHom ℱ x) =
      Sheaf.ΓRes ℱ (op W) x := by
  calc
    J.uliftSheafifiedRepresentableHomEquiv ℱ W
        ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫
          globalSectionsEquivTerminalSheafHom ℱ x) =
      (globalSectionsEquivTerminalSheafHom ℱ x).hom.app (op W) PUnit.unit := by
        simpa using
          sheafifiedRepresentableHomEquiv_terminalSheaf_comp ℱ W
            (globalSectionsEquivTerminalSheafHom ℱ x)
    _ = Sheaf.ΓRes ℱ (op W) x := by
        exact globalSectionsEquivTerminalSheafHom_app_eq_res ℱ W x

-- Proof sketch: apply `Hom(-, ℱ)` to the given coequalizer cofork
-- `h_V^# ⇉ h_U^# ⟶ *`. The resulting map on global sections equalizes the two pullback maps.
private theorem globalSections_equalizer_condition
    (ℱ : Sheaf J (Type (max u v))) :
    Sheaf.ΓRes ℱ (op U) ≫ ℱ.obj.map a.op =
      Sheaf.ΓRes ℱ (op U) ≫ ℱ.obj.map b.op := by
  ext x
  let β : *[J] ⟶ ℱ :=
    globalSectionsEquivTerminalSheafHom ℱ x
  have hw :
      J.sheafifiedRepresentableMap a ≫ (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β =
        J.sheafifiedRepresentableMap b ≫ (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫
          β := by
    exact congrArg (fun k ↦ k ≫ β) (sheafifiedRepresentable_to_terminalSheaf_condition a b)
  calc
    ℱ.obj.map a.op (Sheaf.ΓRes ℱ (op U) x) =
      ℱ.obj.map a.op
        (J.uliftSheafifiedRepresentableHomEquiv ℱ U
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)) := by
            rw [sheafifiedRepresentableHomEquiv_globalSection_comp ℱ U x]
    _ = J.uliftSheafifiedRepresentableHomEquiv ℱ V
        (J.sheafifiedRepresentableMap a ≫
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)) := by
            simpa [Category.assoc, sheafifiedRepresentableMap,
              sheafifiedRepresentableFunctor] using
              (J.uliftSheafifiedRepresentableHomEquiv_naturality a ℱ
                ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)).symm
    _ = J.uliftSheafifiedRepresentableHomEquiv ℱ V
        (J.sheafifiedRepresentableMap b ≫
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)) := by
            rw [hw]
    _ = ℱ.obj.map b.op
        (J.uliftSheafifiedRepresentableHomEquiv ℱ U
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)) := by
            simpa [Category.assoc, sheafifiedRepresentableMap,
              sheafifiedRepresentableFunctor] using
              (J.uliftSheafifiedRepresentableHomEquiv_naturality b ℱ
                ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β))
    _ = ℱ.obj.map b.op (Sheaf.ΓRes ℱ (op U) x) := by
            rw [sheafifiedRepresentableHomEquiv_globalSection_comp ℱ U x]

-- Proof sketch: apply `Hom(-, ℱ)` to the given coequalizer cofork
-- `h_V^# ⇉ h_U^# ⟶ *`. By `Limits.Types.type_equalizer_iff_unique`, the resulting equalizer on
-- Hom-sets says that `Γ(C, ℱ)` is the equalizer of the pullback maps `ℱ(U) ⇉ ℱ(V)`.
/-- Lemma 7.45.2: if the canonical cofork
`h[V]^#[J] ⇉ h[U]^#[J] ⟶ *[J]` is a coequalizer in sheaves on
`(C, J)`, then the global sections of `ℱ` are the equalizer of the restriction maps
`ℱ(U) ⇉ ℱ(V)` induced by `a` and `b`. -/
noncomputable def globalSections_is_equalizer_of_sheafifiedRepresentable_coequalizer
    (ℱ : Sheaf J (Type (max u v)))
    (hcoeq : IsColimit
      (Cofork.ofπ ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from
          (h[U]^#[J]))
        (sheafifiedRepresentable_to_terminalSheaf_condition a b))) :
    IsLimit
      (Fork.ofι (Sheaf.ΓRes ℱ (op U)) (globalSections_equalizer_condition a b ℱ)) := by
  refine Limits.Types.typeEqualizerOfUnique
    (Sheaf.ΓRes ℱ (op U))
    (globalSections_equalizer_condition a b ℱ) ?_
  intro y hy
  let α : h[U]^#[J] ⟶ ℱ := (J.uliftSheafifiedRepresentableHomEquiv ℱ U).symm y
  have hα : J.sheafifiedRepresentableMap a ≫ α = J.sheafifiedRepresentableMap b ≫ α := by
    apply (J.uliftSheafifiedRepresentableHomEquiv ℱ V).injective
    calc
      J.uliftSheafifiedRepresentableHomEquiv ℱ V (J.sheafifiedRepresentableMap a ≫ α) =
        ℱ.obj.map a.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
          simpa [sheafifiedRepresentableMap, sheafifiedRepresentableFunctor] using
            J.uliftSheafifiedRepresentableHomEquiv_naturality a ℱ α
      _ = ℱ.obj.map b.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
          rw [(J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply y]
          exact hy
      _ = J.uliftSheafifiedRepresentableHomEquiv ℱ V (J.sheafifiedRepresentableMap b ≫ α) := by
          symm
          simpa [sheafifiedRepresentableMap, sheafifiedRepresentableFunctor] using
            J.uliftSheafifiedRepresentableHomEquiv_naturality b ℱ α
  let e := Cofork.IsColimit.homIso hcoeq ℱ
  let β : *[J] ⟶ ℱ :=
    e.symm ⟨α, hα⟩
  refine ⟨(globalSectionsEquivTerminalSheafHom ℱ).symm β, ?_, ?_⟩
  · have hβ :
        (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from (h[U]^#[J]) ≫ β = α := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨α, hα⟩)
    calc
      Sheaf.ΓRes ℱ (op U) ((globalSectionsEquivTerminalSheafHom ℱ).symm β) =
        J.uliftSheafifiedRepresentableHomEquiv ℱ U
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β) := by
            symm
            simpa [β] using
              (sheafifiedRepresentableHomEquiv_globalSection_comp ℱ U
                ((globalSectionsEquivTerminalSheafHom ℱ).symm β))
      _ = J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by rw [hβ]
      _ = y := by
          exact (J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply y
  · intro x hx
    apply (globalSectionsEquivTerminalSheafHom ℱ).injective
    apply e.injective
    trans ⟨α, hα⟩
    · apply Subtype.ext
      apply (J.uliftSheafifiedRepresentableHomEquiv ℱ U).injective
      calc
        J.uliftSheafifiedRepresentableHomEquiv ℱ U
            ((e (globalSectionsEquivTerminalSheafHom ℱ x)).1) =
          Sheaf.ΓRes ℱ (op U) x := by
            simpa [e, Cofork.IsColimit.homIso] using
              (sheafifiedRepresentableHomEquiv_globalSection_comp ℱ U x)
      _ = y := hx
      _ = J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
            exact ((J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply y).symm
    · simpa [β] using
        (e.apply_symm_apply ⟨α, hα⟩).symm

-- Proof sketch: apply `Limits.Types.unique_of_type_equalizer` to the equalizer witness
-- constructed above; this directly packages the unique global section restricting to the
-- compatible section `y`.
/-- A section of `ℱ(U)` whose pullbacks along `a` and `b` agree comes from a unique global section
of `ℱ` whenever `h[V]^#[J] ⇉ h[U]^#[J] ⟶ *[J]` is a coequalizer. -/
theorem globalSections_is_equalizer_of_sheafifiedRepresentable_coequalizer_existsUnique
    (ℱ : Sheaf J (Type (max u v)))
    (hcoeq : IsColimit
      (Cofork.ofπ ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from
          (h[U]^#[J]))
        (sheafifiedRepresentable_to_terminalSheaf_condition a b)))
    (y : ℱ.obj.obj (op U))
    (hy : ℱ.obj.map a.op y = ℱ.obj.map b.op y) :
    ∃! x : (Sheaf.Γ J (Type (max u v))).obj ℱ, Sheaf.ΓRes ℱ (op U) x = y := by
  -- Apply the previously constructed equalizer witness in `Type` to the compatible section `y`.
  simpa using
    (Limits.Types.unique_of_type_equalizer
      (f := Sheaf.ΓRes ℱ (op U))
      (g := ℱ.obj.map a.op)
      (h := ℱ.obj.map b.op)
      (w := globalSections_equalizer_condition a b ℱ)
      (t := globalSections_is_equalizer_of_sheafifiedRepresentable_coequalizer
        (J := J) (a := a) (b := b) ℱ hcoeq)
      y hy)

end CategoryTheory.GrothendieckTopology

/-! ### Remark_7_45_3 (from Chap07) -/
open CategoryTheory
open CategoryTheory.TwoSquare
open scoped MorphismOfTopoiIn TwoSquare

noncomputable section

universe u v w

namespace CategoryTheory

variable {B' B C'' C' C D'' D' D : Type u}
variable [Category.{v} B'] [Category.{v} B] [Category.{v} C''] [Category.{v} C'] [Category.{v} C]
variable [Category.{v} D''] [Category.{v} D'] [Category.{v} D]
variable {JB' : GrothendieckTopology B'}
variable {JB : GrothendieckTopology B}
variable {JC'' : GrothendieckTopology C''}
variable {JC' : GrothendieckTopology C'}
variable {JC : GrothendieckTopology C}
variable {JD'' : GrothendieckTopology D''}
variable {JD' : GrothendieckTopology D'}
variable {JD : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.45.3:
- primary domain: base-change morphisms for commutative squares of topoi;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `MorphismOfTopoiIn.baseChange`,
  `MorphismOfTopoiIn.comp`,
  `CategoryTheory.mateEquiv_hcomp`,
  `CategoryTheory.mateEquiv_vcomp`;
- source/core/bridge triage:
  `source-facing`: the vertical-composition law for base change morphisms of topoi;
  `core/canonical`: `MorphismOfTopoiIn.baseChange`, `CategoryTheory.mateEquiv_hcomp`, and
    `MorphismOfTopoiIn.comp`;
  `bridge/view`: the inverse-image `TwoSquare` of one square of topoi.

Primitive data are the four morphisms of topoi in one square together with the inverse-image
square `TwoSquare (g⁻¹) (f⁻¹) (f'⁻¹) (g'⁻¹)`. The base change morphism itself is the owner
declaration `MorphismOfTopoiIn.baseChange`; this remark keeps only the source-facing
vertical-composition formula. Raw equalities of inverse-image composites are therefore only a
bridge into `TwoSquare`, not the public API of this remark. The horizontal-composition formula
below is retained only as a minimal auxiliary companion for `Remark_7_45_4`.
-/

namespace MorphismOfTopoiIn

-- Proof sketch: the composite of the two source-facing base change maps is the horizontal
-- composition of the mates of the lower and upper inverse-image squares. Then `mateEquiv_hcomp`
-- identifies that horizontal composition with the mate of the outer rectangle.
/-- Remark 7.45.3: for two vertically composable commutative squares of topoi, the composite of
their two base change maps is the base change map of the outer rectangle. -/
theorem baseChange_vertical_composite_eq
    (k : MorphismOfTopoiIn JB JB')
    (l : MorphismOfTopoiIn JC JC')
    (m : MorphismOfTopoiIn JD JD')
    (g' : MorphismOfTopoiIn JD' JC')
    (g : MorphismOfTopoiIn JD JC)
    (f' : MorphismOfTopoiIn JC' JB')
    (f : MorphismOfTopoiIn JC JB)
    (upper : TwoSquare (l⁻¹) (f⁻¹) (f'⁻¹) (k⁻¹))
    (lower : TwoSquare (m⁻¹) (g⁻¹) (g'⁻¹) (l⁻¹)) :
    (Functor.associator (f _*) (g _*) (m⁻¹)).hom ≫
        Functor.whiskerLeft
          (f _*)
          (baseChange l g' g m lower) ≫
          (Functor.associator (f _*) (l⁻¹) (g' _*)).inv ≫
            Functor.whiskerRight
              (baseChange k f' f l upper)
              (g' _*) ≫
                (Functor.associator (k⁻¹) (f' _*) (g' _*)).hom =
      baseChange k (g'.comp f') (g.comp f) m (lower ≫ᵥ upper) := by
  change
    ((mateEquiv f.adjunction f'.adjunction upper) ≫ₕ
      (mateEquiv g.adjunction g'.adjunction lower)).natTrans =
      baseChange k (g'.comp f') (g.comp f) m (lower ≫ᵥ upper)
  simpa [baseChange, comp] using
    congrArg TwoSquare.natTrans
      (mateEquiv_hcomp
        g.adjunction
        g'.adjunction
        f.adjunction
        f'.adjunction
        lower
        upper).symm

-- Auxiliary companion: this horizontal-composition formula is not the source statement of
-- Remark 7.45.3. It is kept as minimal canonical topos-level API for `Remark_7_45_4`.
-- Proof sketch: the composite of the two base change maps is the vertical composition of the
-- mates of the right and left inverse-image squares. Then `mateEquiv_vcomp` identifies that
-- vertical composition with the mate of the outer rectangle.
/-- Auxiliary horizontal-composition formula for base change morphisms of topoi. -/
theorem baseChange_horizontal_composite_eq
    (g' : MorphismOfTopoiIn JC' JC'')
    (g : MorphismOfTopoiIn JC JC')
    (f'' : MorphismOfTopoiIn JD'' JC'')
    (f' : MorphismOfTopoiIn JD' JC')
    (f : MorphismOfTopoiIn JD JC)
    (h' : MorphismOfTopoiIn JD' JD'')
    (h : MorphismOfTopoiIn JD JD')
    (left : TwoSquare (h'⁻¹) (f'⁻¹) (f''⁻¹) (g'⁻¹))
    (right : TwoSquare (h⁻¹) (f⁻¹) (f'⁻¹) (g⁻¹)) :
    (Functor.associator (f _*) (h⁻¹) (h'⁻¹)).inv ≫
        Functor.whiskerRight
          (baseChange g f' f h right)
          (h'⁻¹) ≫
          (Functor.associator (g⁻¹) (f' _*) (h'⁻¹)).hom ≫
            Functor.whiskerLeft
              (g⁻¹)
              (baseChange g' f'' f' h' left) ≫
              (Functor.associator (g⁻¹) (g'⁻¹) (f'' _*)).inv =
      baseChange (g.comp g') f'' f (h.comp h') (right ≫ₕ left) := by
  change
    ((mateEquiv f.adjunction f'.adjunction right) ≫ᵥ
      (mateEquiv f'.adjunction f''.adjunction left)).natTrans =
      baseChange (g.comp g') f'' f (h.comp h') (right ≫ₕ left)
  simpa [baseChange, comp] using
    congrArg TwoSquare.natTrans
      (mateEquiv_vcomp
        f.adjunction
        f'.adjunction
        f''.adjunction
        right
        left).symm

end MorphismOfTopoiIn

end CategoryTheory

/-! ### Remark_7_45_4 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.TwoSquare
open scoped MorphismOfTopoiIn TwoSquare

noncomputable section

universe u v w

variable {C'' C' C D'' D' D : Type u}
variable [Category.{v} C''] [Category.{v} C'] [Category.{v} C]
variable [Category.{v} D''] [Category.{v} D'] [Category.{v} D]
variable {JC'' : GrothendieckTopology C''}
variable {JC' : GrothendieckTopology C'}
variable {JC : GrothendieckTopology C}
variable {JD'' : GrothendieckTopology D''}
variable {JD' : GrothendieckTopology D'}
variable {JD : GrothendieckTopology D}

/-- Helper for Remark 7.45.4: an auxiliary ringed-site object carries only the site data needed
to talk about its associated topos. -/
structure RingedSite where
  /-- The underlying site category. -/
  C : Type u
  /-- The category structure on the underlying site. -/
  cat : Category.{v} C
  /-- The Grothendieck topology presenting the associated topos. -/
  J : GrothendieckTopology C

attribute [instance] RingedSite.cat

namespace RingedSite

/-- Helper for Remark 7.45.4: a morphism of auxiliary ringed sites is determined by its
underlying morphism of topoi. -/
structure Hom (X Y : RingedSite.{u, v}) where
  /-- The underlying morphism of topoi attached to the auxiliary ringed-site morphism. -/
  toMorphismOfTopoi : MorphismOfTopoiIn.{u, u, v, v, w} Y.J X.J

/-- Helper for Remark 7.45.4: the auxiliary ringed sites expose the hom type needed by the local
statement without introducing extra structure beyond the underlying morphisms of topoi. -/
instance : Quiver RingedSite where
  Hom X Y := RingedSite.Hom X Y

namespace Hom

/-- Helper for Remark 7.45.4: the local proof treats every auxiliary ringed-site morphism as
carrying an underlying morphism of topoi. -/
class HasToposMorphism (_α : Sort _) {X Y : RingedSite.{u, v}} (_f : X ⟶ Y) : Prop

/-- Helper for Remark 7.45.4: every auxiliary ringed-site morphism automatically satisfies the
local `HasToposMorphism` interface. -/
instance {α : Sort _} {X Y : RingedSite.{u, v}} (f : X ⟶ Y) : HasToposMorphism α f := ⟨⟩

/- Domain-style sampling for Remark 7.45.4:
- primary domain: base-change mates for commutative squares of morphisms of ringed topoi;
- sampled owner API:
  `MorphismOfTopoiIn.comp`,
  `MorphismOfTopoiIn.baseChange`,
  `MorphismOfTopoiIn.baseChange_horizontal_composite_eq`,
  `RingedSite.Hom.HasToposMorphism`,
  `RingedSite.Hom.toMorphismOfTopoi`,
  `CategoryTheory.mateEquiv_hcomp`;
- source/core/bridge triage:
  `source-facing`: the ringed-topos horizontal-composition statement;
  `core/canonical`: `MorphismOfTopoiIn` together with `MorphismOfTopoiIn.baseChange`;
  `bridge/view`: passage from a ringed-site morphism to the bundled bridge owner
    `RingedSite.Hom.HasToposMorphism` and then to the underlying morphism of topoi via
    `RingedSite.Hom.toMorphismOfTopoi`.

Primitive data are the ringed-site morphisms together with commutativity equalities for their
underlying morphisms of topoi. The induced inverse-image `TwoSquare`s are derived bridge data.
The horizontal-composition formula itself belongs to the canonical topos-level owner theorem
`MorphismOfTopoiIn.baseChange_horizontal_composite_eq`, so this file should reuse that owner
directly. -/

variable {X'' X' X Y'' Y' Y : RingedSite}

/-- Helper for Remark 7.45.4: applying inverse image to a commutative square of underlying
morphisms of topoi gives the equality of functor composites needed for base change. -/
private theorem inverseImageCompEq
    (g : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y)
    [HasToposMorphism (Type w) g] [HasToposMorphism (Type w) f']
    [HasToposMorphism (Type w) f] [HasToposMorphism (Type w) h]
    (hcomm :
      MorphismOfTopoiIn.comp
          f.toMorphismOfTopoi
          g.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          f'.toMorphismOfTopoi) :
    (h.toMorphismOfTopoi⁻¹) ⋙ (f'.toMorphismOfTopoi⁻¹) =
      (f.toMorphismOfTopoi⁻¹) ⋙ (g.toMorphismOfTopoi⁻¹) := by
  -- Applying inverse image to the commutative square gives the required equality of composites.
  -- The equality comes from applying `inverseImage` to the commutative square and reorienting it.
  exact
    (show
        (f.toMorphismOfTopoi⁻¹) ⋙ (g.toMorphismOfTopoi⁻¹) =
          (h.toMorphismOfTopoi⁻¹) ⋙ (f'.toMorphismOfTopoi⁻¹) by
      simpa [MorphismOfTopoiIn.comp] using
        congrArg LeftExactAdjunction.inverseImage hcomm).symm

/-- Helper for Remark 7.45.4: a commutative square of the underlying morphisms of topoi induces
the corresponding `TwoSquare` on inverse-image functors. This is the internal bridge from
source-style commutativity data to the canonical square datum used by base change. -/
private def inverseImageSquareOfCompEq
    (g : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (h : Y' ⟶ Y)
    [HasToposMorphism (Type w) g] [HasToposMorphism (Type w) f']
    [HasToposMorphism (Type w) f] [HasToposMorphism (Type w) h]
    (hcomm :
      MorphismOfTopoiIn.comp
          f.toMorphismOfTopoi
          g.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          f'.toMorphismOfTopoi) :
    TwoSquare
      (h.toMorphismOfTopoi⁻¹)
      (f.toMorphismOfTopoi⁻¹)
      (f'.toMorphismOfTopoi⁻¹)
      (g.toMorphismOfTopoi⁻¹) :=
  eqToHom (inverseImageCompEq g f' f h hcomm)

/- Source/core/bridge triage for the public API below:
- `inverseImageSquareOfCompEq` is an internal bridge/view from commutativity of the underlying
  morphisms of topoi to the canonical square owner;
- the public theorem `baseChange_horizontal_composite_eq` is source-facing: it takes commutative
  squares of ringed-topos morphisms with commuting underlying morphisms of topoi, converts them
  to the canonical inverse-image squares internally, and then reuses the owner theorem.
-/

-- Proof sketch: convert the two commutative underlying squares of topoi to their canonical
-- inverse-image `TwoSquare`s using `inverseImageSquareOfCompEq`, then invoke the canonical
-- topos-level owner theorem directly.
/-- Remark 7.45.4: for two horizontally composable squares of morphisms of ringed topoi whose
underlying morphisms of topoi commute, the composite of the two base change maps is the base
change map of the outer rectangle. -/
theorem baseChange_horizontal_composite_eq
    (g' : X'' ⟶ X') (g : X' ⟶ X) (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
    (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
    [HasToposMorphism (Type w) g'] [HasToposMorphism (Type w) g]
    [HasToposMorphism (Type w) f''] [HasToposMorphism (Type w) f']
    [HasToposMorphism (Type w) f] [HasToposMorphism (Type w) h']
    [HasToposMorphism (Type w) h]
    (leftComm :
      MorphismOfTopoiIn.comp
          f'.toMorphismOfTopoi
          g'.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h'.toMorphismOfTopoi
          f''.toMorphismOfTopoi)
    (rightComm :
      MorphismOfTopoiIn.comp
          f.toMorphismOfTopoi
          g.toMorphismOfTopoi =
        MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          f'.toMorphismOfTopoi) :
    (Functor.associator
        (f.toMorphismOfTopoi _*)
        (h.toMorphismOfTopoi⁻¹)
        (h'.toMorphismOfTopoi⁻¹)).inv ≫
        Functor.whiskerRight
          (MorphismOfTopoiIn.baseChange
            g.toMorphismOfTopoi
            f'.toMorphismOfTopoi
            f.toMorphismOfTopoi
            h.toMorphismOfTopoi
            (inverseImageSquareOfCompEq g f' f h rightComm))
          (h'.toMorphismOfTopoi⁻¹) ≫
          (Functor.associator
            (g.toMorphismOfTopoi⁻¹)
            (f'.toMorphismOfTopoi _*)
            (h'.toMorphismOfTopoi⁻¹)).hom ≫
            Functor.whiskerLeft
              (g.toMorphismOfTopoi⁻¹)
              (MorphismOfTopoiIn.baseChange
                g'.toMorphismOfTopoi
                f''.toMorphismOfTopoi
                f'.toMorphismOfTopoi
                h'.toMorphismOfTopoi
                (inverseImageSquareOfCompEq g' f'' f' h' leftComm)) ≫
              (Functor.associator
                (g.toMorphismOfTopoi⁻¹)
                (g'.toMorphismOfTopoi⁻¹)
                (f''.toMorphismOfTopoi _*)).inv =
      MorphismOfTopoiIn.baseChange
        (MorphismOfTopoiIn.comp
          g.toMorphismOfTopoi
          g'.toMorphismOfTopoi)
        f''.toMorphismOfTopoi
        f.toMorphismOfTopoi
        (MorphismOfTopoiIn.comp
          h.toMorphismOfTopoi
          h'.toMorphismOfTopoi)
        (inverseImageSquareOfCompEq g f' f h rightComm ≫ₕ
          inverseImageSquareOfCompEq g' f'' f' h' leftComm) := by
  -- Convert the two commutative underlying squares to inverse-image `TwoSquare`s and then
  -- invoke the canonical topos-level horizontal-composition theorem.
  simpa using
    MorphismOfTopoiIn.baseChange_horizontal_composite_eq
      g'.toMorphismOfTopoi
      g.toMorphismOfTopoi
      f''.toMorphismOfTopoi
      f'.toMorphismOfTopoi
      f.toMorphismOfTopoi
      h'.toMorphismOfTopoi
      h.toMorphismOfTopoi
      (inverseImageSquareOfCompEq g' f'' f' h' leftComm)
      (inverseImageSquareOfCompEq g f' f h rightComm)

end Hom
end RingedSite

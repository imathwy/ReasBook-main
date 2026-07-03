import Mathlib
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_22_1 (from Chap04) -/
open CategoryTheory CategoryTheory.Limits
open Opposite

universe uI vI uC vC uD vD

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/- Domain-style sampling for Definition 4.22.1:
- primary domain: filtered/cofiltered diagrams, their cocones/cones, and canonical split
  section/retraction data on distinguished legs.
- inspected owner-level declarations:
  `CategoryTheory.SplitEpi`,
  `CategoryTheory.SplitMono`,
  `CategoryTheory.Limits.Cocone`,
  `CategoryTheory.Limits.Cone`.
- best owner abstraction:
  `source-facing`: the essentially constant cocone/cone predicates of this file;
  `core/canonical`: `SplitEpi` and `SplitMono` on the distinguished cocone/cone legs;
  `bridge/view`: passage between filtered cocones and cofiltered cones by `op`/`unop`.

Primitive-vs-derived split:
- primitive data: a chosen leg together with its split structure (`SplitEpi` for cocones, dually
  `SplitMono` for cones), plus the eventual factorization condition on all other legs.
- derived API: the raw textbook section/retraction formulas obtained by unpacking that split
  structure, the functoriality under `mapCocone` and `mapCone`, the universal-property owners
  `isColimit` and `isLimit`, and the cofiltered view transported through `op`. -/

/- Source/core/bridge triage for Definition 4.22.1:
- `source-facing`: the filtered-cocone notion and its textbook section/factorization unpacking.
- `core/canonical`: the use of `SplitEpi` on a cocone leg.
- `bridge/view`: the cofiltered-cone notion, obtained by applying the filtered owner to the
  opposite cone.
-/

/-- Definition 4.22.1 (1): a cocone is essentially constant with value its vertex when one leg
admits a retraction from the cocone point and every other transition map eventually factors
through that retraction and the chosen leg. This is the source-facing predicate later applied to
filtered diagrams. -/
def IsEssentiallyConstantFilteredCocone {M : I ⥤ C} (c : Cocone M) : Prop :=
  ∃ (i : I) (σ : SplitEpi (c.ι.app i)),
    ∀ j : I, ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
      M.map jk = c.ι.app j ≫ σ.section_ ≫ M.map ik

/-- Unpacks Definition 4.22.1 (1) into the textbook section-and-factorization data. -/
theorem isEssentiallyConstantFilteredCocone_iff {M : I ⥤ C} (c : Cocone M) :
    IsEssentiallyConstantFilteredCocone c ↔
      ∃ (i : I) (s : c.pt ⟶ M.obj i),
        s ≫ c.ι.app i = 𝟙 c.pt ∧
          ∀ j : I,
            ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
              M.map jk = c.ι.app j ≫ s ≫ M.map ik := by
  constructor
  · rintro ⟨i, σ, hσ⟩
    exact ⟨i, σ.section_, σ.id, hσ⟩
  · rintro ⟨i, s, hs, hfac⟩
    exact ⟨i, ⟨s, hs⟩, hfac⟩

namespace IsEssentiallyConstantFilteredCocone

/-- Postcomposing an essentially constant filtered cocone with a functor preserves essential
constancy. -/
theorem mapCocone {D : Type uD} [Category.{vD} D] {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) (F : C ⥤ D) :
    IsEssentiallyConstantFilteredCocone (F.mapCocone c) := by
  rcases hc with ⟨i, σ, hσ⟩
  refine ⟨i, σ.map F, ?_⟩
  intro j
  rcases hσ j with ⟨k, ik, jk, h⟩
  refine ⟨k, ik, jk, ?_⟩
  simpa using congrArg (fun f ↦ F.map f) h

private theorem nonempty_isColimit {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) : Nonempty (IsColimit c) := by
  rcases hc with ⟨i, σ, hfac⟩
  refine ⟨IsColimit.mk (fun t ↦ σ.section_ ≫ t.ι.app i) ?_ ?_⟩
  · intro t j
    rcases hfac j with ⟨k, ik, jk, hjk⟩
    have h₁ :
        c.ι.app j ≫ σ.section_ ≫ t.ι.app i =
          c.ι.app j ≫ σ.section_ ≫ M.map ik ≫ t.ι.app k := by
      rw [← t.w ik]
      rfl
    have h₂ :
        c.ι.app j ≫ σ.section_ ≫ M.map ik ≫ t.ι.app k =
          M.map jk ≫ t.ι.app k := by
      simpa [Category.assoc] using congrArg (fun f ↦ f ≫ t.ι.app k) hjk.symm
    exact h₁.trans <| h₂.trans <| t.w jk
  · intro t m hm
    have hm' : (σ.section_ ≫ c.ι.app i) ≫ m = σ.section_ ≫ t.ι.app i := by
      simpa [Category.assoc] using congrArg (fun f ↦ σ.section_ ≫ f) (hm i)
    exact (by simp : m = (σ.section_ ≫ c.ι.app i) ≫ m).trans hm'

/-- An essentially constant filtered cocone is a colimit cocone. -/
noncomputable def isColimit {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) : IsColimit c := by
  classical
  exact Classical.choice (nonempty_isColimit hc)

end IsEssentiallyConstantFilteredCocone

/-- Definition 4.22.1 (2): a cone is essentially constant with value its vertex when one leg
admits a retraction to the cone point and every other transition map eventually factors through
that retraction and the chosen leg. This is the source-facing predicate later applied to
cofiltered diagrams. -/
def IsEssentiallyConstantCofilteredCone {M : I ⥤ C} (c : Cone M) : Prop :=
  IsEssentiallyConstantFilteredCocone c.op

/-- Unpacks Definition 4.22.1 (2) into the dual split-mono/factorization data on a distinguished
cone leg. This is the canonical packaging of the textbook retraction data. -/
theorem isEssentiallyConstantCofilteredCone_iff {M : I ⥤ C} (c : Cone M) :
    IsEssentiallyConstantCofilteredCone c ↔
      ∃ (i : I) (σ : SplitMono (c.π.app i)),
        ∀ j : I, ∃ (k : I) (ki : k ⟶ i) (kj : k ⟶ j),
          M.map kj = M.map ki ≫ σ.retraction ≫ c.π.app j := by
  change IsEssentiallyConstantFilteredCocone c.op ↔ _
  constructor
  · rintro ⟨i, τ, hτ⟩
    refine ⟨i.unop, ?_, ?_⟩
    · exact
        { retraction := τ.section_.unop
          id := by
            apply Quiver.Hom.op_inj
            exact τ.id }
    · intro j
      rcases hτ (op j) with ⟨k, ik, jk, hk⟩
      refine ⟨k.unop, ik.unop, jk.unop, ?_⟩
      change M.map jk.unop = M.map ik.unop ≫ τ.section_.unop ≫ c.π.app j
      simpa using congrArg Quiver.Hom.unop hk
  · rintro ⟨i, σ, hfac⟩
    refine ⟨op i, ?_, ?_⟩
    · exact
        { section_ := σ.retraction.op
          id := by
            apply Quiver.Hom.unop_inj
            exact σ.id }
    · intro j
      rcases hfac j.unop with ⟨k, ki, kj, hk⟩
      refine ⟨op k, ki.op, kj.op, ?_⟩
      change (M.map kj).op = (c.π.app j.unop).op ≫ σ.retraction.op ≫ (M.map ki).op
      simpa using congrArg Quiver.Hom.op hk

namespace IsEssentiallyConstantCofilteredCone

/-- Postcomposing an essentially constant cofiltered cone with a functor preserves essential
constancy. -/
theorem mapCone {D : Type uD} [Category.{vD} D] {M : I ⥤ C} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) (F : C ⥤ D) :
    IsEssentiallyConstantCofilteredCone (F.mapCone c) := by
  change IsEssentiallyConstantFilteredCocone ((F.mapCone c).op)
  simpa using (show IsEssentiallyConstantFilteredCocone c.op from hc).mapCocone F.op

/-- An essentially constant cofiltered cone is a limit cone. -/
noncomputable def isLimit {M : I ⥤ C} {c : Cone M} (hc : IsEssentiallyConstantCofilteredCone c) :
    IsLimit c :=
  (show IsEssentiallyConstantFilteredCocone c.op from hc).isColimit.unop

end IsEssentiallyConstantCofilteredCone

/-! ### Definition_4_22_2 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe uI vI uC vC uD vD

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/- Source/core/bridge triage for Definition 4.22.2:
- `source-facing`: the filtered-diagram notion `IsEssentiallyConstantFilteredDiagram`, which says
  that the diagram admits an essentially constant cocone in the sense of Definition 4.22.1, and
  the dual cofiltered-diagram notion defined by existence of an essentially constant cone.
- `core/canonical`: the earlier cocone/cone owners `IsEssentiallyConstantFilteredCocone` and
  `IsEssentiallyConstantCofilteredCone`; the diagram-level predicates here are their canonical
  existence forms.
- `bridge/view`: passage between the cofiltered notion and the filtered notion on the opposite
  diagram.

Primitive-vs-derived split:
- primitive data: only the ambient diagram and an essentially constant cocone/cone witness.
- derived API: the opposite-category bridge and postcomposition invariance. These owner-level
  functoriality statements do not require filteredness assumptions in their public interface.
-/

/-- Definition 4.22.2 (1): a filtered diagram is essentially constant when it admits an essentially
constant cocone in the sense of Definition 4.22.1. For a directed system, this is the same
condition applied to its associated functor. -/
def IsEssentiallyConstantFilteredDiagram (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, IsEssentiallyConstantFilteredCocone c

/-- Definition 4.22.2 (2): a cofiltered diagram is essentially constant when it admits an essentially
constant cone in the sense of Definition 4.22.1. For a directed inverse system, this is the same
condition applied to its associated functor. -/
def IsEssentiallyConstantCofilteredDiagram (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, IsEssentiallyConstantCofilteredCone c

/-- Unfolds Definition 4.22.2 for cofiltered diagrams. -/
theorem isEssentiallyConstantCofilteredDiagram_iff_exists_essentiallyConstantCone
    (M : I ⥤ C) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      ∃ c : Cone M, IsEssentiallyConstantCofilteredCone c :=
  Iff.rfl

/-- Bridge/view reformulation of the cofiltered notion through the opposite filtered diagram. -/
theorem isEssentiallyConstantCofilteredDiagram_iff_op (M : I ⥤ C) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      IsEssentiallyConstantFilteredDiagram M.op := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.op, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c.unop, hc⟩

/-- Postcomposition with a functor preserves essential constancy of diagrams. -/
theorem essentiallyConstantFilteredDiagram_compFunctor
    {D : Type uD} [Category.{vD} D] {M : I ⥤ C} (F : C ⥤ D)
    (hM : IsEssentiallyConstantFilteredDiagram M) :
    IsEssentiallyConstantFilteredDiagram (M ⋙ F) := by
  rcases hM with ⟨c, hc⟩
  exact ⟨F.mapCocone c, hc.mapCocone F⟩

/-- The cofiltered variant of `essentiallyConstantFilteredDiagram_compFunctor`. -/
theorem essentiallyConstantCofilteredDiagram_compFunctor
    {D : Type uD} [Category.{vD} D] {M : I ⥤ C} (F : C ⥤ D)
    (hM : IsEssentiallyConstantCofilteredDiagram M) :
    IsEssentiallyConstantCofilteredDiagram (M ⋙ F) := by
  rcases hM with ⟨c, hc⟩
  refine ⟨F.mapCone c, ?_⟩
  change IsEssentiallyConstantFilteredCocone ((F.mapCone c).op)
  simpa using (show IsEssentiallyConstantFilteredCocone c.op from hc).mapCocone F.op

/-! ### Lemma_4_22_3 (from Chap04) -/
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory

universe uI vI uC vC

section

/- Domain-style sampling for Lemma 4.22.3:
- primary domain: essentially constant filtered/cofiltered diagrams and the resulting actual
  colimit/limit data.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredCocone.isColimit`,
  `IsEssentiallyConstantCofilteredCone.isLimit`,
  `IsEssentiallyConstantFilteredCocone`,
  `IsEssentiallyConstantFilteredDiagram`,
  `CategoryTheory.Limits.ColimitCocone`,
  `CategoryTheory.Limits.LimitCone`.
- best owner abstraction for the hypothesis: the chapter source-facing owners
  `IsEssentiallyConstantFilteredDiagram M` and `IsEssentiallyConstantCofilteredDiagram M`.
- best owner abstraction for the conclusion: `ColimitCocone M` / `LimitCone M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cocone/cone as in Definition 4.22.1.
- derived owner API: `IsEssentiallyConstantFilteredCocone.isColimit` and
  `IsEssentiallyConstantCofilteredCone.isLimit`.
- derived actual-colimit data: a colimit cocone or limit cone for `M`.
- derived duality bridge: `IsColimit.unop`, transporting the filtered cocone owner theorem to the
  cofiltered cone owner theorem.
- later bridge/view formulations via representability/corepresentability of the associated
  ind/pro-object belong to Lemmas 4.22.9 and 4.22.10, not to the main statements here.

Source/core/bridge triage:
- source-facing: the two theorems below, whose hypotheses are exactly the diagram-level notions
  from Definition 4.22.2.
- core/canonical: `ColimitCocone M` and `LimitCone M`.
- bridge/view: representability of `colimit (M ⋙ uliftYoneda)` and corepresentability of
  `limit (M.op ⋙ uliftCoyoneda)`. -/

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]

/-- Helper for Lemma 4.22.3: package an essentially constant filtered cocone as a genuine
colimit cocone without changing its underlying cocone. -/
noncomputable def filteredCoconeToColimitCocone {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) : ColimitCocone M :=
  ⟨c, hc.isColimit⟩

/-- Helper for Lemma 4.22.3: the colimit-cocone packaging preserves essential constancy of the
underlying cocone. -/
theorem filteredCoconeToColimitCocone_isEssentiallyConstant {M : I ⥤ C} {c : Cocone M}
    (hc : IsEssentiallyConstantFilteredCocone c) :
    IsEssentiallyConstantFilteredCocone (filteredCoconeToColimitCocone hc).cocone := by
  -- Unfold the adapter: only the universal-property field was added.
  simpa [filteredCoconeToColimitCocone] using hc

/-- Helper for Lemma 4.22.3: package an essentially constant cofiltered cone as a genuine limit
cone without changing its underlying cone. -/
noncomputable def cofilteredConeToLimitCone {M : I ⥤ C} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) : LimitCone M :=
  ⟨c, hc.isLimit⟩

/-- Helper for Lemma 4.22.3: the limit-cone packaging preserves essential constancy of the
underlying cone. -/
theorem cofilteredConeToLimitCone_isEssentiallyConstant {M : I ⥤ C} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) :
    IsEssentiallyConstantCofilteredCone (cofilteredConeToLimitCone hc).cone := by
  -- Unfold the adapter: only the universal-property field was added.
  simpa [cofilteredConeToLimitCone] using hc

-- Proof sketch: choose an essentially constant cocone from Definition 4.22.2; its distinguished
-- split leg and eventual factorization data already make it colimiting.
/-- Lemma 4.22.3 (1): a diagram satisfying
`IsEssentiallyConstantFilteredDiagram` admits an essentially constant colimit cocone. -/
theorem essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone
    (M : I ⥤ C) (hM : IsEssentiallyConstantFilteredDiagram M) :
    ∃ c : ColimitCocone M, IsEssentiallyConstantFilteredCocone c.cocone := by
  -- Extract the essentially constant cocone already supplied by the definition.
  rcases hM with ⟨c, hc⟩
  -- The adapter adds only the colimit universal property.
  exact ⟨filteredCoconeToColimitCocone hc, filteredCoconeToColimitCocone_isEssentiallyConstant hc⟩

-- Proof sketch: Definition 4.22.2 already identifies cofiltered essential constancy with the
-- existence of an essentially constant cone by direct unfolding; the canonical duality bridge
-- `IsColimit.unop` then transports the filtered cocone owner theorem to a genuine limit cone.
/-- Lemma 4.22.3 (2): a diagram satisfying
`IsEssentiallyConstantCofilteredDiagram` admits an essentially constant limit cone. -/
theorem essentiallyConstantCofilteredDiagram_exists_essentiallyConstant_limitCone
    (M : I ⥤ C) (hM : IsEssentiallyConstantCofilteredDiagram M) :
    ∃ c : LimitCone M, IsEssentiallyConstantCofilteredCone c.cone := by
  -- Unpack the cone witness from the definition-level iff.
  rcases (isEssentiallyConstantCofilteredDiagram_iff_exists_essentiallyConstantCone M).1 hM with
    ⟨c, hc⟩
  -- The adapter adds only the limit universal property.
  exact ⟨cofilteredConeToLimitCone hc, cofilteredConeToLimitCone_isEssentiallyConstant hc⟩

end

/-! ### Remark_4_22_4 (from Chap04) -/
open CategoryTheory.Limits
open CategoryTheory.Functor
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Remark 4.22.4:
- primary domain: ind-objects and representability of the presheaf colimit attached to a filtered
  diagram.
- inspected owner-level declarations:
  `Ind C`,
  `Ind.lim`,
  `Ind.limCompInclusion`,
  `Functor.RepresentableBy`,
  `RepresentableBy.equivUliftYonedaIso`.
- best owner abstraction: the mathlib ind-object category `Ind C`, with the bridge/view to a
  fixed representing object expressed by `Functor.RepresentableBy`.

Primitive-vs-derived split:
- primitive owner data: the filtered diagram `M : I ⥤ C` and its canonical ind-object
  `(Ind.lim I).obj M`.
- derived API: identification of the constant ind-object `Ind.yoneda.obj X` with `(Ind.lim I).obj
  M`, and the induced representability of the presheaf colimit `colimit (M ⋙ uliftYoneda)`.

Source/core/bridge triage:
- `source-facing`: the remark that the big ind-category is `Ind C`.
- `core/canonical`: `Ind C`, `Ind.yoneda`, and `Ind.lim`.
- `bridge/view`: the remaining equivalence below between an isomorphism in `Ind C` and a
  representing structure on the associated presheaf colimit. -/

/- Remark 4.22.4: the big category of ind-objects of `C` is the canonical mathlib construction
`Ind C`. -/
#check Ind C

/- Companion recall: the canonical functor `C ⥤ Ind C` sending `X` to the constant ind-object on
`X` is `Ind.yoneda`. -/
recall Ind.yoneda

/- Companion recall: the constant-system functor `Ind.yoneda : C ⥤ Ind C` is fully faithful. -/
recall Ind.yoneda.fullyFaithful

variable {C}

/- Companion recall: a filtered system in `C` determines an ind-object through the canonical
functor `Ind.lim`. -/
recall Ind.lim

/- Companion recall: computing `Ind.lim` inside presheaves is governed by the canonical comparison
isomorphism `Ind.limCompInclusion`. -/
recall Ind.limCompInclusion

/- Companion recall: the constant ind-object `Ind.yoneda.obj X` becomes the ulift-Yoneda presheaf
through the canonical comparison isomorphism `Ind.yonedaCompInclusion`. -/
recall Ind.yonedaCompInclusion

/- Companion recall: representing data for a presheaf are canonically equivalent to an
isomorphism from `uliftYoneda.obj X`. -/
recall RepresentableBy.equivUliftYonedaIso

/- Companion recall: the textbook ind-Yoneda Hom formula is the canonical owner-level equivalence
`colimitYonedaHomEquiv`, applied to the presheaf presentation supplied by `Ind.limCompInclusion`.
Evaluating `colimit (N ⋙ yoneda)` at `op (M.obj i)` recovers `colim_j Hom_C(M_i, N_j)`. -/
recall colimitYonedaHomEquiv

section

variable {I : Type v} [SmallCategory I] [IsFiltered I]

/-- Bridge/view companion to Remark 4.22.4: the constant ind-object on `X` is isomorphic to the
ind-object of a filtered system exactly when the associated presheaf colimit is represented by
`X`. -/
noncomputable def indLim_iso_yoneda_equiv_representableBy
    (M : I ⥤ C) (X : C) :
    (Ind.yoneda.obj X ≅ (Ind.lim I).obj M) ≃
      (colimit (M ⋙ uliftYoneda.{v})).RepresentableBy X :=
  let hInclusion : (Ind.inclusion C).FullyFaithful := Ind.inclusion.fullyFaithful
  let hLim : (Ind.inclusion C).obj ((Ind.lim I).obj M) ≅ colimit (M ⋙ uliftYoneda.{v}) :=
    Ind.limCompInclusion.app M ≪≫
      (HasColimit.isoOfNatIso (isoWhiskerLeft M uliftYonedaIsoYoneda)).symm
  let hYoneda : (Ind.inclusion C).obj (Ind.yoneda.obj X) ≅ uliftYoneda.obj X :=
    Ind.yonedaCompInclusion.app X ≪≫ (uliftYonedaIsoYoneda.app X).symm
  calc
    (Ind.yoneda.obj X ≅ (Ind.lim I).obj M)
      ≃ ((Ind.inclusion C).obj (Ind.yoneda.obj X) ≅
          (Ind.inclusion C).obj ((Ind.lim I).obj M)) :=
        hInclusion.isoEquiv
    _ ≃ (uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{v})) :=
        Iso.isoCongr hYoneda hLim
    _ ≃ (colimit (M ⋙ uliftYoneda.{v})).RepresentableBy X :=
        (RepresentableBy.equivUliftYonedaIso _ _).symm

end

end CategoryTheory

/-! ### Remark_4_22_5 (from Chap04) -/
universe uC vC

namespace CategoryTheory

open Functor

variable {C : Type uC} [Category.{vC} C]

/- Domain-style sampling for Remark 4.22.5:
- primary domain: the canonical pro-category model `((Ind Cᵒᵖ)ᵒᵖ)` and its owner-level morphism
  formula for diagrams in `C`.
- inspected owner-level declarations:
  `Ind C`,
  `proObjectHomEquivLimitProSystemHomColimitFunctor`,
  `CorepresentableBy.equivUliftCoyonedaIso`,
  `essentiallyConstant_proObject_characterizations`.
- best owner abstractions for this remark:
  `((Ind Cᵒᵖ)ᵒᵖ)` together with `proObjectHomEquivLimitProSystemHomColimitFunctor`; for the
  constant-value criterion, the chapter owner theorem
  `essentiallyConstant_proObject_characterizations` and its fixed-object bridge
  `CorepresentableBy.equivUliftCoyonedaIso`.

Primitive-vs-derived split:
- primitive data: diagrams `F : I ⥤ C` and `G : J ⥤ C`, and an object `X : C` for the
  constant-system comparison.
- derived API: the constant-system embedding `(opOpEquivalence C).inverse ⋙ Ind.yoneda.op`, the
  owner-level Hom formula `proObjectHomEquivLimitProSystemHomColimitFunctor`, the fixed-object
  comparison with `uliftCoyoneda.obj (op X)`, and the essential-constancy criterion recalled
  directly from `essentiallyConstant_proObject_characterizations`.

Source/core/bridge triage:
- `source-facing`: the pro-category model and the formula
  `Mor_{Pro-C}(F, G) = lim_j colim_i Mor_C(F_i, G_j)`.
- `core/canonical`: `((Ind Cᵒᵖ)ᵒᵖ)`, `proObjectHomEquivLimitProSystemHomColimitFunctor`, and
  `IsEssentiallyConstantCofilteredDiagram`.
- `bridge/view`: the fully faithful constant-system embedding and the companion
  `CorepresentableBy ↔ iso to uliftCoyoneda`; this file should recall those owner statements
  directly rather than repackage them as a new existential theorem. -/

/- Remark 4.22.5: a canonical model for the big category `\text{Pro-}\mathcal{C}` of
pro-objects of `C` is the opposite category `((Ind Cᵒᵖ)ᵒᵖ)`, dual to the ind-object construction
of Remark 4.22.4. -/
#check (Ind Cᵒᵖ)ᵒᵖ

/- Companion check: the canonical constant-system embedding of `C` into this pro-category model
is the composite of `(opOpEquivalence C).inverse : C ⥤ Cᵒᵖᵒᵖ` with
`Ind.yoneda.op : Cᵒᵖᵒᵖ ⥤ (Ind Cᵒᵖ)ᵒᵖ`. -/
#check ((opOpEquivalence C).inverse ⋙ Ind.yoneda.op)

/- Companion check: the canonical constant-system embedding into `((Ind Cᵒᵖ)ᵒᵖ)` is fully
faithful, by composing the fully faithful inverse of `opOpEquivalence C` with
`Ind.yoneda.fullyFaithful.op`. -/
#check (opOpEquivalence C).fullyFaithfulInverse.comp Ind.yoneda.fullyFaithful.op

/- Remark 4.22.5: the owner-level morphism formula in the canonical pro-category model identifies
morphisms from the formal pro-object of `G` to the formal pro-object of `F` with the inverse
limit of the Hom-colimit diagram `j ↦ colim_i Hom(F_i, G_j)`. -/
recall proObjectHomEquivLimitProSystemHomColimitFunctor

/- Companion recall: for a fixed `X`, identifying a pro-Hom colimit functor with the constant
pro-object on `X` is exactly the canonical equivalence
`CorepresentableBy.equivUliftCoyonedaIso`. -/
recall CorepresentableBy.equivUliftCoyonedaIso

/- Companion recall: the constant-system criterion for a cofiltered diagram is already owned by
`essentiallyConstant_proObject_characterizations`; together with
`CorepresentableBy.equivUliftCoyonedaIso`, this is the canonical realization-level form of
"being isomorphic to a constant pro-object". -/
recall essentiallyConstant_proObject_characterizations

end CategoryTheory

/-! ### Example_4_22_6 (from Chap04) -/
open CategoryTheory Limits Opposite
open scoped CategoryTheory

universe u v

namespace CategoryTheory

/- Domain-style sampling for Example 4.22.6:
- primary domain: sequential inverse systems as source-facing models for morphisms in the
  pro-category of `C`.
- inspected owner-level declarations:
  `OrderHom.toFunctor`,
  `proObjectHomEquivLimitProSystemHomColimitFunctor`,
  `Types.sectionsEquiv`,
  `Types.limitEquivSections`,
  `Limits.colimitObjIsoColimitCompEvaluation`.
- best owner abstraction:
  `limit (Y ⋙ proSystemHomColimitFunctor X)`.

Primitive-vs-derived split:
  `reindex.toFunctor.op ⋙ X ⟶ Y`.
- derived API: the level maps `X_{reindex(n)} ⟶ Y_n` and their compatibility squares.

Source/core/bridge triage:
- `source-facing`: `SequentialProObjectMorphismRep X Y`, consisting canonically of a reindexing
  order hom and the induced natural transformation of sequential inverse systems.
- `core/canonical`: the pro-object morphism type
  `(colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0})`
  between the associated sequential pro-objects, together with its plain-limit owner
  `limit (Y ⋙ proSystemHomColimitFunctor X)`.
- `bridge/view`: the inverse-limit point `SequentialProObjectMorphismRep.toLimitHom`, built from
  the stagewise Hom-colimit classes via the canonical `Types.Limit.mk` constructor. -/

/-- A representative of a morphism between sequential inverse systems consists of a monotone
reindexing `m : ℕ → ℕ` together with compatible level maps `X_{m(n)} ⟶ Y_n`. -/
structure SequentialProObjectMorphismRep {C : Type u} [Category.{v} C] (X Y : ℕᵒᵖ ⥤ C) where
  reindex : ℕ →o ℕ
  hom : reindex.toFunctor.op ⋙ X ⟶ Y

namespace SequentialProObjectMorphismRep

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

/-- The level map associated to a sequential representative at stage `n`. -/
abbrev map (r : SequentialProObjectMorphismRep X Y) (n : ℕ) :
    X.obj (op (r.reindex n)) ⟶ Y.obj (op n) :=
  r.hom.app (op n)

/-- The naturality square for the level maps of a sequential representative. -/
theorem comm (r : SequentialProObjectMorphismRep X Y) {n n' : ℕ} (h : n ≤ n') :
    CommSq (X.map (homOfLE (r.reindex.monotone h)).op) (r.map n') (r.map n)
      (Y.map (homOfLE h).op) := by
  refine CommSq.mk ?_
  simpa using r.hom.naturality (homOfLE h).op

/-- Build a sequential representative from its source-facing coordinate data. -/
private def ofMaps (reindex : ℕ →o ℕ)
    (map : ∀ n : ℕ, X.obj (op (reindex n)) ⟶ Y.obj (op n))
    (comm : ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      X.map (homOfLE (reindex.monotone h)).op ≫ map n =
        map n' ≫ Y.map (homOfLE h).op) :
    SequentialProObjectMorphismRep X Y where
  reindex := reindex
  hom :=
    { app := fun n ↦ map n.unop
      naturality := fun n n' g ↦ by
        let h : n'.unop ≤ n.unop := leOfHom g.unop
        simpa [h] using comm h }

/-- The class in `colim_i Hom(X_i, Y_n)` represented by the `n`-th level map of a sequential
representative. -/
private noncomputable abbrev classOf (r : SequentialProObjectMorphismRep X Y) (n : ℕ) :
    (proSystemHomColimitFunctor X).obj (Y.obj (op n)) :=
  (colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))).inv <|
    colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
      (ULift.up (r.map n))

private theorem classOf_naturality (r : SequentialProObjectMorphismRep X Y) {n n' : ℕ}
    (h : n ≤ n') :
    (proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n') = r.classOf n := by
  let τ :=
    ((Functor.whiskeringLeft ℕᵒᵖᵒᵖ Cᵒᵖ _).obj X.op).map
      (uliftYoneda.map (Y.map (homOfLE h).op))
  let eₙ := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  let eₙ' := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n'))
  have hmap :
      colim.map τ
          (colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n'))) (op (op (r.reindex n')))
            (ULift.up (r.map n'))) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n')))
          (τ.app (op (op (r.reindex n'))) (ULift.up (r.map n'))) :=
    Types.Colimit.ι_map_apply τ (op (op (r.reindex n'))) (ULift.up (r.map n'))
  have hcolim :
      colim.map τ (eₙ'.hom (r.classOf n')) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
          (ULift.up (r.map n)) := by
    calc
      colim.map τ (eₙ'.hom (r.classOf n')) =
          colim.map τ
            (colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n'))) (op (op (r.reindex n')))
              (ULift.up (r.map n'))) := by
                simp [classOf, eₙ']
      _ = colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n')))
            (τ.app (op (op (r.reindex n'))) (ULift.up (r.map n'))) := hmap
      _ = colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
            (ULift.up (r.map n)) := by
              symm
              refine Types.colimit_sound (((homOfLE (r.reindex.monotone h)).op).op) ?_
              simp [τ, (r.comm h).w]
  have hleft :
      eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n')) =
        colim.map τ (eₙ'.hom (r.classOf n')) := by
    change
      eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n')) =
        colimMap ((X.op ⋙ uliftCoyoneda).whiskerLeft ((evaluation _ _).map (Y.map (homOfLE h).op)))
          (eₙ'.hom (r.classOf n'))
    simpa [eₙ, eₙ', proSystemHomColimitFunctor] using
      congrFun
        (colimit_map_colimitObjIsoColimitCompEvaluation_hom
          (X.op ⋙ uliftCoyoneda) (Y.map (homOfLE h).op)) (r.classOf n')
  have hright :
      colim.map τ (eₙ'.hom (r.classOf n')) = eₙ.hom (r.classOf n) := by
    exact hcolim.trans <| by simp [classOf, eₙ]
  exact eₙ.toEquiv.injective (hleft.trans hright)

/-- The inverse-limit presentation of the pro-object morphism represented by `r`. -/
private noncomputable def toLimitHom (r : SequentialProObjectMorphismRep X Y) :
    limit (Y ⋙ proSystemHomColimitFunctor X) :=
  Types.Limit.mk _ (fun n ↦ r.classOf n.unop) fun i j g ↦ by
    let h : j.unop ≤ i.unop := leOfHom g.unop
    simpa [h] using r.classOf_naturality h

/-- A sequential representative determines a morphism between the associated sequential
pro-objects. -/
noncomputable def toProObjectHom (r : SequentialProObjectMorphismRep X Y) :
    colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0} :=
  (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm r.toLimitHom

/-- Refining the source stages of a sequential representative along a larger monotone reindexing
does not change the underlying level maps in the Hom-colimits. -/
private theorem refine_comm
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) {n n' : ℕ} (h : n ≤ n') :
    X.map (homOfLE (reindex'.monotone h)).op ≫ (X.map (homOfLE (hle n)).op ≫ r.map n) =
      (X.map (homOfLE (hle n')).op ≫ r.map n') ≫ Y.map (homOfLE h).op := by
  -- Reassociate the source transition so that the original compatibility square applies.
  have hsource :
      ((homOfLE (reindex'.monotone h)).op ≫ (homOfLE (hle n)).op) =
        ((homOfLE (hle n')).op ≫ (homOfLE (r.reindex.monotone h)).op) := by
    apply Subsingleton.elim
  calc
    X.map (homOfLE (reindex'.monotone h)).op ≫ (X.map (homOfLE (hle n)).op ≫ r.map n) =
        X.map (((homOfLE (reindex'.monotone h)).op ≫ (homOfLE (hle n)).op)) ≫ r.map n := by
          rw [← Category.assoc, ← X.map_comp]
    _ = X.map (((homOfLE (hle n')).op ≫ (homOfLE (r.reindex.monotone h)).op)) ≫ r.map n := by
          rw [hsource]
    _ =
        (X.map (homOfLE (hle n')).op ≫
          X.map (homOfLE (r.reindex.monotone h)).op) ≫ r.map n := by
          rw [X.map_comp]
    _ = X.map (homOfLE (hle n')).op ≫
        (X.map (homOfLE (r.reindex.monotone h)).op ≫ r.map n) := by
          simp [Category.assoc]
    _ = X.map (homOfLE (hle n')).op ≫ (r.map n' ≫ Y.map (homOfLE h).op) := by
          simp [(r.comm h).w]
    _ = (X.map (homOfLE (hle n')).op ≫ r.map n') ≫ Y.map (homOfLE h).op := by
          simp [Category.assoc]

/-- Enlarging the chosen source stage at each target level gives a canonical refinement of a
sequential representative. -/
private def refine
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    SequentialProObjectMorphismRep X Y :=
  ofMaps reindex'
    (fun n ↦ X.map (homOfLE (hle n)).op ≫ r.map n)
    (fun _ _ h ↦ refine_comm r reindex' hle h)

/-- The class represented at level `n` is unchanged by passing to a larger source stage. -/
private theorem classOf_refine
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) (n : ℕ) :
    (r.refine reindex' hle).classOf n = r.classOf n := by
  let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  -- Passing to a larger source stage does not change the represented colimit class.
  suffices hcolim : e.hom ((r.refine reindex' hle).classOf n) = e.hom (r.classOf n) by
    exact e.toEquiv.injective hcolim
  have hleft :
      e.hom ((r.refine reindex' hle).classOf n) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (reindex' n)))
          (ULift.up (X.map (homOfLE (hle n)).op ≫ r.map n)) := by
    simp [classOf, refine, ofMaps, map, e]
  have hmid :
      colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (reindex' n)))
          (ULift.up (X.map (homOfLE (hle n)).op ≫ r.map n)) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
          (ULift.up (r.map n)) := by
    symm
    refine Types.colimit_sound (((homOfLE (hle n)).op).op) ?_
    simp
  have hright :
      colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
          (ULift.up (r.map n)) =
        e.hom (r.classOf n) := by
    simp [classOf, e]
  exact hleft.trans (hmid.trans hright)

/-- Refinement does not change the represented inverse-limit point. -/
private theorem refine_toLimitHom
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (r.refine reindex' hle).toLimitHom = r.toLimitHom := by
  apply Types.limit_ext
  intro n
  simp [toLimitHom, r.classOf_refine reindex' hle n.unop]

/-- Refinement does not change the represented morphism between the associated pro-objects. -/
private theorem refine_toProObjectHom
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (r.refine reindex' hle).toProObjectHom = r.toProObjectHom := by
  simpa [toProObjectHom] using
    congrArg
      (fun η ↦ (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm η)
      (r.refine_toLimitHom reindex' hle)

/-- Two sequential representatives are equivalent when, after passing to a common monotone
refinement, their level maps agree. -/
def Equivalent (r₁ r₂ : SequentialProObjectMorphismRep X Y) : Prop :=
  ∃ reindex' : ℕ →o ℕ,
    ∃ h₁ : ∀ n : ℕ, r₁.reindex n ≤ reindex' n,
      ∃ h₂ : ∀ n : ℕ, r₂.reindex n ≤ reindex' n,
        ∀ n : ℕ,
          X.map (homOfLE (h₁ n)).op ≫ r₁.map n =
            X.map (homOfLE (h₂ n)).op ≫ r₂.map n

/-- Helper for Example 4.22.6: a concrete map `X_i ⟶ Y_n` represents the `n`-th component of a
limit point when it maps to that component in the Hom-colimit. -/
private abbrev Represents
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X))
    (n i : ℕ) (f : X.obj (op i) ⟶ Y.obj (op n)) : Prop :=
  colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op i)) (ULift.up f) =
    (colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))).hom
      (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ)

/-- Helper for Example 4.22.6: a chosen representative of the `n`-th component of a limit
point. -/
private structure LevelRepresentative
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X)) (n : ℕ) where
  source : ℕ
  hom : X.obj (op source) ⟶ Y.obj (op n)
  represents : Represents ξ n source hom

/-- Helper for Example 4.22.6: a one-step enlargement of a chosen level representative, recording
both the new representative and the adjacent compatibility square. -/
private structure SuccessorRefinement
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X))
    (n : ℕ) (p : LevelRepresentative (X := X) (Y := Y) ξ n) where
  source : ℕ
  le_source : p.source ≤ source
  hom : X.obj (op source) ⟶ Y.obj (op (n + 1))
  represents : Represents ξ (n + 1) source hom
  comm : X.map (homOfLE le_source).op ≫ p.hom =
    hom ≫ Y.map (homOfLE (Nat.le_succ n)).op

/-- Helper for Example 4.22.6: forget the extra compatibility data from a successor refinement
and retain only the new level representative. -/
private def SuccessorRefinement.toLevelRepresentative
    {ξ : limit (Y ⋙ proSystemHomColimitFunctor X)}
    {n : ℕ} {p : LevelRepresentative (X := X) (Y := Y) ξ n}
    (s : SuccessorRefinement (X := X) (Y := Y) ξ n p) :
    LevelRepresentative (X := X) (Y := Y) ξ (n + 1) where
  source := s.source
  hom := s.hom
  represents := s.represents

/-- Helper for Example 4.22.6: each component of a limit point is represented by some source
stage. -/
theorem exists_level_representation
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X)) (n : ℕ) :
    ∃ i : ℕ, ∃ f : X.obj (op i) ⟶ Y.obj (op n), Represents ξ n i f := by
  let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  -- Choose one concrete representative of the `n`-th Hom-colimit class.
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective'
    (e.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ))
  refine ⟨j.unop.unop, y.down, ?_⟩
  simpa [Represents, e] using hy

/-- Helper for Example 4.22.6: a chosen representative at level `n` can be enlarged so that it
comes from a representative of level `n + 1` with the adjacent square commuting. -/
theorem exists_successor_refinement
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X))
    (n i : ℕ)
    (f : X.obj (op i) ⟶ Y.obj (op n))
    (hf : Represents ξ n i f) :
    ∃ k : ℕ, ∃ hik : i ≤ k, ∃ g : X.obj (op k) ⟶ Y.obj (op (n + 1)),
      Represents ξ (n + 1) k g ∧
      X.map (homOfLE hik).op ≫ f = g ≫ Y.map (homOfLE (Nat.le_succ n)).op := by
  obtain ⟨j, g₀, hg₀⟩ := exists_level_representation (X := X) (Y := Y) ξ (n + 1)
  let Fₙ := X.op ⋙ uliftYoneda.obj (Y.obj (op n))
  let Fₙ₁ := X.op ⋙ uliftYoneda.obj (Y.obj (op (n + 1)))
  let eₙ := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  let eₙ₁ := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op (n + 1)))
  let τ :=
    ((Functor.whiskeringLeft ℕᵒᵖᵒᵖ Cᵒᵖ _).obj X.op).map
      (uliftYoneda.map (Y.map (homOfLE (Nat.le_succ n)).op))
  have hlimit :
      (proSystemHomColimitFunctor X).map (Y.map (homOfLE (Nat.le_succ n)).op)
          (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ) =
        limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ := by
    simpa using
      congrFun
        (limit.w (Y ⋙ proSystemHomColimitFunctor X) (homOfLE (Nat.le_succ n)).op) ξ
  have htransport :
      colim.map τ (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) =
        eₙ.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ) := by
    have hleft :
        eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE (Nat.le_succ n)).op)
            (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) =
          colim.map τ (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) := by
      change
        eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE (Nat.le_succ n)).op)
            (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) =
          colimMap ((X.op ⋙ uliftCoyoneda).whiskerLeft
            ((evaluation _ _).map (Y.map (homOfLE (Nat.le_succ n)).op)))
            (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ))
      simpa [eₙ, eₙ₁, proSystemHomColimitFunctor] using
        congrFun
          (colimit_map_colimitObjIsoColimitCompEvaluation_hom
            (X.op ⋙ uliftCoyoneda) (Y.map (homOfLE (Nat.le_succ n)).op))
          (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)
    calc
      colim.map τ (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) =
          eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE (Nat.le_succ n)).op)
            (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) := by
              symm
              exact hleft
      _ = eₙ.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ) := by
            rw [hlimit]
  have hcolim :
      colimit.ι Fₙ (op (op j)) (ULift.up (g₀ ≫ Y.map (homOfLE (Nat.le_succ n)).op)) =
        colimit.ι Fₙ (op (op i)) (ULift.up f) := by
    have hmap_g₀ :
        colim.map τ (colimit.ι Fₙ₁ (op (op j)) (ULift.up g₀)) =
          colim.map τ (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) := by
      rw [hg₀]
    have hmiddle :
        colim.map τ (colimit.ι Fₙ₁ (op (op j)) (ULift.up g₀)) =
          eₙ.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ) :=
      hmap_g₀.trans htransport
    -- Compare the two representatives after transporting the `(n + 1)`-component down to level
    -- `n` using the limit compatibility.
    refine (Eq.trans ?_ hmiddle).trans ?_
    · symm
      simpa [Fₙ, Fₙ₁, τ]
        using Types.Colimit.ι_map_apply τ (op (op j)) (ULift.up g₀)
    · rw [← hf]
  obtain ⟨k, a, b, hab⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff Fₙ).mp hcolim
  let k' : ℕ := k.unop.unop
  have hjk : j ≤ k' := leOfHom a.unop.unop
  have hik : i ≤ k' := leOfHom b.unop.unop
  let g : X.obj (op k') ⟶ Y.obj (op (n + 1)) := X.map (homOfLE hjk).op ≫ g₀
  refine ⟨k', hik, g, ?_, ?_⟩
  · -- Enlarge the representative of level `n + 1` to the common larger stage.
    calc
      colimit.ι Fₙ₁ (op (op k')) (ULift.up g) =
          colimit.ι Fₙ₁ (op (op j)) (ULift.up g₀) := by
            symm
            refine Types.colimit_sound (((homOfLE hjk).op).op) ?_
            simp [Fₙ₁, g]
      _ =
          (colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0})
            (Y.obj (op (n + 1)))).hom
            (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ) := hg₀
  · -- The filtered-colimit witness is exactly the desired adjacent compatibility square.
    simpa [Fₙ, g, k', hik, hjk, Category.assoc] using hab.symm

/-- Helper for Example 4.22.6: adjacent compatibility squares imply compatibility for every
transition map `n' ⟶ n`. -/
theorem comm_of_succ_comm
    (reindex : ℕ →o ℕ)
    (a : ∀ n : ℕ, X.obj (op (reindex n)) ⟶ Y.obj (op n))
    (hsucc : ∀ n : ℕ,
      X.map (homOfLE (reindex.monotone (Nat.le_succ n))).op ≫ a n =
        a (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op) :
    ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      X.map (homOfLE (reindex.monotone h)).op ≫ a n =
        a n' ≫ Y.map (homOfLE h).op := by
  intro n n' h
  induction h with
  | refl =>
      simp
  | @step n' h ih =>
      have hsource :
          (homOfLE (reindex.monotone (Nat.le_succ_of_le h))).op =
            (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
              (homOfLE (reindex.monotone h)).op := by
        apply Subsingleton.elim
      have htarget :
          (homOfLE (Nat.le_succ_of_le h)).op =
            (homOfLE (Nat.le_succ n')).op ≫ (homOfLE h).op := by
        apply Subsingleton.elim
      -- Compose the inductive compatibility with the next adjacent square.
      calc
        X.map (homOfLE (reindex.monotone (Nat.le_succ_of_le h))).op ≫ a n =
            X.map ((homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
                (homOfLE (reindex.monotone h)).op) ≫ a n := by
                  rw [hsource]
        _ = (X.map (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
              X.map (homOfLE (reindex.monotone h)).op) ≫ a n := by
                rw [X.map_comp]
        _ = X.map (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
              (X.map (homOfLE (reindex.monotone h)).op ≫ a n) := by
                simp [Category.assoc]
        _ = X.map (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
              (a n' ≫ Y.map (homOfLE h).op) := by
                rw [ih]
        _ = (X.map (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫ a n') ≫
              Y.map (homOfLE h).op := by
                simp [Category.assoc]
        _ = (a (n' + 1) ≫ Y.map (homOfLE (Nat.le_succ n')).op) ≫
              Y.map (homOfLE h).op := by
                rw [hsucc n']
        _ = a (n' + 1) ≫
              (Y.map (homOfLE (Nat.le_succ n')).op ≫ Y.map (homOfLE h).op) := by
                simp [Category.assoc]
        _ = a (n' + 1) ≫
              Y.map ((homOfLE (Nat.le_succ n')).op ≫ (homOfLE h).op) := by
                rw [← Y.map_comp]
        _ = a (n' + 1) ≫ Y.map (homOfLE (Nat.le_succ_of_le h)).op := by
                rw [htarget]

/-- Helper for Example 4.22.6: every limit point of
`Y ⋙ proSystemHomColimitFunctor X` comes from a sequential representative. -/
theorem exists_rep_of_limit_point
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X)) :
    ∃ r : SequentialProObjectMorphismRep X Y, r.toLimitHom = ξ := by
  classical
  let baseLevel : LevelRepresentative (X := X) (Y := Y) ξ 0 :=
    let h0 := exists_level_representation (X := X) (Y := Y) ξ 0
    { source := Classical.choose h0
      hom := Classical.choose (Classical.choose_spec h0)
      represents := Classical.choose_spec (Classical.choose_spec h0) }
  let successorChoice :
      ∀ n : ℕ,
        (p : LevelRepresentative (X := X) (Y := Y) ξ n) →
          SuccessorRefinement (X := X) (Y := Y) ξ n p := fun n p ↦
    let hs := exists_successor_refinement (X := X) (Y := Y) ξ n p.source p.hom p.represents
    { source := Classical.choose hs
      le_source := Classical.choose (Classical.choose_spec hs)
      hom := Classical.choose (Classical.choose_spec (Classical.choose_spec hs))
      represents := (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec hs))).1
      comm := (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec hs))).2 }
  let choice : ∀ n : ℕ, LevelRepresentative (X := X) (Y := Y) ξ n :=
    Nat.rec (motive := fun n ↦ LevelRepresentative (X := X) (Y := Y) ξ n)
      baseLevel
      (fun n p ↦ (successorChoice n p).toLevelRepresentative)
  have choice_succ :
      ∀ n : ℕ,
        choice (n + 1) = (successorChoice n (choice n)).toLevelRepresentative := by
    intro n
    rfl
  let stage : ℕ → ℕ := fun n ↦ (choice n).source
  let maps : ∀ n : ℕ, X.obj (op (stage n)) ⟶ Y.obj (op n) := fun n ↦ (choice n).hom
  have hrep : ∀ n : ℕ, Represents ξ n (stage n) (maps n) := fun n ↦ (choice n).represents
  have hsucc_le : ∀ n : ℕ, stage n ≤ stage (n + 1) := by
    intro n
    simpa [stage, choice_succ n] using (successorChoice n (choice n)).le_source
  have hsucc_comm :
      ∀ n : ℕ,
        X.map (homOfLE (hsucc_le n)).op ≫ maps n =
          maps (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op := by
    intro n
    simpa [stage, maps, choice_succ n] using (successorChoice n (choice n)).comm
  let reindex : ℕ →o ℕ :=
    { toFun := stage
      monotone' := monotone_nat_of_le_succ hsucc_le }
  let r : SequentialProObjectMorphismRep X Y :=
    ofMaps reindex maps (fun _ _ h ↦ comm_of_succ_comm (X := X) (Y := Y) reindex maps hsucc_comm h)
  have hclass :
      ∀ n : ℕ, r.classOf n = limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ := by
    intro n
    let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
    -- Both classes have the same image in the raw Hom-colimit, so they are equal.
    apply e.toEquiv.injective
    simpa [SequentialProObjectMorphismRep.classOf, SequentialProObjectMorphismRep.map,
      SequentialProObjectMorphismRep.ofMaps, r, reindex, stage, maps, e] using hrep n
  refine ⟨r, ?_⟩
  apply Types.limit_ext
  intro n
  -- Compare the constructed representative with `ξ` componentwise in the limit.
  simpa [SequentialProObjectMorphismRep.toLimitHom] using hclass n.unop

/-- Helper for Example 4.22.6: equality of two level Hom-colimit classes can be witnessed after
passing to one common source stage. -/
private theorem exists_common_stage_of_classOf_eq
    (r₁ r₂ : SequentialProObjectMorphismRep X Y) {n : ℕ}
    (hclass : r₁.classOf n = r₂.classOf n) :
    ∃ k : ℕ, ∃ h₁ : r₁.reindex n ≤ k, ∃ h₂ : r₂.reindex n ≤ k,
      X.map (homOfLE h₁).op ≫ r₁.map n = X.map (homOfLE h₂).op ≫ r₂.map n := by
  let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  have hcolim :
      colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r₁.reindex n)))
          (ULift.up (r₁.map n)) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r₂.reindex n)))
          (ULift.up (r₂.map n)) := by
    simpa [classOf, e] using congrArg e.hom hclass
  -- Equality in the filtered colimit is detected at a common larger index.
  obtain ⟨k, f, g, hfg⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff
      (X.op ⋙ uliftYoneda.obj (Y.obj (op n)))).mp hcolim
  let k' : ℕ := k.unop.unop
  have hk₁ : r₁.reindex n ≤ k' := leOfHom f.unop.unop
  have hk₂ : r₂.reindex n ≤ k' := leOfHom g.unop.unop
  refine ⟨k', hk₁, hk₂, ?_⟩
  simpa [k', hk₁, hk₂] using hfg

/-- Helper for Example 4.22.6: an equality of level maps remains true after enlarging the common
source stage once more. -/
private theorem transport_level_eq
    {n i j k l : ℕ}
    {f : X.obj (op i) ⟶ Y.obj (op n)}
    {g : X.obj (op j) ⟶ Y.obj (op n)}
    {hᵢ : i ≤ k}
    {hⱼ : j ≤ k}
    (heq : X.map (homOfLE hᵢ).op ≫ f = X.map (homOfLE hⱼ).op ≫ g)
    (hkl : k ≤ l) :
    X.map (homOfLE (le_trans hᵢ hkl)).op ≫ f =
      X.map (homOfLE (le_trans hⱼ hkl)).op ≫ g := by
  have hcomp₁ :
      (homOfLE (le_trans hᵢ hkl)).op = (homOfLE hkl).op ≫ (homOfLE hᵢ).op := by
    apply Subsingleton.elim
  have hcomp₂ :
      (homOfLE (le_trans hⱼ hkl)).op = (homOfLE hkl).op ≫ (homOfLE hⱼ).op := by
    apply Subsingleton.elim
  -- Precompose the known equality with the transition map from the larger stage.
  calc
    X.map (homOfLE (le_trans hᵢ hkl)).op ≫ f =
        X.map ((homOfLE hkl).op ≫ (homOfLE hᵢ).op) ≫ f := by
          rw [hcomp₁]
    _ = X.map (homOfLE hkl).op ≫ (X.map (homOfLE hᵢ).op ≫ f) := by
          rw [X.map_comp, Category.assoc]
    _ = X.map (homOfLE hkl).op ≫ (X.map (homOfLE hⱼ).op ≫ g) := by
          rw [heq]
    _ = X.map ((homOfLE hkl).op ≫ (homOfLE hⱼ).op) ≫ g := by
          rw [X.map_comp, Category.assoc]
    _ = X.map (homOfLE (le_trans hⱼ hkl)).op ≫ g := by
          rw [hcomp₂]

/-- Helper for Example 4.22.6: levelwise equality of Hom-colimit classes implies the textbook
common-refinement equivalence of representatives. -/
theorem equivalent_of_level_class_eq
    (r₁ r₂ : SequentialProObjectMorphismRep X Y)
    (hclass : ∀ n : ℕ, r₁.classOf n = r₂.classOf n) :
    r₁.Equivalent r₂ := by
  classical
  let stage : ℕ → ℕ := fun n ↦
    (exists_common_stage_of_classOf_eq r₁ r₂ (hclass n)).choose
  let stage_h₁ : ∀ n : ℕ, r₁.reindex n ≤ stage n := fun n ↦
    (exists_common_stage_of_classOf_eq r₁ r₂ (hclass n)).choose_spec.1
  let stage_h₂ : ∀ n : ℕ, r₂.reindex n ≤ stage n := fun n ↦
    (exists_common_stage_of_classOf_eq r₁ r₂ (hclass n)).choose_spec.2.1
  let stage_eq :
      ∀ n : ℕ,
        X.map (homOfLE (stage_h₁ n)).op ≫ r₁.map n =
          X.map (homOfLE (stage_h₂ n)).op ≫ r₂.map n := fun n ↦
      (exists_common_stage_of_classOf_eq r₁ r₂ (hclass n)).choose_spec.2.2
  let reindexFn : ℕ → ℕ :=
    Nat.rec (stage 0) (fun n m ↦ max m (stage (n + 1)))
  let reindex' : ℕ →o ℕ :=
    { toFun := reindexFn
      monotone' := monotone_nat_of_le_succ fun n ↦ by
        simp [reindexFn] }
  have hstage_le : ∀ n : ℕ, stage n ≤ reindex' n := by
    intro n
    induction n with
    | zero =>
        simp [reindex', reindexFn]
    | succ n ih =>
        simp [reindex', reindexFn]
  have h₁ : ∀ n : ℕ, r₁.reindex n ≤ reindex' n := fun n ↦
    le_trans (stage_h₁ n) (hstage_le n)
  have h₂ : ∀ n : ℕ, r₂.reindex n ≤ reindex' n := fun n ↦
    le_trans (stage_h₂ n) (hstage_le n)
  refine ⟨reindex', h₁, h₂, ?_⟩
  intro n
  -- Transport the stagewise equality to the recursively enlarged common stage.
  simpa [h₁, h₂] using
    transport_level_eq (f := r₁.map n) (g := r₂.map n) (heq := stage_eq n) (hkl := hstage_le n)

/-- The identity representative of a sequential inverse system. -/
def idRep (X : ℕᵒᵖ ⥤ C) : SequentialProObjectMorphismRep X X :=
  ofMaps OrderHom.id
    (fun n ↦ 𝟙 (X.obj (op n)))
    (fun _ _ h ↦ by simp)

/-- Compatibility of the composite representative with transition morphisms. -/
theorem compRep_comm
    {Z : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      X.map (homOfLE ((r.reindex.comp s.reindex).monotone h)).op ≫
          (r.map (s.reindex n) ≫ s.map n) =
        (r.map (s.reindex n') ≫ s.map n') ≫ Z.map (homOfLE h).op := by
  intro n n' h
  calc
    X.map (homOfLE ((r.reindex.comp s.reindex).monotone h)).op ≫
        (r.map (s.reindex n) ≫ s.map n) =
      (X.map (homOfLE (r.reindex.monotone (s.reindex.monotone h))).op ≫
          r.map (s.reindex n)) ≫ s.map n := by simp [Category.assoc]
    _ = (r.map (s.reindex n') ≫ Y.map (homOfLE (s.reindex.monotone h)).op) ≫ s.map n := by
      simp [Category.assoc, (r.comm (s.reindex.monotone h)).w]
    _ = r.map (s.reindex n') ≫
        (Y.map (homOfLE (s.reindex.monotone h)).op ≫ s.map n) := by
      simp [Category.assoc]
    _ = r.map (s.reindex n') ≫ (s.map n' ≫ Z.map (homOfLE h).op) := by
      simp [(s.comm h).w]
    _ = (r.map (s.reindex n') ≫ s.map n') ≫ Z.map (homOfLE h).op := by
      simp [Category.assoc]

/-- Composition of sequential representatives of pro-object morphisms. -/
def compRep
    {Z : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    SequentialProObjectMorphismRep X Z :=
  ofMaps (r.reindex.comp s.reindex)
    (fun n ↦ r.map (s.reindex n) ≫ s.map n)
    (compRep_comm r s)

/-- A representative is a pro-isomorphism if it admits an inverse up to common-refinement
equivalence. -/
def IsProIsomorphism (r : SequentialProObjectMorphismRep X Y) : Prop :=
  ∃ s : SequentialProObjectMorphismRep Y X,
    Equivalent (compRep r s) (idRep X) ∧ Equivalent (compRep s r) (idRep Y)

end SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

-- Proof sketch: choose, for each `n`, a stage of `X` and a map to `Y_n` representing the `n`-th
-- Hom-colimit class of `η`; then enlarge inductively so the chosen stages are monotone and the
-- compatibility squares commute.
/-- Example 4.22.6: every morphism between the associated sequential pro-objects is represented by
a monotone reindexing and compatible level maps. -/
theorem exists_representative
    (η : colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0}) :
    ∃ r : SequentialProObjectMorphismRep X Y, r.toProObjectHom = η := by
  let ξ := proObjectHomEquivLimitProSystemHomColimitFunctor X Y η
  -- Route correction: first solve the source-stage extraction problem for the canonical limit
  -- point, then transport the resulting representative back across the equivalence.
  obtain ⟨r, hr⟩ := SequentialProObjectMorphismRep.exists_rep_of_limit_point
    (X := X) (Y := Y) ξ
  refine ⟨r, ?_⟩
  -- Apply the inverse equivalence to the identified limit point.
  simpa [ξ, SequentialProObjectMorphismRep.toProObjectHom] using
    congrArg
      (fun ζ ↦ (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm ζ) hr

-- Proof sketch: one direction follows by refining both representatives to a common larger
-- monotone sequence and comparing the resulting stage maps; the converse uses that equality after
-- such a common refinement gives the same classes in every Hom-colimit.
/-- Companion to Example 4.22.6: two sequential representatives define the same pro-object
morphism exactly when, after passing to a common monotone refinement, their level maps become
equal. -/
theorem represents_eq_iff_equivalent
    (r₁ r₂ : SequentialProObjectMorphismRep X Y) :
    r₁.toProObjectHom = r₂.toProObjectHom ↔ r₁.Equivalent r₂ := by
  constructor
  · intro h
    -- Apply the comparison equivalence to identify the represented limit points.
    have hlimit : r₁.toLimitHom = r₂.toLimitHom := by
      simpa [SequentialProObjectMorphismRep.toProObjectHom] using
        congrArg (proObjectHomEquivLimitProSystemHomColimitFunctor X Y) h
    have hclass : ∀ n : ℕ, r₁.classOf n = r₂.classOf n := by
      intro n
      -- Equality in the limit is checked componentwise.
      simpa [SequentialProObjectMorphismRep.toLimitHom] using
        congrArg (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n)) hlimit
    exact SequentialProObjectMorphismRep.equivalent_of_level_class_eq r₁ r₂ hclass
  · rintro ⟨reindex', h₁, h₂, heq⟩
    have hclass_refined :
        ∀ n : ℕ,
          (r₁.refine reindex' h₁).classOf n = (r₂.refine reindex' h₂).classOf n := by
      intro n
      let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
      apply e.toEquiv.injective
      -- After refining to the same stages, the level maps agree by hypothesis.
      simp [SequentialProObjectMorphismRep.classOf, SequentialProObjectMorphismRep.refine,
        SequentialProObjectMorphismRep.ofMaps, SequentialProObjectMorphismRep.map, e, heq n]
    have hlimit_refined :
        (r₁.refine reindex' h₁).toLimitHom = (r₂.refine reindex' h₂).toLimitHom := by
      apply Types.limit_ext
      intro n
      simpa [SequentialProObjectMorphismRep.toLimitHom] using hclass_refined n.unop
    -- Route correction: compare both representatives only after moving them to the same reindexing.
    calc
      r₁.toProObjectHom = (r₁.refine reindex' h₁).toProObjectHom := by
        symm
        exact r₁.refine_toProObjectHom reindex' h₁
      _ = (r₂.refine reindex' h₂).toProObjectHom := by
        simpa [SequentialProObjectMorphismRep.toProObjectHom] using
          congrArg
            (fun ξ ↦ (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm ξ)
            hlimit_refined
      _ = r₂.toProObjectHom := by
        exact r₂.refine_toProObjectHom reindex' h₂

end

end CategoryTheory

/-! ### Remark_4_22_7 (from Chap04) -/
open CategoryTheory Limits Opposite Equiv
open scoped CategoryTheory

universe uI vI uJ vJ uC vC

namespace CategoryTheory

/- Domain-style sampling for Remark 4.22.7:
- primary domain: pro-objects via the pro-coyoneda lemma in `CategoryTheory.Limits`.
- inspected owner-level declarations:
  `Limits.colimitCoyonedaHomIsoLimit'`,
  `Limits.colimitObjIsoColimitCompEvaluation`,
  `Types.limitEquivSections`,
  `uliftCoyonedaEquiv`.
- best owner abstraction: `Limits.colimitCoyonedaHomIsoLimit'`.
  The public theorem below is a bridge from that owner to the universe-lifted source-facing
  pro-object formula used in this chapter, with the limit target returned in its plain form.

Primitive-vs-derived split:
- primitive data: the diagram `F : I ⥤ C`.
- core owner: the colimit object `colimit (F.op ⋙ uliftCoyoneda.{uI})`.
- derived API: the Hom-colimit functor notation `proSystemHomColimitFunctor F`;
  pointwise evaluation uses the upstream owner
  `Limits.colimitObjIsoColimitCompEvaluation`, and the final limit target is unlifted again via
  `Limits.preservesLimitIso` for `Types.uliftFunctor`.

Source/core/bridge triage:
- `source-facing`: `proSystemHomColimitFunctor F`, the textbook `X ↦ colim_i Hom(F_i, X)`.
- `core/canonical`: `Limits.colimitCoyonedaHomIsoLimit'`.
- `bridge/view`: the ulift-coyoneda-to-sections comparison needed to express the same
  pro-coyoneda bridge at the universe level used in this chapter, followed by the canonical
  removal of the final `ULift` on the limit object. -/

/-- The Hom-colimit functor attached to a diagram `F`, sending `X` to
`colim_i Hom(F(i), X)`, with the Hom-sets ulifted only as much as needed for the indexing
category of `F`. -/
noncomputable abbrev proSystemHomColimitFunctor
    {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    (F : I ⥤ C) : C ⥤ Type (max uI vC) :=
  colimit (F.op ⋙ uliftCoyoneda.{uI})

section

variable {I : Type uI} {J : Type uJ} {C : Type uC}
variable [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
variable {F : I ⥤ C} {G : J ⥤ C}

private noncomputable def uliftCoyonedaNatTransEquivSections
    (G : J ⥤ C) (H : C ⥤ Type (max uI uJ vC)) :
    ((G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ (Functor.const Jᵒᵖ).obj H) ≃ (G ⋙ H).sections where
  toFun τ :=
    ⟨
      fun j ↦ uliftCoyonedaEquiv.{max uI uJ} (τ.app (op j)),
      fun {j j'} g ↦ by
        simpa using
          (uliftCoyonedaEquiv_naturality.{max uI uJ} (τ.app (op j)) (G.map g)).trans
            (congrArg (uliftCoyonedaEquiv.{max uI uJ}) (τ.naturality g.op))
    ⟩
  invFun s :=
    { app := fun j ↦ uliftCoyonedaEquiv.{max uI uJ}.symm (s.1 j.unop)
      naturality := fun j j' g ↦ by
        simp only [Functor.const_obj_map]
        let hs := congrArg
          (uliftCoyonedaEquiv.{max uI uJ}.symm)
          (s.2 g.unop)
        simpa using
          (uliftCoyonedaEquiv_symm_map.{max uI uJ} (G.map g.unop) (s.1 j'.unop)).symm.trans hs }
  left_inv τ := by
    ext j X x
    rcases x with ⟨x⟩
    simpa using (FunctorToTypes.naturality _ _ (τ.app j) x (ULift.up (𝟙 _))).symm
  right_inv s := by
    ext j
    exact apply_symm_apply (uliftCoyonedaEquiv.{max uI uJ}) (s.1 j)

private noncomputable def colimitUliftCoyonedaHomEquivLimit
    (G : J ⥤ C) (H : C ⥤ Type (max uI uJ vC)) :
    (colimit (G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ H) ≃ limit (G ⋙ H) := by
  let i :
      (colimit (G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ H) ≃
        ((G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ (Functor.const Jᵒᵖ).obj H) :=
    (Equiv.ulift : ULift (colimit (G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶ H) ≃ _).symm.trans
      (IsColimit.homIso (colimit.isColimit (G.op ⋙ uliftCoyoneda.{max uI uJ})) H).toEquiv
  exact ((i.trans (uliftCoyonedaNatTransEquivSections G H)).trans
    (Types.limitEquivSections _).symm)

/-- Remark 4.22.7: for any diagrams `F : \mathcal I \to \mathcal C` and
`G : \mathcal J \to \mathcal C`, the limit of the diagram
`G ⋙ proSystemHomColimitFunctor F` identifies with morphisms from the formal pro-object of `G`
`colim_j Hom(G(j), -)` to the Hom-colimit functor of `F`.
This is the canonical pro-object bridge underlying the textbook formula
`\varprojlim_j \varinjlim_i \operatorname{Hom}(F_i, G_j)`. The explicit `HasLimit` hypothesis is
exactly the small-universe assumption needed to return the final inverse limit without an extra
`ULift`. -/
noncomputable def proObjectHomEquivLimitProSystemHomColimitFunctor
    (F : I ⥤ C) (G : J ⥤ C) [HasLimit (G ⋙ proSystemHomColimitFunctor F)] :
    (colimit (G.op ⋙ uliftCoyoneda.{max uI uJ}) ⟶
      proSystemHomColimitFunctor F ⋙ uliftFunctor.{uJ}) ≃
    limit (G ⋙ proSystemHomColimitFunctor F) := by
  let e :
      limit (G ⋙ proSystemHomColimitFunctor F ⋙ uliftFunctor.{uJ, max uI vC}) ≃
        limit (G ⋙ proSystemHomColimitFunctor F) :=
    (preservesLimitIso
      (uliftFunctor.{uJ, max uI vC})
      (G ⋙ proSystemHomColimitFunctor F)).symm.toEquiv.trans
      (Equiv.ulift :
        ULift (limit (G ⋙ proSystemHomColimitFunctor F)) ≃
          limit (G ⋙ proSystemHomColimitFunctor F))
  exact
    (colimitUliftCoyonedaHomEquivLimit G
      (proSystemHomColimitFunctor F ⋙ uliftFunctor.{uJ, max uI vC})).trans e

/-- The comparison map of `proObjectHomEquivLimitProSystemHomColimitFunctor` is bijective. -/
-- Proof sketch: this is immediate because the comparison is packaged as an equivalence.
theorem proObjectHomEquivLimitProSystemHomColimitFunctor_bijective
    (F : I ⥤ C) (G : J ⥤ C) [HasLimit (G ⋙ proSystemHomColimitFunctor F)] :
    Function.Bijective (proObjectHomEquivLimitProSystemHomColimitFunctor F G) := by
  -- The theorem is purely formal: every equivalence has a bijective underlying function.
  simpa using (proObjectHomEquivLimitProSystemHomColimitFunctor F G).bijective

end

end CategoryTheory

/-! ### Lemma_4_22_8 (from Chap04) -/
/- Domain-style sampling for Lemma 4.22.8:
- primary domain: essentially constant filtered/cofiltered diagrams and their behavior under
  postcomposition by a functor.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredDiagram`,
  `IsEssentiallyConstantCofilteredDiagram`,
  `essentiallyConstantFilteredDiagram_compFunctor`,
  `essentiallyConstantCofilteredDiagram_compFunctor`.
- best owner abstraction for the main statements: the chapter owners
  `IsEssentiallyConstantFilteredDiagram M` and `IsEssentiallyConstantCofilteredDiagram M`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cocone/cone from Definitions 4.22.1 and 4.22.2.
- derived API: the postcomposition invariance theorems now owned directly by
  `Definition_4_22_2`, so this numbered file should recall them rather than re-prove a parallel
  copy.

Source/core/bridge triage:
- `source-facing`: postcomposition preserves essential constancy for filtered and cofiltered
  diagrams.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram M` and
  `IsEssentiallyConstantCofilteredDiagram M`.
- `bridge/view`: owner-level functoriality in `Definition_4_22_2`, itself derived from the
  cocone-level theorem `IsEssentiallyConstantFilteredCocone.mapCocone` and the opposite-category
  definition of `IsEssentiallyConstantCofilteredDiagram`. -/

/- Lemma 4.22.8: postcomposition with a functor preserves essential constancy of filtered
diagrams. The canonical owner theorem lives in `Definition_4_22_2`. -/
recall essentiallyConstantFilteredDiagram_compFunctor

/- Lemma 4.22.8, dual form: postcomposition with a functor preserves essential constancy of
cofiltered diagrams. The canonical owner theorem lives in `Definition_4_22_2`. -/
recall essentiallyConstantCofilteredDiagram_compFunctor

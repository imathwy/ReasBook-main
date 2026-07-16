import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_proof.stacks_project.Chap07.Lemma_7_26_4.Index
import stacks_proof.stacks_project.Chap07.Lemma_7_26_6
import stacks_proof.stacks_project.Chap08.Lemma_8_3_7
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Definition_8_11_1
import stacks_proof.stacks_project.Chap08.Lemma_8_11_8.Part04

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: on one refinement member `I`, the first-branch self-leg
common-owner shell at `op (Over.mk Ī.toMiddleHom)` can be rewritten to the shared-owner
`qI := I.Y.hom` shell evaluated at `op (Over.mk (𝟙 I.Y.left))`, while keeping the same owner leg
`Ī.toMiddleHom`. This isolates the remaining owner-change step before endpoint-independence is
used. -/
private theorem chosen_cover_refinement_member_first_branch_self_leg_to_qI_shell
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj T)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem;
    let qI : I.Y.left ⟶ K.Y := I.Y.hom;
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle.base;
    let hg₁₂ : Ī.toMiddleHom ≫ K₁₂.f = qI :=
      (by
        have hms : Ī.toMiddleHom ≫ Ī.fromMiddleHom = I.f.left := Ī.middle_spec
        have step : (Ī.toMiddleHom ≫ Ī.fromMiddleHom) ≫ T.unop.hom = I.Y.hom := by
          rw [hms]; exact Over.w I.f
        simpa [K₁₂, qI, GrothendieckTopology.Cover.Arrow.base,
          GrothendieckTopology.Cover.Arrow.fromMiddle, Category.assoc] using step);
    -- After the refactor the self-leg owner `K₁₂.f` and the shared owner `qI` no longer index
    -- definitionally equal sheaves, so the self-leg transport is folded into the migrated
    -- qI-shell endpoint comparison: only the chosen owner leg (`Ī.toMiddleHom` vs the identity on
    -- `I.Y.left`) may vary over the shared owner `qI`, and endpoint-independence removes it.
    let selfArrow :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      K₁₂.precomp Ī.toMiddleHom;
    ∀ (s : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (qI ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁)))).1.obj
        (op (Over.mk (𝟙 I.Y.left)))),
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) qI (K := K₁₂) Ī.toMiddleHom hg₁₂).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂) qI (K := selfArrow) (𝟙 I.Y.left)
            (by simpa [selfArrow] using hg₁₂)).hom).hom).1.app
        (op (Over.mk (𝟙 I.Y.left)))) s := by
  -- The first branch already lives over the shared owner `qI`; only the chosen owner leg can
  -- still vary, and endpoint-independence removes that variation.
  intro Ī qI K₁₂ hg₁₂ selfArrow s
  exact chosen_cover_refinement_member_first_branch_qI_leg_eq_identity_leg
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T (R := R) I hImem s

/-- Helper for Lemma 8.11.8: transporting a section through an object equality commutes with
applying a natural transformation, evaluated at the two equal objects. -/
private theorem eqToHom_app_transport
    {D : Type (max u v)} [Category.{v} D] {ℱ 𝒢 : D ⥤ Type (max u v)}
    (M : ℱ ⟶ 𝒢) {X Y : D} (h : X = Y) (a : ℱ.obj X) :
    Eq.mp (congrArg 𝒢.obj h) (M.app X a) = M.app Y (Eq.mp (congrArg ℱ.obj h) a) := by
  cases h
  rfl

/-- Helper for Lemma 8.11.8: the hom and inverse components of the same `mapComp'` cancel even
when their composite-equality witnesses were produced by different tactics. -/
@[reassoc]
private theorem mapComp'_hom_inv_id_toNatTrans_app_of_witness
    {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) {k : b₀ ⟶ b₂}
    (w w' : f ≫ g = k) (X : F.obj b₀) :
    (F.mapComp' f g k w).hom.toNatTrans.app X ≫
      (F.mapComp' f g k w').inv.toNatTrans.app X = 𝟙 _ := by
  have hw : w = w' := Subsingleton.elim _ _
  cases hw
  exact Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' f g k w) X

/-- Helper for Lemma 8.11.8: the inverse/hom analogue of
`mapComp'_hom_inv_id_toNatTrans_app_of_witness`. -/
@[reassoc]
private theorem mapComp'_inv_hom_id_toNatTrans_app_of_witness
    {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) {k : b₀ ⟶ b₂}
    (w w' : f ≫ g = k) (X : F.obj b₀) :
    (F.mapComp' f g k w).inv.toNatTrans.app X ≫
      (F.mapComp' f g k w').hom.toNatTrans.app X = 𝟙 _ := by
  have hw : w = w' := Subsingleton.elim _ _
  cases hw
  exact Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' f g k w) X

/-- Helper for Lemma 8.11.8: solve a morphism equality by inserting inverse/hom identity
shells on both sides of a known `hom ≫ middle ≫ inv` equality. -/
private theorem middle_eq_inv_comp_of_hom_comp_inv_eq
    {D : Type*} [Category D] {A B C E : D}
    {l : A ⟶ B} {li : B ⟶ A} {m : B ⟶ C} {r : C ⟶ E} {ri : E ⟶ C}
    {n : A ⟶ E} (h : l ≫ m ≫ r = n)
    (hl : li ≫ l = 𝟙 B) (hr : r ≫ ri = 𝟙 C) :
    m = li ≫ n ≫ ri := by
  -- Insert the two identity shells and then replace the normalized middle by `n`.
  calc
    m = 𝟙 B ≫ m ≫ 𝟙 C := by simp
    _ = (li ≫ l) ≫ m ≫ (r ≫ ri) := by rw [hl, hr]
    _ = li ≫ (l ≫ m ≫ r) ≫ ri := by simp only [Category.assoc]
    _ = li ≫ n ≫ ri := by rw [h]

/-- Helper for Lemma 8.11.8: cancel an adjacent hom/inverse shell in the middle of a composite. -/
private theorem comp_hom_inv_comp_eq
    {D : Type*} [Category D] {A B C E : D}
    {p : A ⟶ B} {l : B ⟶ C} {r : C ⟶ B} {q : B ⟶ E}
    (h : l ≫ r = 𝟙 B) :
    p ≫ l ≫ r ≫ q = p ≫ q := by
  -- Reassociate once so the cancellable pair is adjacent.
  calc
    p ≫ l ≫ r ≫ q = p ≫ (l ≫ r) ≫ q := by simp only [Category.assoc]
    _ = p ≫ 𝟙 B ≫ q := by rw [h]
    _ = p ≫ q := by simp

/-- Helper for Lemma 8.11.8: reassociate a six-fold composite without asking `simp` to inspect
large concrete endpoints. -/
private theorem comp_six_middle_assoc
    {D : Type*} [Category D] {A B C E G H I : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ G) (e : G ⟶ H)
    (f : H ⟶ I) :
    a ≫ (b ≫ c ≫ d ≫ e) ≫ f = (a ≫ b ≫ c) ≫ (d ≫ e ≫ f) := by
  simp only [Category.assoc]

/-- Helper for the `hsecond` branch of `chosen_cover_member_pulled_cocycle`: the pulled
`(f₂,f₃)` overlap followed by the target `mapComp'` bridge and the local target base-change
normalizes to the common-owner conjugation shell.  The owner leg is abstracted as `g`; in the main
proof it is the identity on the refinement member. -/
private theorem chosen_cover_member_pulled_cocycle_hsecond
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    {Z : C} (qZ : Z ⟶ K.Y)
    (K₂₃ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (K.f ≫ f₂) (K.f ≫ f₃)).Arrow)
    (g : Z ⟶ K₂₃.Y) (hg : g ≫ K₂₃.f = qZ) :
    let F := J.pseudofunctorOver (Type (max u v));
    let A₃ := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃);
    let L₃ :=
      ((F.mapComp' f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A₃);
    let P₂₃ :=
      automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
        (K.f ≫ f₃)
        (by simpa [Category.assoc, _hf₂])
        (by simpa [Category.assoc, _hf₃]);
    let cIso :=
      ((F.map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₃
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃);
    let cIso_q :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qZ
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃));
    let B₂ :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qZ
        (local_overlap_source_object (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂));
    let B₂g :=
      ((F.map qZ.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₂)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))) ≪≫ B₂;
    let C₂₃ :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂) (K.f ≫ f₃) qZ (K := K₂₃) g hg).hom).hom;
    let e₃q :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor qZ).mapIso
        ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₃
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃));
    let E₃ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₃q.hom).hom;
    ((F.map qZ.op.toLoc).toFunctor.map (P₂₃ ≫ L₃ ≫ cIso.hom)) ≫ cIso_q.hom =
      B₂g.hom ≫ C₂₃ ≫ E₃ := by
  intro F A₃ L₃ P₂₃ cIso cIso_q B₂ B₂g C₂₃ e₃q E₃
  let B₃ :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qZ
      (local_overlap_target_object (𝒮 := 𝒮)
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₃))
  let B₃g :=
    ((F.map qZ.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₃)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))) ≪≫ B₃
  have hmiddle :
      ((F.map qZ.op.toLoc).toFunctor.map P₂₃) =
        B₂g.hom ≫ C₂₃ ≫ B₃g.inv := by
    let selfArrow :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      K₂₃.precomp g
    have hself_f : selfArrow.f = qZ := by
      simpa [selfArrow] using hg
    let B₂self :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian selfArrow.f
        (local_overlap_source_object (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂))
    let B₃self :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian selfArrow.f
        (local_overlap_target_object (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₃))
    let B₂gself :=
      ((F.map selfArrow.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₂)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))) ≪≫ B₂self
    let B₃gself :=
      ((F.map selfArrow.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₃)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))) ≪≫ B₃self
    let Cself :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂) (K.f ≫ f₃) selfArrow.f (K := K₂₃) g
          (by simpa [selfArrow] using hg)).hom).hom
    have hself :
        ((F.map selfArrow.f.op.toLoc).toFunctor.map P₂₃) =
          B₂gself.hom ≫ Cself ≫ B₃gself.inv := by
      have hcomponent :=
        automorphism_overlap_hom_secondary_cover_component
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
          (by simpa [Category.assoc, _hf₂])
          (by simpa [Category.assoc, _hf₃])
          selfArrow
      have hexplicit :=
        secondary_cover_descent_iso_on_local_overlap_hom_component_explicit
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂) (K.f ≫ f₃) selfArrow
      have hconj :
          (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (K.f ≫ f₂) (K.f ≫ f₃) selfArrow).hom =
            Cself := by
        dsimp [Cself]
        exact congrArg Iso.hom
          (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _)
      rw [hcomponent, hexplicit]
      dsimp [F, B₂gself, B₃gself, B₂self, B₃self, local_overlap_source_object,
        local_overlap_target_object]
      rw [hconj]
      rfl
    -- Route correction: do not substitute the owner blindly.  First identify the two
    -- common-owner conjugation shells after the owner equality has aligned their endpoints, then
    -- the remaining source/target boundary isomorphisms are definitionally the same.
    cases hself_f
    have hCself : Cself = C₂₃ := by
      dsimp [Cself, C₂₃]
      exact congrArg Iso.hom
        (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _)
    rw [← hCself]
    simpa [B₂g, B₃g, B₂gself, B₃gself, B₂self, B₃self] using hself
  have htarget :
      ((F.map qZ.op.toLoc).toFunctor.map (L₃ ≫ cIso.hom)) ≫ cIso_q.hom =
        B₃g.hom ≫ E₃ := by
    let B₃K :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₃)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)
    let eK :=
      (canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso f₃ K.f
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)
    let Ciso := automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eK.symm.hom
    have hmerge :=
      automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom
        (𝒮 := 𝒮) hAbelian f₃ K.f (K.f ≫ f₃)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) eK
        (by
          simpa [eK] using
            fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
              (hc := canonicalPullbackChoice 𝒮.p) f₃ K.f
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))
    have hmerge' :
        cIso.hom ≫ Ciso.hom =
          ((F.mapComp' f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₃) ≫
            B₃K.hom := by
      simpa [cIso, L₃, B₃K, Ciso, eK, local_overlap_target_object,
        Category.assoc] using hmerge
    have hcancel :
        L₃ ≫
          ((F.mapComp' f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₃) =
          𝟙 _ := by
      dsimp [L₃, F]
      exact Cat.Hom.hom_inv_id_toNatTrans_app
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])) A₃
    have hK :
        L₃ ≫ cIso.hom = B₃K.hom ≫ Ciso.inv := by
      calc
        L₃ ≫ cIso.hom =
            L₃ ≫ cIso.hom ≫ Ciso.hom ≫ Ciso.inv := by
              simpa only [Category.assoc, Category.comp_id] using
                congrArg (fun m => L₃ ≫ cIso.hom ≫ m) Ciso.hom_inv_id.symm
        _ =
            L₃ ≫
              (((F.mapComp' f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
                (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₃) ≫
                B₃K.hom) ≫ Ciso.inv := by
              simpa only [Category.assoc] using
                congrArg (fun m => L₃ ≫ m ≫ Ciso.inv) hmerge'
        _ =
            (L₃ ≫
              ((F.mapComp' f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
                (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₃)) ≫
                B₃K.hom ≫ Ciso.inv := by
              simp only [Category.assoc]
        _ = B₃K.hom ≫ Ciso.inv := by
              simpa only [Category.assoc, Category.id_comp] using
                congrArg (fun m => m ≫ B₃K.hom ≫ Ciso.inv) hcancel
    have hCinv :
        Ciso.inv =
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eK.hom).hom := by
      dsimp [Ciso]
      exact (automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮)
        hAbelian _ _).symm
    have hpull := automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮)
      hAbelian qZ eK.hom
    have hE₃ :
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qZ).mapIso
            (asIso eK.hom)).hom).hom =
          E₃ := by
      exact automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮)
        hAbelian _ _
    have htarget_shell :
        ((F.map qZ.op.toLoc).toFunctor.map Ciso.inv) ≫ cIso_q.hom =
          B₃.hom ≫ E₃ := by
      rw [hCinv, hpull]
      rw [hE₃]
      dsimp [B₃, cIso_q, eK]
      calc
        ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qZ
            ((K.f ≫ f₃) ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).hom ≫
            E₃ ≫
            (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qZ
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (f₃ ^*[canonicalPullbackChoice 𝒮.p]
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)))).inv) ≫
            cIso_q.hom =
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qZ
            ((K.f ≫ f₃) ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).hom ≫
            E₃ ≫
            ((automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qZ
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (f₃ ^*[canonicalPullbackChoice 𝒮.p]
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)))).inv ≫
              cIso_q.hom) := by
            simp only [Category.assoc]
        _ =
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qZ
            ((K.f ≫ f₃) ^*[canonicalPullbackChoice 𝒮.p]
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))).hom ≫
            E₃ ≫ 𝟙 _ := by
            rw [cIso_q.inv_hom_id]
        _ = B₃.hom ≫ E₃ := by
            simp only [B₃, local_overlap_target_object, Category.assoc, Category.comp_id]
    have hmap :
        (F.map qZ.op.toLoc).toFunctor.map (L₃ ≫ cIso.hom) =
          (F.map qZ.op.toLoc).toFunctor.map (B₃K.hom ≫ Ciso.inv) := by
      exact congrArg (fun m => (F.map qZ.op.toLoc).toFunctor.map m) hK
    rw [Functor.map_comp, Functor.map_comp] at hmap
    calc
      ((F.map qZ.op.toLoc).toFunctor.map (L₃ ≫ cIso.hom)) ≫ cIso_q.hom =
          ((F.map qZ.op.toLoc).toFunctor.map L₃ ≫
            (F.map qZ.op.toLoc).toFunctor.map cIso.hom) ≫ cIso_q.hom := by
            rw [Functor.map_comp]
      _ =
          ((F.map qZ.op.toLoc).toFunctor.map B₃K.hom ≫
            (F.map qZ.op.toLoc).toFunctor.map Ciso.inv) ≫ cIso_q.hom := by
            simpa only [Category.assoc] using
              congrArg (fun m => m ≫ cIso_q.hom) hmap
      _ =
          (F.map qZ.op.toLoc).toFunctor.map B₃K.hom ≫ (B₃.hom ≫ E₃) := by
            simpa only [Category.assoc] using
              congrArg (fun m => (F.map qZ.op.toLoc).toFunctor.map B₃K.hom ≫ m)
                htarget_shell
      _ = B₃g.hom ≫ E₃ := by
            simpa [B₃g, B₃K, B₃, Iso.trans_hom, Category.assoc]
  calc
    ((F.map qZ.op.toLoc).toFunctor.map (P₂₃ ≫ L₃ ≫ cIso.hom)) ≫ cIso_q.hom =
        ((F.map qZ.op.toLoc).toFunctor.map P₂₃) ≫
          (((F.map qZ.op.toLoc).toFunctor.map (L₃ ≫ cIso.hom)) ≫ cIso_q.hom) := by
          simp only [Functor.map_comp, Category.assoc]
    _ = (B₂g.hom ≫ C₂₃ ≫ B₃g.inv) ≫ (B₃g.hom ≫ E₃) := by
          rw [hmiddle, htarget]
    _ = B₂g.hom ≫ C₂₃ ≫ E₃ := by
          simpa only [Category.assoc] using
            (comp_hom_inv_comp_eq (p := B₂g.hom ≫ C₂₃)
              (l := B₃g.inv) (r := B₃g.hom) (q := E₃) B₃g.inv_hom_id)

/-- Helper for Lemma 8.11.8: after restricting the direct `(f₁,f₃)` branch along one refinement
member `I`, the remaining term is already the pulled direct conjugation over the shared owner
`qI := I.Y.hom`, evaluated on the identity object of `C / I.Y.left`. This isolates the direct
branch from the pairwise-shell comparison in the final memberwise cocycle calculation. -/
private theorem chosen_cover_refinement_member_direct_branch_restrict_eq_pulled_direct_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj T)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow) :
    let qI : I.Y.left ⟶ K.Y := I.Y.hom;
    let αI :=
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α;
    -- Base-change bridge: the pulled direct conjugation reads the section through
    -- `automorphismUnderlyingSheafBaseChangeIso` along the shared owner `qI`.
    let bIso :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁));
    let cIso :=
      automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃));
    let hObjCast : (op I.Y : (Over K.Y)ᵒᵖ) = op (Over.mk ((𝟙 I.Y.left) ≫ qI)) := by
      rw [Category.id_comp]; rfl;
    (cIso.hom.1.app (op (Over.mk (𝟙 I.Y.left))))
        (Eq.mp (congrArg
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.obj hObjCast)
          ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.map I.f.op
              ((((local_overlap_conjugation_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α))) =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism
              (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom)).hom).1.app
        (op (Over.mk (𝟙 I.Y.left))))
        ((bIso.hom.1.app (op (Over.mk (𝟙 I.Y.left))))
          (Eq.mp (congrArg
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (K.f ^*[canonicalPullbackChoice 𝒮.p]
                  (local_overlap_source_object (𝒮 := 𝒮)
                    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
            αI)) := by
  -- Naturality of the direct conjugation plus the shared-owner base-change identification.
  intro qI αI bIso cIso hObjCast
  set Mh := (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom with hMh
  -- Move the outer restriction inside the conjugation by naturality.
  have hA :
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.map I.f.op
            (Mh.1.app T α) =
        Mh.1.app (op I.Y) αI :=
    sheaf_hom_app_restrict_eq Mh I.f α
  have htrans := eqToHom_app_transport Mh.1 hObjCast αI
  -- The pulled conjugation identity, evaluated at the shared owner object on the bridged section.
  have hPB := automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian qI
    (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom
  have hPBapp := congrFun
    (congrArg (fun φ' => φ'.1.app (op (Over.mk (𝟙 I.Y.left)))) hPB)
    (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast) αI)
  have hPBapp2 :
      Mh.1.app (op (Over.mk (𝟙 I.Y.left ≫ qI)))
          (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast) αI) =
        cIso.inv.1.app (op (Over.mk (𝟙 I.Y.left)))
          ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              ((((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
                (local_overlap_isomorphism
                  (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom)).hom).1.app
            (op (Over.mk (𝟙 I.Y.left))))
            ((bIso.hom.1.app (op (Over.mk (𝟙 I.Y.left))))
              (Eq.mp (congrArg
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                    (K.f ^*[canonicalPullbackChoice 𝒮.p]
                      (local_overlap_source_object (𝒮 := 𝒮)
                        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
                αI))) := by
    simpa only [pseudofunctor_over_map_app_eq_image_app] using hPBapp
  rw [hA]
  exact (congrArg (cIso.hom.1.app (op (Over.mk (𝟙 I.Y.left)))) htrans).trans
    ((congrArg (cIso.hom.1.app (op (Over.mk (𝟙 I.Y.left)))) hPBapp2).trans
      (congrFun
        (congrArg (fun φ' => φ'.1.app (op (Over.mk (𝟙 I.Y.left)))) cIso.inv_hom_id) _))

/-- SUB-LEMMA 2 (`hf23_generic`) for the residual `hcoc0`: the cover-generic `(f₂,f₃)` analogue of
the existing `chosen_cover_overlap_map_eq_pulled_overlap` (which is stated only for `(f₁,f₂)`).
Pulling the `(f₂,f₃)` overlap along `K.f`, conjugated by the `mapComp'_{f₂}`/`mapComp'_{f₃}`
bridges, equals the `(K.f ≫ ·)`-level `(f₂,f₃)` overlap.  Re-derived cover-generically from the
chosen-cover pullback law `automorphism_cover_overlap_pull` for the overlap maps (the `K`-cover has
type `(f₁,f₃)`, so the `(f₂,f₃)` factor must be obtained generically rather than from `K`'s own
overlap datum). -/
private theorem chosen_cover_f23_pulled_overlap
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    {Z : C} (k : Z ⟶ Y) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₂.op.toLoc k.op.toLoc (k ≫ f₂).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))) ≫
      (((J.pseudofunctorOver (Type (max u v))).map k.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃
          (_hf₁ := _hf₂) (_hf₂ := _hf₃))) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₃.op.toLoc k.op.toLoc (k ≫ f₃).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))) =
      automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (k ≫ q) (k ≫ f₂) (k ≫ f₃)
        (by simpa [Category.assoc, _hf₂]) (by simpa [Category.assoc, _hf₃]) := by
  -- The displayed left-hand side is by definition `pullHom (overlap q f₂ f₃) k …`, so the
  -- chosen-cover pullback law for overlap maps identifies it with the `(k ≫ ·)`-level overlap.
  exact automorphism_cover_overlap_pull
    (𝒮 := 𝒮) hGerbe hAbelian k q (k ≫ q) rfl f₂ f₃ _hf₂ _hf₃ (k ≫ f₂) (k ≫ f₃) rfl rfl

/-- SUB-LEMMA 1 (`hMfac`) for the residual `hcoc0` of
`chosen_cover_pairwise_descent_comp_eq_on_refinement_member`.

The composite `Mcomp` of the two `(K.f)`-pulled pairwise overlap maps
`(pf.map K.f).map (overlap q f₁ f₂) ≫ (pf.map K.f).map (overlap q f₂ f₃)` factors, after inserting
the `mapComp'` coherence bridges and cancelling the middle `mapComp'_{f₂}` pair, as the
`(K.f ≫ ·)`-level composite of overlaps wrapped by the outer `mapComp'_{f₁}`/`mapComp'_{f₃}`
bridges.  This is the morphism-level "split + cancel" identity: it follows from the existing
`chosen_cover_overlap_map_eq_pulled_overlap` applied to each factor (the first directly, the second
via its `(f₂,f₃)` analogue `hf23_generic`) followed by `Iso.hom_inv_id`-cancellation of the shared
`mapComp'_{f₂}` bridge. -/
private theorem chosen_cover_Mcomp_pulled_factorization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow) :
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (by simpa [Category.assoc, _hf₁]) (by simpa [Category.assoc, _hf₂])) ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
        (by simpa [Category.assoc, _hf₂]) (by simpa [Category.assoc, _hf₃])) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))) := by
  let F := J.pseudofunctorOver (Type (max u v))
  let A₁ :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))
  let A₂ :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))
  let A₃ :=
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))
  let L₁ :=
    (F.mapComp' f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A₁
  let L₁i :=
    (F.mapComp' f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₁
  let L₂ :=
    (F.mapComp' f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A₂
  let L₂i :=
    (F.mapComp' f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₂
  let L₂' :=
    (F.mapComp' f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A₂
  let L₂i' :=
    (F.mapComp' f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₂
  let L₃ :=
    (F.mapComp' f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A₃
  let L₃i :=
    (F.mapComp' f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₃
  let M₁₂ :=
    ((F.map K.f.op.toLoc).toFunctor.map
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂))
  let M₂₃ :=
    ((F.map K.f.op.toLoc).toFunctor.map
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))
  let P₁₂ :=
    automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
      (by simpa [Category.assoc, _hf₁]) (by simpa [Category.assoc, _hf₂])
  let P₂₃ :=
    automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
      (by simpa [Category.assoc, _hf₂]) (by simpa [Category.assoc, _hf₃])
  change M₁₂ ≫ M₂₃ = L₁i ≫ P₁₂ ≫ P₂₃ ≫ L₃
  have h₁₂raw :
      L₁ ≫ M₁₂ ≫ L₂i = P₁₂ := by
    simpa [F, A₁, A₂, L₁, L₂i, M₁₂, P₁₂] using
      (chosen_cover_overlap_map_eq_pulled_overlap
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ K)
  have h₂₃raw :
      L₂' ≫ M₂₃ ≫ L₃i = P₂₃ := by
    simpa [F, A₂, A₃, L₂', L₃i, M₂₃, P₂₃] using
      (chosen_cover_f23_pulled_overlap
        (𝒮 := 𝒮) hGerbe hAbelian q f₂ f₃ _hf₂ _hf₃ (k := K.f))
  have h₁₂ : M₁₂ = L₁i ≫ P₁₂ ≫ L₂ := by
    refine middle_eq_inv_comp_of_hom_comp_inv_eq h₁₂raw ?_ ?_
    · dsimp [L₁i, L₁, F]
      exact Cat.Hom.inv_hom_id_toNatTrans_app
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])) A₁
    · dsimp [L₂i, L₂, F]
      exact Cat.Hom.inv_hom_id_toNatTrans_app
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])) A₂
  have h₂₃ : M₂₃ = L₂i' ≫ P₂₃ ≫ L₃ := by
    refine middle_eq_inv_comp_of_hom_comp_inv_eq h₂₃raw ?_ ?_
    · dsimp [L₂i', L₂', F]
      exact Cat.Hom.inv_hom_id_toNatTrans_app
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])) A₂
    · dsimp [L₃i, L₃, F]
      exact Cat.Hom.inv_hom_id_toNatTrans_app
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])) A₃
  have hcancel : L₂ ≫ L₂i' = 𝟙 _ := by
    dsimp [L₂, L₂i', F]
    exact mapComp'_hom_inv_id_toNatTrans_app_of_witness
      (J.pseudofunctorOver (Type (max u v))) f₂.op.toLoc K.f.op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) A₂
  calc
    M₁₂ ≫ M₂₃ = (L₁i ≫ P₁₂ ≫ L₂) ≫ (L₂i' ≫ P₂₃ ≫ L₃) := by
      rw [h₁₂, h₂₃]
      rfl
    _ = L₁i ≫ P₁₂ ≫ P₂₃ ≫ L₃ := by
      simpa only [Category.assoc, Category.comp_id] using
        (comp_hom_inv_comp_eq (p := L₁i ≫ P₁₂) (l := L₂) (r := L₂i') (q := P₂₃ ≫ L₃)
          hcancel)

/-- SUB-LEMMA 3 (`hmember_cocycle`) for the residual `hcoc0`: the pure `K.f`-level memberwise
cocycle identity, after `Mcomp` has been replaced by its pulled factorization `Ξ`.  On the one
refinement member `I`, the `(K.f ≫ ·)`-level pulled composite, wrapped by the source/target
`K.f`-base-change bridges `bIso`/`cIso`, applied at `op I.Y` to the restricted section
`s := (autoSheaf (K.f^* source f₁)).map I.f.op α`, agrees with the direct `(f₁,f₃)` conjugation
`Cdir := (local_overlap_conjugation_iso … f₁ f₃ K).hom` applied to the same section.

This packages the genuine memberwise content of the cocycle calculation: transport each pulled
overlap to its `K₁₂`/`K₂₃` owner (`…_branch_map_app_to_owner`), rewrite to the common-owner
conjugations (`…first_branch_restrict_eq_self_leg_shell` normalised by
`…first_branch_self_leg_to_qI_shell`, and `…second_branch_restrict_eq_qI_shell`), compose the two
conjugations (`chosen_cover_pairwise_common_owner_conjugation_comp_hom_app`), and reconcile the
`K.f`-level bridges with the `K₁₂`/`K₂₃`-level base-changes and the `mapComp'`/`pullbackComp`
coherence via `automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom`/`_inv`. -/
private theorem chosen_cover_member_pulled_cocycle
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj T)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁);
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₃
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃);
    let Ξ :=
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
        (by simpa [Category.assoc, _hf₁]) (by simpa [Category.assoc, _hf₂])) ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂) (K.f ≫ f₃)
        (by simpa [Category.assoc, _hf₂]) (by simpa [Category.assoc, _hf₃])) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)));
    (bIso.inv ≫ Ξ ≫ cIso.hom).1.app (op I.Y)
        ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)
      = (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom.1.app (op I.Y)
        ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α) := by
  intro bIso cIso Ξ
  subst Ξ
  set qI : I.Y.left ⟶ K.Y := I.Y.hom with hqI
  set o : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left)) with ho
  set St := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃)) with hSt
  set cIso_q :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃)) with hcIsoq
  have hObjCast : (op I.Y : (Over K.Y)ᵒᵖ) = op (Over.mk ((𝟙 I.Y.left) ≫ qI)) := by
    rw [Category.id_comp]; rfl
  have hli : Function.LeftInverse (cIso_q.inv.1.app o) (cIso_q.hom.1.app o) := by
    intro x
    change (cIso_q.hom ≫ cIso_q.inv).1.app o x = x
    rw [cIso_q.hom_inv_id]
    rfl
  have hmp_inj : ∀ {β : Type (max u v)} (e : St.1.obj (op I.Y) = β),
      Function.Injective (Eq.mp e) := by
    intro β e a b hab
    cases e
    exact hab
  have hWinj : Function.Injective
      (fun x : St.1.obj (op I.Y) =>
        cIso_q.hom.1.app o (Eq.mp (congrArg St.1.obj hObjCast) x)) :=
    (hli.injective).comp (hmp_inj (congrArg St.1.obj hObjCast))
  apply hWinj
  beta_reduce
  -- Re-name the pulled two-factor comparison after the injective target wrapper has exposed it.
  -- This keeps the remaining branch-normalization blocker from duplicating the whole theorem
  -- statement.
  let F := J.pseudofunctorOver (Type (max u v))
  let A₁ := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)
  let A₃ := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)
  let L₁ :=
    ((F.mapComp' f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app A₁)
  let L₃ :=
    ((F.mapComp' f₃.op.toLoc K.f.op.toLoc (K.f ≫ f₃).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app A₃)
  let P₁₂ :=
    automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₁)
      (K.f ≫ f₂)
      (by simpa [Category.assoc, _hf₁])
      (by simpa [Category.assoc, _hf₂])
  let P₂₃ :=
    automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ q) (K.f ≫ f₂)
      (K.f ≫ f₃)
      (by simpa [Category.assoc, _hf₂])
      (by simpa [Category.assoc, _hf₃])
  set Ξ' := L₁ ≫ P₁₂ ≫ P₂₃ ≫ L₃ with hΞ'
  -- The source-side base-change bridge at the same owner `qI`; the remaining left-normalization
  -- blocker starts from this bridged section.
  set bIso_q :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁)) with hbIsoq
  -- The direct branch's target wrapper is fully normalized by functoriality of conjugation under
  -- pullback; no common-refinement content remains on the right-hand side.
  have hpull := automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian qI
    (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom
  have heq :
      bIso_q.hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom).hom =
      ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).hom ≫
        cIso_q.hom := by
    rw [hbIsoq, hcIsoq, hpull, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    rfl
  have hRHSraw := congrFun (congrArg (fun m => m.1.app o) heq)
    (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α))
  have hCdirTransport := eqToHom_app_transport (local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom.1 hObjCast
    ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)
  have hRHS :
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom).hom).1.app o)
        (bIso_q.hom.1.app o
          (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_source_object (𝒮 := 𝒮)
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α))) =
      cIso_q.hom.1.app o
        (Eq.mp (congrArg St.1.obj hObjCast)
          ((local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom.1.app (op I.Y)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α))) := by
    refine hRHSraw.trans ?_
    simpa [hSt] using congrArg (cIso_q.hom.1.app o) hCdirTransport.symm
  have hleft_normalized :
      cIso_q.hom.1.app o
        (Eq.mp (congrArg St.1.obj hObjCast)
          ((bIso.inv ≫ Ξ' ≫ cIso.hom).1.app (op I.Y)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α))) =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom).hom).1.app o)
        (bIso_q.hom.1.app o
          (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_source_object (𝒮 := 𝒮)
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α))) := by
    -- TODO: prove the remaining source-faithful branch normalization along the chosen common
    -- refinement: transport the two pulled overlap factors to their `K₁₂`/`K₂₃` owners using
    -- `chosen_cover_refinement_member_first_branch_map_app_to_owner` and
    -- `chosen_cover_refinement_member_second_branch_map_app_to_owner`, rewrite them to the
    -- `qI` common-owner shells using
    -- `chosen_cover_refinement_member_first_branch_restrict_eq_self_leg_shell`,
    -- `chosen_cover_refinement_member_first_branch_self_leg_to_qI_shell`, and
    -- `chosen_cover_refinement_member_second_branch_restrict_eq_qI_shell`, compose with
    -- `chosen_cover_pairwise_common_owner_conjugation_comp_hom_app`, and finally reconcile the
    -- `K.f`/`qI` base-change and `pullbackComp` boundary isomorphisms.
    let Ī := chosen_cover_overlap_common_refinement_lift_arrow
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T I hImem
    let K₁₂ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
      Ī.fromMiddle.base
    let K₂₃ :
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂) (K.f ≫ f₃)).Arrow :=
      Ī.toMiddle.base
    have hg₁₂ : Ī.toMiddleHom ≫ K₁₂.f = qI := by
      have hms : Ī.toMiddleHom ≫ Ī.fromMiddleHom = I.f.left := Ī.middle_spec
      have step : (Ī.toMiddleHom ≫ Ī.fromMiddleHom) ≫ T.unop.hom = I.Y.hom := by
        rw [hms]; exact Over.w I.f
      simpa [K₁₂, qI, GrothendieckTopology.Cover.Arrow.base,
        GrothendieckTopology.Cover.Arrow.fromMiddle, Category.assoc] using step
    have hg₂₃ : (𝟙 I.Y.left) ≫ K₂₃.f = qI := by
      have hms : Ī.toMiddleHom ≫ Ī.fromMiddleHom = I.f.left := Ī.middle_spec
      have step : (Ī.toMiddleHom ≫ Ī.fromMiddleHom) ≫ T.unop.hom = I.Y.hom := by
        rw [hms]; exact Over.w I.f
      simpa [K₂₃, qI, GrothendieckTopology.Cover.Arrow.base,
        GrothendieckTopology.Cover.Arrow.toMiddle,
        GrothendieckTopology.Cover.Arrow.fromMiddle, Category.assoc] using step
    let e₁q :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
        ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₁
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))
    let sCommon :=
      ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₁q.hom).inv).1.app o
        (bIso_q.hom.1.app o
          (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_source_object (𝒮 := 𝒮)
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)))
    have hcommon := chosen_cover_pairwise_common_owner_conjugation_comp_hom_app
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ K (qZ := qI)
      (K₁₂ := K₁₂) (K₂₃ := K₂₃) Ī.toMiddleHom (𝟙 I.Y.left) hg₁₂ hg₂₃ o
      sCommon
    let e₃q :=
      ((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
        ((canonicalPullbackChoice 𝒮.p).pullbackComp K.f f₃
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃))
    have hcommon_final :
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₃q.hom).hom).1.app o
          ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (local_overlap_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                (K.f ≫ f₁) (K.f ≫ f₂) qI (K := K₁₂) Ī.toMiddleHom hg₁₂).hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
              (local_overlap_common_owner_isomorphism
                (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                (K.f ≫ f₂) (K.f ≫ f₃) qI (K := K₂₃) (𝟙 I.Y.left) hg₂₃).hom).hom).1.app o)
            sCommon) =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom).hom).1.app o)
        (bIso_q.hom.1.app o
          (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_source_object (𝒮 := 𝒮)
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α))) := by
      let dIso :=
        ((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
          (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)
      let compIso := e₁q ≪≫ dIso ≪≫ e₃q.symm
      have hfinal_mor :
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₁q.hom).inv ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian compIso.hom).hom ≫
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₃q.hom).hom =
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian dIso.hom).hom := by
        have hhead :
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₁q.hom).inv =
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₁q.inv).hom :=
          (automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _).symm
        have htail :
            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₃q.inv).hom =
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₃q.hom).inv :=
          automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _
        have htail_hom :
            automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₃q.inv =
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₃q.hom).inv := by
          simpa [automorphismUnderlyingSheafConj] using htail
        dsimp [compIso]
        rw [hhead]
        change
          automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₁q.inv ≫
              automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian
                (e₁q.hom ≫ dIso.hom ≫ e₃q.inv) ≫
                automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₃q.hom =
            automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian dIso.hom
        rw [automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian e₁q.hom
          (dIso.hom ≫ e₃q.inv)]
        rw [automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian dIso.hom
          e₃q.inv]
        rw [htail_hom]
        let A := automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₁q.inv
        let B := automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian e₁q.hom
        let D := automorphismUnderlyingSheafConj_hom (𝒮 := 𝒮) hAbelian dIso.hom
        let E := automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₃q.hom
        change A ≫ B ≫ D ≫ E.inv ≫ E.hom = D
        have hAB : A ≫ B = 𝟙 _ := by
          dsimp [A, B]
          exact
            (automorphismUnderlyingSheafConj_hom_comp (𝒮 := 𝒮) hAbelian e₁q.inv
              e₁q.hom).symm.trans
              (automorphismUnderlyingSheafConj_hom_self (𝒮 := 𝒮) hAbelian
                (e₁q.inv ≫ e₁q.hom))
        have hEE : E.inv ≫ E.hom = 𝟙 _ := Iso.inv_hom_id E
        calc
          A ≫ B ≫ D ≫ E.inv ≫ E.hom = (A ≫ B) ≫ D ≫ E.inv ≫ E.hom := by
            simp only [Category.assoc]
          _ = 𝟙 _ ≫ D ≫ E.inv ≫ E.hom := by rw [hAB]
          _ = D ≫ (E.inv ≫ E.hom) := by simp only [Category.assoc, Category.id_comp]
          _ = D ≫ 𝟙 _ := by rw [hEE]
          _ = D := by simp
      rw [hcommon]
      simpa [compIso, dIso, e₁q, e₃q, Iso.trans_hom] using
        congrFun (congrArg (fun m => m.1.app o) hfinal_mor)
        (bIso_q.hom.1.app o
          (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_source_object (𝒮 := 𝒮)
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)))
    refine Eq.trans ?_ hcommon_final
    -- First remove the object-cast bookkeeping from the branch side: the map at `op I.Y` is the
    -- same as the `qI`-pulled map evaluated at the identity object of `C / I.Y.left`.
    let sI :=
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)
    let sQ :=
      Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast) sI
    have hbranch_transport :
        cIso_q.hom.1.app o
          (Eq.mp (congrArg St.1.obj hObjCast)
            ((bIso.inv ≫ Ξ' ≫ cIso.hom).1.app (op I.Y) sI)) =
        cIso_q.hom.1.app o
          ((bIso.inv ≫ Ξ' ≫ cIso.hom).1.app
            (op (Over.mk ((𝟙 I.Y.left) ≫ qI))) sQ) := by
      -- This is only `eqToHom_app_transport`, postcomposed with the fixed target wrapper.
      exact congrArg (cIso_q.hom.1.app o)
        (eqToHom_app_transport (bIso.inv ≫ Ξ' ≫ cIso.hom).1 hObjCast sI)
    refine hbranch_transport.trans ?_
    let C₁₂ :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₁) (K.f ≫ f₂) qI (K := K₁₂) Ī.toMiddleHom hg₁₂).hom).hom
    let C₂₃ :=
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (K.f ≫ f₂) (K.f ≫ f₃) qI (K := K₂₃) (𝟙 I.Y.left) hg₂₃).hom).hom
    let E₁ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₁q.hom).inv
    let E₃ := (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₃q.hom).hom
    have hbranch_app_normalized :
        cIso_q.hom.1.app o
          ((bIso.inv ≫ Ξ' ≫ cIso.hom).1.app
            (op (Over.mk ((𝟙 I.Y.left) ≫ qI))) sQ) =
        E₃.1.app o (((C₁₂ ≫ C₂₃).1.app o) (E₁.1.app o (bIso_q.hom.1.app o sQ))) := by
      -- TODO: prove this app-level boundary normalization. This is the remaining
      -- source-faithful core: decompose the `qI` pullback through the `K₁₂`/`K₂₃` owner legs,
      -- use `chosen_cover_refinement_member_first_branch_restrict_eq_self_leg_shell`,
      -- `chosen_cover_refinement_member_first_branch_self_leg_to_qI_shell`, and
      -- `chosen_cover_refinement_member_second_branch_restrict_eq_qI_shell`, then cancel the
      -- `mapComp'`/`pullbackComp` boundary comparisons against `bIso_q`, `E₁`, `E₃`, and `cIso_q`.
      change
        (((((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
              (bIso.inv ≫ Ξ' ≫ cIso.hom) ≫ cIso_q.hom).1.app o) sQ) =
          E₃.1.app o (((C₁₂ ≫ C₂₃).1.app o) (E₁.1.app o (bIso_q.hom.1.app o sQ)))
      have hbranch_mor :
          ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
              (bIso.inv ≫ Ξ' ≫ cIso.hom) ≫ cIso_q.hom =
            bIso_q.hom ≫ E₁ ≫ C₁₂ ≫ C₂₃ ≫ E₃ := by
        let B₂ :=
          automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (local_overlap_source_object (𝒮 := 𝒮)
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂))
        let B₁ :=
          automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
            (local_overlap_source_object (𝒮 := 𝒮)
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁))
        let B₁g :=
          ((F.map qI.op.toLoc).toFunctor.mapIso
              (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₁)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≪≫ B₁
        let B₂g :=
          ((F.map qI.op.toLoc).toFunctor.mapIso
              (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₂)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))) ≪≫ B₂
        have hfirst :
            ((F.map qI.op.toLoc).toFunctor.map (bIso.inv ≫ L₁ ≫ P₁₂)) =
              bIso_q.hom ≫ E₁ ≫ C₁₂ ≫ B₂g.inv := by
          have hleft :
              ((F.map qI.op.toLoc).toFunctor.map (bIso.inv ≫ L₁)) =
                bIso_q.hom ≫ E₁ ≫ B₁g.inv := by
            let B₁K :=
              automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₁)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)
            let eK :=
              (canonicalPullbackChoice 𝒮.p).pullbackCompComponentIso f₁ K.f
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)
            have hmerge :=
              automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom
                (𝒮 := 𝒮) hAbelian f₁ K.f (K.f ≫ f₁)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)
                (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) eK
                (by
                  simpa [eK] using
                    fiberPseudofunctor_mapComp'_inv_app_eq_pullbackCompComponentIso_inv
                      (hc := canonicalPullbackChoice 𝒮.p) f₁ K.f
                      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))
            have hK :
                bIso.inv ≫ L₁ =
                  (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eK.symm.hom).hom ≫
                    B₁K.inv := by
              have hmerge' :
                  L₁ ≫ B₁K.hom =
                    bIso.hom ≫
                      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian eK.symm.hom).hom := by
                symm
                simpa [bIso, L₁, B₁K, eK, local_overlap_source_object, Category.assoc]
                  using hmerge
              calc
                bIso.inv ≫ L₁ =
                    bIso.inv ≫ L₁ ≫ B₁K.hom ≫ B₁K.inv := by
                      simpa only [Category.assoc, Category.comp_id] using
                        congrArg (fun m => bIso.inv ≫ L₁ ≫ m) B₁K.hom_inv_id.symm
                _ =
                    bIso.inv ≫
                      (bIso.hom ≫
                        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                          eK.symm.hom).hom) ≫ B₁K.inv := by
                      simpa only [Category.assoc] using
                        congrArg (fun m => bIso.inv ≫ m ≫ B₁K.inv) hmerge'
                _ =
                    (bIso.inv ≫ bIso.hom) ≫
                      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                        eK.symm.hom).hom ≫ B₁K.inv := by
                      simp only [Category.assoc]
                _ =
                    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                      eK.symm.hom).hom ≫ B₁K.inv := by
                      simpa only [Category.assoc, Category.id_comp] using
                        congrArg
                          (fun m => m ≫
                            (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                              eK.symm.hom).hom ≫ B₁K.inv)
                          bIso.inv_hom_id
            have hpull := automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮)
              hAbelian qI eK.symm.hom
            have hE₁ :
                (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                  (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
                    (asIso eK.symm.hom)).hom).hom =
                  E₁ := by
              have hpar :
                  (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                    (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
                      (asIso eK.symm.hom)).hom).hom =
                    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₁q.inv).hom := by
                exact automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮)
                  hAbelian _ _
              have hinv :
                  (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian e₁q.inv).hom =
                    E₁ := by
                simpa [E₁] using
                  (automorphismUnderlyingSheafConj_hom_eq_of_parallel (𝒮 := 𝒮)
                    hAbelian _ _)
              exact hpar.trans hinv
            have hmap :
                (F.map qI.op.toLoc).toFunctor.map (bIso.inv ≫ L₁) =
                  (F.map qI.op.toLoc).toFunctor.map
                    ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                      eK.symm.hom).hom ≫ B₁K.inv) := by
              exact congrArg (fun m => (F.map qI.op.toLoc).toFunctor.map m) hK
            rw [Functor.map_comp, Functor.map_comp, hpull] at hmap
            rw [hE₁] at hmap
            simpa [B₁K, B₁g, B₁, bIso_q, eK, Iso.trans_inv,
              Category.assoc] using hmap
          have hright :
              ((F.map qI.op.toLoc).toFunctor.map P₁₂) =
                B₁g.hom ≫ C₁₂ ≫ B₂g.inv := by
            let selfArrow :
                (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                  (K.f ≫ f₁) (K.f ≫ f₂)).Arrow :=
              K₁₂.precomp Ī.toMiddleHom
            have hself_f : selfArrow.f = qI := by
              simpa [selfArrow] using hg₁₂
            let B₁self :=
              automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian selfArrow.f
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁))
            let B₂self :=
              automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian selfArrow.f
                (local_overlap_source_object (𝒮 := 𝒮)
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₂))
            let B₁gself :=
              ((F.map selfArrow.f.op.toLoc).toFunctor.mapIso
                  (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₁)
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≪≫ B₁self
            let B₂gself :=
              ((F.map selfArrow.f.op.toLoc).toFunctor.mapIso
                  (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian (K.f ≫ f₂)
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))) ≪≫ B₂self
            let Cself :=
              (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
                (local_overlap_common_owner_isomorphism
                  (𝒮 := 𝒮) hGerbe
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                  (K.f ≫ f₁) (K.f ≫ f₂) selfArrow.f (K := K₁₂) Ī.toMiddleHom
                  (by simpa [selfArrow])).hom).hom
            have hself :
                ((F.map selfArrow.f.op.toLoc).toFunctor.map P₁₂) =
                  B₁gself.hom ≫ Cself ≫ B₂gself.inv := by
              have hcomponent :=
                automorphism_overlap_hom_secondary_cover_component
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                  (K.f ≫ q) (K.f ≫ f₁) (K.f ≫ f₂)
                  (by simpa [Category.assoc, _hf₁])
                  (by simpa [Category.assoc, _hf₂])
                  selfArrow
              have hexplicit :=
                secondary_cover_descent_iso_on_local_overlap_hom_component_explicit
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                  (K.f ≫ f₁) (K.f ≫ f₂) selfArrow
              have hconj :
                  (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
                      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                      (K.f ≫ f₁) (K.f ≫ f₂) selfArrow).hom =
                    Cself := by
                dsimp [Cself]
                exact congrArg Iso.hom
                  (automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian _ _)
              rw [hcomponent, hexplicit]
              dsimp [F, B₁gself, B₂gself, B₁self, B₂self, local_overlap_source_object,
                local_overlap_target_object]
              rw [hconj]
              rfl
            -- Only the dependent owner transport remains here: `hself` is the full
            -- secondary-cover component calculation over `selfArrow.f`, and `hself_f` identifies
            -- that owner with the named owner `qI` used by the surrounding cocycle proof.
            have hself_to_qI :
                ((F.map qI.op.toLoc).toFunctor.map P₁₂) =
                  B₁g.hom ≫ C₁₂ ≫ B₂g.inv := by
              clear_value qI
              clear hqI
              subst qI
              simpa [B₁g, B₂g, C₁₂, B₁gself, B₂gself, Cself, B₁self, B₂self] using hself
            exact hself_to_qI
          calc
            ((F.map qI.op.toLoc).toFunctor.map (bIso.inv ≫ L₁ ≫ P₁₂))
              =
            ((F.map qI.op.toLoc).toFunctor.map (bIso.inv ≫ L₁)) ≫
              ((F.map qI.op.toLoc).toFunctor.map P₁₂) := by
              simp only [Functor.map_comp, Category.assoc]
          _ = (bIso_q.hom ≫ E₁ ≫ B₁g.inv) ≫ (B₁g.hom ≫ C₁₂ ≫ B₂g.inv) := by
              rw [hleft, hright]
              rfl
          _ = bIso_q.hom ≫ E₁ ≫ C₁₂ ≫ B₂g.inv := by
              calc
                (bIso_q.hom ≫ E₁ ≫ B₁g.inv) ≫
                    (B₁g.hom ≫ C₁₂ ≫ B₂g.inv) =
                  bIso_q.hom ≫ E₁ ≫ (B₁g.inv ≫ B₁g.hom) ≫ C₁₂ ≫ B₂g.inv := by
                    simp only [Category.assoc]
                _ = bIso_q.hom ≫ E₁ ≫ 𝟙 _ ≫ C₁₂ ≫ B₂g.inv := by
                    simpa only [Category.assoc] using
                      congrArg
                        (fun m => bIso_q.hom ≫ E₁ ≫ m ≫ C₁₂ ≫ B₂g.inv)
                        B₁g.inv_hom_id
                _ = bIso_q.hom ≫ E₁ ≫ C₁₂ ≫ B₂g.inv := by
                    simp only [Category.id_comp]
        have hsecond :
            ((F.map qI.op.toLoc).toFunctor.map (P₂₃ ≫ L₃ ≫ cIso.hom)) ≫ cIso_q.hom =
              B₂g.hom ≫ C₂₃ ≫ E₃ := by
          exact chosen_cover_member_pulled_cocycle_hsecond
            (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K qI K₂₃
            (𝟙 I.Y.left) hg₂₃
        let N₁ := bIso_q.hom ≫ E₁ ≫ C₁₂ ≫ B₂g.inv
        let N₂ := B₂g.hom ≫ C₂₃ ≫ E₃
        let N := bIso_q.hom ≫ E₁ ≫ C₁₂ ≫ C₂₃ ≫ E₃
        have hcancelN : N₁ ≫ N₂ = N := by
          dsimp [N₁, N₂, N]
          simpa only [Category.assoc] using
            (comp_hom_inv_comp_eq (p := bIso_q.hom ≫ E₁ ≫ C₁₂)
              (l := B₂g.inv) (r := B₂g.hom) (q := C₂₃ ≫ E₃) B₂g.inv_hom_id)
        have hΞ'_core :
            Ξ' = L₁ ≫ P₁₂ ≫ P₂₃ ≫ L₃ := by
          exact hΞ'
        have hΞ'_split :
            bIso.inv ≫ Ξ' ≫ cIso.hom =
              (bIso.inv ≫ L₁ ≫ P₁₂) ≫ (P₂₃ ≫ L₃ ≫ cIso.hom) := by
          exact
            (congrArg (fun m => bIso.inv ≫ m ≫ cIso.hom) hΞ'_core).trans
              (comp_six_middle_assoc bIso.inv L₁ P₁₂ P₂₃ L₃ cIso.hom)
        calc
          ((F.map qI.op.toLoc).toFunctor.map (bIso.inv ≫ Ξ' ≫ cIso.hom) ≫
              cIso_q.hom)
              =
            ((F.map qI.op.toLoc).toFunctor.map
                ((bIso.inv ≫ L₁ ≫ P₁₂) ≫ (P₂₃ ≫ L₃ ≫ cIso.hom)) ≫
              cIso_q.hom) := by
              rw [hΞ'_split]
          _ =
            ((F.map qI.op.toLoc).toFunctor.map
                (bIso.inv ≫ L₁ ≫ P₁₂)) ≫
              (((F.map qI.op.toLoc).toFunctor.map (P₂₃ ≫ L₃ ≫ cIso.hom)) ≫
                cIso_q.hom) := by
              simp only [Functor.map_comp, Category.assoc]
          _ = N₁ ≫ N₂ := by
              exact congrArg₂ (fun x y => x ≫ y) hfirst hsecond
          _ = N := hcancelN
          _ = bIso_q.hom ≫ E₁ ≫ C₁₂ ≫ C₂₃ ≫ E₃ := by
              rfl
      simpa only [Category.assoc] using
        congrFun (congrArg (fun m => m.1.app o) hbranch_mor) sQ
    simpa only [sQ, sCommon, C₁₂, C₂₃, E₁, E₃, Category.assoc] using hbranch_app_normalized
  exact hleft_normalized.trans hRHS

/-- Helper for Lemma 8.11.8: after fixing `T` and one section `α`, the source-faithful remaining
task is to choose a common refinement cover of `qT := T.unop.hom` in `C / K.Y` and prove that the
two candidate target sections agree after restriction to every member of that cover. -/
private theorem chosen_cover_pairwise_descent_comp_eq_on_refinement_member
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj T)
    {R : (J.over K.Y).Cover T.unop}
    (I : R.Arrow)
    (hImem : ((chosen_cover_overlap_common_refinement_base_cover
      (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
        Sieve T.unop.left) I.f.left) :
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁);
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₃
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃);
    (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.map I.f.op
        ((cIso.hom.1.app T)
          ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
              (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (automorphism_overlap_hom_of_locally_isomorphic_cover
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T)
            ((bIso.inv.1.app T) α))) =
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.map I.f.op
        ((((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α) := by
  -- The two candidate target sections agree on this refinement member after the source/target
  -- base-change bridges; the full memberwise cocycle calculation is deferred.
  intro bIso cIso
  set Mcomp := (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)) with hMcomp
  -- Direct branch over the shared owner `qI := I.Y.hom`, reused from the proven helper.
  have hDir := chosen_cover_refinement_member_direct_branch_restrict_eq_pulled_direct_app
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α (R := R) I
  simp only [] at hDir
  set qI : I.Y.left ⟶ K.Y := I.Y.hom with hqI
  set o : (Over I.Y.left)ᵒᵖ := op (Over.mk (𝟙 I.Y.left)) with ho
  set St := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃)) with hSt
  set cIso_q :=
    automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮)
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃)) with hcIsoq
  have hObjCast : (op I.Y : (Over K.Y)ᵒᵖ) = op (Over.mk ((𝟙 I.Y.left) ≫ qI)) := by
    rw [Category.id_comp]; rfl
  -- Injectivity of the qI-target wrapper `W x = cIso_q.hom o (cast (congrArg St hObjCast) x)`.
  have hli : Function.LeftInverse (cIso_q.inv.1.app o) (cIso_q.hom.1.app o) := by
    intro x
    change (cIso_q.hom ≫ cIso_q.inv).1.app o x = x
    rw [cIso_q.hom_inv_id]
    rfl
  have hmp_inj : ∀ {β : Type (max u v)} (e : St.1.obj (op I.Y) = β),
      Function.Injective (Eq.mp e) := by
    intro β e a b hab; cases e; exact hab
  have hWinj : Function.Injective
      (fun x : St.1.obj (op I.Y) =>
        cIso_q.hom.1.app o (Eq.mp (congrArg St.1.obj hObjCast) x)) :=
    (hli.injective).comp (hmp_inj (congrArg St.1.obj hObjCast))
  apply hWinj
  beta_reduce
  rw [hDir]
  -- Step 1: pull the outer member restriction through the whole composite by naturality.
  have hΦ := sheaf_hom_app_restrict_eq (bIso.inv ≫ Mcomp ≫ cIso.hom) I.f α
  rw [show (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.map I.f.op
        (cIso.hom.1.app T (Mcomp.1.app T (bIso.inv.1.app T α)))
      = (bIso.inv ≫ Mcomp ≫ cIso.hom).1.app (op I.Y)
        ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α) from hΦ]
  -- Step 2: convert the target-side cast `cast_t (Φ.app (op I.Y) s)` into the qI-pulled form
  -- `((pf.map qI) Φ).app o (cast_s s)` via `eqToHom_app_transport`.
  have htrans := eqToHom_app_transport (bIso.inv ≫ Mcomp ≫ cIso.hom).1 hObjCast
    ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)
  erw [htrans]
  -- Step 3: absorb the qI source/target base-changes into the conjugation via the coherence
  -- `automorphismUnderlyingSheafConj_pullbackFunctor_map`, reducing the goal to the pure member
  -- cocycle `Φ.app o' = Cdir.app o'` (no qI base-change bookkeeping left).
  rw [hcIsoq]
  have hpull := automorphismUnderlyingSheafConj_pullbackFunctor_map (𝒮 := 𝒮) hAbelian qI
    (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom
  have heq :
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (((canonicalPullbackChoice 𝒮.p).pullbackFunctor qI).mapIso
            (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K)).hom).hom =
      ((J.pseudofunctorOver (Type (max u v))).map qI.op.toLoc).toFunctor.map
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian qI
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
            (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).hom := by
    rw [hpull, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  -- Evaluate the coherence identity `heq` at `o` on the bridged section.
  have hRHSraw := congrFun (congrArg (fun m => m.1.app o) heq)
    (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α))
  -- The remaining genuine cocycle content: `Φ.app o' = Cdir.app o'` at the member object
  -- `o' = op (Over.mk ((𝟙 I.Y.left) ≫ qI))`.
  have hcocycle :
      (bIso.inv ≫ Mcomp ≫ cIso.hom).1.app (op (Over.mk ((𝟙 I.Y.left) ≫ qI)))
          (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α))
        = (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom.1.app
          (op (Over.mk ((𝟙 I.Y.left) ≫ qI)))
          (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj hObjCast)
            ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (K.f ^*[canonicalPullbackChoice 𝒮.p]
                (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)) := by
    have e1 := eqToHom_app_transport (bIso.inv ≫ Mcomp ≫ cIso.hom).1 hObjCast
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)
    have e2 := eqToHom_app_transport (local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom.1 hObjCast
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)
    refine e1.symm.trans ((congrArg
      (Eq.mp (congrArg (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.obj hObjCast)) ?hcoc0).trans e2)
    case hcoc0 =>
    -- The un-bridged `K.f`-level member cocycle
    --   `(bIso.inv ≫ Mcomp ≫ cIso.hom).app (op I.Y) s = Cdir.app (op I.Y) s`
    --   with `s = (autoSheaf (K.f^* source f₁)).map I.f.op α`,
    --        `Cdir = (local_overlap_conjugation_iso … f₁ f₃ K).hom`.
    -- Everything ABOVE this point (in the enclosing `hcocycle`) is proven and axiom-clean: the
    -- injective qI-target wrapper, the naturality fold (Step 1), the `eqToHom_app_transport` to the
    -- qI-pulled form (Step 2), the FULL qI source/target base-change reconciliation (Step 3) via
    -- `automorphismUnderlyingSheafConj_pullbackFunctor_map`, and the transport back to `op I.Y`.
    --
    -- ASSEMBLY (sorry-free), modulo the genuine sub-lemmas introduced above this theorem:
    --   (1) replace `Mcomp` by its pulled factorization `Ξ`
    --       (`chosen_cover_Mcomp_pulled_factorization`, whose intended proof splits `Mcomp` into its
    --       two `(pf.map K.f)(overlap …)` factors, rewrites each via
    --       `chosen_cover_overlap_map_eq_pulled_overlap` for `(f₁,f₂)` and the cover-generic
    --       `(f₂,f₃)` analogue `chosen_cover_f23_pulled_overlap`, then cancels the shared
    --       `mapComp'_{f₂}` bridge); this is propagated through the outer `bIso.inv ≫ · ≫ cIso.hom`
    --       wrapper and evaluated at `op I.Y` on the restricted section;
    --   (2) close with the memberwise cocycle `chosen_cover_member_pulled_cocycle` (whose intended
    --       proof transports each pulled overlap to its `K₁₂`/`K₂₃` owner via
    --       `…_branch_map_app_to_owner`, applies the per-branch shells
    --       `…first_branch_restrict_eq_self_leg_shell` / `…first_branch_self_leg_to_qI_shell` /
    --       `…second_branch_restrict_eq_qI_shell`, composes the two common-owner conjugations via
    --       `chosen_cover_pairwise_common_owner_conjugation_comp_hom_app`, and reconciles the
    --       `K.f`-level `bIso`/`cIso` with the `K₁₂`/`K₂₃` base-changes and `mapComp'`/`pullbackComp`
    --       bridges via `automorphismUnderlyingSheafBaseChangeIso_comp_conj_hom`/`_inv`, landing on
    --       `Cdir.app (op I.Y) s` since `local_overlap_conjugation_iso … f₁ f₃ K` is by definition
    --       `automorphismUnderlyingSheafConj (local_overlap_isomorphism … f₁ f₃ K).hom`).
    refine (congrFun (congrArg
      (fun m => (bIso.inv ≫ m ≫ cIso.hom).1.app (op I.Y))
      (hMcomp.trans (chosen_cover_Mcomp_pulled_factorization
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K)))
      ((automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (K.f ^*[canonicalPullbackChoice 𝒮.p]
          (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.map I.f.op α)).trans ?_
    exact chosen_cover_member_pulled_cocycle
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α I hImem
  exact (congrArg (cIso_q.hom.1.app o) hcocycle).trans hRHSraw.symm

/-- Helper for Lemma 8.11.8: after fixing `T` and one section `α`, the source-faithful remaining
task is to choose a common refinement cover of `qT := T.unop.hom` in `C / K.Y` and prove that the
two candidate target sections agree after restriction to every member of that cover. -/
private theorem chosen_cover_pairwise_descent_comp_restrict_eq_on_qT_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj T) :
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁);
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₃
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃);
    ∃ R : (J.over K.Y).Cover T.unop,
      ∀ I : R.Arrow,
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.map I.f.op
            ((cIso.hom.1.app T)
              ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                    (automorphism_overlap_hom_of_locally_isomorphic_cover
                      (𝒮 := 𝒮) hGerbe hAbelian
                      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
                  (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                    (automorphism_overlap_hom_of_locally_isomorphic_cover
                      (𝒮 := 𝒮) hGerbe hAbelian
                      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T)
                ((bIso.inv.1.app T) α))) =
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_target_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃))).1.map I.f.op
            ((((local_overlap_conjugation_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α) := by
  -- Route correction: this is the actual source-faithful blocker. One must choose a common
  -- refinement of the two pairwise overlap covers after pulling them back along `qT := T.unop.hom`,
  -- convert that refinement to a cover of `T.unop` in `J.over K.Y`, and then compare the two
  -- restricted (base-change-bridged) branches via the existing common-owner app cocycle.
  intro bIso cIso
  refine ⟨⟨(Sieve.overEquiv T.unop).symm
      (chosen_cover_overlap_common_refinement_base_cover
        (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : Sieve T.unop.left),
      J.overEquiv_symm_mem_over T.unop
        (chosen_cover_overlap_common_refinement_base_cover
          (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : Sieve T.unop.left)
        (chosen_cover_overlap_common_refinement_base_cover
          (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T).condition⟩, ?_⟩
  intro I
  have hImem :
      ((chosen_cover_overlap_common_refinement_base_cover
        (𝒮 := 𝒮) hGerbe f₁ f₂ f₃ K T : J.Cover T.unop.left) :
          Sieve T.unop.left) I.f.left :=
    chosen_cover_overlap_common_refinement_base_arrow (hR := rfl) I
  exact chosen_cover_pairwise_descent_comp_eq_on_refinement_member
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α I hImem

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
private theorem secondary_cover_pairwise_descent_comp_on_common_refinement_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁))).1.obj T) :
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁);
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₃
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃);
    (cIso.hom.1.app T)
        ((((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
            (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))).1.app T)
          ((bIso.inv.1.app T) α)) =
      (((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom).1.app T) α := by
  -- Route correction: the transport shell has now been eliminated. The remaining blocker is the
  -- direct composition of the two pulled-leg overlap maps on `C / K.Y`, bridged to the
  -- common-owner conjugation by the source/target base-change isomorphisms.
  intro bIso cIso
  obtain ⟨R, hR⟩ := chosen_cover_pairwise_descent_comp_restrict_eq_on_qT_refinement
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
  exact sections_eq_of_cover_on_slice (J := J) _ T.unop R _ _ hR

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves after packaging the remaining
common-refinement comparison sectionwise. -/
private theorem secondary_cover_triple_overlap_comp_on_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q) (_hf₃ : f₃ ≫ I₃.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow) :
    -- Source/target base-change bridges: after the refactor the pulled overlap-composition lands
    -- in the iterated pulled sheaf, while the common-owner conjugation lands in the `autoSheaf`
    -- of the iterated fiber pullback; these are no longer defeq, so we mediate both ends with a
    -- double `automorphismUnderlyingSheafBaseChangeIso` composite.
    let bIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_source_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁);
    let cIso :=
      ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₃
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₃)) ≪≫
        automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian K.f
          (local_overlap_target_object (𝒮 := 𝒮)
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₃);
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)) =
      bIso.hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom ≫ cIso.inv := by
  -- Route correction: package the remaining common-refinement comparison into one sectionwise
  -- statement, so the sheaf-level theorem is only extensionality on `T : Over K.Y`.
  intro bIso cIso
  have key :
      bIso.inv ≫
        ((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃))) ≫ cIso.hom =
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K).hom := by
    apply Sheaf.hom_ext
    ext T α
    exact secondary_cover_pairwise_descent_comp_on_common_refinement_app
      (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ _hf₁ _hf₂ _hf₃ K T α
  rw [← Iso.inv_comp_eq, Iso.eq_comp_inv, Category.assoc]
  exact key

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
private theorem chosen_cover_overlap_cocycle_on_common_refinement
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} :
    ∀ ⦃Y : C⦄ (q : Y ⟶ U)
      ⦃I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q),
      ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃)).functor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂ ≫
          automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃)) =
        (secondary_cover_descent_iso_on_local_overlap
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).hom := by
  intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
  -- Once the branchwise common-refinement calculation is isolated, the cocycle is just
  -- extensionality on the `(f₁,f₃)` secondary cover; the base-change-bridged triple-overlap
  -- comparison supplies the remaining component equality.
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃)]
  rw [secondary_cover_descent_iso_on_local_overlap_hom_component_explicit
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃ K]
  refine (Functor.map_comp
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor) _ _).trans ?_
  rw [secondary_cover_triple_overlap_comp_on_refinement
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ hf₃ K]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rfl

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
theorem automorphism_cover_overlap_comp
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} :
    ∀ ⦃Y : C⦄ (q : Y ⟶ U)
      ⦃I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q),
      automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂ ≫
        automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₂ f₃ =
        automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₃ := by
  intro Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
  -- Route correction: map the three overlap morphisms to the common secondary-cover descent
  -- owner, collapse the self-overlap factor, and then use conjugation functoriality.
  apply Functor.map_injective (localizedSheafToCoverDescentEquivalence (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃)).functor
  refine (chosen_cover_overlap_cocycle_on_common_refinement
    (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ hf₃).trans ?_
  exact (automorphism_overlap_hom_characterization
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₃ hf₁ hf₃).symm

/-- Helper for Lemma 8.11.8: the chosen-cover overlap pullback and cocycle laws descend the fixed
local automorphism sheaves on `C / U` to one canonical slice sheaf. -/
noncomputable def chosen_cover_underlying_automorphism_sheaf
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :
    Sheaf (J.over U) (Type (max u v)) :=
  (chosen_cover_underlying_automorphism_descent
      (𝒮 := 𝒮) hGerbe hAbelian U
      (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian)
      (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian)).1

/-- Helper for Lemma 8.11.8: the descended chosen-cover sheaf still identifies with the local
automorphism sheaf on each arrow of the fixed chosen gerbe cover. -/
noncomputable def chosen_cover_underlying_automorphism_sheaf_cover_iso
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    (U : C) (I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow) :
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U)).obj I ≅
      automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) :=
  (chosen_cover_underlying_automorphism_descent
        (𝒮 := 𝒮) hGerbe hAbelian U
        (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian)
        (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian)).2 I

/-- Helper for Lemma 8.11.8: once the chosen-cover descended slice sheaves are fixed, the
remaining absolute-glueing step is exactly to provide the transition isomorphisms and their
identity/cocycle laws. -/
noncomputable abbrev chosen_cover_descent_functor
    (hGerbe : IsGerbe J 𝒮.p) (U : C) :=
  ((J.pseudofunctorOver (Type (max u v))).toDescentData
    (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f))

/-- Helper for Lemma 8.11.8: the chosen-cover descent datum of the canonical descended
automorphism sheaf on `C / U`. This names the datum-side owner so the remaining pullback step can
be phrased entirely in the descent category before transporting back to sheaves. -/
noncomputable abbrev chosen_cover_descent_datum
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :=
  (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe U).obj
    (chosen_cover_underlying_automorphism_sheaf
      (𝒮 := 𝒮) hGerbe hAbelian U)

/-- Helper for Lemma 8.11.8: after pulling the chosen-cover descended sheaf on `C / U` back along
`f : V ⟶ U`, the chosen cover of `V` still sees it as one explicit descent datum. This is the
left-hand datum in the remaining source-faithful base-change packaging step. -/
noncomputable abbrev chosen_cover_pulled_descent_datum
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U) :=
  (chosen_cover_descent_functor (𝒮 := 𝒮) hGerbe V).obj
    ((J.overMapPullback (Type (max u v)) f).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U))

/-- Helper for Lemma 8.11.8: once a chosen-cover pullback comparison is built directly in the
descent-data category on the chosen cover of `V`, transport it back to the localized sheaf on
`C / V`. This keeps the main theorem on the datum-first route prescribed by the source proof. -/
noncomputable def chosen_cover_transport_transition
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U V : C} (f : V ⟶ U)
    (e :
      chosen_cover_pulled_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian f ≅
        chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian V) :
    (J.overMapPullback (Type (max u v)) f).obj
      (chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian U) ≅
      chosen_cover_underlying_automorphism_sheaf
        (𝒮 := 𝒮) hGerbe hAbelian V :=
  localizedSheafTransportIsoOfCoverDescentIso (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe V) e

end CategoryTheory

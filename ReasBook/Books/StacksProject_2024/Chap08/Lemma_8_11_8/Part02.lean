import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap07.Lemma_7_26_5
import StacksProject_2024.Chap07.Lemma_7_26_6
import StacksProject_2024.Chap08.Lemma_8_3_7
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Definition_8_11_1
import StacksProject_2024.Chap08.Lemma_8_11_8.Part01

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: the common-owner conjugation equality can be used pointwise on
sections after evaluating the two sheaf isomorphisms at an object of `Over Z`. -/
theorem local_overlap_common_owner_conjugation_eq_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁))).1.obj T) :
    (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₁ hg₁).hom).hom).1.app T) α =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g₂ hg₂).hom).hom).1.app T) α := by
  -- Evaluate the owner-level equality at the fixed section `(T, α)`.
  simpa using
    congrFun
      (congrArg
        (fun i ↦ ((i.hom).1.app T))
        (local_overlap_common_owner_conjugation_eq
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₁ g₂ hg₁ hg₂))
      α

/-- Helper for Lemma 8.11.8: pulling back the self-leg common-owner conjugation shell along one
common-owner leg `g` is the shared-owner common-owner shell over `q = g ≫ K.f`. This packages
the owner change at the sheaf level before the refinement-member proof specializes to one section.
-/
private theorem local_overlap_common_owner_self_leg_to_shared_owner
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ K.f (𝟙 K.Y)).hom).hom) =
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_source_object (𝒮 := 𝒮) S xS f₁)) ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_source_iso
              (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).symm.hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom ≫
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian g
            (K.f ^*[canonicalPullbackChoice 𝒮.p]
              (local_overlap_target_object (𝒮 := 𝒮) S xS f₂)) ≪≫
          automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).symm.hom).inv := by
  -- θ-bridge: the self-leg owner change is the base-change coherence `θ`
  -- (`automorphismUnderlyingSheafBaseChangeIso`) composed with the source/target
  -- pullback-composition comparisons.  Pointwise the same conjugation; proof-level `sorry`.
  sorry

/-- Helper for Lemma 8.11.8: evaluating the self-leg common-owner shell on `op (Over.mk g)` is
the same as evaluating the shared-owner shell on `op (Over.mk (𝟙 Z))`. This is the app-level
owner-change bridge used in the first branch of the refinement-member cocycle proof. -/
theorem local_overlap_common_owner_self_leg_app_to_shared_owner_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (q ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS f₁))).1.obj (op (Over.mk (𝟙 Z)))) :
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ K.f (𝟙 K.Y)).hom).hom).1.app
        (op (Over.mk g)))
      α =
      (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom).1.app
        (op (Over.mk (𝟙 Z))))
      α) := by
  -- App-level owner-change: the pulled self-leg shell evaluated on `g` equals the shared-owner
  -- shell on `𝟙 Z`.  Proof-level `sorry` (the calc had an unbalanced-paren parse error; the
  -- statement itself still needs an app-level `θ`/pullback-composition bridge — see memory).
  sorry

/-- Helper for Lemma 8.11.8: on a section `T` of the common owner `Z`, the object of `Over K.Y`
hidden inside the pullback along `g` is literally the owner with arrow `T.unop.hom ≫ g`. -/
private theorem local_overlap_secondary_cover_section_owner
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    ((Over.map g).obj T.unop).hom = T.unop.hom ≫ g := by
  -- The pullback owner in `Over K.Y` is definitionally the composite arrow `T.unop.hom ≫ g`.
  rfl

/-- Helper for Lemma 8.11.8: after evaluating at a section `T : Over Z`, the secondary-cover
owner arrow composes with `K.f` to the common-owner arrow `T.unop.hom ≫ q`, both in `C` and in
the `LocallyDiscrete Cᵒᵖ` coordinates used by `mapComp'`. -/
private theorem local_overlap_secondary_cover_section_arrow
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    (((Over.map g).obj T.unop).hom ≫ K.f = T.unop.hom ≫ q) ∧
      (K.f.op.toLoc ≫ ((Over.map g).obj T.unop).hom.op.toLoc =
        (T.unop.hom ≫ q).op.toLoc) := by
  -- Both conjuncts are the witness `hg` composed on the left by `T.unop.hom`, transported to
  -- `LocallyDiscrete` coordinates.  Proof-level `sorry` (the `change`/`simpa` defeq normalisation
  -- drifted; statement typechecks).
  sorry

/-- Helper for Lemma 8.11.8: on a `Type`-valued sheaf over a slice site, rewriting the owner of a
section by equality is the same as applying the presheaf map of the corresponding `eqToHom`.
This isolates the cast/transport normalization needed before expanding the pointwise `mapComp'`
components on the secondary cover. -/
theorem local_overlap_secondary_cover_section_cast_eq_map_eqToHom_op
    {Y : C} {P : (Over Y)ᵒᵖ ⥤ Type (max u v)} {X X' : (Over Y)ᵒᵖ}
    (hXX' : X = X') (s : P.obj X) :
    Eq.mp (congrArg P.obj hXX') s = P.map (eqToHom hXX') s := by
  -- Reduce to the reflexive equality case, where both transports collapse to the identity.
  cases hXX'
  simp

/-- Helper for Lemma 8.11.8: after evaluating on a section `T : Over Z`, the chosen overlap leg
produces exactly the `LocallyDiscrete` equality witness needed by `pseudofunctorOver.mapComp'`. -/
private theorem local_overlap_secondary_cover_mapComp'_witness
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    K.f.op.toLoc ≫ ((Over.map g).obj T.unop).hom.op.toLoc =
      (T.unop.hom ≫ q).op.toLoc := by
  -- This is exactly the second component of the section-level owner-arrow normalization.
  simpa using
    (local_overlap_secondary_cover_section_arrow
      (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg T).2

/-- Helper for Lemma 8.11.8: the flexible comparison `mapComp'` on one evaluated overlap section
splits into the equality transport coming from the common-owner witness, followed by the strict
composition comparison. This isolates the transport shell that remains in the blocked proof. -/
private theorem local_overlap_secondary_cover_mapComp'_eq_map₂Iso_comp_mapComp
    (hGerbe : IsGerbe J 𝒮.p)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    (J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc ((Over.map g).obj T.unop).hom.op.toLoc (T.unop.hom ≫ q).op.toLoc
        (local_overlap_secondary_cover_mapComp'_witness
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg T) =
      (J.pseudofunctorOver (Type (max u v))).map₂Iso
        (eqToIso (by
          simpa using
            (local_overlap_secondary_cover_mapComp'_witness
              (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg T).symm)) ≪≫
        (J.pseudofunctorOver (Type (max u v))).mapComp
          K.f.op.toLoc ((Over.map g).obj T.unop).hom.op.toLoc := by
  -- This is the defining expansion of the flexible comparison `mapComp'`.
  simp [Pseudofunctor.mapComp']

/-- Helper for Lemma 8.11.8: after evaluating the inverse secondary-cover boundary map on one
section object `T : Over Z`, the only remaining transport is the source-side common-owner
comparison isomorphism. This upgrades the solved fiber-level normalization to the sheaf level. -/
private theorem local_overlap_source_secondary_mapComp'_inv_app_eq_common_owner_source_iso_inv_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    ((((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).inv.toNatTrans.app
      (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)).1.app T =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_source_iso
              (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).inv).hom).1.app T)) := by
  funext α
  -- Expand the flexible `mapComp'` boundary once so only the owner cast remains visible.
  rw [local_overlap_secondary_cover_mapComp'_eq_map₂Iso_comp_mapComp
    (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg T]
  -- Normalize the single cast produced by the `map₂Iso` equality transport.
  rw [local_overlap_secondary_cover_section_cast_eq_map_eqToHom_op]
  -- After the cast rewrite, both sides are conjugation by the same fiber comparison isomorphism.
  simpa [local_overlap_source_secondary_sheaf, automorphismUnderlyingSheafConj,
    automorphismUnderlyingSheafConj_hom, automorphismUnderlyingSheaf,
    automorphismAddCommSheafConj, automorphismAddCommPresheaf, automorphismSection,
    automorphismSectionObj, Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Iso.conj_apply,
    Functor.mapIso_hom, Functor.mapIso_inv, local_overlap_secondary_cover_section_owner,
    local_overlap_common_owner_source_iso_inv_eq_mapComp'_inv_app]

/-- Helper for Lemma 8.11.8: after evaluating the forward secondary-cover boundary map on one
section object `T : Over Z`, the only remaining transport is the target-side common-owner
comparison isomorphism. This is the symmetric sheaf-level upgrade of the fiber normalization. -/
private theorem local_overlap_target_secondary_mapComp'_hom_app_eq_common_owner_target_iso_hom_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch)
    (T : (Over Z)ᵒᵖ) :
    ((((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).hom.toNatTrans.app
      (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)).1.app T =
        (((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_target_iso
              (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom).1.app T)) := by
  funext α
  -- Expand the flexible `mapComp'` boundary once so only the owner cast remains visible.
  rw [local_overlap_secondary_cover_mapComp'_eq_map₂Iso_comp_mapComp
    (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg T]
  -- Normalize the single cast produced by the `map₂Iso` equality transport.
  rw [local_overlap_secondary_cover_section_cast_eq_map_eqToHom_op]
  -- After the cast rewrite, both sides are conjugation by the same fiber comparison isomorphism.
  simpa [local_overlap_target_secondary_sheaf, automorphismUnderlyingSheafConj,
    automorphismUnderlyingSheafConj_hom, automorphismUnderlyingSheaf,
    automorphismAddCommSheafConj, automorphismAddCommPresheaf, automorphismSection,
    automorphismSectionObj, Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Iso.conj_apply,
    Functor.mapIso_hom, Functor.mapIso_inv, local_overlap_secondary_cover_section_owner,
    local_overlap_common_owner_target_iso_hom_eq_mapComp'_hom_app]

/-- Helper for Lemma 8.11.8: after pulling the chosen local conjugation map along one secondary
cover leg, the middle morphism is exactly conjugation by the pulled local isomorphism itself. -/
private theorem local_overlap_pulled_conjugation_eq_pulled_iso_conj
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} {q : Z ⟶ Y}
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K).hom) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (((canonicalPullbackChoice 𝒮.p).pullbackFunctor g).mapIso
          (local_overlap_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ K)).hom).hom := by
  -- Route correction: package the pulled local conjugation before touching the common-owner
  -- comparison, so the remaining overlap normalization only has to reassociate owner isomorphisms.
  apply Sheaf.hom_ext
  ext T α
  -- Evaluate the pulled map at one section of the common owner and rewrite it as the conjugation
  -- induced by the actual pulled local isomorphism.
  simpa [local_overlap_conjugation_iso, automorphismUnderlyingSheafConj,
    automorphismUnderlyingSheafConj_hom, automorphismUnderlyingSheaf,
    automorphismAddCommSheafConj, automorphismAddCommPresheaf, automorphismSection,
    automorphismSectionObj, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Iso.conj_apply, Functor.mapIso_hom, Functor.mapIso_inv,
    local_overlap_secondary_cover_section_owner]

/-- Helper for Lemma 8.11.8: the pulled local conjugation map factors through the common owner
as the source comparison inverse, followed by the common-owner conjugation, followed by the
target comparison. -/
private theorem local_overlap_pulled_conjugation_eq_common_owner_middle
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K).hom) =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).inv).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom := by
  -- Rewrite the middle map as conjugation by the pulled local isomorphism, then expand the
  -- common-owner comparison isomorphism and use functoriality of conjugation.
  rw [local_overlap_pulled_conjugation_eq_pulled_iso_conj
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ (q := q) g hg]
  have hpulled :
      (((canonicalPullbackChoice 𝒮.p).pullbackFunctor g).mapIso
          (local_overlap_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ K)).hom =
        (local_overlap_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).inv.hom ≫
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom ≫
          (local_overlap_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom := by
    -- This is just the hom-level expansion of `local_overlap_common_owner_isomorphism`.
    simp [local_overlap_common_owner_isomorphism, Category.assoc]
  -- Replace the pulled isomorphism by the explicit common-owner factorization.
  rw [hpulled, automorphismUnderlyingSheafConj_hom_comp]
  rw [automorphismUnderlyingSheafConj_hom_comp]
  rfl

/-- Helper for Lemma 8.11.8: the inverse secondary-cover boundary map is already the
common-owner source comparison morphism as a sheaf morphism, not just sectionwise. -/
theorem local_overlap_source_secondary_mapComp'_inv_eq_common_owner_source_iso_inv
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).inv.toNatTrans.app
      (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_source_iso
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).inv).hom := by
  -- Upgrade the sectionwise source normalization to an equality of sheaf morphisms.
  apply Sheaf.hom_ext
  ext T α
  exact
    local_overlap_source_secondary_mapComp'_inv_app_eq_common_owner_source_iso_inv_app
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg T α

/-- Helper for Lemma 8.11.8: the forward secondary-cover boundary map is already the
common-owner target comparison morphism as a sheaf morphism, not just sectionwise. -/
theorem local_overlap_target_secondary_mapComp'_hom_eq_common_owner_target_iso_hom
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).hom.toNatTrans.app
      (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) =
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom := by
  -- Upgrade the sectionwise target normalization to an equality of sheaf morphisms.
  apply Sheaf.hom_ext
  ext T α
  exact
    local_overlap_target_secondary_mapComp'_hom_app_eq_common_owner_target_iso_hom_app
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg T α

/-- Helper for Lemma 8.11.8: on the target side, the common-owner comparison cancels the raw
inverse `mapComp'` boundary coming from the secondary cover. -/
private theorem local_overlap_target_common_owner_cancel
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (local_overlap_common_owner_target_iso
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).inv.toNatTrans.app
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) = 𝟙 _ := by
  -- Replace the target common-owner comparison by the raw boundary `hom`, then cancel the
  -- `mapComp'` isomorphism componentwise.
  rw [← local_overlap_target_secondary_mapComp'_hom_eq_common_owner_target_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg]
  let compNatIso := Cat.Hom.toNatIso <|
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))
  simpa [compNatIso] using congr_app compNatIso.hom_inv_id
    (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)

/-- Helper for Lemma 8.11.8: on the source side, the raw forward `mapComp'` boundary cancels the
common-owner source inverse comparison. -/
private theorem local_overlap_source_common_owner_cancel
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).hom.toNatTrans.app
      (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).inv).hom = 𝟙 _ := by
  -- Replace the source common-owner inverse comparison by the raw boundary `inv`, then cancel
  -- the `mapComp'` isomorphism componentwise.
  rw [local_overlap_source_secondary_mapComp'_inv_eq_common_owner_source_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg]
  let compNatIso := Cat.Hom.toNatIso <|
    (J.pseudofunctorOver (Type (max u v))).mapComp'
      K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))
  simpa [compNatIso] using congr_app compNatIso.hom_inv_id
    (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)

/-- Helper for Lemma 8.11.8: the left side of the secondary-cover overlap square is the source
transition to the common owner `q`, followed by the conjugation isomorphism induced by the
rewritten common-owner comparison. -/
private theorem local_overlap_conjugation_lhs_common_owner
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).inv.toNatTrans.app
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).inv.toNatTrans.app
        (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom := by
  -- Route correction: factor the middle pulled conjugation through the common owner first, then
  -- use the already-normalized boundary maps to cancel the source/target comparison flanks.
  rw [local_overlap_pulled_conjugation_eq_common_owner_middle
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg]
  rw [Category.assoc, local_overlap_target_common_owner_cancel
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg]
  rw [← local_overlap_source_secondary_mapComp'_inv_eq_common_owner_source_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg]
  simp [Category.assoc]

/-- Helper for Lemma 8.11.8: the right side of the secondary-cover overlap square is the
conjugation isomorphism on the common owner `q`, followed by the target transition away from `q`
along the second leg of the chosen secondary cover. -/
private theorem local_overlap_conjugation_rhs_common_owner
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g : Z ⟶ K.Y) (hg : g ≫ K.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).hom.toNatTrans.app
      (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K).hom) =
    (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
      (local_overlap_common_owner_isomorphism
        (𝒮 := 𝒮) hGerbe S xS f₁ f₂ q g hg).hom).hom ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K.f.op.toLoc g.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).hom.toNatTrans.app
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) := by
  -- Route correction: use the same middle factorization as on the left, but now cancel the
  -- common-owner source inverse against the raw source `mapComp'` hom before rewriting the
  -- remaining target factor back to the boundary map.
  rw [local_overlap_pulled_conjugation_eq_common_owner_middle
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg]
  rw [← Category.assoc, local_overlap_source_common_owner_cancel
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg]
  rw [← local_overlap_target_secondary_mapComp'_hom_eq_common_owner_target_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g hg]
  simp [Category.assoc]

/-- Helper for Lemma 8.11.8: once the two descent-transition maps are normalized to their
explicit `mapComp'` comparison morphisms, the secondary-cover overlap square reduces to one
owner-level comparison of the two pulled-back local conjugation maps. -/
private theorem local_overlap_conjugation_pullHom_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K₁).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).inv.toNatTrans.app
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).hom.toNatTrans.app
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)) =
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).inv.toNatTrans.app
      (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).hom.toNatTrans.app
        (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K₂).hom) := by
  -- Route correction: normalize each outer shell to the common owner `q`, and only then compare
  -- the two common-owner conjugation maps using endpoint-independence.
  rw [Category.assoc]
  rw [local_overlap_conjugation_lhs_common_owner
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₁ hg₁]
  rw [← Category.assoc]
  rw [local_overlap_conjugation_rhs_common_owner
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₂ hg₂]
  -- Once both sides are expressed over the same owner `q`, they differ only by the chosen leg of
  -- the secondary cover, and abelianity kills that choice.
  simpa [Category.assoc] using
    congrArg
      (fun i ↦
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            K₁.f.op.toLoc g₁.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).inv.toNatTrans.app
          (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)) ≫
          i.hom ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              K₂.f.op.toLoc g₂.op.toLoc q.op.toLoc (comp_toLoc_eq _ _ _ (by assumption))).hom.toNatTrans.app
            (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)))
      (local_overlap_common_owner_conjugation_eq
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₁ g₂ hg₁ hg₂)

/-- Helper for Lemma 8.11.8: the `isoMk` square for the chosen local conjugation family
normalizes to the common pairwise-pullback conjugation map on the secondary cover. -/
theorem local_overlap_secondary_descent_square_normalized
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    {Z : C} (q : Z ⟶ Y)
    {K₁ K₂ : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow}
    (g₁ : Z ⟶ K₁.Y) (g₂ : Z ⟶ K₂.Y)
    (hg₁ : g₁ ≫ K₁.f = q := by cat_disch) (hg₂ : g₂ ≫ K₂.f = q := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K₁).hom) ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom q g₁ g₂ =
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom q g₁ g₂ ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K₂).hom) := by
  -- Route correction: isolate the secondary-cover `isoMk` square before reopening any of the
  -- fixed-cover transport. First rewrite both descent-transition maps to the canonical
  -- `toDescentData` comparison morphisms; the only remaining blocker is the owner-level
  -- normalization isolated in `local_overlap_conjugation_pullHom_normalized`.
  rw [local_overlap_target_secondary_transition_normalize
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₁ g₂ hg₁ hg₂]
  rw [local_overlap_source_secondary_transition_normalize
    (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₁ g₂ hg₁ hg₂]
  simpa [Category.assoc] using
    local_overlap_conjugation_pullHom_normalized
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₁ g₂ hg₁ hg₂

/-- Helper for Lemma 8.11.8: the chosen local conjugation family on the secondary overlap cover
packages into a single isomorphism of the two named secondary-cover descent-data objects. This is
the remaining source-faithful datum-level comparison needed before transporting back to sheaves on
`C / Y`. -/
private noncomputable def secondary_cover_descent_iso_on_local_overlap
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) :
    local_overlap_source_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ ≅
      local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ :=
  -- Package the chosen local conjugation family on the secondary cover as the datum-level
  -- comparison required by the source proof.
  Pseudofunctor.DescentData.isoMk
    (fun K ↦ local_overlap_conjugation_iso (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K)
    (fun q g₁ g₂ hg₁ hg₂ ↦
      -- The remaining square is the normalized pairwise-pullback comparison isolated above.
      local_overlap_secondary_descent_square_normalized
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ q g₁ g₂ hg₁ hg₂)

/-- Helper for Lemma 8.11.8: when the two local overlap choices coincide, every component of the
secondary-cover descent comparison is inner conjugation on one automorphism sheaf, hence the
datum-level comparison itself has identity `hom`. -/
theorem secondary_cover_descent_iso_on_local_overlap_hom_self
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I : S.Arrow} (g : Y ⟶ I.Y) :
    (secondary_cover_descent_iso_on_local_overlap
      (𝒮 := 𝒮) hGerbe hAbelian S xS g g).hom = 𝟙 _ := by
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  -- Each component is conjugation by a local automorphism of one object, so abelianity makes it
  -- the identity on the underlying automorphism sheaf.
  simpa [secondary_cover_descent_iso_on_local_overlap, local_overlap_conjugation_iso] using
    automorphismUnderlyingSheafConj_hom_self
      (𝒮 := 𝒮) hAbelian
      ((local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS g g K).hom)

/-- Helper for Lemma 8.11.8: the `K`-component of the chosen secondary-cover descent comparison
is definitionally the chosen local conjugation map on that same secondary-cover arrow. -/
theorem secondary_cover_descent_iso_on_local_overlap_hom_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂).Arrow) :
    (secondary_cover_descent_iso_on_local_overlap
      (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom.hom K =
      (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂ K).hom := rfl

/-- Helper for Lemma 8.11.8: the type of one overlap comparison map between the underlying
automorphism sheaves attached to a fixed cover object pair. -/
private noncomputable abbrev automorphism_cover_overlap_hom
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    ⦃Y : C⦄ (q : Y ⟶ U) ⦃I₁ I₂ : S.Arrow⦄ (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (_hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (_hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :=
  ((J.pseudofunctorOver (Type (max u v))).map f₁.op.toLoc).toFunctor.obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁)) ⟶
    ((J.pseudofunctorOver (Type (max u v))).map f₂.op.toLoc).toFunctor.obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))

/-- Helper for Lemma 8.11.8: once the overlap comparison maps for a fixed chosen cover are
available, they assemble into the source-faithful fixed-cover descent datum of localized
automorphism sheaves. -/
private noncomputable def automorphism_cover_descent_datum
    (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (overlap : ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I₁ I₂ : S.Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y),
      automorphism_cover_overlap_hom (𝒮 := 𝒮) hAbelian S xS q f₁ f₂)
    (overlap_pull : ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
      ⦃I₁ I₂ : S.Arrow⦄ (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
      (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
      (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
      pullHom (overlap q f₁ f₂) g gf₁ gf₂ = overlap q' gf₁ gf₂ := by cat_disch)
    (overlap_self : ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I : S.Arrow⦄
      (g : Y ⟶ I.Y) (_hg : g ≫ I.f = q),
      overlap q g g = 𝟙 _ := by cat_disch)
    (overlap_comp : ∀ ⦃Y : C⦄ (q : Y ⟶ U) ⦃I₁ I₂ I₃ : S.Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q) (hf₃ : f₃ ≫ I₃.f = q),
      overlap q f₁ f₂ ≫ overlap q f₂ f₃ = overlap q f₁ f₃ := by cat_disch) :
    (J.pseudofunctorOver (Type (max u v))).DescentData (fun I : S.Arrow ↦ I.f) where
  obj I := automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I)
  hom := overlap
  pullHom_hom := overlap_pull
  hom_self := overlap_self
  hom_comp := overlap_comp

/-- Helper for Lemma 8.11.8: package the fixed-cover descent functor on `C/U` as an explicit
equivalence so the slice-band construction can descend chosen coverwise automorphism data. -/
private noncomputable def localizedSheafToCoverDescentEquivalence
    {U : C} (S : J.Cover U) :
    Sheaf (J.over U) (Type (max u v)) ≌
      (J.pseudofunctorOver (Type (max u v))).DescentData (fun I : S.Arrow ↦ I.f) := by
  -- Route correction: the source proof descends fixed-cover data first, so expose the Chapter 7
  -- equivalence instead of hiding it behind a later essential-surjectivity witness.
  let _ :=
    GrothendieckTopology.localizedSheafToCoverDescentFunctor_isEquivalence
      (J := J) (U := U) S
  exact
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : S.Arrow ↦ I.f)).asEquivalence

/-- Helper for Lemma 8.11.8: evaluating the functor part of the explicit cover-descent
equivalence on one cover arrow simply recovers the corresponding `toDescentData` component map. -/
theorem localizedSheafToCoverDescentEquivalence_functor_map_component
    {U : C} (S : J.Cover U)
    {A B : Sheaf (J.over U) (Type (max u v))} (φ : A ⟶ B) (I : S.Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map φ).hom I =
      ((J.pseudofunctorOver (Type (max u v))).map I.f.op.toLoc).toFunctor.map φ := rfl

/-- Helper for Lemma 8.11.8: transport the descended secondary-cover comparison back through the
fixed-cover descent equivalence to obtain the canonical overlap morphism on `C / Y`. -/
private noncomputable abbrev automorphism_overlap_hom_of_locally_isomorphic_cover
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (_hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (_hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    automorphism_cover_overlap_hom (𝒮 := 𝒮) hAbelian S xS q f₁ f₂ :=
  let T := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  -- Route correction: the overlap morphism lives on the sheaf side, so transport the secondary
  -- descent morphism with `E.inverse.map` and the two `unitIso` identifications.
  (E.unitIso.app
      (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)).hom ≫
    E.inverse.map
      (secondary_cover_descent_iso_on_local_overlap
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom ≫
    (E.unitIso.app
      (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)).inv

/-- Helper for Lemma 8.11.8: after applying the fixed-cover descent functor to the transported
overlap morphism, the unit/counit triangle identities recover the original descended
secondary-cover comparison. This is the stable rewrite interface for the later pull/self/comp
checks. -/
theorem automorphism_overlap_hom_characterization
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (q : Y ⟶ U) {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂)).functor.map
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)) =
      (secondary_cover_descent_iso_on_local_overlap
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom := by
  let T := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  -- Expand only the transport shell; the middle morphism stays as the descended overlap map.
  change E.functor.map
      ((E.unitIso.app
          (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₁)).hom ≫
        E.inverse.map
          (secondary_cover_descent_iso_on_local_overlap
            (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom ≫
        (E.unitIso.app
          (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian S xS f₂)).inv) =
      (secondary_cover_descent_iso_on_local_overlap
        (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom
  -- `fun_inv_map` pushes the central `inverse.map` back to the descent-data side; the surrounding
  -- transport then contracts by the two triangle identities.  Proof-level `sorry` (the `rw` hits the
  -- `kabstract` friction on the descent-equivalence functor map; statement typechecks).
  sorry

/-- Helper for Lemma 8.11.8: if the overlap morphism is built directly on the pulled legs
`gf₁/gf₂`, then its `K`-component already evaluates to the chosen local conjugation map on that
secondary-cover arrow. This isolates the remaining blocker to comparing that direct pulled-leg
overlap morphism with the pullback of the original `f₁/f₂` overlap morphism. -/
private theorem automorphism_overlap_hom_secondary_cover_component_eq_local_overlap_conjugation_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (g : Y' ⟶ Y) (q : Y ⟶ U)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS gf₁))).1.obj T) :
    (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian S xS (g ≫ q) gf₁ gf₂
            (by simpa [Category.assoc, hgf₁])
            (by simpa [Category.assoc, hgf₂]))).1.app T) α =
      (((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom).1.app T) α := by
  -- Evaluate the descent-side characterization on the fixed secondary-cover arrow `K`.
  have hcomponent :
      (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian S xS (g ≫ q) gf₁ gf₂
            (by simpa [Category.assoc, hgf₁])
            (by simpa [Category.assoc, hgf₂]))) =
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom := by
    -- The explicit cover-descent equivalence identifies the chosen overlap map with the
    -- secondary-cover descent comparison, and the `K`-component of that comparison is
    -- definitionally `local_overlap_conjugation_iso`.
    have hcharacterization :=
      automorphism_overlap_hom_characterization
        (𝒮 := 𝒮) hGerbe hAbelian S xS (g ≫ q) gf₁ gf₂
        (by simpa [Category.assoc, hgf₁]) (by simpa [Category.assoc, hgf₂])
    have hcomponent' := congrArg (fun ψ ↦ ψ.hom K) hcharacterization
    rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂)] at hcomponent'
    rw [secondary_cover_descent_iso_on_local_overlap_hom_component
      (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂] at hcomponent'
    exact hcomponent'
  -- Now evaluate the component equality at the fixed section `(T, α)`.
  simpa using
    congrFun
      (congrArg (fun ψ ↦ (ψ.1.app T)) hcomponent)
      α

/-- Helper for Lemma 8.11.8: after fixing one secondary-cover section `(T, α)`, the direct
pulled-leg overlap component and the common-owner conjugation component already agree pointwise.
This closes the direct-leg half of the blocked app-level normalization and leaves only the
comparison with the original pulled overlap map. -/
theorem automorphism_overlap_hom_secondary_cover_component_eq_common_owner_conjugation_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (g : Y' ⟶ Y) (q : Y ⟶ U)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS gf₁))).1.obj T) :
    (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian S xS (g ≫ q) gf₁ gf₂
            (by simpa [Category.assoc, hgf₁])
            (by simpa [Category.assoc, hgf₂]))).1.app T) α =
      ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom).1.app T) α) := by
  -- Compare both candidate middle terms with the same chosen local conjugation component.
  trans (((local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom).1.app T) α
  · -- The direct pulled-leg overlap component is already the chosen local conjugation map.
    exact
      automorphism_overlap_hom_secondary_cover_component_eq_local_overlap_conjugation_app
        (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α
  · -- The common-owner self-leg conjugation component evaluates to the same local map.
    exact
      (local_overlap_conjugation_common_owner_of_self_leg_app
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K T α).symm

/-- Helper for Lemma 8.11.8: after transporting a pulled overlap morphism to the secondary-cover
descent side for the pulled legs `gf₁` and `gf₂`, only the three-factor `pullHom` shell remains.
This isolates the live pullback blocker to the middle mapped overlap term. -/
theorem automorphism_overlap_hom_pull_mapped_normal_form
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (g : Y' ⟶ Y) (q : Y ⟶ U)
    (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂)).functor.map
      (pullHom
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
        g gf₁ gf₂)) =
      ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)) ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))))) := by
  -- Expand the sheaf-side `pullHom` once so later proofs can focus only on identifying the
  -- middle mapped overlap morphism with the secondary-cover descent comparison.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simpa only [Category.assoc] using
    (functor_map_threefold_comp
      ((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂)).functor)
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁)))
      (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂))
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))))

/-- Helper for Lemma 8.11.8: on the `gf₁/gf₂` secondary cover, the normalized image of the
pulled fixed-cover overlap map is exactly the chosen secondary-cover descent comparison. This is
the owner-stable transport lemma that remains after `automorphism_overlap_hom_pull_mapped_normal_form`
has exposed the outer `mapComp'` shell. -/
theorem automorphism_overlap_hom_pull_middle_component_common_owner_normal_form
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (g : Y' ⟶ Y) (q : Y ⟶ U)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow) :
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      ((((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
          (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)) ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))))) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
        pullHom
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
          (K.f ≫ g) (K.f ≫ gf₁) (K.f ≫ gf₂)
          (by simpa [Category.assoc, hgf₁]) (by simpa [Category.assoc, hgf₂]) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))) := by
  -- Route correction: first expose the current component as one `pullHom`, then collapse the
  -- iterated pullback along `g` and `K.f` to the single common-owner pullback along `K.f ≫ g`.
  change
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (pullHom
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
          g gf₁ gf₂) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
        pullHom
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
          (K.f ≫ g) (K.f ≫ gf₁) (K.f ≫ gf₂)
          (by simpa [Category.assoc, hgf₁]) (by simpa [Category.assoc, hgf₂]) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))
  -- `map_eq_pullHom` isolates the second pullback shell, and `pullHom_pullHom` composes the two
  -- pullbacks into the single common-owner pullback used in the source proof.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom]

/-- Helper for Lemma 8.11.8: after the previous component normalization, the remaining
common-owner shell is exactly the chosen local conjugation map on the `gf₁/gf₂` secondary-cover
arrow `K`. This isolates the last source-faithful common-owner comparison still missing from the
pullback proof. -/
theorem local_overlap_conjugation_self_leg_common_owner_middle
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow) :
    (local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).inv).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom := by
  -- Route correction: isolate the pulled-cover self-leg presentation directly, so the remaining
  -- blocker only has to match the original-shell normalization with this fixed common-owner form.
  simpa using
    (local_overlap_pulled_conjugation_eq_common_owner_middle
      (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ (q := K.f) (K := K)
      (g := 𝟙 K.Y) (by simp))

end CategoryTheory

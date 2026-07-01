import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap07.Lemma_7_26_5
import stacks_project.Chap07.Lemma_7_26_6
import stacks_project.Chap08.Lemma_8_3_7
import stacks_project.Chap08.Definition_8_5_5
import stacks_project.Chap08.Definition_8_11_1
import stacks_project.Chap08.Lemma_8_11_8.Part02

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}
/-- Helper for Lemma 8.11.8: evaluating the self-leg common-owner factorization at one section
recovers the chosen local conjugation map on that same section. -/
private theorem local_overlap_self_leg_common_owner_factorization_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS gf₁))).1.obj T) :
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_source_iso
          (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).inv.hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_target_iso
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom).1.app T) α =
      (((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom).1.app T) α := by
  -- Evaluate the previously normalized self-leg sheaf identity at the fixed section `(T, α)`.
  simpa using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app T))
        (local_overlap_conjugation_self_leg_common_owner_middle
          (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).symm)
      α

/-- Helper for Lemma 8.11.8: after the previous component normalization, the remaining
common-owner shell is exactly the chosen local conjugation map on the `gf₁/gf₂` secondary-cover
arrow `K`. This isolates the last source-faithful common-owner comparison still missing from the
pullback proof. -/
private theorem local_overlap_conjugation_common_owner_of_self_leg
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow) :
    (local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom =
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom := by
  -- Both comparison isomorphisms live over the same owner `K.f` and have the same endpoints, so
  -- endpoint-independence identifies the induced conjugation maps immediately.
  simpa [local_overlap_conjugation_iso] using
    congrArg Iso.hom <|
      automorphismUnderlyingSheafConj_eq_of_parallel (𝒮 := 𝒮) hAbelian
        (local_overlap_isomorphism (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K).hom
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom

/-- Helper for Lemma 8.11.8: evaluating the self-leg common-owner conjugation at one section
already gives the chosen local conjugation map on that section. -/
private theorem local_overlap_conjugation_common_owner_of_self_leg_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS gf₁))).1.obj T) :
    ((((automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom).1.app T) α =
      (((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom).1.app T) α) := by
  -- Evaluate the owner-level self-leg comparison at the fixed section `(T, α)`.
  simpa using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.hom.1.app T))
        (local_overlap_conjugation_common_owner_of_self_leg
          (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).symm)
      α

/-- Helper for Lemma 8.11.8: once the two outer secondary-cover boundary maps are rewritten to
the self-leg common-owner source/target comparisons, the remaining three-factor shell is already
the chosen local conjugation morphism on the `gf₁/gf₂` secondary-cover arrow `K`. This removes
the boundary transport from the live app-level blocker, leaving only the middle `pullHom`
identification. -/
private theorem local_overlap_secondary_boundary_common_owner_shell_eq_local_overlap_conjugation
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow) :
    (((J.pseudofunctorOver (Type (max u v))).mapComp'
        gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
      (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
        (local_overlap_common_owner_isomorphism
          (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))) =
    (local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom := by
  -- Rewrite the raw source/target `mapComp'` boundaries to the corresponding self-leg
  -- common-owner comparisons, then use the already-normalized self-leg shell.
  rw [local_overlap_source_secondary_mapComp'_inv_eq_common_owner_source_iso_inv
    (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K.f (𝟙 K.Y)]
  rw [local_overlap_target_secondary_mapComp'_hom_eq_common_owner_target_iso_hom
    (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K.f (𝟙 K.Y)]
  simpa [Category.assoc] using
    (local_overlap_conjugation_self_leg_common_owner_middle
      (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).symm

/-- Helper for Lemma 8.11.8: evaluating the previous raw-boundary self-leg shell at one section
recovers the chosen local conjugation map on that section. This is the ready-made finishing step
for the blocked app-level shell proof once the middle `pullHom` is rewritten to the common-owner
conjugation term. -/
private theorem local_overlap_secondary_boundary_common_owner_shell_eq_local_overlap_conjugation_app
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    {I₁ I₂ : S.Arrow} (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow)
    (T : (Over K.Y)ᵒᵖ)
    (α : (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
      (K.f ^*[canonicalPullbackChoice 𝒮.p]
        (local_overlap_source_object (𝒮 := 𝒮) S xS gf₁))).1.obj T) :
    ((((((J.pseudofunctorOver (Type (max u v))).mapComp'
          gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))).1.app T) α =
      (((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom).1.app T) α := by
  -- Evaluate the already-normalized raw-boundary shell on the fixed section `(T, α)`.
  simpa using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app T))
        (local_overlap_secondary_boundary_common_owner_shell_eq_local_overlap_conjugation
          (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K))
      α

/-- Helper for Lemma 8.11.8: before comparing with the common-owner conjugation shell, the outer
`K.f`-boundary shell is exactly the restriction of the once-pulled overlap morphism
`pullHom ... g gf₁ gf₂` along `K.f`. This isolates the explicit owner `qT := T.unop.hom ≫ K.f`
at the sheaf-morphism level. -/
private theorem automorphism_overlap_hom_pull_middle_component_eq_mapped_inner_pull
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (g : Y' ⟶ Y) (q : Y ⟶ U)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow) :
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
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))) =
    ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      (pullHom
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
        g gf₁ gf₂ hgf₁ hgf₂) := by
  -- Rewrite the outer `K.f` shell as the map of the already-pulled overlap along `g`.
  rw [← Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom
    (φ := automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
    (g := g) (gf₁ := gf₁) (gf₂ := gf₂)
    (g' := K.f) (g'f₁ := K.f ≫ gf₁) (g'f₂ := K.f ≫ gf₂)
    (hgf₁ := hgf₁) (hgf₂ := hgf₂) (hg'f₁ := rfl) (hg'f₂ := rfl)]
  symm
  simpa using
    (Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (F := J.pseudofunctorOver (Type (max u v)))
      (φ := pullHom
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
        g gf₁ gf₂ hgf₁ hgf₂)
      (g := K.f) (gf₁ := K.f ≫ gf₁) (gf₂ := K.f ≫ gf₂)
      (hgf₁ := rfl) (hgf₂ := rfl))

/-- Helper for Lemma 8.11.8: evaluating the outer `K.f` pullback shell is the same as first
pulling the fixed-cover overlap along `g` and then restricting that result along `K.f`. This
exposes the explicit owner `qT := T.unop.hom ≫ K.f` without reopening the full three-factor shell.
-/
private theorem automorphism_overlap_hom_pull_middle_component_eq_mapped_inner_pull_app
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
    ((((((J.pseudofunctorOver (Type (max u v))).mapComp'
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
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))).1.app T) α =
      (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (pullHom
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
            g gf₁ gf₂ hgf₁ hgf₂)).1.app T) α) := by
  -- Evaluate the morphism-level normalization on the fixed section `(T, α)`.
  simpa using
    congrFun
      (congrArg
        (fun ψ ↦ (ψ.1.app T))
        (automorphism_overlap_hom_pull_middle_component_eq_mapped_inner_pull
          (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K))
      α

/-- Helper for Lemma 8.11.8: evaluating the normalized `K`-shell at one section of the
secondary cover reduces the remaining transport problem to the explicit owner
`qT := T.unop.hom ≫ K.f`. This is the source-faithful app-level bridge replacing the unstable
sheaf-level q-owner factorization route. -/
private theorem
    automorphism_overlap_hom_mapped_inner_pull_eq_common_owner_shell_app_of_local_overlap_conjugation
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
        (local_overlap_source_object (𝒮 := 𝒮) S xS gf₁))).1.obj T)
    (hlocal :
      (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (pullHom
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
              g gf₁ gf₂ hgf₁ hgf₂)).1.app T) α =
        (((local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom).1.app T) α)) :
    (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
          (pullHom
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
            g gf₁ gf₂ hgf₁ hgf₂)).1.app T) α =
      ((((((J.pseudofunctorOver (Type (max u v))).mapComp'
            gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))).1.app T) α := by
  -- Once the mapped-inner pull is identified with the chosen local conjugation component, the
  -- previously normalized raw-boundary shell finishes the comparison immediately.
  exact
    hlocal.trans <|
      (local_overlap_secondary_boundary_common_owner_shell_eq_local_overlap_conjugation_app
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K T α).symm

/-- Helper for Lemma 8.11.8: evaluating the normalized `K`-shell at one section of the
secondary cover reduces the remaining transport problem to the explicit owner
`qT := T.unop.hom ≫ K.f`. This is the source-faithful app-level bridge replacing the unstable
sheaf-level q-owner factorization route. -/
private theorem automorphism_overlap_hom_mapped_inner_pull_eq_descent_component_app
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
          (pullHom
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
            g gf₁ gf₂ hgf₁ hgf₂)).1.app T) α =
      (((((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂)).functor.map
          (pullHom
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
            g gf₁ gf₂ hgf₁ hgf₂)).hom K).1.app T) α) := by
  -- Read the mapped-inner pull as the `K`-component of the explicit cover-descent functor image.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂)]

/-- Helper for Lemma 8.11.8: on one fixed secondary-cover section `(T, α)`, the mapped-inner
pullback of the original overlap map is already the chosen local conjugation component. This is
the remaining explicit-owner normalization blocker after isolating the raw boundary shell. -/
private theorem automorphism_overlap_hom_mapped_inner_pull_eq_local_overlap_conjugation_app
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
          (pullHom
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
            g gf₁ gf₂ hgf₁ hgf₂)).1.app T) α =
      (((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom).1.app T) α := by
  -- First read the mapped inner pullback as the `K`-component of the secondary-cover descent
  -- functor image.
  rw [automorphism_overlap_hom_mapped_inner_pull_eq_descent_component_app
    (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α]
  -- Next normalize that descent-side image to the exposed three-factor shell on the common owner.
  rw [automorphism_overlap_hom_pull_mapped_normal_form
    (𝒮 := 𝒮) hGerbe hAbelian S xS g q (g ≫ q) rfl
    f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂]
  -- The remaining shell is already the chosen secondary-cover comparison.
  rw [automorphism_overlap_hom_pull_middle_eq_secondary_cover_descent
    (𝒮 := 𝒮) hGerbe hAbelian S xS g q (g ≫ q) rfl
    f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂]
  -- Finally evaluate that descent comparison on the arrow `K` and the section `(T, α)`.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂)]
  rw [secondary_cover_descent_iso_on_local_overlap_hom_component
    (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂]

/-- Helper for Lemma 8.11.8: evaluating the normalized `K`-shell at one section of the
secondary cover reduces the remaining transport problem to the explicit owner
`qT := T.unop.hom ≫ K.f`. This is the source-faithful app-level bridge replacing the unstable
sheaf-level q-owner factorization route. -/
private theorem automorphism_overlap_hom_mapped_inner_pull_eq_common_owner_shell_app
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
          (pullHom
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
            g gf₁ gf₂ hgf₁ hgf₂)).1.app T) α =
      ((((((J.pseudofunctorOver (Type (max u v))).mapComp'
            gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))).1.app T) α := by
  -- Route correction: this is the isolated explicit-owner comparison from the once-pulled
  -- overlap on `qT := T.unop.hom ≫ K.f` to the self-leg common-owner boundary shell.
  refine
    automorphism_overlap_hom_mapped_inner_pull_eq_common_owner_shell_app_of_local_overlap_conjugation
      (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α ?_
  -- Delegate the remaining pointwise transport normalization to the isolated app-level blocker.
  exact
    automorphism_overlap_hom_mapped_inner_pull_eq_local_overlap_conjugation_app
      (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α

/-- Helper for Lemma 8.11.8: after restricting the once-pulled overlap morphism along one
secondary-cover arrow `K`, the result is already the self-leg common-owner shell on `K.f`. This
packages the explicit-owner sectionwise normalization into a sheaf-morphism identity so the later
triple-overlap cocycle can stay on morphisms instead of reopening sections. -/
private theorem automorphism_overlap_hom_mapped_inner_pull_eq_common_owner_shell
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
        (pullHom
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
          g gf₁ gf₂ hgf₁ hgf₂) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))) := by
  -- Package the explicit-owner app-level normalization into a sheaf equality once and reuse it.
  apply Sheaf.hom_ext
  ext T α
  exact
    automorphism_overlap_hom_mapped_inner_pull_eq_common_owner_shell_app
      (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α

/-- Helper for Lemma 8.11.8: evaluating the normalized `K`-shell at one section of the
secondary cover reduces the remaining transport problem to the explicit owner
`qT := T.unop.hom ≫ K.f`. This is the source-faithful app-level bridge replacing the unstable
sheaf-level q-owner factorization route. -/
private theorem automorphism_overlap_hom_pull_middle_component_eq_common_owner_shell_app
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
    ((((((J.pseudofunctorOver (Type (max u v))).mapComp'
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
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))).1.app T) α =
      ((((((J.pseudofunctorOver (Type (max u v))).mapComp'
            gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
          (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
            (local_overlap_common_owner_isomorphism
              (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))).1.app T) α := by
  -- Route correction: isolate the exact app-level middle-shell comparison still missing from the
  -- source proof. Once this explicit owner-level bridge is available, the outer boundary shell is
  -- already handled by `local_overlap_secondary_boundary_common_owner_shell_eq_local_overlap_conjugation_app`.
  trans (((((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
        (pullHom
          (automorphism_overlap_hom_of_locally_isomorphic_cover
            (𝒮 := 𝒮) hGerbe hAbelian S xS q f₁ f₂)
          g gf₁ gf₂ hgf₁ hgf₂)).1.app T) α)
  · -- First expose the explicit owner `qT := T.unop.hom ≫ K.f` by collapsing the outer shell.
    exact
      automorphism_overlap_hom_pull_middle_component_eq_mapped_inner_pull_app
        (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α
  · -- The remaining app-level transport is precisely the isolated explicit-owner bridge above.
    exact
      automorphism_overlap_hom_mapped_inner_pull_eq_common_owner_shell_app
        (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α

/-- Helper for Lemma 8.11.8: evaluating the normalized `K`-shell at one section of the
secondary cover reduces the remaining transport problem to the explicit owner
`qT := T.unop.hom ≫ K.f`. This is the source-faithful app-level bridge replacing the unstable
sheaf-level q-owner factorization route. -/
theorem automorphism_overlap_hom_pull_middle_component_eq_local_overlap_conjugation_app
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
    ((((((J.pseudofunctorOver (Type (max u v))).mapComp'
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
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))).1.app T) α =
      (((local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom).1.app T) α := by
  -- Route correction: first rewrite the middle evaluated `pullHom` shell to the self-leg
  -- common-owner shell over the explicit owner `qT := T.unop.hom ≫ K.f`.
  trans ((((((J.pseudofunctorOver (Type (max u v))).mapComp'
          gf₁.op.toLoc K.f.op.toLoc (K.f ≫ gf₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₁))) ≫
        (automorphismUnderlyingSheafConj (𝒮 := 𝒮) hAbelian
          (local_overlap_common_owner_isomorphism
            (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂ K.f (𝟙 K.Y)).hom).hom ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
            gf₂.op.toLoc K.f.op.toLoc (K.f ≫ gf₂).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂)))).1.app T) α
  · -- This is the remaining explicit-owner bridge isolated above.
    exact
      automorphism_overlap_hom_pull_middle_component_eq_common_owner_shell_app
        (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α
  · -- Once the middle term is rewritten, the surrounding raw boundary shell is already solved.
    exact
      local_overlap_secondary_boundary_common_owner_shell_eq_local_overlap_conjugation_app
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K T α

/-- Helper for Lemma 8.11.8: after the previous component normalization, the remaining
common-owner shell is exactly the chosen local conjugation map on the `gf₁/gf₂` secondary-cover
arrow `K`. This isolates the last source-faithful common-owner comparison still missing from the
pullback proof. -/
private theorem automorphism_overlap_hom_pull_middle_component_eq_local_overlap_conjugation
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (g : Y' ⟶ Y) (q : Y ⟶ U)
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂).Arrow) :
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
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))) =
    (local_overlap_conjugation_iso
      (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂ K).hom := by
  -- Package the sectionwise shell equality into a sheaf morphism equality.
  apply Sheaf.hom_ext
  ext T α
  exact
    automorphism_overlap_hom_pull_middle_component_eq_local_overlap_conjugation_app
      (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K T α

private theorem automorphism_overlap_hom_pull_middle_eq_secondary_cover_descent
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y' Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (g : Y' ⟶ Y) (q : Y ⟶ U)
    (q' : Y' ⟶ U) (_hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (_hf₁ : f₁ ≫ I₁.f = q) (_hf₂ : f₂ ≫ I₂.f = q)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
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
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I₂))))) =
      (secondary_cover_descent_iso_on_local_overlap
        (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂).hom := by
  -- Route correction: isolate the secondary-cover image of the normalized three-factor shell
  -- before returning to the fixed-cover pullback law. The remaining work is a componentwise
  -- comparison in descent data, proved by `Pseudofunctor.DescentData.hom_ext`.
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  -- Evaluate the descent-data equality on the secondary-cover arrow `K`. The left side is now
  -- the `K.f`-pullback of the normalized three-factor shell, and the right side is the chosen
  -- local conjugation morphism on that same cover leg.
  rw [localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
    (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS gf₁ gf₂)]
  rw [secondary_cover_descent_iso_on_local_overlap_hom_component
    (𝒮 := 𝒮) hGerbe hAbelian S xS gf₁ gf₂]
  -- First normalize the evaluated three-factor shell to the common owner `K.f ≫ g`, then use
  -- the remaining common-owner identification on that owner.
  rw [automorphism_overlap_hom_pull_middle_component_common_owner_normal_form
    (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K]
  rw [automorphism_overlap_hom_pull_middle_component_eq_local_overlap_conjugation
    (𝒮 := 𝒮) hGerbe hAbelian S xS g q f₁ f₂ _hf₁ _hf₂ gf₁ gf₂ hgf₁ hgf₂ K]

/-- Helper for Lemma 8.11.8: the fixed-cover overlap morphism is the identity when the two local
choices agree. This closes the `overlap_self` branch of the source-faithful descent datum. -/
theorem automorphism_cover_overlap_self
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (S : J.Cover U)
    (xS : ∀ I : S.Arrow, 𝒮.p.Fiber I.Y)
    (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian S xS q g g = 𝟙 _ := by
  let T := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS g g
  let E := localizedSheafToCoverDescentEquivalence (J := J) T
  -- Apply the faithful descent functor and use the already-identified image of the overlap map.
  apply Functor.map_injective E.functor
  rw [automorphism_overlap_hom_characterization
    (𝒮 := 𝒮) hGerbe hAbelian S xS q g g (hf₁ := hg) (hf₂ := hg), Functor.map_id]
  -- On the descent-data side, the self-overlap comparison is already the identity.
  exact
    secondary_cover_descent_iso_on_local_overlap_hom_self
      (𝒮 := 𝒮) hGerbe hAbelian S xS g

/-- Helper for Lemma 8.11.8: reconstruct a localized `Type`-valued sheaf from a fixed-cover
descent datum by inverting the Chapter 7 equivalence. -/
private noncomputable def localizedSheafFromCoverDescentData
    {U : C} (S : J.Cover U)
    (D : (J.pseudofunctorOver (Type (max u v))).DescentData (fun I : S.Arrow ↦ I.f)) :
    Sheaf (J.over U) (Type (max u v)) :=
  (localizedSheafToCoverDescentEquivalence (J := J) S).inverse.obj D

/-- Helper for Lemma 8.11.8: an isomorphism of fixed-cover descent data induces an isomorphism of
the reconstructed localized sheaves by applying the inverse half of the Chapter 7 equivalence. -/
private noncomputable def localizedSheafFromCoverDescentData_mapIso
    {U : C} (S : J.Cover U)
    {D₁ D₂ : (J.pseudofunctorOver (Type (max u v))).DescentData (fun I : S.Arrow ↦ I.f)}
    (e : D₁ ≅ D₂) :
    localizedSheafFromCoverDescentData (J := J) S D₁ ≅
      localizedSheafFromCoverDescentData (J := J) S D₂ :=
  -- Route correction: the source proof builds transition and comparison maps on descent data
  -- first, and only afterwards transports them back to sheaves on the localized site.
  (localizedSheafToCoverDescentEquivalence (J := J) S).inverse.mapIso e

/-- Helper for Lemma 8.11.8: the reconstructed localized sheaf carries the canonical comparison
back to the chosen fixed-cover descent datum via the counit of the Chapter 7 equivalence. -/
private noncomputable def localizedSheafFromCoverDescentData_counitIso
    {U : C} (S : J.Cover U)
    (D : (J.pseudofunctorOver (Type (max u v))).DescentData (fun I : S.Arrow ↦ I.f)) :
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj
        (localizedSheafFromCoverDescentData (J := J) S D) ≅ D :=
  (localizedSheafToCoverDescentEquivalence (J := J) S).counitIso.app D

/-- Helper for Lemma 8.11.8: an isomorphism between two explicit cover-descent data objects can
be transported back to an isomorphism of the corresponding localized sheaves by the unit of the
Chapter 7 equivalence. This isolates all later sheaf-side transport away from the structural task
of constructing the descent-data comparison itself. -/
private noncomputable def localizedSheafTransportIsoOfCoverDescentIso
    {U : C} (S : J.Cover U)
    {A B : Sheaf (J.over U) (Type (max u v))}
    (e :
      ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj A ≅
        ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj B) :
    A ≅ B :=
  ((localizedSheafToCoverDescentEquivalence (J := J) S).unitIso.app A) ≪≫
    localizedSheafFromCoverDescentData_mapIso (J := J) S e ≪≫
      ((localizedSheafToCoverDescentEquivalence (J := J) S).unitIso.app B).symm

/-- Helper for Lemma 8.11.8: after transporting a cover-descent isomorphism back to sheaves, the
explicit cover-descent functor sends the resulting sheaf morphism right back to the original
descent morphism. This is the stable rewrite interface for later slice-comparison and transition
packaging. -/
theorem localizedSheafTransportIsoOfCoverDescentIso_functor_map
    {U : C} (S : J.Cover U)
    {A B : Sheaf (J.over U) (Type (max u v))}
    (e :
      ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj A ≅
        ((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : S.Arrow ↦ I.f)).obj B) :
    ((localizedSheafToCoverDescentEquivalence (J := J) S).functor.map
      (localizedSheafTransportIsoOfCoverDescentIso (J := J) S e).hom) =
        e.hom := by
  -- Expand the unit-shell transport once; the equivalence triangle identities contract the
  -- surrounding terms and leave the original descent morphism.
  simp [localizedSheafTransportIsoOfCoverDescentIso, Category.assoc]

/-- Helper for Lemma 8.11.8: once the fixed-cover overlap maps satisfy the descent axioms, invert
the Chapter 7 cover-descent equivalence to obtain the descended slice sheaf together with its
componentwise comparison to the chosen local automorphism sheaves on the cover. -/
private theorem fixed_cover_underlying_automorphism_descent
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
    ∃ FU : Sheaf (J.over U) (Type (max u v)),
      ∀ I : S.Arrow,
        (((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj FU).obj I ≅
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (xS I) := by
  let D :=
    automorphism_cover_descent_datum
      (𝒮 := 𝒮) hAbelian S xS overlap overlap_pull overlap_self overlap_comp
  let FU := localizedSheafFromCoverDescentData (J := J) S D
  let ε := localizedSheafFromCoverDescentData_counitIso (J := J) S D
  refine ⟨FU, ?_⟩
  intro I
  -- Read the counit of the cover-descent equivalence componentwise at the chosen cover arrow.
  refine
    { hom := ε.hom.hom I
      inv := ε.inv.hom I
      hom_inv_id := by
        -- The component inverse law is the descent-data inverse law evaluated at `I`.
        change
          (ε.hom ≫ ε.inv).hom I =
            (((𝟙
                (((J.pseudofunctorOver (Type (max u v))).toDescentData
                  (fun I : S.Arrow ↦ I.f)).obj FU)) :
                (((J.pseudofunctorOver (Type (max u v))).toDescentData
                  (fun I : S.Arrow ↦ I.f)).obj FU) ⟶
                  (((J.pseudofunctorOver (Type (max u v))).toDescentData
                    (fun I : S.Arrow ↦ I.f)).obj FU)).hom I)
        exact congrArg (fun ψ ↦ ψ.hom I) ε.hom_inv_id
      inv_hom_id := by
        -- The reverse component inverse law is extracted from the descent-data counit as well.
        change
          (ε.inv ≫ ε.hom).hom I =
            (((𝟙 D) : D ⟶ D).hom I)
        exact congrArg (fun ψ ↦ ψ.hom I) ε.inv_hom_id }

/-- Helper for Lemma 8.11.8: once the fixed-cover pullback and composition laws are available for
the chosen gerbe cover of `U`, the chosen local automorphism sheaves descend to a single sheaf on
the slice site `C / U`. This isolates the source proof's Step 3 from the later global absolute
glueing and comparison packaging. -/
theorem chosen_cover_underlying_automorphism_descent
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C)
    (overlap_pull : ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
      ⦃I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
      (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
      (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
      pullHom
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)
        g gf₁ gf₂ =
      automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q' gf₁ gf₂ := by
        cat_disch)
    (overlap_comp : ∀ ⦃Y : C⦄ (q : Y ⟶ U)
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
        cat_disch) :
    ∃ FU : Sheaf (J.over U) (Type (max u v)),
      ∀ I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow,
        (((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj FU).obj I ≅
          automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I) := by
  let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U
  let xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U
  -- Step 3 of the source proof is now a direct specialization of the generic fixed-cover descent.
  simpa [S, xS] using
    (fixed_cover_underlying_automorphism_descent
      (𝒮 := 𝒮) hAbelian S xS
      (overlap := automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian S xS)
      (overlap_pull := overlap_pull)
      (overlap_self := automorphism_cover_overlap_self
        (𝒮 := 𝒮) hGerbe hAbelian S xS)
      (overlap_comp := overlap_comp))

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` descends the local underlying
automorphism sheaves to one sheaf on `C / U` once the fixed-cover overlap pullback law is
available. -/
theorem automorphism_cover_overlap_pull
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U : C} :
    ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
      ⦃I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow⦄
      (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
      (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
      (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
      (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
      pullHom
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)
        g gf₁ gf₂ =
      automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q' gf₁ gf₂ := by
  intro Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  let T' := local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) gf₁ gf₂
  let E' := localizedSheafToCoverDescentEquivalence (J := J) T'
  -- Route correction: after `map_injective`, the fixed-cover pullback law reduces to the one
  -- secondary-cover transport identity isolated above, followed by the already-proved
  -- characterization of overlap morphisms on the pulled legs.
  apply Functor.map_injective E'.functor
  rw [automorphism_overlap_hom_pull_mapped_normal_form
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  rw [automorphism_overlap_hom_pull_middle_eq_secondary_cover_descent
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
  symm
  exact
    automorphism_overlap_hom_characterization
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      q' gf₁ gf₂

/-- Helper for Lemma 8.11.8: the fixed chosen gerbe cover of `U` satisfies the cocycle law for
the overlap morphisms between local underlying automorphism sheaves. -/
theorem chosen_cover_overlap_map_to_secondary_cover_descent
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
      ((((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≫
          (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
            (automorphism_overlap_hom_of_locally_isomorphic_cover
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
          (((J.pseudofunctorOver (Type (max u v))).mapComp'
              f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
              (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂))))) =
      (secondary_cover_descent_iso_on_local_overlap
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).hom := by
  -- Specialize the generic pullback-to-secondary-cover comparison to the fixed chosen gerbe cover.
  exact
    automorphism_overlap_hom_pull_middle_eq_secondary_cover_descent
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      K.f q (K.f ≫ q) rfl f₁ f₂ hf₁ hf₂ (K.f ≫ f₁) (K.f ≫ f₂) rfl rfl

/-- Helper for Lemma 8.11.8: after passing one chosen-cover overlap morphism to the secondary
cover, each component is already the chosen local conjugation map on that same secondary-cover
arrow. This is the component-level normalization used in the mixed-cover comparison. -/
theorem chosen_cover_overlap_map_to_secondary_cover_descent_component
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) {U Y : C}
    (q : Y ⟶ U)
    {I₁ I₂ I₃ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) f₁ f₃).Arrow) :
    ∀ L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂)).Arrow,
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (K.f ≫ f₁) (K.f ≫ f₂))).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).mapComp'
            f₁.op.toLoc K.f.op.toLoc (K.f ≫ f₁).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁))) ≫
            (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (automorphism_overlap_hom_of_locally_isomorphic_cover
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q f₁ f₂)) ≫
            (((J.pseudofunctorOver (Type (max u v))).mapComp'
                f₂.op.toLoc K.f.op.toLoc (K.f ≫ f₂).op.toLoc
                (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂)))))).hom L =
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (K.f ≫ f₁) (K.f ≫ f₂) L).hom := by
  intro L
  -- Evaluate the already-proved secondary-cover normalization on the fixed arrow `L`.
  have hcomponent :=
    congrArg (fun ψ ↦ ψ.hom L)
      (chosen_cover_overlap_map_to_secondary_cover_descent
        (𝒮 := 𝒮) hGerbe hAbelian q f₁ f₂ f₃ hf₁ hf₂ K)
  -- The descent comparison component is definitionally the chosen local conjugation on `L`.
  simpa [secondary_cover_descent_iso_on_local_overlap_hom_component]
    using hcomponent

end CategoryTheory

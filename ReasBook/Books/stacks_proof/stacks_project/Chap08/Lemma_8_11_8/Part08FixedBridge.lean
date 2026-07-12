import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap08.Lemma_8_11_8.Part08BaseComponent
import StacksProject_2024.Chap08.Lemma_8_11_8.Part08AssemblyBridges

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] canonicalPullbackChoice

private theorem mapComp'_inv_app_eq_mapComp_fixed {B : Type*} [Bicategory B]
    [Bicategory.Strict B] (F : Pseudofunctor B Cat)
    {b₀ b₁ b₂ : B} {a : b₀ ⟶ b₁} {b : b₁ ⟶ b₂}
    {c : b₀ ⟶ b₂} {w : a ≫ b = c} {X : (F.obj b₀)} :
    (F.mapComp' a b c w).inv.toNatTrans.app X =
      (F.mapComp a b).inv.toNatTrans.app X ≫ eqToHom (by rw [w]) := by
  subst w
  simp only [Pseudofunctor.mapComp'_eq_mapComp, eqToHom_refl, Category.comp_id]

private theorem mapComp'_hom_app_eq_mapComp_fixed {B : Type*} [Bicategory B]
    [Bicategory.Strict B] (F : Pseudofunctor B Cat)
    {b₀ b₁ b₂ : B} {a : b₀ ⟶ b₁} {b : b₁ ⟶ b₂}
    {c : b₀ ⟶ b₂} {w : a ≫ b = c} {X : (F.obj b₀)} :
    (F.mapComp' a b c w).hom.toNatTrans.app X =
      eqToHom (by rw [w]) ≫ (F.mapComp a b).hom.toNatTrans.app X := by
  subst w
  simp only [Pseudofunctor.mapComp'_eq_mapComp, eqToHom_refl, Category.id_comp]

private theorem cover_cancel_fixed {D1 D2 D3 D4 : Type*} [Category D1]
    [Category D2] [Category D3] [Category D4]
    (Ga : Functor D1 D2) (Gb : Functor D2 D3) (Gc : Functor D3 D4)
    {a b c : D1} (e : a ≅ b) (z : b ⟶ c) :
    Gc.map (Gb.map (Ga.map e.inv)) ≫ Gc.map (Gb.map (Ga.map e.hom ≫ Ga.map z)) =
      Gc.map (Gb.map (Ga.map z)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp]

private theorem natiso_conj_fixed {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] {Fa : Functor C₁ C₃} {H : Functor C₁ C₂} {G : Functor C₂ C₃}
    (α : Fa ≅ H ⋙ G) {X Y : C₁} (f : X ⟶ Y) {Z : C₃}
    (rest : Fa.obj Y ⟶ Z) :
    α.hom.app X ≫ (H ⋙ G).map f ≫ α.inv.app Y ≫ rest = Fa.map f ≫ rest := by
  slice_lhs 1 3 => rw [NatIso.naturality_2]

private theorem assemble_mid_fixed {D : Type*} [Category D] {O0 O1 O2 O3 O4 O7 : D}
    {p1 : O0 ⟶ O1} {p2 : O1 ⟶ O2} {M1 : O2 ⟶ O3} {M2 : O3 ⟶ O4}
    {M34 : O4 ⟶ O2} {suf : O2 ⟶ O7} (hmid : M1 ≫ M2 ≫ M34 = 𝟙 O2) :
    p1 ≫ p2 ≫ M1 ≫ M2 ≫ M34 ≫ suf = p1 ≫ p2 ≫ suf := by
  rw [reassoc_of% hmid]

private theorem assemble_hT_fixed {D : Type*} [Category D] {O0 O1 O2 O3 O4 O5 O6 : D}
    {a : O0 ⟶ O1} {b : O1 ⟶ O2} {m : O2 ⟶ O3} {ci : O3 ⟶ O4}
    {ch : O4 ⟶ O5} {ac : O5 ⟶ O6} {cl' : O3 ⟶ O5} {lo : O0 ⟶ O6}
    (hcov : ci ≫ ch = cl') (hfull : a ≫ b ≫ m ≫ cl' ≫ ac = lo) :
    (a ≫ b ≫ m ≫ ci) ≫ ch ≫ ac = lo := by
  rw [← hfull, ← hcov]
  simp only [Category.assoc]

private theorem assemble_right_fixed {D : Type*} [Category D] {O0 O2 O3 O4 O5 O6 : D}
    {a : O0 ⟶ O2} {s : O2 ⟶ O0} {cj : O0 ⟶ O3} {t : O3 ⟶ O4}
    {fl : O4 ⟶ O5} {ci : O5 ⟶ O6} {lo : O3 ⟶ O6}
    (hS : a ≫ s = 𝟙 O0) (hT : t ≫ fl ≫ ci = lo) :
    cj ≫ lo ≫ 𝟙 O6 = a ≫ ((s ≫ cj ≫ t) ≫ fl) ≫ ci := by
  rw [Category.comp_id, ← hT]
  simp only [Category.assoc]
  rw [← Category.assoc a s, hS, Category.id_comp]

private theorem cancel_two_iso_prefix_after_fixed {D : Type*} [Category D] {X A B C H : D}
    (p : X ⟶ A) (e₁ : A ≅ B) (e₂ : B ≅ C) {tail : A ⟶ H} :
    p ≫ tail = p ≫ e₁.hom ≫ e₂.hom ≫ ((e₂.inv ≫ e₁.inv) ≫ tail) := by
  simp [Category.assoc]

private theorem finish_fixed_bridge {D : Type*} [Category D] {X A B C E F G : D}
    {p : X ⟶ A} {ch : A ⟶ B} {cmid : B ⟶ C} (e : E ≅ C)
    {lc : A ⟶ F} {lt : F ⟶ E} {s : C ⟶ G}
    (h : ch ≫ cmid ≫ e.inv = lc ≫ lt) :
    (p ≫ ch) ≫ cmid ≫ s = p ≫ lc ≫ lt ≫ e.hom ≫ s := by
  calc
    (p ≫ ch) ≫ cmid ≫ s = p ≫ (ch ≫ cmid ≫ e.inv) ≫ e.hom ≫ s := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = p ≫ (lc ≫ lt) ≫ e.hom ≫ s := by
      rw [h]
    _ = p ≫ lc ≫ lt ≫ e.hom ≫ s := by
      simp only [Category.assoc]

private theorem pullback_cover_target_secondary_cover_right_component_decompose_fixed
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (assembly_local_overlap_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) =
    ((assembly_chosen_to_local_overlap_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L ≫
      (assembly_clai_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) := by
  have hid : (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) = 𝟙 _ := by
    rw [local_overlap_target_secondary_transition_normalize
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base)
      (K.f ≫ g₁) (K.f ≫ g₂) (q := L.f) (𝟙 L.Y) (𝟙 L.Y)]
    simpa [Cat.Hom.toNatIso] using
      Iso.inv_hom_id_app (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)))
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₂ := I₂.base) (K.f ≫ g₂))
  rw [hid]
  rw [pullback_cover_target_secondary_cover_right_branch_exposed
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L]
  rw [pullback_cover_target_secondary_cover_middle_component_as_conjugation
    (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂ K L]
  refine assemble_right_fixed ?hS ?hT
  case hS =>
    have w₁ : g₁.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₁).op.toLoc := by
      simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    erw [← srcmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (cov := (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).hom)
        g₁ K.f L.f w₁]
    rw [Iso.hom_comp_eq_id]
    rw [mapComp'_inv_app_eq_mapComp_fixed (J.pseudofunctorOver (Type (max u v)))]
    simp only [assembly_chosen_to_local_overlap_source_bridge,
      assembly_clai_source_to_ssdd_bridge, assembly_ssdd_to_local_overlap_source_bridge,
      Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, op_comp, Quiver.Hom.comp_toLoc,
      eqToHom_refl, Category.comp_id, Iso.inv_hom_id_assoc]
    rfl
  case hT =>
    have w₂ : g₂.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₂).op.toLoc := by
      simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    simp only [localizedSheafToCoverDescentEquivalence_functor_map_component,
      Iso.trans_inv, Functor.mapIso_inv]
    erw [← tgtmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (cinv := (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).inv)
        g₂ K.f L.f w₂]
    refine assemble_hT_fixed (cover_cancel_fixed _ _ _
      (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)
      ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) ?hfull
    rw [mapComp'_hom_app_eq_mapComp_fixed (J.pseudofunctorOver (Type (max u v)))]
    simp only [assembly_clai_target_to_tsdd_bridge, assembly_local_overlap_target_to_tsdd_bridge,
      Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc, eqToHom_map, op_comp, Quiver.Hom.comp_toLoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    have hinner :
        ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
            ((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc)).app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))).inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map (g₂.op.toLoc ≫ K.f.op.toLoc)).toFunctor.map
                (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv = 𝟙 _ := by
      erw [natiso_conj_fixed (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc))
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom]
      erw [← Functor.map_comp]
      simp
    have hmid :
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
            (((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc).hom.toNatTrans.app
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base))) ≫
          ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
                (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) ≫
            ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
              (((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc)).app
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))).inv ≫
                ((J.pseudofunctorOver (Type (max u v))).map (g₂.op.toLoc ≫ K.f.op.toLoc)).toFunctor.map
                  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv) = 𝟙 _ := by
      erw [← Functor.map_comp, ← Functor.map_comp]
      rw [hinner]
      simp
    exact assemble_mid_fixed hmid

private theorem pullback_cover_y_transition_chosen_middle_rhs_assembly_bridge_fixed
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    ((assembly_chosen_to_local_overlap_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂) (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁]) (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map (chosen_cover_underlying_automorphism_sheaf_cover_iso (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)))).hom K)).hom L ≫
      (assembly_clai_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) =
    (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (assembly_local_overlap_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) := by
  exact (pullback_cover_target_secondary_cover_right_component_decompose_fixed
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L).symm

private theorem pullback_cover_y_transition_chosen_middle_fixed
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
  (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
      (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ hg₁ hg₂
  =
  ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
    (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
      (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
      (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
      (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom ≫
    (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv := by
  have huncancelled :=
    to_chosen_middle_descent_base_component_square_api
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂
  simpa [Category.assoc, ← Functor.map_comp] using
    congrArg
      (fun f ↦
        ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv ≫ f)
      huncancelled

/-- Fixed-`(K,L)` varying-base bridge API for Lemma 8.11.8: once the abstract
`toDescentData (fun I => I.f)` middle component is transported through the target
`assembly_clai_target_to_ssdd_bridge`, it is the local-overlap conjugation component followed by
the descent-target bridge. -/
theorem pullback_cover_target_secondary_cover_fixed_bridge_normalization_api
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂).Arrow)
    (L : (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
              r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L =
      ((assembly_clai_target_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (assembly_ssdd_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_descent_to_local_overlap_target_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv)) := by
  have hmiddle :=
    congrArg
      (fun f ↦
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
              (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
          (((localizedSheafToCoverDescentEquivalence (J := J)
              (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
                (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map f).hom K)).hom L))
      (pullback_cover_y_transition_chosen_middle_fixed
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂)
  refine hmiddle.trans ?_
  let a := ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv
  let b := ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv
  let c :=
    (chosen_cover_descent_datum (𝒮 := 𝒮) hGerbe hAbelian U).hom
      (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q) (f₁ := g₁) (f₂ := g₂)
      (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
      (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom
  let d :=
    (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv
  let Φ :
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)) ⟶
        ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.obj
          ((((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).obj I₂)) → _ := fun f ↦
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map f).hom K)).hom L)
  change
    Φ (a ≫ b ≫ c ≫ d) =
      ((assembly_clai_target_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (assembly_ssdd_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_descent_to_local_overlap_target_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv)
  dsimp only [Φ]
  erw [Functor.map_comp]
  erw [Functor.map_comp]
  erw [Functor.map_comp]
  erw [Functor.map_comp]
  erw [Functor.map_comp]
  erw [Functor.map_comp]
  let A := (((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map a).hom K)).hom L)
  let B := (((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map b).hom K)).hom L)
  let Cmid := (((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map c).hom K)).hom L)
  let Dtail := (((localizedSheafToCoverDescentEquivalence (J := J)
      (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂))).functor.map
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂)).functor.map d).hom K)).hom L)
  change
    A ≫ B ≫ Cmid ≫ Dtail =
      ((assembly_clai_target_to_ssdd_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (assembly_ssdd_to_local_overlap_source_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
        (local_overlap_conjugation_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
        (assembly_descent_to_local_overlap_target_bridge
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv)
  let P :=
    (assembly_clai_target_to_ssdd_bridge
      (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
    (assembly_ssdd_to_local_overlap_source_bridge
      (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom
  let Ch := (assembly_chosen_to_local_overlap_source_bridge
    (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom
  have hAB : A ≫ B = P ≫ Ch := by
    dsimp only [A, B, P, Ch, a, b]
    simp only [localizedSheafToCoverDescentEquivalence_functor_map_component,
      assembly_clai_target_to_ssdd_bridge, assembly_chosen_to_local_overlap_source_bridge,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc]
    exact cancel_two_iso_prefix_after_fixed _
      (assembly_clai_source_to_ssdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L)
      (assembly_ssdd_to_local_overlap_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L)
  let E := assembly_clai_target_to_tsdd_bridge
    (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L
  let LC := (local_overlap_conjugation_iso
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom
  let LT := (assembly_local_overlap_target_to_tsdd_bridge
    (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom
  let S := ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y).inv))
  have hDtail : Dtail = S := by
    dsimp only [Dtail, d, S]
    simp only [localizedSheafToCoverDescentEquivalence_functor_map_component,
      Functor.mapIso_inv]
    rfl
  have hid :
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) = 𝟙 _ := by
    rw [local_overlap_target_secondary_transition_normalize
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (I₁ := I₁.base) (I₂ := I₂.base)
      (K.f ≫ g₁) (K.f ≫ g₂) (q := L.f) (𝟙 L.Y) (𝟙 L.Y)]
    simpa [Cat.Hom.toNatIso] using
      Iso.inv_hom_id_app (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)))
        (local_overlap_target_secondary_sheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) (I₂ := I₂.base) (K.f ≫ g₂))
  have hC : Ch ≫ Cmid ≫ E.inv = LC ≫ LT := by
    dsimp only [Ch, Cmid, E, LC, LT, c]
    simpa only [hid, Category.assoc, Category.comp_id] using
      pullback_cover_y_transition_chosen_middle_rhs_assembly_bridge_fixed
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  slice_lhs 1 2 => rw [hAB]
  rw [hDtail]
  simp only [assembly_descent_to_local_overlap_target_bridge,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  change (P ≫ Ch) ≫ Cmid ≫ S = P ≫ LC ≫ LT ≫ E.hom ≫ S
  exact finish_fixed_bridge E hC

end

end CategoryTheory

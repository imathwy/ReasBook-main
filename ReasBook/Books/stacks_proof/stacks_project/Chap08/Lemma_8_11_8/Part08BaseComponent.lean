import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.Chap08.Lemma_8_11_8.CoherenceAPI
import StacksProject_2024.Chap08.Lemma_8_11_8.Part08BaseFixedBridge

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

/-- Tiny category adapter: insert an adjacent `inv ≫ hom` pair after a fixed prefix. -/
private theorem insert_iso_inv_hom {D : Type*} [Category D]
    {A B C E : D} (p : A ⟶ B) (e : C ≅ B) (tail : B ⟶ E) :
    p ≫ tail = p ≫ e.inv ≫ e.hom ≫ tail := by
  simp

/-- Tiny category adapter: replace a prefix ending in `e.inv` by a named source prefix, then
expose the cancelling `e.hom` in front of the remaining tail. -/
private theorem replace_iso_inv_tail {D : Type*} [Category D]
    {A B C E : D} {p : A ⟶ B} {rhs : A ⟶ C} (e : C ≅ B) {tail : B ⟶ E}
    (h : rhs = p ≫ e.inv) :
    p ≫ tail = rhs ≫ e.hom ≫ tail := by
  rw [h]
  simp [Category.assoc]

/-- Tiny category adapter for the source-transition normal form: replace a two-step prefix ending
in `e.inv` by a named source prefix, then expose the cancelling `e.hom` before the tail. -/
private theorem replace_iso_inv_tail₂ {D : Type*} [Category D]
    {A B C E F : D} {p : A ⟶ B} {q : B ⟶ C} {rhs : A ⟶ E}
    (e : E ≅ C) {tail : C ⟶ F}
    (h : rhs = p ≫ q ≫ e.inv) :
    p ≫ q ≫ tail = rhs ≫ e.hom ≫ tail := by
  rw [h]
  simp [Category.assoc]

/-- Abstract assembler for the local-object transition square: once the source transition has
normalized the pullback-cover shell and the residual `cover_iso.inv ≫ cover_iso.hom` is known to
cancel, the target-side branch gives the desired local-object component square. -/
private theorem assemble_local_object_transition {D : Type*} [Category D]
    {O0 O1 O2 O3 O4 O5 : D}
    (dpull : O0 ⟶ O1) (ps : O1 ⟶ O2) (ciInv : O2 ⟶ O3) (ciHom : O3 ⟶ O2)
    (cl : O2 ⟶ O4) (bcInv : O4 ⟶ O5)
    (hc : ciInv ≫ ciHom = 𝟙 O2) :
    (dpull ≫ ps ≫ ciInv) ≫ ciHom ≫ cl ≫ bcInv = dpull ≫ ps ≫ cl ≫ bcInv := by
  rw [Category.assoc, Category.assoc, ← Category.assoc ciInv, hc, Category.id_comp]

/-- Tiny category adapter: expose a raw middle morphism by inserting `inv ≫ hom` pairs on both
sides. -/
private theorem wrap_two_iso_cancel {D : Type*} [Category D] {A A' B B' F : D}
    (e₁ : B ≅ A) (e₂ : B' ≅ A') (m : A ⟶ A') (tail : A' ⟶ F) :
    m ≫ tail = e₁.inv ≫ (e₁.hom ≫ m ≫ e₂.inv) ≫ e₂.hom ≫ tail := by
  simp [Category.assoc]

/-- Tiny category adapter: cancel the two `inv ≫ hom` shells around a middle morphism after a
fixed prefix. -/
private theorem cancel_two_iso_shells_after_prefix {D : Type*} [Category D]
    {X A A' B B' F : D} (p : X ⟶ A) (e₁ : B ≅ A) (e₂ : B' ≅ A')
    (m : A ⟶ A') (tail : A' ⟶ F) :
    p ≫ e₁.inv ≫ (e₁.hom ≫ m ≫ e₂.inv) ≫ e₂.hom ≫ tail =
      p ≫ m ≫ tail := by
  simp [Category.assoc]

/-- Tiny functorial adapter: after three functor layers, cancel an adjacent `hom ≫ inv` pair
before a fixed tail. -/
private theorem cancel_three_functor_iso_hom_inv_tail
    {D₁ D₂ D₃ D₄ : Type*} [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    (F : D₁ ⥤ D₂) (G : D₂ ⥤ D₃) (H : D₃ ⥤ D₄)
    {A B : D₁} {E : D₂} (e : A ≅ B) (tail : F.obj A ⟶ E) :
    H.map (G.map (F.map e.hom)) ≫ H.map (G.map (F.map e.inv ≫ tail)) =
      H.map (G.map tail) := by
  rw [← H.map_comp, ← G.map_comp, ← Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, Category.id_comp]

/-- Tiny category adapter: reassociate a five-step composite after a head rewrite. -/
private theorem reassoc_five {D : Type*} [Category D] {A B C E F G : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ F) (e : F ⟶ G) :
    ((a ≫ b ≫ c) ≫ d ≫ e) = a ≫ b ≫ c ≫ d ≫ e := by
  simp [Category.assoc]

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

/-- Local name for the chosen-cover overlap descent datum.  This exposes the counit
compatibility used to rewrite one `chosen_cover_descent_datum` transition into the raw overlap
map, without importing later Part08/Part09 files. -/
private noncomputable def chosen_cover_overlap_descent_datum_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :
    (J.pseudofunctorOver (Type (max u v))).DescentData
      (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f) :=
  automorphism_cover_descent_datum (𝒮 := 𝒮) hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (fun {_Y} _q {_I₁ _I₂} f₁ f₂ ↦
      let S := chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U
      let xS := chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U
      let E :=
        localizedSheafToCoverDescentEquivalence (J := J)
          (local_overlap_isomorphism_cover (𝒮 := 𝒮) hGerbe S xS f₁ f₂)
      (E.unitIso.app (local_overlap_source_secondary_sheaf
        (𝒮 := 𝒮) hAbelian S xS f₁)).hom ≫
        E.inverse.map
          (secondary_cover_descent_iso_on_local_overlap
            (𝒮 := 𝒮) hGerbe hAbelian S xS f₁ f₂).hom ≫
        (E.unitIso.app (local_overlap_target_secondary_sheaf
          (𝒮 := 𝒮) hAbelian S xS f₂)).inv)
    (automorphism_cover_overlap_pull (𝒮 := 𝒮) hGerbe hAbelian (U := U))
    (fun {_Y} q {_I} g hg ↦
      automorphism_cover_overlap_self (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g hg)
    (automorphism_cover_overlap_comp (𝒮 := 𝒮) hGerbe hAbelian)

/-- Local counit for `chosen_cover_overlap_descent_datum_base`. -/
private noncomputable def chosen_cover_overlap_descent_datum_counitIso_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮) (U : C) :
    ((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow ↦ I.f)).obj
      (chosen_cover_underlying_automorphism_sheaf (𝒮 := 𝒮) hGerbe hAbelian U) ≅
      chosen_cover_overlap_descent_datum_base (𝒮 := 𝒮) hGerbe hAbelian U :=
  localizedSheafFromCoverDescentData_counitIso (J := J)
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_cover_overlap_descent_datum_base (𝒮 := 𝒮) hGerbe hAbelian U)

/-- Counit square exposing one chosen-cover overlap transition. -/
private theorem chosen_cover_descent_datum_overlap_component_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (q : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = q := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = q := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom ≫
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂) =
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂)).hom := by
  exact (chosen_cover_overlap_descent_datum_counitIso_base
    (𝒮 := 𝒮) hGerbe hAbelian U).hom.comm q g₁ g₂ hg₁ hg₂

/-- Raw overlap normal form for `chosen_cover_descent_datum`. -/
private theorem chosen_cover_descent_datum_overlap_raw_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (q : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = q := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = q := by cat_disch) :
    (chosen_cover_descent_datum
      (𝒮 := 𝒮) hGerbe hAbelian U).hom q g₁ g₂ =
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁)).hom ≫
        (automorphism_overlap_hom_of_locally_isomorphic_cover
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U) q g₁ g₂) ≫
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂)).inv := by
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv _).mpr
    (chosen_cover_descent_datum_overlap_component_base
      (𝒮 := 𝒮) hGerbe hAbelian q g₁ g₂ hg₁ hg₂).symm

/-- Named left side of the target `y` tail comparison. -/
private noncomputable abbrev pullback_cover_y_tail_left_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :=
  (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂
        (_hf₁ := hg₁) (_hf₂ := hg₂))

/-- Named right side of the target `y` tail comparison. -/
private noncomputable abbrev pullback_cover_y_tail_right_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :=
  (automorphism_overlap_hom_of_locally_isomorphic_cover
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂
      (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
      (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂])) ≫
    ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
      ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
    (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv

/-- Fixed-`(K,L)` left-branch normal form for the target `y` tail. -/
private theorem pullback_cover_y_tail_left_exposed_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
        (pullback_cover_y_tail_left_base
          (𝒮 := 𝒮) hGerbe hAbelian q y r
          (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂)).hom K)).hom L) =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_refinement_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (pullback_cover_y_tail_overlap_cover_base
              (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
              (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L) ≫
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_refinement_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (pullback_cover_y_tail_overlap_cover_base
              (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
          ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso
              (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
            (((J.pseudofunctorOver (Type (max u v))).toDescentData
                (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
              (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
                r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) := by
  exact pullback_cover_target_secondary_cover_left_branch_exposed
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L

/-- Morphism-level right-branch normal form: expose the raw overlap as its chosen-local tail. -/
private theorem pullback_cover_y_tail_right_overlap_tail_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    pullback_cover_y_tail_right_base
      (𝒮 := 𝒮) hGerbe hAbelian q y r
      (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂ =
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian g₁
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (local_overlap_source_object
          (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) g₁)
        (local_overlap_target_object
          (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₂ := I₂.base) g₂)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian g₂
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv := by
  dsimp [pullback_cover_y_tail_right_base]
  rw [automorphism_overlap_hom_eq_chosen_local_tail
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂
    (by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
    (by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂])]
  exact reassoc_five _ _ _ _ _

/-- RHS assembly bridge for the chosen-cover middle tail, independent of the base fixed bridge. -/
private theorem pullback_cover_target_secondary_cover_right_component_decompose_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    (local_overlap_conjugation_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (assembly_local_overlap_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) =
    ((assembly_chosen_to_local_overlap_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom
              (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q)
              (f₁ := g₁) (f₂ := g₂)
              (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
              (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫
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
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
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
        (cov := (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).hom)
        g₁ K.f L.f w₁]
    rw [Iso.hom_comp_eq_id]
    rw [mapComp'_inv_app_eq_mapComp_fixed (J.pseudofunctorOver (Type (max u v)))]
    simp only [assembly_chosen_to_local_overlap_source_bridge,
      assembly_clai_source_to_ssdd_bridge, assembly_ssdd_to_local_overlap_source_bridge,
      Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Iso.trans_hom,
      Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Category.assoc, op_comp, Quiver.Hom.comp_toLoc, eqToHom_refl,
      Category.comp_id, Iso.inv_hom_id_assoc]
    rfl
  case hT =>
    have w₂ : g₂.op.toLoc ≫ K.f.op.toLoc = (K.f ≫ g₂).op.toLoc := by
      simp [← Quiver.Hom.comp_toLoc, ← op_comp]
    simp only [localizedSheafToCoverDescentEquivalence_functor_map_component,
      Iso.trans_inv, Functor.mapIso_inv]
    erw [← tgtmerge (𝒮 := 𝒮) hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (cinv := (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).inv)
        g₂ K.f L.f w₂]
    refine assemble_hT_fixed (cover_cancel_fixed _ _ _
      (chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U I₂.base)
      ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
        (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom)) ?hfull
    rw [mapComp'_hom_app_eq_mapComp_fixed (J.pseudofunctorOver (Type (max u v)))]
    simp only [assembly_clai_target_to_tsdd_bridge, assembly_local_overlap_target_to_tsdd_bridge,
      Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv]
    simp only [Functor.map_comp, Category.assoc, op_comp, Quiver.Hom.comp_toLoc,
      eqToHom_refl, Category.id_comp]
    have hinner :
        ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc).hom.toNatTrans.app
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)) ≫
          ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map
              (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
            ((Cat.Hom.toNatIso
              ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc)).app
                (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))).inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map
                (g₂.op.toLoc ≫ K.f.op.toLoc)).toFunctor.map
                (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv = 𝟙 _ := by
      erw [natiso_conj_fixed
          (Cat.Hom.toNatIso
            ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc))
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
              (((Cat.Hom.toNatIso
                ((J.pseudofunctorOver (Type (max u v))).mapComp g₂.op.toLoc K.f.op.toLoc)).app
                  (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y))).inv ≫
                ((J.pseudofunctorOver (Type (max u v))).map
                  (g₂.op.toLoc ≫ K.f.op.toLoc)).toFunctor.map
                  (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
                    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                    (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv) = 𝟙 _ := by
      erw [← Functor.map_comp, ← Functor.map_comp]
      rw [hinner]
      simp
    exact assemble_mid_fixed hmid

private theorem pullback_cover_y_transition_chosen_middle_rhs_assembly_bridge_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    ((assembly_chosen_to_local_overlap_source_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      ((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (pullback_cover_y_tail_overlap_cover_base
              (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
          ((chosen_cover_descent_datum
            (𝒮 := 𝒮) hGerbe hAbelian U).hom
              (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q)
              (f₁ := g₁) (f₂ := g₂)
              (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
              (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]) ≫
            (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
              (chosen_cover_underlying_automorphism_sheaf_cover_iso
                (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom) ≫
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
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂) L).hom ≫
      (assembly_local_overlap_target_to_tsdd_bridge
        (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
      (local_overlap_target_secondary_descent_data
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) := by
  exact (pullback_cover_target_secondary_cover_right_component_decompose_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L).symm

/-- Source-secondary self-leg normal form used by the fixed `(K,L)` source boundary. -/
private theorem pullback_cover_y_source_boundary_self_leg_normalize_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    (local_overlap_source_secondary_descent_data
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
      (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) =
      (((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)).inv.toNatTrans.app
        (local_overlap_source_secondary_sheaf
          (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (K.f ≫ g₁))) ≫
        (((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)).hom.toNatTrans.app
          (local_overlap_source_secondary_sheaf
            (𝒮 := 𝒮) hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (K.f ≫ g₁))) :=
  local_overlap_source_secondary_transition_normalize
    (𝒮 := 𝒮) hGerbe hAbelian
    (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
    (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
    (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)
    (q := L.f) (K₁ := L) (K₂ := L) (𝟙 L.Y) (𝟙 L.Y)
    (Category.id_comp L.f) (Category.id_comp L.f)

/-- Fixed `(K,L)` normal form for the source chosen-local boundary. -/
private theorem pullback_cover_y_source_boundary_component_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    ((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom))).hom K)).hom L =
        ((assembly_clai_source_to_ssdd_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).hom ≫
          (local_overlap_source_secondary_descent_data
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
            (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
            L.f (𝟙 L.Y) (𝟙 L.Y) ≫
          (assembly_clai_target_to_ssdd_bridge
            (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) := by
  have hid :
      (local_overlap_source_secondary_descent_data
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (I₂ := I₂.base) (K.f ≫ g₁) (K.f ≫ g₂)).hom
        L.f (𝟙 L.Y) (𝟙 L.Y) = 𝟙 _ := by
    rw [pullback_cover_y_source_boundary_self_leg_normalize_base
      (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ K L]
    simpa [Cat.Hom.toNatIso] using
      Iso.inv_hom_id_app (Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          L.f.op.toLoc (𝟙 L.Y).op.toLoc L.f.op.toLoc (by cat_disch)))
        (local_overlap_source_secondary_sheaf (𝒮 := 𝒮) hAbelian
          (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) (K.f ≫ g₁))
  rw [hid, Category.id_comp,
    localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K) _ L,
    localizedSheafToCoverDescentEquivalence_functor_map_component (J := J)
      (pullback_cover_y_tail_overlap_cover_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂) _ K]
  simp only [assembly_clai_target_to_ssdd_bridge, Iso.trans_inv, Functor.mapIso_inv,
    Iso.symm_inv]
  exact (Iso.hom_inv_id_assoc _ _).symm

private theorem pullback_cover_y_transition_chosen_middle_rhs_normalization_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
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
          (automorphismUnderlyingSheafBaseChangeIso
            (𝒮 := 𝒮) hAbelian I₂.f y)).inv)).hom K)).hom L) =
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
          (𝒮 := 𝒮) hGerbe hAbelian q y g₁ g₂ K L).inv) := by
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
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map f).hom K)).hom L)
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
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map a).hom K)).hom L)
  let B := (((localizedSheafToCoverDescentEquivalence (J := J)
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map b).hom K)).hom L)
  let Cmid := (((localizedSheafToCoverDescentEquivalence (J := J)
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map c).hom K)).hom L)
  let Dtail := (((localizedSheafToCoverDescentEquivalence (J := J)
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map d).hom K)).hom L)
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
      pullback_cover_y_transition_chosen_middle_rhs_assembly_bridge_base
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  slice_lhs 1 2 => rw [hAB]
  rw [hDtail]
  simp only [assembly_descent_to_local_overlap_target_bridge,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  change (P ≫ Ch) ≫ Cmid ≫ S = P ≫ LC ≫ LT ≫ E.hom ≫ S
  exact finish_fixed_bridge E hC

/-- Base morphism comparison with the chosen-cover middle transition exposed.  This isolates the
only non-adapter bridge needed before the raw chosen-cover overlap cancels the cover isomorphism
shells. -/
private theorem pullback_cover_y_transition_chosen_middle_refined_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso
              (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
              r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
        (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
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
          (automorphismUnderlyingSheafBaseChangeIso
            (𝒮 := 𝒮) hAbelian I₂.f y)).inv)).hom K)).hom L) := by
  exact (pullback_cover_y_transition_fixed_bridge_normalization_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L).trans
    (pullback_cover_y_transition_chosen_middle_rhs_normalization_base
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L).symm

/-- Base morphism comparison with the chosen-cover middle transition exposed, recovered from the
fixed `(K,L)` component bridge by two applications of cover-descent faithfulness. -/
private theorem pullback_cover_y_transition_chosen_middle_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂ hg₁ hg₂) =
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
  haveI :
      (localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (pullback_cover_y_tail_overlap_cover_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂)).faithful
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (pullback_cover_y_tail_overlap_cover_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  haveI :
      (localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).faithful
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro L
  exact pullback_cover_y_transition_chosen_middle_refined_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L

/-- Base morphism form of the target `y` tail after cancelling the leading chosen-local
comparison.  This is the small non-component interface behind
`pullback_cover_y_tail_transition_component_base`. -/
private theorem pullback_cover_y_tail_transition_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso
          (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
          r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂)) =
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
        (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv) ≫
      pullback_cover_y_tail_right_base
        (𝒮 := 𝒮) hGerbe hAbelian q y r
        (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂ := by
  rw [pullback_cover_y_transition_chosen_middle_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂]
  rw [chosen_cover_descent_datum_overlap_raw_base
    (𝒮 := 𝒮) hGerbe hAbelian (r ≫ q)
      (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂
      (by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
      (by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂])]
  dsimp [pullback_cover_y_tail_right_base]
  simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using
    cancel_two_iso_shells_after_prefix
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv)
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁.base))
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂.base))
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom ≫
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)

/-- Fixed-`(K,L)` transition form of the target `y` tail.  This is the component-level
interface left after the leading chosen-local comparison is cancelled in
`pullback_cover_y_tail_over_chosen_overlap_refined_base`. -/
private theorem pullback_cover_y_tail_transition_component_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
      ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso
            (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
        (((J.pseudofunctorOver (Type (max u v))).toDescentData
            (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
            r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K) =
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          ((chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
            (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv) ≫
        ((automorphismUnderlyingSheafBaseChangeIso
            (𝒮 := 𝒮) hAbelian g₁
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)).hom ≫
          (chosen_local_automorphism_iso
            (𝒮 := 𝒮) hGerbe hAbelian
            (local_overlap_source_object
              (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (I₁ := I₁.base) g₁)
            (local_overlap_target_object
              (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
              (I₂ := I₂.base) g₂)).hom ≫
          (automorphismUnderlyingSheafBaseChangeIso
            (𝒮 := 𝒮) hAbelian g₂
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)).inv ≫
          ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
            ((chosen_local_automorphism_iso
              (𝒮 := 𝒮) hGerbe hAbelian
              (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
              (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
          ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
            (automorphismUnderlyingSheafBaseChangeIso
              (𝒮 := 𝒮) hAbelian I₂.f y).inv))).hom K) := by
  have hbase := pullback_cover_y_tail_transition_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂
  rw [pullback_cover_y_tail_right_overlap_tail_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂] at hbase
  simpa only [localizedSheafToCoverDescentEquivalence_functor_map_component, Functor.map_comp,
    Functor.mapIso_inv, Category.assoc] using
    congrArg
      (fun m ↦
        ((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor.map m)
      hbase

/-- Fixed-`(K,L)` transition form of the target `y` tail.  The second refinement is now
pure functorial transport of the `K`-component transition. -/
private theorem pullback_cover_y_tail_transition_refined_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
        ((((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
            (automorphismUnderlyingSheafBaseChangeIso
              (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
          (((J.pseudofunctorOver (Type (max u v))).toDescentData
              (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
            (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
              r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))).hom K)).hom L) =
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_refinement_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
        (((localizedSheafToCoverDescentEquivalence (J := J)
            (pullback_cover_y_tail_overlap_cover_base
              (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
          (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
              ((chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
                (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).inv) ≫
            ((automorphismUnderlyingSheafBaseChangeIso
                (𝒮 := 𝒮) hAbelian g₁
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)).hom ≫
              (chosen_local_automorphism_iso
                (𝒮 := 𝒮) hGerbe hAbelian
                (local_overlap_source_object
                  (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                  (I₁ := I₁.base) g₁)
                (local_overlap_target_object
                  (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
                  (I₂ := I₂.base) g₂)).hom ≫
              (automorphismUnderlyingSheafBaseChangeIso
                (𝒮 := 𝒮) hAbelian g₂
                (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)).inv ≫
              ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                ((chosen_local_automorphism_iso
                  (𝒮 := 𝒮) hGerbe hAbelian
                  (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
                  (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
              ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
                (automorphismUnderlyingSheafBaseChangeIso
                  (𝒮 := 𝒮) hAbelian I₂.f y).inv))).hom K)).hom L) := by
  simpa only [localizedSheafToCoverDescentEquivalence_functor_map_component] using
    congrArg
      (fun m ↦
        ((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor.map m)
      (pullback_cover_y_tail_transition_component_base
        (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K)

/-- Fixed-`(K,L)` component form of the target `y` tail comparison.  This is the intentionally
small remaining interface: all outer descent/functor transport has already been evaluated. -/
private theorem pullback_cover_y_tail_over_chosen_overlap_refined_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow)
    (L : (pullback_cover_y_tail_overlap_refinement_base
      (𝒮 := 𝒮) hGerbe q g₁ g₂ K).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
        (pullback_cover_y_tail_left_base
          (𝒮 := 𝒮) hGerbe hAbelian q y r
          (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂)).hom K)).hom L) =
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.map
      (((localizedSheafToCoverDescentEquivalence (J := J)
          (pullback_cover_y_tail_overlap_cover_base
            (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
        (pullback_cover_y_tail_right_base
          (𝒮 := 𝒮) hGerbe hAbelian q y r
          (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂)).hom K)).hom L) := by
  rw [pullback_cover_y_tail_left_exposed_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L]
  rw [pullback_cover_y_tail_right_overlap_tail_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂]
  have htail := pullback_cover_y_tail_transition_refined_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L
  rw [htail]
  exact cancel_three_functor_iso_hom_inv_tail
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor)
    (((J.pseudofunctorOver (Type (max u v))).map K.f.op.toLoc).toFunctor)
    (((J.pseudofunctorOver (Type (max u v))).map L.f.op.toLoc).toFunctor)
    (chosen_local_automorphism_iso
      (𝒮 := 𝒮) hGerbe hAbelian
      (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
      (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y))
    ((automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian g₁
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)).hom ≫
      (chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (local_overlap_source_object
          (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₁ := I₁.base) g₁)
        (local_overlap_target_object
          (𝒮 := 𝒮) (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
          (I₂ := I₂.base) g₂)).hom ≫
      (automorphismUnderlyingSheafBaseChangeIso
        (𝒮 := 𝒮) hAbelian g₂
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)).inv ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso
          (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        (automorphismUnderlyingSheafBaseChangeIso
          (𝒮 := 𝒮) hAbelian I₂.f y).inv)

/-- One local-overlap component of the target `y` tail comparison. -/
private theorem pullback_cover_y_tail_over_chosen_overlap_component_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch)
    (K : (pullback_cover_y_tail_overlap_cover_base (𝒮 := 𝒮) hGerbe q g₁ g₂).Arrow) :
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
      (pullback_cover_y_tail_left_base
        (𝒮 := 𝒮) hGerbe hAbelian q y r
        (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂)).hom K) =
    (((localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.map
      (pullback_cover_y_tail_right_base
        (𝒮 := 𝒮) hGerbe hAbelian q y r
        (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂)).hom K) := by
  haveI :
      (localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_refinement_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).faithful
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (pullback_cover_y_tail_overlap_refinement_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂ K)).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro L
  exact pullback_cover_y_tail_over_chosen_overlap_refined_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K L

/-- Base morphism form of the target `y` tail comparison, proved by descending to the
local-overlap component API. -/
private theorem pullback_cover_y_tail_over_chosen_overlap_base_api
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    pullback_cover_y_tail_left_base
      (𝒮 := 𝒮) hGerbe hAbelian q y r
      (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂ =
    pullback_cover_y_tail_right_base
      (𝒮 := 𝒮) hGerbe hAbelian q y r
      (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂ := by
  haveI :
      (localizedSheafToCoverDescentEquivalence (J := J)
        (pullback_cover_y_tail_overlap_cover_base
          (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor.Faithful :=
    (localizedSheafToCoverDescentFullyFaithful (J := J)
      (pullback_cover_y_tail_overlap_cover_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂)).faithful
  apply Functor.map_injective
    (localizedSheafToCoverDescentEquivalence (J := J)
      (pullback_cover_y_tail_overlap_cover_base
        (𝒮 := 𝒮) hGerbe q g₁ g₂)).functor
  apply Pseudofunctor.DescentData.hom_ext
  intro K
  exact pullback_cover_y_tail_over_chosen_overlap_component_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂ K

/-- Named morphism-level target `y` tail comparison, proved by local-overlap descent. -/
private theorem pullback_cover_y_tail_over_chosen_overlap_named_base
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    pullback_cover_y_tail_left_base
      (𝒮 := 𝒮) hGerbe hAbelian q y r
      (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂ =
    pullback_cover_y_tail_right_base
      (𝒮 := 𝒮) hGerbe hAbelian q y r
      (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂ := by
  exact pullback_cover_y_tail_over_chosen_overlap_base_api
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂

/-- Component-level blocker behind the target tail: after moving the `y` transition through the
left chosen-local comparison, the result is the raw chosen-cover overlap followed by the right
chosen-local/base-change tail. -/
private theorem pullback_cover_y_tail_over_chosen_overlap_api
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂
          (_hf₁ := hg₁) (_hf₂ := hg₂)) =
    (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂])) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv := by
  change
    pullback_cover_y_tail_left_base
      (𝒮 := 𝒮) hGerbe hAbelian q y r
      (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂ =
    pullback_cover_y_tail_right_base
      (𝒮 := 𝒮) hGerbe hAbelian q y r
      (I₁ := I₁) (I₂ := I₂) g₁ g₂ hg₁ hg₂
  exact pullback_cover_y_tail_over_chosen_overlap_named_base
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂

/-- Target-side component API for the pullback-cover local-object comparison.

This is the remaining small interface behind `pullback_cover_local_object_component_transition_api`:
after the pullback-cover source shell has been removed, the chosen-local/base-change/descent tail
is the chosen-cover transition followed by the target chosen-local/base-change tail. -/
private theorem pullback_cover_target_component_transition_api
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch) (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom r g₁ g₂
          (_hf₁ := hg₁) (_hf₂ := hg₂)) =
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
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
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv) := by
  have htail := pullback_cover_y_tail_over_chosen_overlap_api
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂
  rw [chosen_cover_descent_datum_overlap_raw_base
    (𝒮 := 𝒮) hGerbe hAbelian (r ≫ q)
      (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂
      (by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
      (by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂])]
  rw [htail]
  simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using
    wrap_two_iso_cancel
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₁.base))
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂.base))
      (automorphism_overlap_hom_of_locally_isomorphic_cover
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U)
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U)
        (r ≫ q) (I₁ := I₁.base) (I₂ := I₂.base) g₁ g₂
        (_hf₁ := by change g₁ ≫ (I₁.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₁])
        (_hf₂ := by change g₂ ≫ (I₂.f ≫ q) = r ≫ q; rw [← Category.assoc, hg₂]))
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)

/-- Component-level naturality API for the local-object comparison on the pullback cover.

This is the small missing interface behind the base component square: the comparison
`pullback_cover_local_object_component_iso` should commute with the pullback-cover transition
before the chosen-cover source component is cancelled. -/
private theorem pullback_cover_local_object_component_transition_api
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((pullback_cover_local_object_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y I₁).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
          r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂) =
    (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
      ((J.overMapPullback (Type (max u v)) q).obj
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U))).hom
        r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂) ≫
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
        ((pullback_cover_local_object_component_iso
          (𝒮 := 𝒮) hGerbe hAbelian q y I₂).hom) := by
  have htarget := pullback_cover_target_component_transition_api
    (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂
  have hsource := pullback_cover_source_component_transition
    (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂
  rw [Functor.mapIso_inv, Functor.mapIso_inv] at htarget
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp] at hsource
  simp only [pullback_cover_local_object_component_iso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  erw [htarget, reassoc_of% hsource]
  have hcancel :
      ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).inv ≫
        ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₂.base).hom = 𝟙 _ := by
    rw [← Functor.map_comp]
    simp
  exact assemble_local_object_transition _ _ _ _ _ _ hcancel

/-- Local component API for Part08: the base `toDescentData (· .f)` transition rewritten into
the chosen-cover normal form before any `(K,L)` secondary-cover assembly is introduced. -/
theorem to_chosen_middle_descent_base_component_square_api
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (q : Y ⟶ U) (y : 𝒮.p.Fiber Y)
    {Z : C} (r : Z ⟶ Y)
    {I₁ I₂ : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = r := by cat_disch)
    (hg₂ : g₂ ≫ I₂.f = r := by cat_disch) :
    ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₁.base)
          (I₁.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₁.f y)).inv ≫
      (((J.pseudofunctorOver (Type (max u v))).toDescentData
        (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
        (automorphismUnderlyingSheaf (𝒮 := 𝒮) hAbelian y)).hom
          r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂) =
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
        ((chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
          (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
          (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom) ≫
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv := by
  apply comp_left_eq_of_iso
    (((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.mapIso
      (pullback_cover_source_component_iso (𝒮 := 𝒮) hGerbe hAbelian q I₁))
  have hlocal :=
    pullback_cover_local_object_component_transition_api
      (𝒮 := 𝒮) hGerbe hAbelian q y r g₁ g₂ hg₁ hg₂
  have hsct :=
    pullback_cover_source_component_transition
      (𝒮 := 𝒮) hGerbe hAbelian q r g₁ g₂ hg₁ hg₂
  simp only [pullback_cover_local_object_component_iso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc] at hlocal
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] at hsct
  simp only [Functor.mapIso_hom, Functor.mapIso_inv]
  erw [hlocal]
  simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using
    replace_iso_inv_tail₂
      (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
        (chosen_cover_underlying_automorphism_sheaf_cover_iso
          (𝒮 := 𝒮) hGerbe hAbelian U I₂.base))
      (p :=
        (((J.pseudofunctorOver (Type (max u v))).toDescentData
          (fun I : (chosen_cover_pullback_cover (𝒮 := 𝒮) hGerbe q).Arrow ↦ I.f)).obj
          ((J.overMapPullback (Type (max u v)) q).obj
            (chosen_cover_underlying_automorphism_sheaf
              (𝒮 := 𝒮) hGerbe hAbelian U))).hom
            r g₁ g₂ (_hf₁ := hg₁) (_hf₂ := hg₂))
      (q :=
        ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
          (pullback_cover_source_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian q I₂).hom)
      (rhs :=
        ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          (pullback_cover_source_component_iso
            (𝒮 := 𝒮) hGerbe hAbelian q I₁).hom ≫
        ((J.pseudofunctorOver (Type (max u v))).map g₁.op.toLoc).toFunctor.map
          (chosen_cover_underlying_automorphism_sheaf_cover_iso
            (𝒮 := 𝒮) hGerbe hAbelian U I₁.base).inv ≫
        (chosen_cover_descent_datum
          (𝒮 := 𝒮) hGerbe hAbelian U).hom
          (i₁ := I₁.base) (i₂ := I₂.base) (q := r ≫ q)
          (f₁ := g₁) (f₂ := g₂)
          (_hf₁ := by
            have h₁ : g₁ ≫ I₁.f = r := hg₁
            simp only [GrothendieckTopology.Cover.Arrow.base_f]
            exact (reassoc_of% h₁) q)
          (_hf₂ := by
            have h₂ : g₂ ≫ I₂.f = r := hg₂
            simp only [GrothendieckTopology.Cover.Arrow.base_f]
            exact (reassoc_of% h₂) q))
      (tail :=
        ((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.map
          (chosen_local_automorphism_iso (𝒮 := 𝒮) hGerbe hAbelian
            (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U I₂.base)
            (I₂.f ^*[canonicalPullbackChoice 𝒮.p] y)).hom ≫
        (((J.pseudofunctorOver (Type (max u v))).map g₂.op.toLoc).toFunctor.mapIso
          (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian I₂.f y)).inv)
      hsct

end

end CategoryTheory

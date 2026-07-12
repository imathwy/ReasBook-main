import StacksProject_2024.Chap08.Lemma_8_11_8.Part11.CommonOwnerFrontier

universe u v w

namespace CategoryTheory

open StackInGroupoidsOver
open Opposite
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {𝒮 : StackInGroupoidsOver J}

/-- Helper for Lemma 8.11.8: the pure sheaf-over-site identity triangle.  Composing the
`overMapPullbackComp f (𝟙 U)` comparison with the congruence `(f ≫ 𝟙 U) = f` gives the pullback
of the canonical `overMapPullbackId` comparison. -/
theorem overMapPullbackComp_hom_congr_comp_id
    {U V : C} (f : V ⟶ U)
    (F : Sheaf (J.over U) (Type (max u v))) :
    ((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).app F).hom ≫
        ((J.overMapPullbackCongr (Type (max u v))
          (by simp : f ≫ 𝟙 U = f)).app F).hom =
      ((J.overMapPullback (Type (max u v)) f).map
        (((J.overMapPullbackId (Type (max u v)) U).app F).hom)) := by
  have h := congrArg (fun η => η.app F)
    (J.overMapPullback_comp_id (Type (max u v)) f)
  have h' :
      (J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).inv.app F ≫
          ((J.overMapPullback (Type (max u v)) f).map
            (((J.overMapPullbackId (Type (max u v)) U).app F).hom)) =
        (J.overMapPullbackCongr (Type (max u v))
          (by simp : f ≫ 𝟙 U = f)).hom.app F := by
    simpa only [NatTrans.comp_app, Functor.comp_obj, Functor.id_obj, Category.comp_id] using h
  -- `h` says `comp.inv ≫ map(overMapPullbackId) = congr`; cancel `comp.hom`.
  change
    ((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).hom.app F) ≫
        ((J.overMapPullbackCongr (Type (max u v))
          (by simp : f ≫ 𝟙 U = f)).hom.app F) =
      ((J.overMapPullback (Type (max u v)) f).map
        (((J.overMapPullbackId (Type (max u v)) U).app F).hom))
  rw [← h']
  change
    ((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).app F).hom ≫
        ((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).app F).inv ≫
          ((J.overMapPullback (Type (max u v)) f).map
            (((J.overMapPullbackId (Type (max u v)) U).app F).hom)) =
      ((J.overMapPullback (Type (max u v)) f).map
        (((J.overMapPullbackId (Type (max u v)) U).app F).hom))
  rw [Iso.hom_inv_id_assoc]

theorem overMapPullbackComp_hom_congr_comp_id_assoc
    {U V : C} (f : V ⟶ U)
    (F : Sheaf (J.over U) (Type (max u v)))
    {G : Sheaf (J.over V) (Type (max u v))}
    (a : (J.overMapPullback (Type (max u v)) f).obj F ⟶ G) :
    (((J.overMapPullbackComp (Type (max u v)) f (𝟙 U)).app F).hom ≫
        ((J.overMapPullbackCongr (Type (max u v))
          (by simp : f ≫ 𝟙 U = f)).app F).hom) ≫ a =
      ((J.overMapPullback (Type (max u v)) f).map
        (((J.overMapPullbackId (Type (max u v)) U).app F).hom)) ≫ a := by
  rw [overMapPullbackComp_hom_congr_comp_id]
  rfl

/-- Helper for Lemma 8.11.8: changing only the propositional equality carried by a
chosen-cover arrow transports the standard cover/local-object/base-change tail by the
corresponding `overMapPullbackCongr` component. Keeping the two arrow records explicit avoids
rewriting under `chosen_gerbe_cover_object`. -/
private theorem chosen_cover_component_tail_congr
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (f₀ f₁ : Y ⟶ U) (h01 : f₀ = f₁)
    (h₀ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) f₀)
    (h₁ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) f₁)
    (x : 𝒮.p.Fiber U) :
    ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U ⟨Y, f₀, h₀⟩).hom) ≫
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U ⟨Y, f₀, h₀⟩)
        (f₁ ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁ x).inv =
    ((J.overMapPullbackCongr (Type (max u v)) h01).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).hom ≫
      ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U ⟨Y, f₁, h₁⟩).hom) ≫
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U ⟨Y, f₁, h₁⟩)
        (f₁ ^*[canonicalPullbackChoice 𝒮.p] x)).hom) ≫
      (automorphismUnderlyingSheafBaseChangeIso (𝒮 := 𝒮) hAbelian f₁ x).inv := by
  cases h01
  have hp : h₀ = h₁ := Subsingleton.elim _ _
  cases hp
  simp [GrothendieckTopology.overMapPullbackCongr_eq_eqToIso]
  rfl

/-- Helper for Lemma 8.11.8: changing only the propositional equality carried by a
chosen-cover arrow transports the standard cover/local-object tail by the corresponding
`overMapPullbackCongr` component. This is the local-object form without the final base-change
tail. -/
private theorem chosen_cover_component_tail_congr_local
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Y : C} (f₀ f₁ : Y ⟶ U) (h01 : f₀ = f₁)
    (h₀ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) f₀)
    (h₁ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U) f₁)
    (z : 𝒮.p.Fiber U) :
    ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U ⟨Y, f₀, h₀⟩).hom) ≫
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U ⟨Y, f₀, h₀⟩)
        (f₁ ^*[canonicalPullbackChoice 𝒮.p] z)).hom) =
    ((J.overMapPullbackCongr (Type (max u v)) h01).app
        (chosen_cover_underlying_automorphism_sheaf
          (𝒮 := 𝒮) hGerbe hAbelian U)).hom ≫
      ((chosen_cover_underlying_automorphism_sheaf_cover_iso
        (𝒮 := 𝒮) hGerbe hAbelian U ⟨Y, f₁, h₁⟩).hom) ≫
      ((chosen_local_automorphism_iso
        (𝒮 := 𝒮) hGerbe hAbelian
        (chosen_gerbe_cover_object (𝒮 := 𝒮) hGerbe U ⟨Y, f₁, h₁⟩)
        (f₁ ^*[canonicalPullbackChoice 𝒮.p] z)).hom) := by
  cases h01
  have hp : h₀ = h₁ := Subsingleton.elim _ _
  cases hp
  simp [GrothendieckTopology.overMapPullbackCongr_eq_eqToIso]
  rfl

/-- Helper for Lemma 8.11.8: move an `overMapPullbackCongr` through the outer pullback
`mapComp'` inverse. -/
private theorem overMapPullbackCongr_mapComp'_inv
    {U V Z : C} {f₀ f₁ : V ⟶ U} (h01 : f₀ = f₁)
    (g : Z ⟶ V)
    (G : Sheaf (J.over U) (Type (max u v))) :
    (((Cat.Hom.toNatIso
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₀.op.toLoc g.op.toLoc (g ≫ f₀).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).inv) ≫
      ((J.overMapPullbackCongr (Type (max u v))
        (by rw [h01] : g ≫ f₀ = g ≫ f₁)).hom.app G) =
    ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((J.overMapPullbackCongr (Type (max u v)) h01).hom.app G) ≫
      (((Cat.Hom.toNatIso
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).inv) := by
  cases h01
  simp [GrothendieckTopology.overMapPullbackCongr_eq_eqToIso]
  have hmap :
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
          (𝟙 ((J.overMapPullback (Type (max u v)) f₀).obj G)) =
        𝟙 _ := by
    exact Functor.map_id _ _
  rw [hmap]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Helper for Lemma 8.11.8: associative form of
`overMapPullbackCongr_mapComp'_inv`, for rewriting the identity-pullback source shell inside a
longer telescope. -/
private theorem overMapPullbackCongr_mapComp'_inv_assoc
    {U V Z : C} {f₀ f₁ : V ⟶ U} (h01 : f₀ = f₁)
    (g : Z ⟶ V)
    (G : Sheaf (J.over U) (Type (max u v)))
    {H : Sheaf (J.over Z) (Type (max u v))}
    (a : ((J.overMapPullback (Type (max u v)) (g ≫ f₁)).obj G) ⟶ H) :
    ((((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₀.op.toLoc g.op.toLoc (g ≫ f₀).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).inv) ≫
      ((J.overMapPullbackCongr (Type (max u v))
        (by rw [h01] : g ≫ f₀ = g ≫ f₁)).hom.app G)) ≫ a =
    (((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((J.overMapPullbackCongr (Type (max u v)) h01).hom.app G) ≫
      (((Cat.Hom.toNatIso ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).inv)) ≫ a := by
  rw [overMapPullbackCongr_mapComp'_inv (J := J) h01 g G]
  rfl

/-- Helper for Lemma 8.11.8: cancelling the two `mapComp'` boundaries around an equality of
inner legs leaves exactly the pulled `overMapPullbackCongr` component. -/
private theorem overMapPullback_mapComp'_inv_hom_congr
    {U V Z : C} {f₀ f₁ : V ⟶ U} (h01 : f₀ = f₁)
    (g : Z ⟶ V)
    (G : Sheaf (J.over U) (Type (max u v))) :
    (((Cat.Hom.toNatIso
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₀.op.toLoc g.op.toLoc (g ≫ f₀).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).inv) ≫
      (((Cat.Hom.toNatIso
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc g.op.toLoc (g ≫ f₀).op.toLoc
          (by
            rw [← h01]
            simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).hom) =
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
      ((J.overMapPullbackCongr (Type (max u v)) h01).hom.app G) := by
  cases h01
  simp [GrothendieckTopology.overMapPullbackCongr_eq_eqToIso]
  exact
    (Cat.Hom.inv_hom_id_toNatTrans_app
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₀.op.toLoc g.op.toLoc (f₀.op.toLoc ≫ g.op.toLoc)
        (by rfl)) G).trans (Functor.map_id _ _).symm

/-- Helper for Lemma 8.11.8: associative form of
`overMapPullback_mapComp'_inv_hom_congr`, for cancelling an identity-source `mapComp'` pair
inside a longer owner telescope. -/
theorem overMapPullback_mapComp'_inv_hom_congr_assoc
    {U V Z : C} {f₀ f₁ : V ⟶ U} (h01 : f₀ = f₁)
    (g : Z ⟶ V)
    (G : Sheaf (J.over U) (Type (max u v)))
    {H : Sheaf (J.over Z) (Type (max u v))}
    (a : ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.obj
        ((J.overMapPullback (Type (max u v)) f₁).obj G) ⟶ H) :
    ((((Cat.Hom.toNatIso
      ((J.pseudofunctorOver (Type (max u v))).mapComp'
        f₀.op.toLoc g.op.toLoc (g ≫ f₀).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).inv) ≫
      (((Cat.Hom.toNatIso
        ((J.pseudofunctorOver (Type (max u v))).mapComp'
          f₁.op.toLoc g.op.toLoc (g ≫ f₀).op.toLoc
          (by
            rw [← h01]
            simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app G).hom)) ≫ a =
      ((J.pseudofunctorOver (Type (max u v))).map g.op.toLoc).toFunctor.map
        ((J.overMapPullbackCongr (Type (max u v)) h01).hom.app G) ≫ a := by
  rw [overMapPullback_mapComp'_inv_hom_congr (J := J) h01 g G]
  rfl

/-- Helper for Lemma 8.11.8: the hom and inverse components of the same `mapComp'` cancel even
when their composite-equality witnesses were produced by different tactics. -/
@[reassoc]
private theorem mapComp'_hom_inv_id_toNatTrans_app_of_witness_part11
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
`mapComp'_hom_inv_id_toNatTrans_app_of_witness_part11`. -/
@[reassoc]
private theorem mapComp'_inv_hom_id_toNatTrans_app_of_witness_part11
    {B : Type*} [Bicategory B] [Bicategory.Strict B]
    (F : Pseudofunctor B Cat) {b₀ b₁ b₂ : B}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) {k : b₀ ⟶ b₂}
    (w w' : f ≫ g = k) (X : F.obj b₀) :
    (F.mapComp' f g k w).inv.toNatTrans.app X ≫
      (F.mapComp' f g k w').hom.toNatTrans.app X = 𝟙 _ := by
  have hw : w = w' := Subsingleton.elim _ _
  cases hw
  exact Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' f g k w) X

/-- Part11-local form of the counit compatibility for the chosen-cover overlap descent datum. -/
private theorem chosen_cover_descent_datum_overlap_component_part11
    (hGerbe : IsGerbe J 𝒮.p) (hAbelian : HasAbelianAutomorphismSheaves 𝒮)
    {U Z : C} (q : Z ⟶ U)
    {I₁ I₂ : (chosen_gerbe_cover (𝒮 := 𝒮) hGerbe U).Arrow}
    (g₁ : Z ⟶ I₁.Y) (g₂ : Z ⟶ I₂.Y)
    (hg₁ : g₁ ≫ I₁.f = q := by cat_disch) (hg₂ : g₂ ≫ I₂.f = q := by cat_disch) :
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
  exact (chosen_cover_overlap_descent_datum_counitIso_part11
    (𝒮 := 𝒮) hGerbe hAbelian U).hom.comm q g₁ g₂ hg₁ hg₂

end CategoryTheory

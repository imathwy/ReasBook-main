import StacksProject_2024.Chap21.SiteAbelianDerived
import StacksProject_2024.Chap21.Lemma_21_7_3.Comparison

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory

namespace Sheaf

variable {C : Type u} [Category.{max u v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]
variable [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]

/- The left-exactness clause in Lemma 21.10.5 is already the canonical owner instance on the
inclusion `sheafToPresheaf`. -/
section

variable (p : ℕ)

#synth PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{max u v})

end

/-- Helper for Lemma 21.10.5: morphisms from the free abelian representable presheaf on `U`
identify with sections over `U`. -/
private noncomputable def freeAbelianRepresentableHomEquivSections
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) ≃ P.obj (op U) :=
  ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv

/-- Helper for Lemma 21.10.5: postcomposition on morphisms from the free abelian representable
presheaf is evaluation of the target morphism on the corresponding section. -/
private theorem freeAbelianRepresentableHomEquivSections_comp
    {U : C} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (f : ((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) (η : P ⟶ Q) :
    freeAbelianRepresentableHomEquivSections U Q (f ≫ η) =
      η.app (op U) (freeAbelianRepresentableHomEquivSections U P f) := by
  -- Proof comment: unfold the free/forget and Yoneda bridges, then use their standard
  -- right-naturality formulas.
  change
    yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) (f ≫ η)) =
      η.app (op U) (yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) f))
  have hcomp :
      ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) (f ≫ η) =
        (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) f) ≫
          ((Functor.whiskeringRight Cᵒᵖ AddCommGrpCat (Type (max u v))).obj
            (forget AddCommGrpCat)).map η := by
    simpa using
      (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_right f η
  rw [hcomp]
  simpa using
      (yonedaEquiv_comp
        (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) f)
        (((Functor.whiskeringRight Cᵒᵖ AddCommGrpCat (Type (max u v))).obj
        (forget AddCommGrpCat)).map η))

/-- Helper for Lemma 21.10.5: the free abelian representable/sections equivalence sends the zero
morphism to the zero section. -/
private theorem freeAbelianRepresentableHomEquivSections_zero
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    freeAbelianRepresentableHomEquivSections U P
        (0 : ((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) = 0 := by
  -- Proof comment: evaluate the zero target map on the identity generator of the representable.
  let G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} := (yoneda.obj U) ⋙ AddCommGrpCat.free
  calc
    freeAbelianRepresentableHomEquivSections U P (0 : G ⟶ P) =
        (0 : G ⟶ P).app (op U)
          (freeAbelianRepresentableHomEquivSections U G (𝟙 G)) := by
            simpa [G] using
              (freeAbelianRepresentableHomEquivSections_comp
                (P := G) (Q := P) (𝟙 G) (0 : G ⟶ P))
    _ = 0 := by
      change (0 : G.obj (op U) ⟶ P.obj (op U))
          (freeAbelianRepresentableHomEquivSections U G (𝟙 G)) = 0
      rfl

/-- Helper for Lemma 21.10.5: the free abelian representable/sections equivalence is additive. -/
private theorem freeAbelianRepresentableHomEquivSections_add
    {U : C} {P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (a b : ((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) :
    freeAbelianRepresentableHomEquivSections U P (a + b) =
      freeAbelianRepresentableHomEquivSections U P a +
        freeAbelianRepresentableHomEquivSections U P b := by
  -- Proof comment: compose the identity generator with `a + b`, then use pointwise addition on
  -- the target section group.
  let G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} := (yoneda.obj U) ⋙ AddCommGrpCat.free
  calc
    freeAbelianRepresentableHomEquivSections U P (a + b) =
        (a + b).app (op U) (freeAbelianRepresentableHomEquivSections U G (𝟙 G)) := by
            simpa [G] using
              (freeAbelianRepresentableHomEquivSections_comp
                (P := G) (Q := P) (𝟙 G) (a + b))
    _ = a.app (op U) (freeAbelianRepresentableHomEquivSections U G (𝟙 G)) +
          b.app (op U) (freeAbelianRepresentableHomEquivSections U G (𝟙 G)) := by
            change ((a.app (op U)) + (b.app (op U)))
                (freeAbelianRepresentableHomEquivSections U G (𝟙 G)) =
              a.app (op U) (freeAbelianRepresentableHomEquivSections U G (𝟙 G)) +
                b.app (op U) (freeAbelianRepresentableHomEquivSections U G (𝟙 G))
            rfl
    _ = freeAbelianRepresentableHomEquivSections U P (𝟙 G ≫ a) +
          freeAbelianRepresentableHomEquivSections U P (𝟙 G ≫ b) := by
            rw [← freeAbelianRepresentableHomEquivSections_comp (P := G) (Q := P) (𝟙 G) a]
            rw [← freeAbelianRepresentableHomEquivSections_comp (P := G) (Q := P) (𝟙 G) b]
    _ = freeAbelianRepresentableHomEquivSections U P a +
          freeAbelianRepresentableHomEquivSections U P b := by
            rw [Category.id_comp, Category.id_comp]

/-- Helper for Lemma 21.10.5: the free abelian representable/sections equivalence upgrades to an
additive equivalence. -/
private noncomputable def freeAbelianRepresentableHomAddEquivSections
    (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) ≃+ P.obj (op U) where
  toEquiv := freeAbelianRepresentableHomEquivSections U P
  map_add' := freeAbelianRepresentableHomEquivSections_add

/-- Helper for Lemma 21.10.5: the additive free-representable/sections equivalence turns
postcomposition into evaluation of the target map on the corresponding section. -/
private theorem freeAbelianRepresentableHomAddEquivSections_comp
    {U : C} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (g : ((yoneda.obj U) ⋙ AddCommGrpCat.free) ⟶ P) (η : P ⟶ Q) :
    freeAbelianRepresentableHomAddEquivSections U Q (g ≫ η) =
      η.app (op U) (freeAbelianRepresentableHomAddEquivSections U P g) := by
  -- Proof comment: the additive wrapper has the same underlying function as the earlier
  -- equivalence, so the composition formula is unchanged.
  exact freeAbelianRepresentableHomEquivSections_comp g η

/-- Helper for Lemma 21.10.5: the sheafified free abelian representable on `U`, which is the
canonical source object for the owner `Ext` description of `H^p(U, -)`. -/
private abbrev freeAbelianRepresentableSheaf
    (U : C) : Sheaf J AddCommGrpCat.{max u v} :=
  (presheafToSheaf J AddCommGrpCat.{max u v}).obj ((yoneda.obj U) ⋙ AddCommGrpCat.free)

/-- Helper for Lemma 21.10.5: sections over `U` identify additively with morphisms from the
sheafified free abelian representable on `U`. -/
private noncomputable def siteAbelianSectionsAddEquivRepresentableFreeHom
    (U : C) (F : Sheaf J AddCommGrpCat.{max u v}) :
    ((siteAbelianSectionsFunctor J U).obj F) ≃+
      (freeAbelianRepresentableSheaf (J := J) U ⟶ F) :=
  -- Proof comment: first recover a presheaf morphism from the section, then move it across the
  -- sheafification adjunction.
  ((freeAbelianRepresentableHomAddEquivSections U F.1).symm).trans
    ((sheafificationAdjunction J AddCommGrpCat.{max u v}).homAddEquiv _ F).symm

omit [HasExt (Sheaf J AddCommGrpCat.{max u v})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: the additive sections/representable-free comparison is natural in
the sheaf variable. -/
private theorem freeAbelianRepresentableHomAddEquivSections_map_naturality
    {U : C} {F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G)
    (x : (siteAbelianSectionsFunctor J U).obj F) :
    freeAbelianRepresentableHomAddEquivSections U G.1
        (((freeAbelianRepresentableHomAddEquivSections U F.1).symm x) ≫ f.1) =
      (siteAbelianSectionsFunctor J U).map f x := by
  -- Proof comment: specialize the postcomposition formula to the representative corresponding to
  -- `x`, so the right-hand side becomes evaluation of `f` on that section.
  calc
    freeAbelianRepresentableHomAddEquivSections U G.1
        (((freeAbelianRepresentableHomAddEquivSections U F.1).symm x) ≫ f.1) =
      f.1.app (op U)
        (freeAbelianRepresentableHomAddEquivSections U F.1
          ((freeAbelianRepresentableHomAddEquivSections U F.1).symm x)) := by
            exact
              freeAbelianRepresentableHomAddEquivSections_comp
                ((freeAbelianRepresentableHomAddEquivSections U F.1).symm x) f.1
    _ = (siteAbelianSectionsFunctor J U).map f x := by
      rw [(freeAbelianRepresentableHomAddEquivSections U F.1).apply_symm_apply]
      rfl

omit [HasExt (Sheaf J AddCommGrpCat.{max u v})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: the additive sections/representable-free comparison is natural in
the sheaf variable. -/
private theorem siteAbelianSectionsAddEquivRepresentableFreeHom_naturality
    {U : C} {F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G)
    (x : (siteAbelianSectionsFunctor J U).obj F) :
    siteAbelianSectionsAddEquivRepresentableFreeHom (J := J) U G
        ((siteAbelianSectionsFunctor J U).map f x) =
      siteAbelianSectionsAddEquivRepresentableFreeHom (J := J) U F x ≫ f :=
by
  -- Proof comment: unfold the additive comparison to a presheaf morphism, rewrite the mapped
  -- section in the `g ≫ f.1` normal form, and then apply adjunction naturality on the sheaf side.
  have hmap :
      (freeAbelianRepresentableHomAddEquivSections U G.1).symm
          ((siteAbelianSectionsFunctor J U).map f x) =
        ((freeAbelianRepresentableHomAddEquivSections U F.1).symm x) ≫ f.1 := by
    apply (freeAbelianRepresentableHomAddEquivSections U G.1).injective
    simpa using
      (freeAbelianRepresentableHomAddEquivSections_map_naturality (J := J) (U := U) f x).symm
  change
    ((sheafificationAdjunction J AddCommGrpCat.{max u v}).homEquiv _ G).symm
        ((freeAbelianRepresentableHomAddEquivSections U G.1).symm
          ((siteAbelianSectionsFunctor J U).map f x)) =
      ((sheafificationAdjunction J AddCommGrpCat.{max u v}).homEquiv _ F).symm
        ((freeAbelianRepresentableHomAddEquivSections U F.1).symm x) ≫ f
  rw [hmap]
  simpa using
    (sheafificationAdjunction J AddCommGrpCat.{max u v}).homEquiv_naturality_right_symm
      ((freeAbelianRepresentableHomAddEquivSections U F.1).symm x) f

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: under `Ext.addEquiv₀`, the degree-zero Ext map is ordinary
postcomposition. -/
private theorem extZero_addEquiv₀_map
    {A F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G)
    (e : Abelian.Ext A F 0) :
    Abelian.Ext.addEquiv₀ (((Abelian.Ext.mk₀ f).postcomp A (add_zero 0)) e) =
      Abelian.Ext.addEquiv₀ e ≫ f := by
  obtain ⟨g, rfl⟩ := Abelian.Ext.homEquiv₀.symm.surjective e
  -- Proof comment: replace the degree-zero Ext class by an actual morphism and compute the
  -- Yoneda product with `mk₀ f`.
  rw [← Abelian.Ext.homEquiv₀_symm_apply]
  change
    Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ g).comp (Abelian.Ext.mk₀ f) (add_zero 0)) =
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) ≫ f
  rw [Abelian.Ext.mk₀_comp_mk₀]
  have hg₀ : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ g) = g := by
    apply Abelian.Ext.homEquiv₀.symm.injective
    simp [Abelian.Ext.homEquiv₀_symm_apply]
  apply Abelian.Ext.homEquiv₀.symm.injective
  simp [Abelian.Ext.homEquiv₀_symm_apply, hg₀]

/-- Helper for Lemma 21.10.5: ordinary morphisms from the sheafified free abelian representable
identify additively with its degree-zero `Ext` classes. -/
private noncomputable def representableFreeHomAddEquivExtZero
    (U : C) (F : Sheaf J AddCommGrpCat.{max u v}) :
    (freeAbelianRepresentableSheaf (J := J) U ⟶ F) ≃+
      Abelian.Ext (freeAbelianRepresentableSheaf (J := J) U) F 0 :=
  Abelian.Ext.addEquiv₀.symm

/-- Helper for Lemma 21.10.5: the degree-zero `Ext` owner gives an additive-group isomorphism
from ordinary morphisms out of the sheafified free abelian representable. -/
private noncomputable def representableFreeHomIsoExtZero
    (U : C) (F : Sheaf J AddCommGrpCat.{max u v}) :
    AddCommGrpCat.of (freeAbelianRepresentableSheaf (J := J) U ⟶ F) ≅
      (Abelian.extFunctorObj (freeAbelianRepresentableSheaf (J := J) U) 0).obj F :=
  (representableFreeHomAddEquivExtZero (J := J) U F).toAddCommGrpIso

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: applying `Abelian.Ext.addEquiv₀` to the degree-zero Ext class
coming from a morphism recovers that morphism. -/
private theorem representableFreeHomAddEquivExtZero_apply_addEquiv₀
    (U : C) (F : Sheaf J AddCommGrpCat.{max u v})
    (g : freeAbelianRepresentableSheaf (J := J) U ⟶ F) :
    Abelian.Ext.addEquiv₀ (representableFreeHomAddEquivExtZero (J := J) U F g) = g := by
  exact Abelian.Ext.addEquiv₀.apply_symm_apply g

/-- Helper for Lemma 21.10.5: the degree-zero `Ext` functor from the sheafified free abelian
representable on `U`. -/
private abbrev extZeroRepresentableFunctor
    (U : C) : Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
  Abelian.extFunctorObj (freeAbelianRepresentableSheaf (J := J) U) 0

/-- Helper for Lemma 21.10.5: package the additive comparison
`Γ(U, -) ≅ Ext^0(freeAbelianRepresentableSheaf U, -)` as a natural isomorphism. -/
private noncomputable def siteAbelianSectionsExtZeroComponent
    (U : C) (F : Sheaf J AddCommGrpCat.{max u v}) :
    (siteAbelianSectionsFunctor J U).obj F ≅
      (extZeroRepresentableFunctor (J := J) U).obj F :=
  (siteAbelianSectionsAddEquivRepresentableFreeHom (J := J) U F).toAddCommGrpIso ≪≫
    representableFreeHomIsoExtZero (J := J) U F

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: the component comparison evaluates by the composite additive
equivalence `Γ(U, F) ≃ Ext^0(freeAbelianRepresentableSheaf U, F)`. -/
private theorem siteAbelianSectionsExtZeroComponent_hom_apply
    (U : C) (F : Sheaf J AddCommGrpCat.{max u v})
    (x : (siteAbelianSectionsFunctor J U).obj F) :
    (siteAbelianSectionsExtZeroComponent (J := J) U F).hom x =
      representableFreeHomAddEquivExtZero (J := J) U F
        (siteAbelianSectionsAddEquivRepresentableFreeHom (J := J) U F x) := by
  rfl

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: the degree-zero Ext owner map is postcomposition on Ext classes. -/
private theorem extZeroRepresentableFunctor_map_eq_postcomp
    {U : C} {F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G) :
    (extZeroRepresentableFunctor (J := J) U).map f =
      AddCommGrpCat.ofHom
        ((Abelian.Ext.mk₀ f).postcomp (freeAbelianRepresentableSheaf (J := J) U) (add_zero 0)) := by
  rfl

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: after applying `Abelian.Ext.addEquiv₀`, the degree-zero Ext owner
map is ordinary postcomposition. -/
private theorem extZeroRepresentableFunctor_addEquiv₀_map_apply
    {U : C} {F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G)
    (e : Abelian.Ext (freeAbelianRepresentableSheaf (J := J) U) F 0) :
    Abelian.Ext.addEquiv₀ (((extZeroRepresentableFunctor (J := J) U).map f) e) =
      Abelian.Ext.addEquiv₀ e ≫ f := by
  rw [extZeroRepresentableFunctor_map_eq_postcomp (J := J) (U := U) f]
  exact extZero_addEquiv₀_map (J := J)
    (A := freeAbelianRepresentableSheaf (J := J) U) f e

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: the componentwise comparison
`Γ(U, F) ≅ Ext^0(freeAbelianRepresentableSheaf U, F)` is natural in `F`, evaluated at a section
`x`. -/
private theorem siteAbelianSectionsExtZeroComponent_naturality_apply
    {U : C} {F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G)
    (x : (siteAbelianSectionsFunctor J U).obj F) :
    (siteAbelianSectionsExtZeroComponent (J := J) U G).hom
        ((siteAbelianSectionsFunctor J U).map f x) =
      (extZeroRepresentableFunctor (J := J) U).map f
        ((siteAbelianSectionsExtZeroComponent (J := J) U F).hom x) := by
  -- Proof comment: rewrite both sides through the `Ext^0 = Hom` bridge, then reduce to the
  -- already proved sections-to-Hom naturality.
  rw [siteAbelianSectionsExtZeroComponent_hom_apply (J := J) U G
    ((siteAbelianSectionsFunctor J U).map f x)]
  rw [siteAbelianSectionsExtZeroComponent_hom_apply (J := J) U F x]
  -- Proof comment: applying `Ext.addEquiv₀` turns the right-hand side into plain postcomposition.
  apply Abelian.Ext.addEquiv₀.injective
  rw [representableFreeHomAddEquivExtZero_apply_addEquiv₀ (J := J) U G
    (siteAbelianSectionsAddEquivRepresentableFreeHom (J := J) U G
      ((siteAbelianSectionsFunctor J U).map f x))]
  rw [extZeroRepresentableFunctor_addEquiv₀_map_apply (J := J) (U := U) f
    (representableFreeHomAddEquivExtZero (J := J) U F
      (siteAbelianSectionsAddEquivRepresentableFreeHom (J := J) U F x))]
  rw [representableFreeHomAddEquivExtZero_apply_addEquiv₀ (J := J) U F
    (siteAbelianSectionsAddEquivRepresentableFreeHom (J := J) U F x)]
  exact
    siteAbelianSectionsAddEquivRepresentableFreeHom_naturality (J := J) (U := U) f x

/-- Helper for Lemma 21.10.5: package the additive comparison
`Γ(U, -) ≅ Ext^0(freeAbelianRepresentableSheaf U, -)` as a natural isomorphism. -/
private noncomputable def siteAbelianSectionsIsoExtZeroRepresentableFree
    (U : C) :
    siteAbelianSectionsFunctor J U ≅
      extZeroRepresentableFunctor (J := J) U :=
  NatIso.ofComponents
    (siteAbelianSectionsExtZeroComponent (J := J) U)
    (fun {F G} f ↦ by
      -- Proof comment: naturality of the `NatIso` is checked pointwise on sections over `U`.
      ext x
      exact siteAbelianSectionsExtZeroComponent_naturality_apply (J := J) (U := U) f x)

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: in every degree, the map of the Ext owner functor is the canonical
postcomposition map on Ext classes. -/
private theorem extFunctorObj_map_eq_postcomp
    {U : C} {F G : Sheaf J AddCommGrpCat.{max u v}} (f : F ⟶ G) (p : ℕ) :
    (Abelian.extFunctorObj (freeAbelianRepresentableSheaf (J := J) U) p).map f =
      AddCommGrpCat.ofHom
        ((Abelian.Ext.mk₀ f).postcomp (freeAbelianRepresentableSheaf (J := J) U)
          (add_zero p)) := by
  -- The Ext-functor owner is defined by the degree-`p` postcomposition map.
  rfl

omit [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.10.5: the cohomology-presheaf owner is literally the degree-`p`
`Ext` object from the sheafified free representable at `U`. -/
private theorem cohomologyPresheafFunctor_obj_obj_eq_ext
    (U : C) (F : Sheaf J AddCommGrpCat.{max u v}) (p : ℕ) :
    (((Sheaf.cohomologyPresheafFunctor J p).obj F).obj (op U)) =
      AddCommGrpCat.of
        (Abelian.Ext
          (freeAbelianRepresentableSheaf (J := J) U)
          F p) := by
  -- Unfolding the owner shows that the value at `U` is definitionally this `Ext^p` object.
  rfl

/-- Companion for Lemma 21.10.5: after evaluating at `U`, the degree-`p` right derived functor of
the inclusion `sheafToPresheaf J AddCommGrpCat` is canonically identified with the additive
functor `F ↦ H^p(U, F)`. -/
theorem abelianSheafInclusion_rightDerived_eval_is_cohomologyAtObject
    (U : C) (p : ℕ) :
    IsIsomorphic
      ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p) ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)))
      (((Sheaf.cohomologyPresheafFunctor J p :
          Sheaf J AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U))) := by
  -- Evaluate the presheaf-valued comparison at `U` to obtain the fixed-object bridge.
  rcases CategoryTheory.Sheaf.cohomologyPresheafComparison (J := J) p with ⟨e⟩
  exact ⟨Functor.isoWhiskerRight e
    ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U))⟩

/-- Companion for Lemma 21.10.5: objectwise over a fixed `U`, the degree-`p` right derived
functor of the inclusion computes the canonical cohomology object `F.H' p U`. -/
theorem cohomologyAtObject_isomorphic
    (U : C) (p : ℕ) (F : Sheaf J AddCommGrpCat.{max u v}) :
    IsIsomorphic
      (((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj (op U)))
      (F.H' p U) := by
  rcases abelianSheafInclusion_rightDerived_eval_is_cohomologyAtObject J U p with ⟨e⟩
  simpa [Sheaf.H'] using (show IsIsomorphic
    (((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).obj (op U)))
    ((((Sheaf.cohomologyPresheafFunctor J p).obj F).obj (op U))) from ⟨e.app F⟩)

/- 
Domain-style sampling for Lemma 21.10.5:
- primary domain: right derived functors of the canonical inclusion `sheafToPresheaf` for abelian
  sheaves on a site, and the canonical cohomology-presheaf owner
  `Sheaf.cohomologyPresheafFunctor`;
- sampled owner declarations:
  `sheafToPresheaf`,
  `Sheaf.cohomologyPresheafFunctor`,
  `Sheaf.cohomologyPresheaf`,
  `CategoryTheory.Functor.rightDerived`;
- best owner abstraction: the functor-level comparison between
  `(sheafToPresheaf J AddCommGrpCat).rightDerived p` and
  `Sheaf.cohomologyPresheafFunctor J p`, with evaluation at `U` and objectwise specialization as
  bridge API.

Source/core/bridge triage:
- `source-facing`: the functor-level comparison identifying the degree-`p` right derived functor of
  the inclusion with the cohomology-presheaf functor;
- `core/canonical`: the owners `sheafToPresheaf`, `Sheaf.cohomologyPresheafFunctor`, and
  `Sheaf.cohomologyPresheaf`;
- `bridge/view`: evaluation at a fixed object `U`, or evaluation at a fixed abelian sheaf `F`.
-/

/-- Lemma 21.10.5, owner form: the degree-`p` right derived functor of the inclusion
`sheafToPresheaf J AddCommGrpCat` is canonically identified with the cohomology-presheaf functor.
The left-exactness clause is already the instance
`PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat)`. -/
@[stacks 03AY]
theorem abelianSheafInclusion_rightDerived_presheafComparison
    (p : ℕ) :
    IsIsomorphic
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p)
      (Sheaf.cohomologyPresheafFunctor J p :
        Sheaf J AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) := by
  -- The public owner theorem is the canonical comparison already proved in the shared API.
  exact CategoryTheory.Sheaf.cohomologyPresheafComparison (J := J) p

/-- Companion for Lemma 21.10.5: this compatibility alias exposes the owner comparison under the
older local theorem name used by downstream code. -/
theorem abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor
    (p : ℕ) :
    IsIsomorphic
      ((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p)
      (Sheaf.cohomologyPresheafFunctor J p :
        Sheaf J AddCommGrpCat.{max u v} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) := by
  exact abelianSheafInclusion_rightDerived_presheafComparison (J := J) p

/-- Lemma 21.10.5: the right derived functor of the inclusion
`Sheaf J AddCommGrpCat ⥤ Cᵒᵖ ⥤ AddCommGrpCat` in degree `p` is isomorphic to the
cohomology presheaf functor `F ↦ (U ↦ H^p(U, F))`; the left exactness of the inclusion is supplied
by the existing `PreservesFiniteLimits` instance on `sheafToPresheaf`. -/
@[stacks 03AY]
theorem abelianSheafInclusion_rightDerived_obj_is_cohomologyPresheaf
    (p : ℕ) (F : Sheaf J AddCommGrpCat.{max u v}) :
    IsIsomorphic
      (((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F)
      (F.cohomologyPresheaf p : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) := by
  rcases abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor J p with ⟨e⟩
  exact ⟨e.app F⟩

end Sheaf

end CategoryTheory

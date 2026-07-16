import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap13.Lemma_13_10_5
import stacks_proof.stacks_project.Chap13.Lemma_13_6_2
import stacks_proof.stacks_project.Chap13.Lemma_13_6_11
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap13.Lemma_13_11_2
import stacks_proof.stacks_project.Chap13.Lemma_13_11_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 13.11.6:
- primary domain: derived-category localization of bounded homotopy categories by
  quasi-isomorphisms;
- sampled owner declarations:
  `HomotopyCategory.quasiIso`,
  `HomotopyCategory.subcategoryAcyclic`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.lift`,
  `DerivedCategory.Qh`,
  `Functor.kernel`;
- best owner abstraction: the ambient owners are the unbounded quasi-isomorphism morphism
  property `HomotopyCategory.quasiIso 𝒜 (up ℤ)` and the acyclic triangulated subcategory
  `HomotopyCategory.subcategoryAcyclic 𝒜`; on the bounded categories, the source-facing objects
  are their inverse-image/restricted views along the inclusion `ObjectProperty.ι`.
- primitive vs. derived API: the primitive data are the bounded homotopy object properties from
  `Definition_13_8_1`, the canonical quotient functor `DerivedCategory.Qh`, and the ambient
  quasi-isomorphism / acyclic owners. The bounded localization functors and their kernel /
  localization statements are the derived bridge/view layer.
- source/core/bridge triage:
  `source-facing`: `Qis⁺(𝒜)`, `Qis⁻(𝒜)`, `Qisᵇ(𝒜)`, the bounded derived functors, and the nine
    localization statements of Lemma 13.11.6;
  `core/canonical`: `HomotopyCategory.quasiIso 𝒜 (up ℤ)`,
    `HomotopyCategory.subcategoryAcyclic 𝒜`, `DerivedCategory.Qh`, and `Functor.kernel`;
  `bridge/view`: inverse images to `K⁺(𝒜)`, `K⁻(𝒜)`, `Kᵇ(𝒜)` and the induced functors
    `K^*(𝒜) ⥤ D^*(𝒜)`.

The bounded quasi-isomorphism morphism properties are high-frequency bridge owners used downstream,
so they remain named here. The bounded acyclic object properties are only the direct inverse-image
views of `HomotopyCategory.subcategoryAcyclic 𝒜`, so this file uses source-facing notation for
them rather than introducing a second public owner layer. -/

/- Reuse the Chapter 13 boundedness owners on cochain complexes and their homotopy categories from
`Definition_13_8_1` and the bounded derived-category owners from `Definition_13_11_3`; this file
adds localization results on top of that canonical API rather than redeclaring parallel
bounded-derived notions. -/

/-- The quasi-isomorphisms in `K^+(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedBelowHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁺(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (HomotopyCategory.plus 𝒜).ι

/-- The quasi-isomorphisms in `K^-(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedAboveHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁻(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (HomotopyCategory.minus 𝒜).ι

/-- The quasi-isomorphisms in `K^b(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (Kᵇ(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (HomotopyCategory.bounded 𝒜).ι

scoped notation "Qis⁺(" A:arg ")" => boundedBelowHomotopyQuasiIso A
scoped notation "Qis⁻(" A:arg ")" => boundedAboveHomotopyQuasiIso A
scoped notation "Qisᵇ(" A:arg ")" => boundedHomotopyQuasiIso A

scoped notation "Ac⁺(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (HomotopyCategory.plus A))
scoped notation "Ac⁻(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (HomotopyCategory.minus A))
scoped notation "Acᵇ(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (HomotopyCategory.bounded A))

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded-below homotopy objects
to bounded-below derived objects, via the canonical owner `DerivedCategory.IsGE`. -/
theorem qh_obj_mem_t_plus
    (X : K⁺(𝒜)) :
    (t.plus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  have hK : CochainComplex.plus 𝒜 K := by
    simpa [K, HomotopyCategory.plus] using X.property
  rcases hK with ⟨n, hn⟩
  letI : K.IsStrictlyGE n := by simpa [K] using hn
  letI : K.IsGE n := inferInstance
  let e : DerivedCategory.Qh.obj X.obj ≅ DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app K
  have hQ : (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Q.obj K) := by
    refine ⟨n, ?_⟩
    change (DerivedCategory.Q.obj K).IsGE n
    exact (DerivedCategory.isGE_Q_obj_iff K n).2 inferInstance
  exact (t.plus : ObjectProperty (D(𝒜))).prop_of_iso e.symm hQ

/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded-above homotopy objects
to bounded-above derived objects, via the canonical owner `DerivedCategory.IsLE`. -/
theorem qh_obj_mem_t_minus
    (X : K⁻(𝒜)) :
    (t.minus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  have hK : CochainComplex.minus 𝒜 K := by
    simpa [K, HomotopyCategory.minus] using X.property
  rcases hK with ⟨n, hn⟩
  letI : K.IsStrictlyLE n := by simpa [K] using hn
  letI : K.IsLE n := inferInstance
  let e : DerivedCategory.Qh.obj X.obj ≅ DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app K
  have hQ : (t.minus : ObjectProperty (D(𝒜))) (DerivedCategory.Q.obj K) := by
    refine ⟨n, ?_⟩
    change (DerivedCategory.Q.obj K).IsLE n
    exact (DerivedCategory.isLE_Q_obj_iff K n).2 inferInstance
  exact (t.minus : ObjectProperty (D(𝒜))).prop_of_iso e.symm hQ

-- Proof sketch: a bounded complex has cohomology vanishing outside a finite interval, and the
-- identity functor sends bounded complexes to the same derived objects, so both the bounded-below
-- and bounded-above vanishing conditions hold in the image.
/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded homotopy objects to
bounded derived objects. -/
theorem qh_obj_mem_t_bounded
    (X : Kᵇ(𝒜)) :
    (t.bounded : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  -- Split boundedness of the representing complex into lower and upper support bounds.
  have hX : CochainComplex.bounded 𝒜 X.obj.as := by
    simpa [HomotopyCategory.bounded] using X.property
  rcases hX with ⟨hplus, hminus⟩
  rw [derivedCategory_t_bounded_iff]
  constructor
  ·
    let Xplus : K⁺(𝒜) :=
      ⟨X.obj, (HomotopyCategory.plus_iff (𝒜 := 𝒜) X.obj).2 hplus⟩
    -- Reuse the bounded-below bridge on the same underlying homotopy object.
    have hPlus : (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj X.obj) := by
      change (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj Xplus.obj)
      exact qh_obj_mem_t_plus (𝒜 := 𝒜) Xplus
    exact (derivedCategory_t_plus_iff (𝒜 := 𝒜) (DerivedCategory.Qh.obj X.obj)).1 hPlus
  ·
    let Xminus : K⁻(𝒜) :=
      ⟨X.obj, (HomotopyCategory.minus_iff (𝒜 := 𝒜) X.obj).2 hminus⟩
    -- Reuse the bounded-above bridge on the same underlying homotopy object.
    have hMinus : (t.minus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj X.obj) := by
      change (t.minus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj Xminus.obj)
      exact qh_obj_mem_t_minus (𝒜 := 𝒜) Xminus
    exact (derivedCategory_t_minus_iff (𝒜 := 𝒜) (DerivedCategory.Qh.obj X.obj)).1 hMinus

/-- The canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)`. -/
abbrev mapBoundedBelowHomotopyToDerivedBelow
    :
    K⁺(𝒜) ⥤ D⁺(𝒜) :=
  (t.plus : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_plus

/-- The canonical functor `K^-(\mathcal A) ⟶ D^-(\mathcal A)`. -/
abbrev mapBoundedAboveHomotopyToDerivedAbove
    :
    K⁻(𝒜) ⥤ D⁻(𝒜) :=
  (t.minus : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_minus

/-- The canonical functor `K^b(\mathcal A) ⟶ D^b(\mathcal A)`. -/
abbrev mapBoundedHomotopyToDerivedBounded
    :
    Kᵇ(𝒜) ⥤ Dᵇ(𝒜) :=
  (t.bounded : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_bounded

namespace Functor

/-- If `Q : C ⥤ D` is essentially surjective and `F.map` is surjective on morphisms between
objects in the image of `Q`, then `F` is full. -/
theorem full_of_comp_essSurj
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    (F : D ⥤ E) (Q : C ⥤ D) [Q.EssSurj]
    (h :
      ∀ {X Y : C},
        Function.Surjective
          (fun f : Q.obj X ⟶ Q.obj Y => F.map f)) :
    F.Full := by
  -- Proof comment: choose essential-surjectivity representatives for the source and target, pull
  -- the morphism back to objects in the image of `Q`, lift it there using `h`, and transport it
  -- back along the chosen isomorphisms.
  refine Functor.Full.mk ?_
  intro X Y f
  obtain ⟨X', ⟨eX⟩⟩ := Functor.EssSurj.mem_essImage (F := Q) X
  obtain ⟨Y', ⟨eY⟩⟩ := Functor.EssSurj.mem_essImage (F := Q) Y
  obtain ⟨g, hg⟩ := h
    (F.map eX.hom ≫ f ≫ F.map eY.inv)
  refine ⟨eX.inv ≫ g ≫ eY.hom, ?_⟩
  calc
    F.map (eX.inv ≫ g ≫ eY.hom)
        = F.map eX.inv ≫ (F.map g ≫ F.map eY.hom) := by
            simp [Functor.map_comp]
    _ = F.map eX.inv ≫ (F.map eX.hom ≫ f ≫ F.map eY.inv) ≫ F.map eY.hom := by
          simp [hg, Category.assoc]
    _ = f := by
          simp [Category.assoc]

/-- If `Q : C ⥤ D` is essentially surjective and `F.map` is injective on morphisms between
objects in the image of `Q`, then `F` is faithful. -/
theorem faithful_of_comp_essSurj
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    (F : D ⥤ E) (Q : C ⥤ D) [Q.EssSurj]
    (h :
      ∀ (X Y : C),
        Function.Injective
          (fun f : Q.obj X ⟶ Q.obj Y => F.map f)) :
    F.Faithful := by
  -- Proof comment: compare two morphisms after transporting them to chosen `Q.obj`-models of
  -- their source and target; injectivity there descends back along the chosen isomorphisms.
  refine Functor.Faithful.mk ?_
  intro X Y f g hfg
  obtain ⟨X', ⟨eX⟩⟩ := Functor.EssSurj.mem_essImage (F := Q) X
  obtain ⟨Y', ⟨eY⟩⟩ := Functor.EssSurj.mem_essImage (F := Q) Y
  have hmap :
      F.map (eX.hom ≫ f ≫ eY.inv) =
        F.map (eX.hom ≫ g ≫ eY.inv) := by
    simpa [Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ F.map eX.hom ≫ k ≫ F.map eY.inv) hfg
  have hEq :
      eX.hom ≫ f ≫ eY.inv =
        eX.hom ≫ g ≫ eY.inv :=
    h X' Y' hmap
  simpa [Category.assoc] using
    congrArg (fun k ↦ eX.inv ≫ k ≫ eY.hom) hEq

end Functor

/-- Helper for Lemma 13.11.6: the canonical comparison natural transformation
`Localization.fac` can be rewritten in the reassociated form used when denominators are pushed
across a localization lift. -/
private lemma localization_fac_hom_naturality_assoc
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]
    (G : C ⥤ E) (hG : W.IsInvertedBy G)
    {X Y : C} (f : X ⟶ Y) :
    (Localization.fac G hG L).hom.app X ≫ G.map f =
      (Localization.lift G hG L).map (L.map f) ≫
        (Localization.fac G hG L).hom.app Y := by
  -- Proof comment: this is just naturality of `Localization.fac`, rewritten so the lifted map
  -- appears on the left-hand side where the roof-comparison proofs need it.
  simpa using ((Localization.fac G hG L).hom.naturality f).symm

/-- Helper for Lemma 13.11.6: after postcomposing by the denominator of a left fraction, the
image of that fraction through `Localization.lift` matches the ambient roof obtained by
`Localization.fac`. -/
private lemma localizationLift_leftFraction_postcomp_assoc
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]
    (G : C ⥤ E) (hG : W.IsInvertedBy G)
    {X Y : C} (φ : W.LeftFraction X Y) :
    (((Localization.lift G hG L).map (φ.map L (Localization.inverts L W))) ≫
        (Localization.fac G hG L).hom.app Y) ≫
      G.map φ.s =
      (Localization.fac G hG L).hom.app X ≫ G.map φ.f := by
  let e := Localization.fac G hG L
  -- Proof comment: push the denominator across `Localization.fac`, then collapse the localized
  -- roof against that denominator inside the lifted functor.
  calc
    (((Localization.lift G hG L).map (φ.map L (Localization.inverts L W))) ≫ e.hom.app Y) ≫
        G.map φ.s
        =
          ((Localization.lift G hG L).map (φ.map L (Localization.inverts L W))) ≫
            (e.hom.app Y ≫ G.map φ.s) := by
              simp [Category.assoc]
    _ =
          ((Localization.lift G hG L).map (φ.map L (Localization.inverts L W))) ≫
            ((Localization.lift G hG L).map (L.map φ.s) ≫ e.hom.app φ.Y') := by
              simpa using
                congrArg
                  (fun k ↦
                    (Localization.lift G hG L).map
                      (φ.map L (Localization.inverts L W)) ≫ k)
                  (localization_fac_hom_naturality_assoc L G hG φ.s)
    _ =
          (Localization.lift G hG L).map
            (φ.map L (Localization.inverts L W) ≫ L.map φ.s) ≫
              e.hom.app φ.Y' := by
                rw [← Functor.map_comp_assoc]
    _ = (Localization.lift G hG L).map (L.map φ.f) ≫ e.hom.app φ.Y' := by
          simpa using
            congrArg
              (fun k ↦ (Localization.lift G hG L).map k ≫ e.hom.app φ.Y')
              (MorphismProperty.LeftFraction.map_comp_map_s φ L (Localization.inverts L W))
    _ = e.hom.app X ≫ G.map φ.f := by
          rw [localization_fac_hom_naturality_assoc L G hG φ.f]

/-- Helper for Lemma 13.11.6: after precomposing by the denominator of a right fraction, the
image of that fraction through `Localization.lift` matches the ambient roof obtained by
`Localization.fac`. -/
private lemma localizationLift_rightFraction_precomp_assoc
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]
    (G : C ⥤ E) (hG : W.IsInvertedBy G)
    {X Y : C} (φ : W.RightFraction X Y) :
    (Localization.lift G hG L).map (L.map φ.s) ≫
        (((Localization.lift G hG L).map (φ.map L (Localization.inverts L W))) ≫
          (Localization.fac G hG L).hom.app Y) =
    (Localization.lift G hG L).map (L.map φ.s) ≫
        ((Localization.fac G hG L).hom.app X ≫ φ.map G hG) := by
  let e := Localization.fac G hG L
  have h₁ :
      (Localization.lift G hG L).map (L.map φ.s) ≫
          (((Localization.lift G hG L).map (φ.map L (Localization.inverts L W))) ≫
            e.hom.app Y) =
        ((Localization.lift G hG L).map (L.map φ.s) ≫
          (Localization.lift G hG L).map (φ.map L (Localization.inverts L W))) ≫
            e.hom.app Y := by
    -- Proof comment: reassociate so the two lifted maps can be combined first.
    simp [Category.assoc]
  have h₂ :
      ((Localization.lift G hG L).map (L.map φ.s) ≫
          (Localization.lift G hG L).map (φ.map L (Localization.inverts L W))) ≫
            e.hom.app Y =
        (Localization.lift G hG L).map
          (L.map φ.s ≫ φ.map L (Localization.inverts L W)) ≫
            e.hom.app Y := by
    -- Proof comment: combine the two lifted morphisms into the lifted composite roof.
    simpa [Category.assoc] using
      (Functor.map_comp_assoc
        (F := Localization.lift G hG L)
        (f := L.map φ.s)
        (g := φ.map L (Localization.inverts L W))
        (h := e.hom.app Y)).symm
  have h₃ :
      (Localization.lift G hG L).map
          (L.map φ.s ≫ φ.map L (Localization.inverts L W)) ≫
            e.hom.app Y =
        (Localization.lift G hG L).map (L.map φ.f) ≫ e.hom.app Y := by
    -- Proof comment: the right-fraction denominator collapses against the represented roof.
    rw [MorphismProperty.RightFraction.map_s_comp_map]
  have h₄ :
      (Localization.lift G hG L).map (L.map φ.f) ≫ e.hom.app Y =
        e.hom.app φ.X' ≫ G.map φ.f := by
    -- Proof comment: rewrite the numerator via the naturality square of `Localization.fac`.
    rw [localization_fac_hom_naturality_assoc L G hG φ.f]
  have h₅ :
      e.hom.app φ.X' ≫ G.map φ.f =
        ((Localization.lift G hG L).map (L.map φ.s) ≫ e.hom.app X) ≫
          φ.map G hG := by
    -- Proof comment: rewrite the numerator in `G` as denominator followed by the right-fraction
    -- morphism, then transport the denominator across `Localization.fac`.
    calc
      e.hom.app φ.X' ≫ G.map φ.f
          = e.hom.app φ.X' ≫ (G.map φ.s ≫ φ.map G hG) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ e.hom.app φ.X' ≫ k)
                  (MorphismProperty.RightFraction.map_s_comp_map φ G hG)
      _ = ((Localization.lift G hG L).map (L.map φ.s) ≫ e.hom.app X) ≫ φ.map G hG := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ k ≫ φ.map G hG)
                (localization_fac_hom_naturality_assoc L G hG φ.s)
  have h₆ :
      ((Localization.lift G hG L).map (L.map φ.s) ≫ e.hom.app X) ≫
          φ.map G hG =
        (Localization.lift G hG L).map (L.map φ.s) ≫
          (e.hom.app X ≫ φ.map G hG) := by
    -- Proof comment: put the result back into the reassociated form of the target.
    simp [Category.assoc]
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))

/-- Helper for Lemma 13.11.6: mapping an explicit left-fraction roof through a localization lift
conjugates it by the canonical `Localization.fac` comparison isomorphism. -/
private theorem localization_lift_map_leftFraction
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]
    (G : C ⥤ E) (hG : W.IsInvertedBy G)
    {X Y : C} (φ : W.LeftFraction X Y) :
    (Localization.lift G hG L).map (φ.map L (Localization.inverts L W)) =
      (Localization.fac G hG L).hom.app X ≫
        φ.map G hG ≫
        (Localization.fac G hG L).inv.app Y := by
  let e := Localization.fac G hG L
  have hs : IsIso (G.map φ.s) := hG _ φ.hs
  have hpost :
      (Localization.lift G hG L).map (φ.map L (Localization.inverts L W)) ≫ e.hom.app Y =
        e.hom.app X ≫ φ.map G hG := by
    -- Proof comment: cancel the denominator image from the explicit postcomposition identity.
    apply (cancel_mono (G.map φ.s)).1
    simpa [Category.assoc, MorphismProperty.LeftFraction.map_comp_map_s] using
      localizationLift_leftFraction_postcomp_assoc L G hG φ
  -- Proof comment: a final cancellation of the comparison isomorphism yields the conjugation
  -- formula for the lifted left fraction.
  apply (cancel_mono (e.hom.app Y)).1
  change (Localization.lift G hG L).map (φ.map L (Localization.inverts L W)) ≫ e.hom.app Y =
    (e.hom.app X ≫ φ.map G hG ≫ e.inv.app Y) ≫ e.hom.app Y
  calc
    (Localization.lift G hG L).map (φ.map L (Localization.inverts L W)) ≫ e.hom.app Y
        = e.hom.app X ≫ φ.map G hG := hpost
    _ = (e.hom.app X ≫ φ.map G hG ≫ e.inv.app Y) ≫ e.hom.app Y := by
          rw [Category.assoc, Category.assoc, e.inv_hom_id_app]
          simp

/-- Helper for Lemma 13.11.6: mapping an explicit right-fraction roof through a localization lift
conjugates it by the canonical `Localization.fac` comparison isomorphism. -/
private theorem localization_lift_map_rightFraction
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]
    (G : C ⥤ E) (hG : W.IsInvertedBy G)
    {X Y : C} (φ : W.RightFraction X Y) :
    (Localization.lift G hG L).map (φ.map L (Localization.inverts L W)) =
      (Localization.fac G hG L).hom.app X ≫
        φ.map G hG ≫
        (Localization.fac G hG L).inv.app Y := by
  let e := Localization.fac G hG L
  have hs : IsIso (L.map φ.s) := Localization.inverts L W φ.s φ.hs
  have hpre :
      (Localization.lift G hG L).map (φ.map L (Localization.inverts L W)) ≫ e.hom.app Y =
        e.hom.app X ≫ φ.map G hG := by
    -- Proof comment: cancel the image of the denominator inside the localization lift.
    apply (cancel_epi ((Localization.lift G hG L).map (L.map φ.s))).1
    simpa [Category.assoc] using localizationLift_rightFraction_precomp_assoc L G hG φ
  -- Proof comment: as on the left-fraction side, cancel the comparison isomorphism to obtain the
  -- final conjugation formula.
  apply (cancel_mono (e.hom.app Y)).1
  change (Localization.lift G hG L).map (φ.map L (Localization.inverts L W)) ≫ e.hom.app Y =
    (e.hom.app X ≫ φ.map G hG ≫ e.inv.app Y) ≫ e.hom.app Y
  calc
    (Localization.lift G hG L).map (φ.map L (Localization.inverts L W)) ≫ e.hom.app Y
        = e.hom.app X ≫ φ.map G hG := hpre
    _ = (e.hom.app X ≫ φ.map G hG ≫ e.inv.app Y) ≫ e.hom.app Y := by
          rw [Category.assoc, Category.assoc, e.inv_hom_id_app]
          simp

/-- Helper for Lemma 13.11.6: any quasi-isomorphism out of a bounded-below object in
`K(\mathcal A)` can be refined so that the target is again bounded below. -/
lemma quasiIso_to_bounded_below_refinement
    (X : K⁺(𝒜)) {Y : K(𝒜)} (s : X.obj ⟶ Y)
    (hs : HomotopyCategory.quasiIso 𝒜 (up ℤ) s) :
    ∃ (Y' : K⁺(𝒜)) (t : Y ⟶ Y'.obj), HomotopyCategory.quasiIso 𝒜 (up ℤ) t := by
  -- Proof comment: the source bound on `X` forces eventual homology vanishing on `Y`, so
  -- Lemma 13.11.5 supplies a bounded-below truncation quasi-isomorphic to `Y`.
  rw [HomotopyCategory.mem_quasiIso_iff] at hs
  obtain ⟨a, hXge⟩ :=
    (CochainComplex.plus_iff 𝒜 X.obj.as).1
      ((HomotopyCategory.plus_iff (𝒜 := 𝒜) X.obj).1 X.property)
  have hYeventual : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (Y.as.homology n) := by
    refine ⟨a, ?_⟩
    intro n hn
    let KX : CochainComplex 𝒜 ℤ := X.obj.as
    let _ : KX.IsStrictlyGE a := by
      simpa [KX] using hXge
    let _ : KX.HasHomology n := inferInstance
    have hXhomology : IsZero (KX.homology n) :=
      CochainComplex.isZero_of_isGE (K := KX) a n hn
    have hXhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj X.obj)) := by
      simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
        HomotopyCategory.quotient_obj_as] using
        (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KX).isZero_iff).2
          hXhomology
    have hYhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Y)) := by
      exact IsZero.of_iso hXhomotopy
        ((asIso ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).map s)).symm)
    let KY : CochainComplex 𝒜 ℤ := Y.as
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, KY] using
      (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KY).isZero_iff).1
        hYhomotopy
  obtain ⟨a, hπ, htrunc⟩ :=
    exists_quasiIso_to_truncGE_of_eventually_isZero_homology (K := Y.as) hYeventual
  let Y' : K⁺(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := Y.as) a), by
      -- Proof comment: the truncation bound gives the bounded-below structure on the refined
      -- target.
      rw [HomotopyCategory.plus_iff]
      exact (CochainComplex.plus_iff 𝒜 _).2 ⟨a, htrunc⟩⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: pass the truncation map to the homotopy category.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.πTruncGE (K := Y.as) a)
  · -- Proof comment: the truncation map is a quasi-isomorphism by construction.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.πTruncGE (K := Y.as) a)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hπ)

/-- Helper for Lemma 13.11.6: any quasi-isomorphism into a bounded-above object in
`K(\mathcal A)` can be refined so that the source is again bounded above. -/
lemma quasiIso_from_bounded_above_refinement
    (X : K⁻(𝒜)) {Y : K(𝒜)} (s : Y ⟶ X.obj)
    (hs : HomotopyCategory.quasiIso 𝒜 (up ℤ) s) :
    ∃ (Y' : K⁻(𝒜)) (t : Y'.obj ⟶ Y), HomotopyCategory.quasiIso 𝒜 (up ℤ) t := by
  -- Proof comment: this is the dual truncation argument, using eventual high-degree vanishing on
  -- `Y` inherited from the bounded-above source `X`.
  rw [HomotopyCategory.mem_quasiIso_iff] at hs
  obtain ⟨b, hXle⟩ :=
    (CochainComplex.minus_iff 𝒜 X.obj.as).1
      ((HomotopyCategory.minus_iff (𝒜 := 𝒜) X.obj).1 X.property)
  have hYeventual : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (Y.as.homology n) := by
    refine ⟨b, ?_⟩
    intro n hn
    let KX : CochainComplex 𝒜 ℤ := X.obj.as
    let _ : KX.IsStrictlyLE b := by
      simpa [KX] using hXle
    let _ : KX.HasHomology n := inferInstance
    have hXhomology : IsZero (KX.homology n) :=
      CochainComplex.isZero_of_isLE (K := KX) b n hn
    have hXhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj X.obj)) := by
      simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
        HomotopyCategory.quotient_obj_as] using
        (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KX).isZero_iff).2
          hXhomology
    have hYhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Y)) := by
      exact IsZero.of_iso hXhomotopy
        (asIso ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).map s))
    let KY : CochainComplex 𝒜 ℤ := Y.as
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, KY] using
      (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KY).isZero_iff).1
        hYhomotopy
  obtain ⟨b, hι, htrunc⟩ :=
    exists_quasiIso_from_truncLE_of_eventually_isZero_homology (K := Y.as) hYeventual
  let Y' : K⁻(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncLE (K := Y.as) b), by
      -- Proof comment: the truncation bound gives the bounded-above structure on the refined
      -- source.
      rw [HomotopyCategory.minus_iff]
      exact (CochainComplex.minus_iff 𝒜 _).2 ⟨b, htrunc⟩⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: pass the truncation inclusion to the homotopy category.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.ιTruncLE (K := Y.as) b)
  · -- Proof comment: the truncation inclusion is a quasi-isomorphism by construction.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.ιTruncLE (K := Y.as) b)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hι)

-- Proof sketch: identify quasi-isomorphisms in the ambient homotopy category with the Verdier
-- morphism property of the acyclic subcategory, then restrict along the inclusion
-- `K^{+}(\mathcal A) ⥤ K(\mathcal A)`.
/-- First localization statement of Lemma 13.11.6: the saturated multiplicative system
corresponding to `Ac^{+}(\mathcal A)` is precisely `Qis^{+}(\mathcal A)`. -/
@[stacks 05RW]
theorem boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Ac⁺(𝒜)).trW =
      Qis⁺(𝒜) := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedBelowHomotopyQuasiIso, HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]

-- Proof sketch: an object of `K^{+}(\mathcal A)` maps to zero in `D^{+}(\mathcal A)` exactly
-- when its image in the unbounded derived category is acyclic, which is the defining condition of
-- `Ac^{+}(\mathcal A)`.
/-- Second localization statement of Lemma 13.11.6: the kernel of
`K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)` is `Ac^{+}(\mathcal A)`. -/
@[stacks 05RW]
theorem kernel_mapBoundedBelowHomotopyToDerivedBelow_eq_acyclic
    :
    Functor.kernel mapBoundedBelowHomotopyToDerivedBelow =
      Ac⁺(𝒜) := by
  -- Compare the bounded-below lift with the ambient quotient functor on underlying derived objects.
  ext X
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  let e :
      ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.plus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_plus).app X
  constructor
  · intro hX
    have hUnderlying : IsZero (ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X)) :=
      ιplus.map_isZero hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := e.isZero_iff.1 hUnderlying
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := hQh
    rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)] at hker
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hker
  · intro hX
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := by
      rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)]
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := hker
    have hUnderlying : IsZero (ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X)) :=
      e.isZero_iff.2 hQh
    exact IsZero.of_full_of_faithful_of_isZero ιplus _ hUnderlying

/-- Helper for Lemma 13.11.6: the bounded-below derived functor inverts the Verdier morphism
property attached to the bounded-below acyclic subcategory. -/
theorem mapBoundedBelowHomotopyToDerivedBelow_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Ac⁺(𝒜)).trW)
      mapBoundedBelowHomotopyToDerivedBelow := by
  intro X Y f hf
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  have hQis : Qis⁺(𝒜) f := by
    simpa [boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  have hUnderlying :
      IsIso (((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is exactly the
    -- unbounded derived localization inverting a quasi-isomorphism.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.plus 𝒜).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.plus 𝒜).ι.map f)
      (by simpa [boundedBelowHomotopyQuasiIso] using hQis)
  have hLifted :
      IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := by
    -- Proof comment: the lift-to-inclusion comparison transports invertibility back to `D⁺`.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.plus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_plus)
        f)).2 hUnderlying
  let _ : IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := hLifted
  exact isIso_of_fully_faithful ιplus (mapBoundedBelowHomotopyToDerivedBelow.map f)

/-- Helper for Lemma 13.11.6: a chosen cochain-level preimage of a bounded-below derived object
has vanishing homology in sufficiently negative degrees. -/
theorem boundedBelow_objPreimage_eventually_isZero_homology
    (X : D⁺(𝒜)) :
    ∃ a : ℤ, ∀ i < a, IsZero ((DerivedCategory.Q.objPreimage X.obj).homology i) := by
  -- Proof comment: transfer the bounded-below vanishing of `X` along the canonical preimage
  -- isomorphism in the ambient derived category.
  obtain ⟨a, ha⟩ := (derivedCategory_t_plus_iff (K := X.obj)).1 X.property
  refine ⟨a, ?_⟩
  intro i hi
  have hXi : IsZero ((H^i).obj X.obj) := ha i hi
  have hQpreimage :
      IsZero
        ((H^i).obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj))) := by
    let e :
        (H^i).obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj)) ≅
          (H^i).obj X.obj :=
      (H^i).mapIso (DerivedCategory.Q.objObjPreimageIso X.obj)
    exact (e.isZero_iff).2 hXi
  exact
    (((DerivedCategory.homologyFunctorFactors 𝒜 i).app
      (DerivedCategory.Q.objPreimage X.obj)).isZero_iff).1 hQpreimage

/-- Helper for Lemma 13.11.6: every bounded-below derived object admits a bounded-below homotopy
representative. -/
theorem mapBoundedBelowHomotopyToDerivedBelow_essSurj
    :
    (mapBoundedBelowHomotopyToDerivedBelow (𝒜 := 𝒜)).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  let K : CochainComplex 𝒜 ℤ := DerivedCategory.Q.objPreimage Y.obj
  obtain ⟨a, hK⟩ := boundedBelow_objPreimage_eventually_isZero_homology (𝒜 := 𝒜) Y
  obtain ⟨a, hπ, htrunc⟩ :=
    exists_quasiIso_to_truncGE_of_eventually_isZero_homology (K := K) ⟨a, hK⟩
  let X : K⁺(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := K) a), by
      -- Proof comment: Lemma 13.11.5 produces a lower truncation which is bounded below.
      rw [HomotopyCategory.plus_iff]
      exact (CochainComplex.plus_iff 𝒜 _).2 ⟨a, htrunc⟩⟩
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  let eplus :
      ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.plus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_plus).app X
  let eQh :
      DerivedCategory.Qh.obj X.obj ≅
        DerivedCategory.Q.obj (CochainComplex.truncGE (K := K) a) := by
    simpa [X, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app (CochainComplex.truncGE (K := K) a)
  have hQπ : IsIso (DerivedCategory.Q.map (CochainComplex.πTruncGE (K := K) a)) := by
    -- Proof comment: the truncation map is a quasi-isomorphism, hence an isomorphism in `D(𝒜)`.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hπ
  let eAmbient :
      ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X) ≅ Y.obj :=
    eplus ≪≫ eQh ≪≫
      (asIso (DerivedCategory.Q.map (CochainComplex.πTruncGE (K := K) a))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso Y.obj
  let hFF :
      ιplus.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιplus
  exact ⟨X, ⟨hFF.preimageIso eAmbient⟩⟩

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded-below
localization model to `D^{+}(\mathcal A)`. -/
noncomputable abbrev boundedBelowLocalizationComparisonFunctor :
    ((Ac⁺(𝒜)).trW).Localization ⥤ D⁺(𝒜) :=
  Localization.lift mapBoundedBelowHomotopyToDerivedBelow
    mapBoundedBelowHomotopyToDerivedBelow_inverts_acyclic_trW
    ((Ac⁺(𝒜)).trW).Q

/-- Helper for Lemma 13.11.6: the bounded-below comparison functor is essentially surjective. -/
theorem boundedBelow_localization_comparison_essSurj
    :
    (boundedBelowLocalizationComparisonFunctor (𝒜 := 𝒜)).EssSurj := by
  let E := boundedBelowLocalizationComparisonFunctor (𝒜 := 𝒜)
  let hEss :
      mapBoundedBelowHomotopyToDerivedBelow.EssSurj :=
    mapBoundedBelowHomotopyToDerivedBelow_essSurj (𝒜 := 𝒜)
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨X, ⟨eX⟩⟩ := hEss.mem_essImage Y
  refine ⟨((Ac⁺(𝒜)).trW).Q.obj X, ⟨?_⟩⟩
  -- Proof comment: compare `E` with `mapBoundedBelowHomotopyToDerivedBelow` on an actual
  -- bounded-below complex and then reuse the chosen representative of `Y`.
  let eFac :
      E.obj (((Ac⁺(𝒜)).trW).Q.obj X) ≅
        mapBoundedBelowHomotopyToDerivedBelow.obj X :=
    (Localization.fac mapBoundedBelowHomotopyToDerivedBelow
      mapBoundedBelowHomotopyToDerivedBelow_inverts_acyclic_trW
      ((Ac⁺(𝒜)).trW).Q).app X
  exact eFac ≪≫ eX

/-- Helper for Lemma 13.11.6: the ambient bounded-below derived functor
`K^{+}(\mathcal A) ⟶ D(\mathcal A)` inverts the Verdier morphism property attached to
`Ac^{+}(\mathcal A)`. -/
theorem mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Ac⁺(𝒜)).trW)
      (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh) := by
  intro X Y f hf
  have hQis : Qis⁺(𝒜) f := by
    simpa [boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  -- Proof comment: after forgetting to the ambient homotopy category, this is exactly the
  -- unbounded derived localization inverting a quasi-isomorphism.
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.plus 𝒜).ι.map f))
  exact Localization.inverts
    (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
    (HomotopyCategory.quasiIso 𝒜 (up ℤ))
    ((HomotopyCategory.plus 𝒜).ι.map f)
    (by simpa [boundedBelowHomotopyQuasiIso] using hQis)

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded-below
localization model to the ambient derived category `D(\mathcal A)`. -/
noncomputable abbrev boundedBelowAmbientLocalizationComparisonFunctor :
    ((Ac⁺(𝒜)).trW).Localization ⥤ D(𝒜) :=
  Localization.lift
    (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh)
    mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
    ((Ac⁺(𝒜)).trW).Q

/-- Helper for Lemma 13.11.6: postcomposing a bounded-below left-fraction representative by a
further denominator in `Qis^{+}(\mathcal A)` does not change the represented localization
morphism. -/
private lemma boundedBelowLeftFraction_map_postcomp_eq
    {X Y Z : K⁺(𝒜)} (φ : ((Ac⁺(𝒜)).trW).LeftFraction X Y)
    (t : φ.Y' ⟶ Z) (ht : ((Ac⁺(𝒜)).trW) (φ.s ≫ t)) :
    φ.map
        ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)
        (Localization.inverts
          ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)
          ((Ac⁺(𝒜)).trW)) =
      (MorphismProperty.LeftFraction.mk (φ.f ≫ t) (φ.s ≫ t) ht).map
        ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)
        (Localization.inverts
          ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)
          ((Ac⁺(𝒜)).trW)) := by
  -- Proof comment: compare the original roof and its postcomposed refinement through the obvious
  -- common target `Z`.
  exact
    (MorphismProperty.LeftFraction.map_eq_iff
      (L := ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization))
      (W := ((Ac⁺(𝒜)).trW)) _ _).2 <| by
      refine ⟨Z, t, 𝟙 Z, ?_, ?_, ht⟩
      · simp
      · simp

/-- Helper for Lemma 13.11.6: passing a bounded-below roof through the ambient comparison
functor gives the corresponding ambient roof, conjugated by the canonical `Localization.fac`
isomorphisms. -/
private theorem boundedBelowAmbientLocalizationComparison_map_leftFraction
    {X Y : K⁺(𝒜)} (φ : ((Ac⁺(𝒜)).trW).LeftFraction X Y) :
    (boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map
        (φ.map
          ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)
          (Localization.inverts
            ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)
            ((Ac⁺(𝒜)).trW))) =
      (Localization.fac
        (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh)
        mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
        ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)).hom.app X ≫
        φ.map
          (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh)
          mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW ≫
        (Localization.fac
          (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh)
          mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
          ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)).inv.app Y := by
  -- Proof comment: this is exactly the general lift-on-left-fractions comparison for the bounded-
  -- below localization and the ambient derived functor.
  simpa [boundedBelowAmbientLocalizationComparisonFunctor] using
    localization_lift_map_leftFraction
      ((((Ac⁺(𝒜)).trW).Q) : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization)
      (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh)
      mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
      φ

/-- Helper for Lemma 13.11.6: any ambient morphism between bounded-below objects comes from a
unique morphism in `K^{+}(\mathcal A)`. -/
private theorem boundedBelow_preimage_hom
    {X Y : K⁺(𝒜)} (f : X.obj ⟶ Y.obj) :
    ∃ g : X ⟶ Y, ((HomotopyCategory.plus 𝒜).ι.map g) = f := by
  let ιplus : K⁺(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.plus 𝒜)
  let hFF : ιplus.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ιplus
  -- Proof comment: this packages the fully faithful inclusion `K^{+}(\mathcal A) ↪ K(\mathcal A)`
  -- in the existential form needed to descend ambient roof refinements.
  exact ⟨hFF.preimage f, hFF.map_preimage f⟩

/-- Helper for Lemma 13.11.6: every ambient derived morphism between bounded-below homotopy
objects is represented by a left fraction whose denominator still lies in `K^{+}(\mathcal A)`. -/
theorem boundedBelow_ambient_localization_comparison_surjective_on_Q_obj_hom
    (X Y : K⁺(𝒜)) :
    Function.Surjective
      (fun g : (((Ac⁺(𝒜)).trW).Q.obj X ⟶ ((Ac⁺(𝒜)).trW).Q.obj Y) =>
        (boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map g) := by
  let Qplus : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization := ((Ac⁺(𝒜)).trW).Q
  let F := boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)
  let G : K⁺(𝒜) ⥤ D(𝒜) := ((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh
  let eX :
      F.obj (Qplus.obj X) ≅ G.obj X :=
    (Localization.fac G
      mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
      Qplus).app X
  let eY :
      F.obj (Qplus.obj Y) ≅ G.obj Y :=
    (Localization.fac G
      mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
      Qplus).app Y
  intro h
  let hAmbient : DerivedCategory.Qh.obj X.obj ⟶ DerivedCategory.Qh.obj Y.obj :=
    eX.inv ≫ h ≫ eY.hom
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction
    (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
    (HomotopyCategory.quasiIso 𝒜 (up ℤ))
    hAmbient
  obtain ⟨Z, t, ht⟩ := quasiIso_to_bounded_below_refinement (𝒜 := 𝒜) Y φ.s φ.hs
  obtain ⟨fZ, hfZ⟩ := boundedBelow_preimage_hom (𝒜 := 𝒜) (φ.f ≫ t)
  obtain ⟨sZ, hsZeq⟩ := boundedBelow_preimage_hom (𝒜 := 𝒜) (φ.s ≫ t)
  have hfZeq' : fZ.hom = φ.f ≫ t := by
    simpa using hfZ
  have hsZeq' : sZ.hom = φ.s ≫ t := by
    simpa using hsZeq
  have hsComp :
      HomotopyCategory.quasiIso 𝒜 (up ℤ) (φ.s ≫ t) := by
    exact (HomotopyCategory.quasiIso 𝒜 (up ℤ)).comp_mem _ _ φ.hs ht
  have hsZqis : Qis⁺(𝒜) sZ := by
    change
      HomotopyCategory.quasiIso 𝒜 (up ℤ)
        sZ.hom
    rw [hsZeq']
    exact hsComp
  have hsZ :
      ((Ac⁺(𝒜)).trW) sZ := by
    simpa [boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hsZqis
  let ψ : ((Ac⁺(𝒜)).trW).LeftFraction X Y :=
    MorphismProperty.LeftFraction.mk fZ sZ hsZ
  let ψAmbient : (HomotopyCategory.quasiIso 𝒜 (up ℤ)).LeftFraction X.obj Y.obj :=
    MorphismProperty.LeftFraction.mk
      fZ.hom
      sZ.hom
      (by
        rw [hsZeq']
        exact hsComp)
  have hψmap :
      ψ.map G mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW =
        ψAmbient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) := by
    -- Proof comment: the bounded-below roof is literally the ambient roof after applying the
    -- inclusion `K^{+}(\mathcal A) ↪ K(\mathcal A)`.
    rfl
  have hψAmbient :
      ψAmbient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) =
        hAmbient := by
    -- Proof comment: refine the ambient denominator by `t`; the represented morphism does not
    -- change after postcomposing both roof arrows by a further quasi-isomorphism.
    have hrefine :
        φ.map
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (Localization.inverts
              (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
              (HomotopyCategory.quasiIso 𝒜 (up ℤ))) =
          ψAmbient.map
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (Localization.inverts
              (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) := by
      exact
        (MorphismProperty.LeftFraction.map_eq_iff
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (HomotopyCategory.quasiIso 𝒜 (up ℤ))
          φ ψAmbient).2 <| by
            refine ⟨Z.obj, t, 𝟙 _, ?_, ?_, hsComp⟩
            · simpa [ψAmbient, Category.assoc] using hsZeq'.symm
            · simpa [ψAmbient, Category.assoc] using hfZeq'.symm
    calc
      ψAmbient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ)))
          =
        φ.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) := hrefine.symm
      _ = hAmbient := hφ.symm
  refine ⟨ψ.map Qplus (Localization.inverts Qplus ((Ac⁺(𝒜)).trW)), ?_⟩
  calc
    F.map (ψ.map Qplus (Localization.inverts Qplus ((Ac⁺(𝒜)).trW)))
        = eX.hom ≫ ψ.map G mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW ≫ eY.inv := by
            simpa [F, Qplus] using
              boundedBelowAmbientLocalizationComparison_map_leftFraction (𝒜 := 𝒜) ψ
    _ = eX.hom ≫ hAmbient ≫ eY.inv := by
          rw [hψmap, hψAmbient]
          rfl
    _ = h := by
          calc
            eX.hom ≫ hAmbient ≫ eY.inv
                = eX.hom ≫ (eX.inv ≫ h ≫ eY.hom) ≫ eY.inv := by rfl
            _ = (eX.hom ≫ eX.inv) ≫ h ≫ (eY.hom ≫ eY.inv) := by
                  simp [Category.assoc]
            _ = h := by
                  simp

/-- Helper for Lemma 13.11.6: if two bounded-below roofs have the same image in the ambient
derived category, then they already agree in the bounded-below localization. -/
theorem boundedBelow_ambient_localization_comparison_injective_on_Q_obj_hom
    (X Y : K⁺(𝒜)) :
    Function.Injective
      (fun g : (((Ac⁺(𝒜)).trW).Q.obj X ⟶ ((Ac⁺(𝒜)).trW).Q.obj Y) =>
        (boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map g) := by
  let Qplus : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization := ((Ac⁺(𝒜)).trW).Q
  let F := boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)
  let G : K⁺(𝒜) ⥤ D(𝒜) := ((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh
  let eX :
      F.obj (Qplus.obj X) ≅ G.obj X :=
    (Localization.fac G
      mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
      Qplus).app X
  let eY :
      F.obj (Qplus.obj Y) ≅ G.obj Y :=
    (Localization.fac G
      mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
      Qplus).app Y
  intro g₁ g₂ h
  obtain ⟨φ, hφ₁, hφ₂⟩ := Localization.exists_leftFraction₂
    Qplus ((Ac⁺(𝒜)).trW) g₁ g₂
  have hsQis :
      Qis⁺(𝒜) φ.s := by
    simpa [boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using φ.hs
  let φ₁Ambient : (HomotopyCategory.quasiIso 𝒜 (up ℤ)).LeftFraction X.obj Y.obj :=
    MorphismProperty.LeftFraction.mk
      φ.f.hom
      φ.s.hom
      (by simpa [boundedBelowHomotopyQuasiIso] using hsQis)
  let φ₂Ambient : (HomotopyCategory.quasiIso 𝒜 (up ℤ)).LeftFraction X.obj Y.obj :=
    MorphismProperty.LeftFraction.mk
      φ.f'.hom
      φ.s.hom
      (by simpa [boundedBelowHomotopyQuasiIso] using hsQis)
  have hmap₁ :
      F.map (φ.fst.map Qplus (Localization.inverts Qplus ((Ac⁺(𝒜)).trW))) =
        eX.hom ≫ φ₁Ambient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) ≫
          eY.inv := by
    -- Proof comment: the first bounded-below roof is the corresponding ambient roof after
    -- forgetting the bounded structure.
    simpa [F, Qplus, φ₁Ambient] using
      boundedBelowAmbientLocalizationComparison_map_leftFraction (𝒜 := 𝒜) φ.fst
  have hmap₂ :
      F.map (φ.snd.map Qplus (Localization.inverts Qplus ((Ac⁺(𝒜)).trW))) =
        eX.hom ≫ φ₂Ambient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) ≫
          eY.inv := by
    -- Proof comment: the second bounded-below roof is handled by the same comparison formula.
    simpa [F, Qplus, φ₂Ambient] using
      boundedBelowAmbientLocalizationComparison_map_leftFraction (𝒜 := 𝒜) φ.snd
  have hAmbientMap :
      φ₁Ambient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) =
        φ₂Ambient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) := by
    have h' :
        eX.inv ≫ F.map g₁ ≫ eY.hom =
          eX.inv ≫ F.map g₂ ≫ eY.hom := by
      exact congrArg (fun k ↦ eX.inv ≫ k ≫ eY.hom) h
    -- Proof comment: cancel the `Localization.fac` conjugation to reduce to equality of the two
    -- ambient left fractions.
    rw [hφ₁, hmap₁, hφ₂, hmap₂] at h'
    simpa [Category.assoc] using h'
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ :=
    (MorphismProperty.LeftFraction.map_eq_iff
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      φ₁Ambient φ₂Ambient).1 hAmbientMap
  obtain ⟨Z', u, hu⟩ :=
    quasiIso_to_bounded_below_refinement (𝒜 := 𝒜) Y (φ.s.hom ≫ t₁) ht
  obtain ⟨u₁, hu₁eq⟩ := boundedBelow_preimage_hom
    (𝒜 := 𝒜) (X := φ.Y') (Y := Z') (t₁ ≫ u)
  obtain ⟨u₂, hu₂eq⟩ := boundedBelow_preimage_hom
    (𝒜 := 𝒜) (X := φ.Y') (Y := Z') (t₂ ≫ u)
  have hu₁eq' : u₁.hom = t₁ ≫ u := by
    simpa using hu₁eq
  have hu₂eq' : u₂.hom = t₂ ≫ u := by
    simpa using hu₂eq
  have hsRefined :
      Qis⁺(𝒜) (φ.s ≫ u₁) := by
    -- Proof comment: postcomposing the ambient relation by the bounded-below refinement keeps the
    -- denominator inside the quasi-isomorphisms.
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((HomotopyCategory.plus 𝒜).ι.map (φ.s ≫ u₁))
    rw [Functor.map_comp, hu₁eq]
    simpa [Category.assoc] using
      (HomotopyCategory.quasiIso 𝒜 (up ℤ)).comp_mem _ _ ht hu
  have hsRefinedTrW :
      ((Ac⁺(𝒜)).trW) (φ.s ≫ u₁) := by
    simpa [boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hsRefined
  have hrel :
      MorphismProperty.LeftFractionRel φ.fst φ.snd := by
    refine ⟨Z', u₁, u₂, ?_, ?_, hsRefinedTrW⟩
    · apply (ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map_injective
      simpa [Category.assoc, hu₁eq', hu₂eq'] using congrArg (fun k ↦ k ≫ u) hst
    · apply (ObjectProperty.ι (HomotopyCategory.plus 𝒜)).map_injective
      simpa [Category.assoc, hu₁eq', hu₂eq'] using congrArg (fun k ↦ k ≫ u) hft
  have hfracEq :
      φ.fst.map Qplus (Localization.inverts Qplus ((Ac⁺(𝒜)).trW)) =
        φ.snd.map Qplus (Localization.inverts Qplus ((Ac⁺(𝒜)).trW)) := by
    exact
      (MorphismProperty.LeftFraction.map_eq_iff
        Qplus ((Ac⁺(𝒜)).trW) φ.fst φ.snd).2 hrel
  rw [hφ₁, hφ₂]
  exact hfracEq

/-- Helper for Lemma 13.11.6: the comparison from the bounded-below localization model to the
ambient derived category is fully faithful. -/
theorem boundedBelow_ambient_localization_comparison_fullyFaithful :
    Nonempty (boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).FullyFaithful := by
  -- Proof comment: the localization functor is essentially surjective, so the hom-set bijections
  -- on actual `Q.obj` models promote to full faithfulness for the whole localization.
  let F := boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)
  let Q : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization := ((Ac⁺(𝒜)).trW).Q
  letI : Q.EssSurj := Localization.essSurj Q ((Ac⁺(𝒜)).trW)
  letI : F.Full :=
    Functor.full_of_comp_essSurj F Q
      (by
        intro X Y
        exact boundedBelow_ambient_localization_comparison_surjective_on_Q_obj_hom
          (𝒜 := 𝒜) X Y)
  letI : F.Faithful :=
    Functor.faithful_of_comp_essSurj F Q
      (by
        intro X Y
        exact boundedBelow_ambient_localization_comparison_injective_on_Q_obj_hom
          (𝒜 := 𝒜) X Y)
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

-- Proof sketch: Lemma 13.11.5 makes the bounded-below quasi-isomorphisms cofinal in the ambient
-- derived-category localization, so the canonical functor `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)`
-- satisfies the universal property of localization at `Qis^{+}(\mathcal A)`.
/-- Third localization statement of Lemma 13.11.6: the canonical functor
`K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)` realizes `D^{+}(\mathcal A)` as the localization of
`K^{+}(\mathcal A)` at `Qis^{+}(\mathcal A)`. -/
@[stacks 05RW]
theorem mapBoundedBelowHomotopyToDerivedBelow_isLocalization
    :
    Functor.IsLocalization
      mapBoundedBelowHomotopyToDerivedBelow
      (Qis⁺(𝒜)) := by
  let F := boundedBelowLocalizationComparisonFunctor (𝒜 := 𝒜)
  let Q : K⁺(𝒜) ⥤ ((Ac⁺(𝒜)).trW).Localization := ((Ac⁺(𝒜)).trW).Q
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  let Famb := boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)
  let eComp :
      F ⋙ ιplus ≅ Famb :=
    Localization.liftNatIso Q ((Ac⁺(𝒜)).trW)
      (Q ⋙ (F ⋙ ιplus))
      (Q ⋙ Famb)
      (F ⋙ ιplus)
      Famb
      ((Functor.associator Q F ιplus).symm ≪≫
        Functor.isoWhiskerRight
          (Localization.fac
            mapBoundedBelowHomotopyToDerivedBelow
            mapBoundedBelowHomotopyToDerivedBelow_inverts_acyclic_trW Q)
          ιplus ≪≫
        (ObjectProperty.liftCompιIso
          (t.plus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_plus) ≪≫
        (Localization.fac
          (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh)
          mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW Q).symm)
  obtain ⟨hFFAmb⟩ :
      Nonempty Famb.FullyFaithful :=
    boundedBelow_ambient_localization_comparison_fullyFaithful (𝒜 := 𝒜)
  let _ : Famb.Full := hFFAmb.full
  let _ : Famb.Faithful := hFFAmb.faithful
  let _ : F.Full := Functor.Full.of_comp_faithful_iso (F := F) (G := ιplus) (H := Famb) eComp
  let _ : F.Faithful := Functor.Faithful.of_comp_iso eComp
  let _ : F.EssSurj := boundedBelow_localization_comparison_essSurj (𝒜 := 𝒜)
  have hEqv : F.IsEquivalence := by
    exact
      { faithful := inferInstance
        full := inferInstance
        essSurj := inferInstance }
  let _ : F.IsEquivalence := hEqv
  have hLoc :
      mapBoundedBelowHomotopyToDerivedBelow.IsLocalization ((Ac⁺(𝒜)).trW) := by
    -- Proof comment: the bounded-below comparison functor is now an equivalence, so the bounded
    -- derived functor has the universal property of the source localization.
    exact
      Functor.IsLocalization.of_equivalence_target
        Q
        ((Ac⁺(𝒜)).trW)
        mapBoundedBelowHomotopyToDerivedBelow
        F.asEquivalence
        (Localization.fac
          mapBoundedBelowHomotopyToDerivedBelow
          mapBoundedBelowHomotopyToDerivedBelow_inverts_acyclic_trW
          Q)
  simpa [boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hLoc

-- Proof sketch: use the unbounded identification between quasi-isomorphisms and the Verdier
-- morphism property of acyclic complexes, then restrict it to the bounded-above full subcategory.
/-- Fourth localization statement of Lemma 13.11.6: the saturated multiplicative system
corresponding to `Ac^{-}(\mathcal A)` is precisely `Qis^{-}(\mathcal A)`. -/
@[stacks 05RW]
theorem boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Ac⁻(𝒜)).trW =
      Qis⁻(𝒜) := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedAboveHomotopyQuasiIso, HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]

-- Proof sketch: bounded-above objects die in `D^{-}(\mathcal A)` exactly when their image in the
-- unbounded derived category is acyclic, giving the same kernel criterion as in the bounded-below
-- case.
/-- Fifth localization statement of Lemma 13.11.6: the kernel of
`K^{-}(\mathcal A) ⟶ D^{-}(\mathcal A)` is `Ac^{-}(\mathcal A)`. -/
@[stacks 05RW]
theorem kernel_mapBoundedAboveHomotopyToDerivedAbove_eq_acyclic
    :
    Functor.kernel mapBoundedAboveHomotopyToDerivedAbove =
      Ac⁻(𝒜) := by
  -- Compare the bounded-above lift with the ambient quotient functor on underlying derived objects.
  ext X
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  let e :
      ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.minus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_minus).app X
  constructor
  · intro hX
    have hUnderlying : IsZero (ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X)) :=
      ιminus.map_isZero hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := e.isZero_iff.1 hUnderlying
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := hQh
    rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)] at hker
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hker
  · intro hX
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := by
      rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)]
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := hker
    have hUnderlying : IsZero (ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X)) :=
      e.isZero_iff.2 hQh
    exact IsZero.of_full_of_faithful_of_isZero ιminus _ hUnderlying

/-- Helper for Lemma 13.11.6: the bounded-above derived functor inverts the Verdier morphism
property attached to the bounded-above acyclic subcategory. -/
theorem mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Ac⁻(𝒜)).trW)
      mapBoundedAboveHomotopyToDerivedAbove := by
  intro X Y f hf
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  have hQis : Qis⁻(𝒜) f := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  have hUnderlying :
      IsIso (((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is exactly the
    -- unbounded derived localization inverting a quasi-isomorphism.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.minus 𝒜).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.minus 𝒜).ι.map f)
      (by simpa [boundedAboveHomotopyQuasiIso] using hQis)
  have hLifted :
      IsIso (ιminus.map (mapBoundedAboveHomotopyToDerivedAbove.map f)) := by
    -- Proof comment: the lift-to-inclusion comparison transports invertibility back to `D⁻`.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_minus)
        f)).2 hUnderlying
  let _ : IsIso (ιminus.map (mapBoundedAboveHomotopyToDerivedAbove.map f)) := hLifted
  exact isIso_of_fully_faithful ιminus (mapBoundedAboveHomotopyToDerivedAbove.map f)

/-- Helper for Lemma 13.11.6: a chosen cochain-level preimage of a bounded-above derived object
has vanishing homology in sufficiently large degrees. -/
theorem boundedAbove_objPreimage_eventually_isZero_homology
    (X : D⁻(𝒜)) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((DerivedCategory.Q.objPreimage X.obj).homology i) := by
  -- Proof comment: transfer the bounded-above vanishing of `X` along the canonical preimage
  -- isomorphism in the ambient derived category.
  obtain ⟨b, hb⟩ := (derivedCategory_t_minus_iff (K := X.obj)).1 X.property
  refine ⟨b, ?_⟩
  intro i hi
  have hXi : IsZero ((H^i).obj X.obj) := hb i hi
  have hQpreimage :
      IsZero
        ((H^i).obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj))) := by
    let e :
        (H^i).obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj)) ≅
          (H^i).obj X.obj :=
      (H^i).mapIso (DerivedCategory.Q.objObjPreimageIso X.obj)
    exact (e.isZero_iff).2 hXi
  exact
    (((DerivedCategory.homologyFunctorFactors 𝒜 i).app
      (DerivedCategory.Q.objPreimage X.obj)).isZero_iff).1 hQpreimage

/-- Helper for Lemma 13.11.6: every bounded-above derived object admits a bounded-above homotopy
representative. -/
theorem mapBoundedAboveHomotopyToDerivedAbove_essSurj
    :
    (mapBoundedAboveHomotopyToDerivedAbove (𝒜 := 𝒜)).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  let K : CochainComplex 𝒜 ℤ := DerivedCategory.Q.objPreimage Y.obj
  obtain ⟨b, hK⟩ := boundedAbove_objPreimage_eventually_isZero_homology (𝒜 := 𝒜) Y
  obtain ⟨b, hι, htrunc⟩ :=
    exists_quasiIso_from_truncLE_of_eventually_isZero_homology (K := K) ⟨b, hK⟩
  let X : K⁻(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncLE (K := K) b), by
      rw [HomotopyCategory.minus_iff]
      exact (CochainComplex.minus_iff 𝒜 _).2 ⟨b, htrunc⟩⟩
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  let eminus :
      ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.minus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_minus).app X
  let eQh :
      DerivedCategory.Qh.obj X.obj ≅
        DerivedCategory.Q.obj (CochainComplex.truncLE (K := K) b) := by
    simpa [X, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app (CochainComplex.truncLE (K := K) b)
  have hQι : IsIso (DerivedCategory.Q.map (CochainComplex.ιTruncLE (K := K) b)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hι
  let eAmbient :
      ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X) ≅ Y.obj :=
    eminus ≪≫ eQh ≪≫
      asIso (DerivedCategory.Q.map (CochainComplex.ιTruncLE (K := K) b)) ≪≫
        DerivedCategory.Q.objObjPreimageIso Y.obj
  let hFF :
      ιminus.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιminus
  exact ⟨X, ⟨hFF.preimageIso eAmbient⟩⟩

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded-above
localization model to `D^{-}(\mathcal A)`. -/
noncomputable abbrev boundedAboveLocalizationComparisonFunctor :
    ((Ac⁻(𝒜)).trW).Localization ⥤ D⁻(𝒜) :=
  Localization.lift mapBoundedAboveHomotopyToDerivedAbove
    mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW
    ((Ac⁻(𝒜)).trW).Q

/-- Helper for Lemma 13.11.6: the bounded-above comparison functor is essentially surjective. -/
theorem boundedAbove_localization_comparison_essSurj
    :
    (boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)).EssSurj := by
  let F := boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)
  let hEss :
      mapBoundedAboveHomotopyToDerivedAbove.EssSurj :=
    mapBoundedAboveHomotopyToDerivedAbove_essSurj (𝒜 := 𝒜)
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨X, ⟨eX⟩⟩ := hEss.mem_essImage Y
  refine ⟨((Ac⁻(𝒜)).trW).Q.obj X, ⟨?_⟩⟩
  let eFac :
      F.obj (((Ac⁻(𝒜)).trW).Q.obj X) ≅
        mapBoundedAboveHomotopyToDerivedAbove.obj X :=
    (Localization.fac mapBoundedAboveHomotopyToDerivedAbove
      mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW
      ((Ac⁻(𝒜)).trW).Q).app X
  exact eFac ≪≫ eX

/-- Helper for Lemma 13.11.6: the ambient bounded-above derived functor
`K^{-}(\mathcal A) ⟶ D(\mathcal A)` inverts the Verdier morphism property attached to
`Ac^{-}(\mathcal A)`. -/
theorem mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Ac⁻(𝒜)).trW)
      (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh) := by
  intro X Y f hf
  have hQis : Qis⁻(𝒜) f := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.minus 𝒜).ι.map f))
  exact Localization.inverts
    (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
    (HomotopyCategory.quasiIso 𝒜 (up ℤ))
    ((HomotopyCategory.minus 𝒜).ι.map f)
    (by simpa [boundedAboveHomotopyQuasiIso] using hQis)

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded-above
localization model to the ambient derived category `D(\mathcal A)`. -/
noncomputable abbrev boundedAboveAmbientLocalizationComparisonFunctor :
    ((Ac⁻(𝒜)).trW).Localization ⥤ D(𝒜) :=
  Localization.lift
    (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh)
    mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
    ((Ac⁻(𝒜)).trW).Q

/-- Helper for Lemma 13.11.6: precomposing a bounded-above right-fraction representative by a
further denominator in `Qis^{-}(\mathcal A)` does not change the represented localization
morphism. -/
private lemma boundedAboveRightFraction_map_precomp_eq
    {X Y Z : K⁻(𝒜)} (φ : ((Ac⁻(𝒜)).trW).RightFraction X Y)
    (t : Z ⟶ φ.X') (ht : ((Ac⁻(𝒜)).trW) (t ≫ φ.s)) :
    φ.map
        ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
        (Localization.inverts
          ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
          ((Ac⁻(𝒜)).trW)) =
      (MorphismProperty.RightFraction.mk (t ≫ φ.s) ht (t ≫ φ.f)).map
        ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
        (Localization.inverts
          ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
          ((Ac⁻(𝒜)).trW)) := by
  -- Proof comment: compare the original roof and its precomposed refinement through the obvious
  -- common source `Z`.
  exact
    (MorphismProperty.RightFraction.map_eq_iff
      (L := ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization))
      (W := ((Ac⁻(𝒜)).trW)) _ _).2 <| by
      refine ⟨Z, t, 𝟙 Z, ?_, ?_, ht⟩
      · simp
      · simp

/-- Helper for Lemma 13.11.6: passing a bounded-above roof through the ambient comparison
functor gives the corresponding ambient roof, conjugated by the canonical `Localization.fac`
isomorphisms. -/
private theorem boundedAboveAmbientLocalizationComparison_map_rightFraction
    {X Y : K⁻(𝒜)} (φ : ((Ac⁻(𝒜)).trW).RightFraction X Y) :
    (boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map
        (φ.map
          ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
          (Localization.inverts
            ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
            ((Ac⁻(𝒜)).trW))) =
      (Localization.fac
        (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh)
        mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
        ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)).hom.app X ≫
        φ.map
          (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh)
          mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW ≫
        (Localization.fac
          (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh)
          mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
          ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)).inv.app Y := by
  -- Proof comment: this is the right-fraction version of the same conjugation formula.
  simpa [boundedAboveAmbientLocalizationComparisonFunctor] using
    localization_lift_map_rightFraction
      ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
      (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh)
      mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
      φ

/-- Helper for Lemma 13.11.6: any ambient morphism between bounded-above objects comes from a
unique morphism in `K^{-}(\mathcal A)`. -/
private theorem boundedAbove_preimage_hom
    {X Y : K⁻(𝒜)} (f : X.obj ⟶ Y.obj) :
    ∃ g : X ⟶ Y, ((HomotopyCategory.minus 𝒜).ι.map g) = f := by
  let ιminus : K⁻(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.minus 𝒜)
  let hFF : ιminus.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ιminus
  -- Proof comment: this packages the fully faithful inclusion `K^{-}(\mathcal A) ↪ K(\mathcal A)`
  -- so that ambient source refinements can be descended to bounded-above roofs.
  exact ⟨hFF.preimage f, hFF.map_preimage f⟩

/-- Helper for Lemma 13.11.6: every ambient derived morphism between bounded-above homotopy
objects is represented by a right fraction whose source still lies in `K^{-}(\mathcal A)`. -/
theorem boundedAbove_ambient_localization_comparison_surjective_on_Q_obj_hom
    (X Y : K⁻(𝒜)) :
    Function.Surjective
      (fun g : (((Ac⁻(𝒜)).trW).Q.obj X ⟶ ((Ac⁻(𝒜)).trW).Q.obj Y) =>
        (boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map g) := by
  let Qminus : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := ((Ac⁻(𝒜)).trW).Q
  let F := boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)
  let G : K⁻(𝒜) ⥤ D(𝒜) := ((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh
  let eX :
      F.obj (Qminus.obj X) ≅ G.obj X :=
    (Localization.fac G
      mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
      Qminus).app X
  let eY :
      F.obj (Qminus.obj Y) ≅ G.obj Y :=
    (Localization.fac G
      mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
      Qminus).app Y
  intro h
  let hAmbient : DerivedCategory.Qh.obj X.obj ⟶ DerivedCategory.Qh.obj Y.obj :=
    eX.inv ≫ h ≫ eY.hom
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction
    (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
    (HomotopyCategory.quasiIso 𝒜 (up ℤ))
    hAmbient
  obtain ⟨Z, t, ht⟩ := quasiIso_from_bounded_above_refinement (𝒜 := 𝒜) X φ.s φ.hs
  obtain ⟨fZ, hfZ⟩ := boundedAbove_preimage_hom (𝒜 := 𝒜) (t ≫ φ.f)
  obtain ⟨sZ, hsZeq⟩ := boundedAbove_preimage_hom (𝒜 := 𝒜) (t ≫ φ.s)
  have hfZeq' : fZ.hom = t ≫ φ.f := by
    simpa using hfZ
  have hsZeq' : sZ.hom = t ≫ φ.s := by
    simpa using hsZeq
  have hsComp :
      HomotopyCategory.quasiIso 𝒜 (up ℤ) (t ≫ φ.s) := by
    exact (HomotopyCategory.quasiIso 𝒜 (up ℤ)).comp_mem _ _ ht φ.hs
  have hsZqis : Qis⁻(𝒜) sZ := by
    change
      HomotopyCategory.quasiIso 𝒜 (up ℤ)
        sZ.hom
    rw [hsZeq']
    exact hsComp
  have hsZ :
      ((Ac⁻(𝒜)).trW) sZ := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hsZqis
  let ψ : ((Ac⁻(𝒜)).trW).RightFraction X Y :=
    MorphismProperty.RightFraction.mk sZ hsZ fZ
  let ψAmbient : (HomotopyCategory.quasiIso 𝒜 (up ℤ)).RightFraction X.obj Y.obj :=
    MorphismProperty.RightFraction.mk
      sZ.hom
      (by
        rw [hsZeq']
        exact hsComp)
      fZ.hom
  have hψmap :
      ψ.map G mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW =
        ψAmbient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) := by
    -- Proof comment: the bounded-above roof is exactly the ambient roof transported through the
    -- inclusion `K^{-}(\mathcal A) ↪ K(\mathcal A)`.
    rfl
  have hψAmbient :
      ψAmbient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) =
        hAmbient := by
    -- Proof comment: precomposing the ambient roof by the further quasi-isomorphism `t` leaves
    -- the represented right-fraction morphism unchanged.
    have hrefine :
        φ.map
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (Localization.inverts
              (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
              (HomotopyCategory.quasiIso 𝒜 (up ℤ))) =
          ψAmbient.map
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (Localization.inverts
              (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
              (HomotopyCategory.quasiIso 𝒜 (up ℤ))) := by
      exact
        (MorphismProperty.RightFraction.map_eq_iff
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (HomotopyCategory.quasiIso 𝒜 (up ℤ))
          φ ψAmbient).2 <| by
            refine ⟨Z.obj, t, 𝟙 _, ?_, ?_, hsComp⟩
            · simpa [ψAmbient, Category.assoc] using hsZeq'.symm
            · simpa [ψAmbient, Category.assoc] using hfZeq'.symm
    calc
      ψAmbient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ)))
          =
        φ.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) := hrefine.symm
      _ = hAmbient := hφ.symm
  refine ⟨ψ.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)), ?_⟩
  calc
    F.map (ψ.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)))
        = eX.hom ≫ ψ.map G mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW ≫ eY.inv := by
            simpa [F, Qminus] using
              boundedAboveAmbientLocalizationComparison_map_rightFraction (𝒜 := 𝒜) ψ
    _ = eX.hom ≫ hAmbient ≫ eY.inv := by
          rw [hψmap, hψAmbient]
          rfl
    _ = h := by
          calc
            eX.hom ≫ hAmbient ≫ eY.inv
                = eX.hom ≫ (eX.inv ≫ h ≫ eY.hom) ≫ eY.inv := by rfl
            _ = (eX.hom ≫ eX.inv) ≫ h ≫ (eY.hom ≫ eY.inv) := by
                  simp [Category.assoc]
            _ = h := by
                  simp

/-- Helper for Lemma 13.11.6: if two bounded-above roofs have the same image in the ambient
derived category, then they already agree in the bounded-above localization. -/
theorem boundedAbove_ambient_localization_comparison_injective_on_Q_obj_hom
    (X Y : K⁻(𝒜)) :
    Function.Injective
      (fun g : (((Ac⁻(𝒜)).trW).Q.obj X ⟶ ((Ac⁻(𝒜)).trW).Q.obj Y) =>
        (boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map g) := by
  let Qminus : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := ((Ac⁻(𝒜)).trW).Q
  let F := boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)
  let G : K⁻(𝒜) ⥤ D(𝒜) := ((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh
  let eX :
      F.obj (Qminus.obj X) ≅ G.obj X :=
    (Localization.fac G
      mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
      Qminus).app X
  let eY :
      F.obj (Qminus.obj Y) ≅ G.obj Y :=
    (Localization.fac G
      mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
      Qminus).app Y
  intro g₁ g₂ h
  obtain ⟨φ₁, hφ₁⟩ := Localization.exists_rightFraction
    Qminus ((Ac⁻(𝒜)).trW) g₁
  obtain ⟨φ₂, hφ₂⟩ := Localization.exists_rightFraction
    Qminus ((Ac⁻(𝒜)).trW) g₂
  have hs₁Qis :
      Qis⁻(𝒜) φ₁.s := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using φ₁.hs
  have hs₂Qis :
      Qis⁻(𝒜) φ₂.s := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using φ₂.hs
  let φ₁Ambient : (HomotopyCategory.quasiIso 𝒜 (up ℤ)).RightFraction X.obj Y.obj :=
    MorphismProperty.RightFraction.mk
      φ₁.s.hom
      (by simpa [boundedAboveHomotopyQuasiIso] using hs₁Qis)
      φ₁.f.hom
  let φ₂Ambient : (HomotopyCategory.quasiIso 𝒜 (up ℤ)).RightFraction X.obj Y.obj :=
    MorphismProperty.RightFraction.mk
      φ₂.s.hom
      (by simpa [boundedAboveHomotopyQuasiIso] using hs₂Qis)
      φ₂.f.hom
  have hmap₁ :
      F.map (φ₁.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW))) =
        eX.hom ≫ φ₁Ambient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) ≫
          eY.inv := by
    -- Proof comment: the first bounded-above roof is already the ambient roof after forgetting
    -- the bounded-above structure.
    simpa [F, Qminus, φ₁Ambient] using
      boundedAboveAmbientLocalizationComparison_map_rightFraction (𝒜 := 𝒜) φ₁
  have hmap₂ :
      F.map (φ₂.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW))) =
        eX.hom ≫ φ₂Ambient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) ≫
          eY.inv := by
    -- Proof comment: the second roof uses the same transport formula.
    simpa [F, Qminus, φ₂Ambient] using
      boundedAboveAmbientLocalizationComparison_map_rightFraction (𝒜 := 𝒜) φ₂
  have hAmbientMap :
      φ₁Ambient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) =
        φ₂Ambient.map
          (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
          (Localization.inverts
            (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
            (HomotopyCategory.quasiIso 𝒜 (up ℤ))) := by
    have h' :
        eX.inv ≫ F.map g₁ ≫ eY.hom =
          eX.inv ≫ F.map g₂ ≫ eY.hom := by
      exact congrArg (fun k ↦ eX.inv ≫ k ≫ eY.hom) h
    -- Proof comment: cancel the localization comparison isomorphisms to compare ambient roofs.
    rw [hφ₁, hmap₁, hφ₂, hmap₂] at h'
    simpa [Category.assoc] using h'
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      φ₁Ambient φ₂Ambient).1 hAmbientMap
  obtain ⟨Z', u, hu⟩ :=
    quasiIso_from_bounded_above_refinement (𝒜 := 𝒜) X (t₁ ≫ φ₁.s.hom) ht
  obtain ⟨u₁, hu₁eq⟩ := boundedAbove_preimage_hom
    (𝒜 := 𝒜) (X := Z') (Y := φ₁.X') (u ≫ t₁)
  obtain ⟨u₂, hu₂eq⟩ := boundedAbove_preimage_hom
    (𝒜 := 𝒜) (X := Z') (Y := φ₂.X') (u ≫ t₂)
  have hu₁eq' : u₁.hom = u ≫ t₁ := by
    simpa using hu₁eq
  have hu₂eq' : u₂.hom = u ≫ t₂ := by
    simpa using hu₂eq
  have hsRefined :
      Qis⁻(𝒜) (u₁ ≫ φ₁.s) := by
    -- Proof comment: after refining the common source, the new denominator is still a
    -- quasi-isomorphism in `K^{-}(\mathcal A)`.
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((HomotopyCategory.minus 𝒜).ι.map (u₁ ≫ φ₁.s))
    rw [Functor.map_comp, hu₁eq]
    simpa [Category.assoc] using
      (HomotopyCategory.quasiIso 𝒜 (up ℤ)).comp_mem _ _ hu ht
  have hsRefinedTrW :
      ((Ac⁻(𝒜)).trW) (u₁ ≫ φ₁.s) := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hsRefined
  have hrel :
      MorphismProperty.RightFractionRel φ₁ φ₂ := by
    refine ⟨Z', u₁, u₂, ?_, ?_, hsRefinedTrW⟩
    · apply (ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map_injective
      simpa [Category.assoc, hu₁eq', hu₂eq'] using congrArg (fun k ↦ u ≫ k) hst
    · apply (ObjectProperty.ι (HomotopyCategory.minus 𝒜)).map_injective
      simpa [Category.assoc, hu₁eq', hu₂eq'] using congrArg (fun k ↦ u ≫ k) hft
  have hfracEq :
      φ₁.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) =
        φ₂.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) := by
    exact
      (MorphismProperty.RightFraction.map_eq_iff
        Qminus ((Ac⁻(𝒜)).trW) φ₁ φ₂).2 hrel
  rw [hφ₁, hφ₂]
  exact hfracEq

/-- Helper for Lemma 13.11.6: the comparison from the bounded-above localization model to the
ambient derived category is fully faithful. -/
theorem boundedAbove_ambient_localization_comparison_fullyFaithful :
    Nonempty (boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).FullyFaithful := by
  -- Proof comment: the dual hom-set bijections on `Q.obj`-objects extend to the whole source
  -- because the localization functor is essentially surjective.
  let F := boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)
  let Q : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := ((Ac⁻(𝒜)).trW).Q
  letI : Q.EssSurj := Localization.essSurj Q ((Ac⁻(𝒜)).trW)
  letI : F.Full :=
    Functor.full_of_comp_essSurj F Q
      (by
        intro X Y
        exact boundedAbove_ambient_localization_comparison_surjective_on_Q_obj_hom
          (𝒜 := 𝒜) X Y)
  letI : F.Faithful :=
    Functor.faithful_of_comp_essSurj F Q
      (by
        intro X Y
        exact boundedAbove_ambient_localization_comparison_injective_on_Q_obj_hom
          (𝒜 := 𝒜) X Y)
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

/-- Helper for Lemma 13.11.6: the bounded-above comparison functor from the localization model
to `D^{-}(\mathcal A)` is an equivalence. -/
theorem boundedAboveLocalizationComparisonFunctor_isEquivalence
    :
    (boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)).IsEquivalence := by
  let F := boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)
  let Q : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := ((Ac⁻(𝒜)).trW).Q
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  let Famb := boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)
  let eComp :
      F ⋙ ιminus ≅ Famb :=
    Localization.liftNatIso Q ((Ac⁻(𝒜)).trW)
      (Q ⋙ (F ⋙ ιminus))
      (Q ⋙ Famb)
      (F ⋙ ιminus)
      Famb
      ((Functor.associator Q F ιminus).symm ≪≫
        Functor.isoWhiskerRight
          (Localization.fac
            mapBoundedAboveHomotopyToDerivedAbove
            mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW Q)
          ιminus ≪≫
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_minus) ≪≫
        (Localization.fac
          (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh)
          mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW Q).symm)
  obtain ⟨hFFAmb⟩ :
      Nonempty Famb.FullyFaithful :=
    boundedAbove_ambient_localization_comparison_fullyFaithful (𝒜 := 𝒜)
  let _ : Famb.Full := hFFAmb.full
  let _ : Famb.Faithful := hFFAmb.faithful
  let _ : F.Full := Functor.Full.of_comp_faithful_iso (F := F) (G := ιminus) (H := Famb) eComp
  let _ : F.Faithful := Functor.Faithful.of_comp_iso eComp
  let _ : F.EssSurj := boundedAbove_localization_comparison_essSurj (𝒜 := 𝒜)
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

-- Proof sketch: Lemma 13.11.5 yields bounded-above representatives for the denominators in the
-- ambient localization, so the bounded-above functor has the universal property of localization at
-- `Qis^{-}(\mathcal A)`.
/-- Sixth localization statement of Lemma 13.11.6: the canonical functor
`K^{-}(\mathcal A) ⟶ D^{-}(\mathcal A)` realizes `D^{-}(\mathcal A)` as the localization of
`K^{-}(\mathcal A)` at `Qis^{-}(\mathcal A)`. -/
@[stacks 05RW]
theorem mapBoundedAboveHomotopyToDerivedAbove_isLocalization
    :
    Functor.IsLocalization
      mapBoundedAboveHomotopyToDerivedAbove
      (Qis⁻(𝒜)) := by
  let Q : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := ((Ac⁻(𝒜)).trW).Q
  let F := boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)
  have hEqv : F.IsEquivalence :=
    boundedAboveLocalizationComparisonFunctor_isEquivalence (𝒜 := 𝒜)
  let _ : F.IsEquivalence := hEqv
  have hLoc :
      mapBoundedAboveHomotopyToDerivedAbove.IsLocalization ((Ac⁻(𝒜)).trW) := by
    -- Proof comment: once the bounded-above comparison functor is an equivalence, the bounded-
    -- above derived functor inherits the universal property of the source localization.
    exact
      Functor.IsLocalization.of_equivalence_target
        Q
        ((Ac⁻(𝒜)).trW)
        mapBoundedAboveHomotopyToDerivedAbove
        F.asEquivalence
        (Localization.fac
          mapBoundedAboveHomotopyToDerivedAbove
          mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW
          Q)
  simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hLoc

-- Proof sketch: identify quasi-isomorphisms with the Verdier morphism property of acyclic
-- complexes in the ambient homotopy category and restrict to the bounded full subcategory.
/-- Seventh localization statement of Lemma 13.11.6: the saturated multiplicative system
corresponding to `Ac^{b}(\mathcal A)` is precisely `Qis^{b}(\mathcal A)`. -/
@[stacks 05RW]
theorem boundedAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Acᵇ(𝒜)).trW =
      Qisᵇ(𝒜) := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedHomotopyQuasiIso, HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]

-- Proof sketch: a bounded homotopy object becomes zero in `D^{b}(\mathcal A)` exactly when its
-- image in `D(\mathcal A)` is acyclic, so the kernel is the bounded acyclic subcategory.
/-- Eighth localization statement of Lemma 13.11.6: the kernel of
`K^{b}(\mathcal A) ⟶ D^{b}(\mathcal A)` is `Ac^{b}(\mathcal A)`. -/
@[stacks 05RW]
theorem kernel_mapBoundedHomotopyToDerivedBounded_eq_acyclic
    :
    Functor.kernel mapBoundedHomotopyToDerivedBounded =
      Acᵇ(𝒜) := by
  -- Compare the bounded lift with the ambient quotient functor on underlying derived objects.
  ext X
  let ιbounded : Dᵇ(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.bounded : ObjectProperty (D(𝒜)))
  let e :
      ιbounded.obj (mapBoundedHomotopyToDerivedBounded.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.bounded : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_bounded).app X
  constructor
  · intro hX
    have hUnderlying : IsZero (ιbounded.obj (mapBoundedHomotopyToDerivedBounded.obj X)) :=
      ιbounded.map_isZero hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := e.isZero_iff.1 hUnderlying
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := hQh
    rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)] at hker
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hker
  · intro hX
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := by
      rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)]
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := hker
    have hUnderlying : IsZero (ιbounded.obj (mapBoundedHomotopyToDerivedBounded.obj X)) :=
      e.isZero_iff.2 hQh
    exact IsZero.of_full_of_faithful_of_isZero ιbounded _ hUnderlying

/-- Helper for Lemma 13.11.6: the bounded derived functor inverts the Verdier morphism property
attached to the bounded acyclic subcategory. -/
theorem mapBoundedHomotopyToDerivedBounded_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Acᵇ(𝒜)).trW)
      mapBoundedHomotopyToDerivedBounded := by
  intro X Y f hf
  let ιbounded : Dᵇ(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.bounded : ObjectProperty (D(𝒜)))
  have hQis : Qisᵇ(𝒜) f := by
    simpa [boundedAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  have hUnderlying :
      IsIso (((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is exactly the
    -- unbounded derived localization inverting a quasi-isomorphism.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.bounded 𝒜).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.bounded 𝒜).ι.map f)
      (by simpa [boundedHomotopyQuasiIso] using hQis)
  have hLifted :
      IsIso (ιbounded.map (mapBoundedHomotopyToDerivedBounded.map f)) := by
    -- Proof comment: the lift-to-inclusion comparison transports invertibility back to `Dᵇ`.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.bounded : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_bounded)
        f)).2 hUnderlying
  let _ : IsIso (ιbounded.map (mapBoundedHomotopyToDerivedBounded.map f)) := hLifted
  exact isIso_of_fully_faithful ιbounded (mapBoundedHomotopyToDerivedBounded.map f)

/- Proof sketch: apply the bounded-below refinement argument to the quasi-isomorphism
`s : X ⟶ Y`, but keep track of the ambient bounded-above hypothesis on `Y`; the lower truncation
produced there is a truncation of `Y.as`, so it remains bounded above as well. -/
/-- Helper for Lemma 13.11.6: the retained degree `n` of the lower truncation embedding
`embeddingUpIntGE a` is indexed by `n - a`. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (a n : ℤ) (han : a ≤ n) :
    (ComplexShape.embeddingUpIntGE a).f (Int.toNat (n - a)) = n := by
  -- Proof comment: on the retained range, the embedding is the affine map `i ↦ a + i`.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 13.11.6: above the cutoff, smart lower truncation keeps the original term. -/
private noncomputable def truncGE_term_iso_of_gt
    (K : CochainComplex 𝒜 ℤ) (a n : ℤ) (han : a < n) :
    (K.truncGE a).X n ≅ K.X n :=
  let i : ℕ := Int.toNat (n - a)
  let hi' : (ComplexShape.embeddingUpIntGE a).f i = n :=
    embeddingUpIntGE_toNat_sub_eq a n (le_of_lt han)
  let hboundary : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE i := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hi0
    have : a = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntGE] using hi'
    omega
  K.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 13.11.6: if `K` is strictly zero above `b`, then any smart lower truncation
at a cutoff `a ≤ b` is still strictly zero above `b`. -/
private theorem truncGE_isStrictlyLE_of_isStrictlyLE
    (K : CochainComplex 𝒜 ℤ) (a b : ℤ)
    (ha_le_b : a ≤ b) (hK : K.IsStrictlyLE b) :
    (K.truncGE a).IsStrictlyLE b := by
  -- Proof comment: for `n > b`, the cutoff lies strictly below `n`, so the truncation term is
  -- canonically the original term of `K`, which already vanishes.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have han : a < n := lt_of_le_of_lt ha_le_b hn
  exact ((truncGE_term_iso_of_gt (K := K) a n han).isZero_iff).2
    (by
      rw [CochainComplex.isStrictlyLE_iff] at hK
      exact hK n hn)

/-- Helper for Lemma 13.11.6: a quasi-isomorphism from a bounded complex to a bounded-above
complex can be refined so that the target is bounded on both sides. -/
lemma quasiIso_to_bounded_refinement_of_bounded_above
    (X : Kᵇ(𝒜)) (Y : K⁻(𝒜)) (s : X.obj ⟶ Y.obj)
    (hs : HomotopyCategory.quasiIso 𝒜 (up ℤ) s) :
    ∃ (Y' : Kᵇ(𝒜)) (t : Y.obj ⟶ Y'.obj), HomotopyCategory.quasiIso 𝒜 (up ℤ) t := by
  -- Proof comment: keep the source-proof route from the bounded-below refinement, but choose the
  -- lower cutoff `a := min a₀ b` so the smart truncation of `Y` is still bounded above by `b`.
  let Xplus : K⁺(𝒜) :=
    ⟨X.obj, (HomotopyCategory.plus_iff (𝒜 := 𝒜) X.obj).2 <| by
      exact (CochainComplex.bounded_iff 𝒜 X.obj.as).1
        ((HomotopyCategory.bounded_iff (𝒜 := 𝒜) X.obj).1 X.property) |>.1⟩
  rw [HomotopyCategory.mem_quasiIso_iff] at hs
  obtain ⟨a₀, hXge⟩ :=
    (CochainComplex.plus_iff 𝒜 Xplus.obj.as).1
      ((HomotopyCategory.plus_iff (𝒜 := 𝒜) Xplus.obj).1 Xplus.property)
  obtain ⟨b, hYle⟩ :=
    (CochainComplex.minus_iff 𝒜 Y.obj.as).1
      ((HomotopyCategory.minus_iff (𝒜 := 𝒜) Y.obj).1 Y.property)
  let a : ℤ := min a₀ b
  have ha_le_b : a ≤ b := by
    dsimp [a]
    exact Int.min_le_right _ _
  have hYeventual : ∀ n : ℤ, n < a → IsZero (Y.obj.as.homology n) := by
    intro n hn
    let KX : CochainComplex 𝒜 ℤ := Xplus.obj.as
    let _ : KX.IsStrictlyGE a₀ := by
      simpa [KX] using hXge
    let _ : KX.HasHomology n := inferInstance
    have hXhomology : IsZero (KX.homology n) :=
      CochainComplex.isZero_of_isGE (K := KX) a₀ n (lt_of_lt_of_le hn <| by
        dsimp [a]
        exact Int.min_le_left _ _)
    have hXhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Xplus.obj)) := by
      simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
        HomotopyCategory.quotient_obj_as] using
        (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KX).isZero_iff).2
          hXhomology
    have hYhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Y.obj)) := by
      exact IsZero.of_iso hXhomotopy
        ((asIso ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).map s)).symm)
    let KY : CochainComplex 𝒜 ℤ := Y.obj.as
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, KY] using
      (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KY).isZero_iff).1
        hYhomotopy
  let KY : CochainComplex 𝒜 ℤ := Y.obj.as
  have hYge : KY.IsGE a := by
    -- Proof comment: vanishing of homology below `a` upgrades to the standard exactness owner.
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    simpa [KY] using hYeventual n hn
  let _ : KY.IsGE a := hYge
  have hπ : QuasiIso (CochainComplex.πTruncGE (K := KY) a) := inferInstance
  have htruncGE : (CochainComplex.truncGE (K := KY) a).IsStrictlyGE a := inferInstance
  have htruncLE : (CochainComplex.truncGE (K := KY) a).IsStrictlyLE b := by
    -- Proof comment: the chosen cutoff satisfies `a ≤ b`, so the retained terms above `b` are
    -- exactly the already-vanishing terms of `Y`.
    simpa [KY] using truncGE_isStrictlyLE_of_isStrictlyLE (K := KY) a b ha_le_b hYle
  have hY'bounded :
      HomotopyCategory.bounded 𝒜
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := KY) a)) := by
    -- Proof comment: the chosen lower truncation is bounded below by construction and remains
    -- bounded above because the original target was already bounded above.
    rw [HomotopyCategory.bounded_iff]
    exact (CochainComplex.bounded_iff 𝒜 _).2
      ⟨(CochainComplex.plus_iff 𝒜 _).2 ⟨a, htruncGE⟩,
        (CochainComplex.minus_iff 𝒜 _).2 ⟨b, htruncLE⟩⟩
  let Y' : Kᵇ(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := KY) a),
      hY'bounded⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: the denominator is again the truncation map in the homotopy category.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.πTruncGE (K := KY) a)
  · -- Proof comment: this truncation map is the quasi-isomorphism produced by Lemma 13.11.5.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.πTruncGE (K := KY) a)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hπ)

/-- Helper for Lemma 13.11.6: a bounded-above complex whose image in the derived category is
bounded is quasi-isomorphic to a bounded complex. -/
lemma bounded_from_boundedAbove_derived_representative
    (Y : K⁻(𝒜))
    (hY :
      (t.bounded : ObjectProperty (D(𝒜)))
        (DerivedCategory.Qh.obj Y.obj)) :
    ∃ (Y' : Kᵇ(𝒜)) (t : Y.obj ⟶ Y'.obj), HomotopyCategory.quasiIso 𝒜 (up ℤ) t := by
  let KY : CochainComplex 𝒜 ℤ := Y.obj.as
  have hYbounded := hY
  rw [derivedCategory_t_bounded_iff] at hYbounded
  obtain ⟨a₀, hYplus⟩ := hYbounded.1
  obtain ⟨b, hYle⟩ :=
    (CochainComplex.minus_iff 𝒜 KY).1
      ((HomotopyCategory.minus_iff (𝒜 := 𝒜) Y.obj).1 Y.property)
  let a : ℤ := min a₀ b
  have ha_le_b : a ≤ b := by
    dsimp [a]
    exact Int.min_le_right _ _
  have hYeventual : ∀ n : ℤ, n < a → IsZero (KY.homology n) := by
    intro n hn
    have hQh :
        IsZero ((H^n).obj (DerivedCategory.Qh.obj Y.obj)) := by
      exact hYplus n (lt_of_lt_of_le hn <| by
        dsimp [a]
        exact Int.min_le_left _ _)
    let eQh :
        DerivedCategory.Qh.obj Y.obj ≅ DerivedCategory.Q.obj KY := by
      simpa [KY, HomotopyCategory.quotient_obj_as] using
        (DerivedCategory.quotientCompQhIso 𝒜).app KY
    have hQ :
        IsZero ((H^n).obj (DerivedCategory.Q.obj KY)) := by
      exact ((H^n).mapIso eQh).isZero_iff.1 hQh
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj, KY] using
      (((DerivedCategory.homologyFunctorFactors 𝒜 n).app KY).isZero_iff).1 hQ
  have hKYge : KY.IsGE a := by
    -- Proof comment: convert the derived lower vanishing bound into exactness of `KY`.
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hYeventual n hn
  let _ : KY.IsGE a := hKYge
  have hπ : QuasiIso (CochainComplex.πTruncGE (K := KY) a) := inferInstance
  have htruncGE : (CochainComplex.truncGE (K := KY) a).IsStrictlyGE a := inferInstance
  have htruncLE : (CochainComplex.truncGE (K := KY) a).IsStrictlyLE b := by
    -- Proof comment: smart lower truncation leaves the already-vanishing high degrees unchanged.
    simpa [KY] using truncGE_isStrictlyLE_of_isStrictlyLE (K := KY) a b ha_le_b hYle
  have hY'bounded :
      HomotopyCategory.bounded 𝒜
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := KY) a)) := by
    -- Proof comment: the truncated complex is bounded below by construction and remains bounded
    -- above because `Y` was already bounded above.
    rw [HomotopyCategory.bounded_iff]
    exact (CochainComplex.bounded_iff 𝒜 _).2
      ⟨(CochainComplex.plus_iff 𝒜 _).2 ⟨a, htruncGE⟩,
        (CochainComplex.minus_iff 𝒜 _).2 ⟨b, htruncLE⟩⟩
  let Y' : Kᵇ(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := KY) a),
      hY'bounded⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: the comparison map is the truncation map viewed in the homotopy category.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.πTruncGE (K := KY) a)
  · -- Proof comment: the truncation map is a quasi-isomorphism because `KY` is exact below `a`.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.πTruncGE (K := KY) a)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hπ)

/-- Helper for Lemma 13.11.6: the bounded-above comparison functor is an equivalence. -/
theorem boundedAbove_localization_comparison_isEquivalence
    :
    (boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)).IsEquivalence := by
  exact boundedAboveLocalizationComparisonFunctor_isEquivalence (𝒜 := 𝒜)

/-- Helper for Lemma 13.11.6: every bounded homotopy object is also bounded above. -/
theorem bounded_homotopy_obj_mem_minus
    (X : Kᵇ(𝒜)) :
    (HomotopyCategory.minus 𝒜) X.obj := by
  -- Proof comment: boundedness supplies both one-sided bounds, so we may forget the lower bound.
  rw [HomotopyCategory.minus_iff]
  exact (CochainComplex.bounded_iff 𝒜 X.obj.as).1
    ((HomotopyCategory.bounded_iff (𝒜 := 𝒜) X.obj).1 X.property) |>.2

/-- Helper for Lemma 13.11.6: the canonical inclusion `K^{b}(\mathcal A) ⥤ K^{-}(\mathcal A)`. -/
noncomputable abbrev boundedToBoundedAboveHomotopyFunctor :
    Kᵇ(𝒜) ⥤ K⁻(𝒜) :=
  (HomotopyCategory.minus 𝒜).lift
    ((HomotopyCategory.bounded 𝒜).ι)
    bounded_homotopy_obj_mem_minus

/-- Helper for Lemma 13.11.6: every bounded derived object is also bounded above. -/
theorem bounded_derived_obj_mem_minus
    (X : Dᵇ(𝒜)) :
    (t.minus : ObjectProperty (D(𝒜))) X.obj := by
  -- Proof comment: a bounded derived object already satisfies the upper vanishing half.
  have hX := X.property
  rw [derivedCategory_t_bounded_iff] at hX
  exact (derivedCategory_t_minus_iff (𝒜 := 𝒜) X.obj).2 hX.2

/-- Helper for Lemma 13.11.6: the canonical inclusion `D^{b}(\mathcal A) ⥤ D^{-}(\mathcal A)`. -/
noncomputable abbrev boundedDerivedToDerivedAboveFunctor :
    Dᵇ(𝒜) ⥤ D⁻(𝒜) :=
  (t.minus : ObjectProperty (D(𝒜))).lift
    ((t.bounded : ObjectProperty (D(𝒜))).ι)
    bounded_derived_obj_mem_minus

/-- Helper for Lemma 13.11.6: the inclusion `K^{b}(\mathcal A) ⥤ K^{-}(\mathcal A)` sends
bounded acyclic Verdier morphisms to morphisms inverted in the bounded-above localization. -/
theorem boundedToBoundedAboveLocalization_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Acᵇ(𝒜)).trW)
      (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙
        ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)) := by
  intro X Y f hf
  let F := boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)
  let Qminus : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization :=
    ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
  let ιminus : K⁻(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.minus 𝒜)
  let ιbounded : Kᵇ(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.bounded 𝒜)
  let eComp :
      F ⋙ ιminus ≅ ιbounded :=
    ObjectProperty.liftCompιIso
      (HomotopyCategory.minus 𝒜)
      ((HomotopyCategory.bounded 𝒜).ι)
      bounded_homotopy_obj_mem_minus
  have hBoundedQis : Qisᵇ(𝒜) f := by
    simpa [boundedAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  have hBounded :
      IsIso (((ιbounded) ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: bounded acyclic denominators are exactly bounded quasi-isomorphisms.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.bounded 𝒜).ι.map f))
    rw [DerivedCategory.isIso_Qh_map_iff]
    simpa [boundedHomotopyQuasiIso] using hBoundedQis
  have hMinus :
      IsIso (((F ⋙ ιminus) ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: transport the ambient invertibility statement to the bounded-above route.
    exact
      ((NatIso.isIso_map_iff
        (Functor.isoWhiskerRight eComp DerivedCategory.Qh)
        f)).2 hBounded
  have hMinusQis : Qis⁻(𝒜) (F.map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, the image of `f` is a
    -- quasi-isomorphism in `K^{-}(\mathcal A)`.
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((HomotopyCategory.minus 𝒜).ι.map (F.map f))
    rw [← DerivedCategory.isIso_Qh_map_iff]
    simpa using hMinus
  have hMinusTrW : ((Ac⁻(𝒜)).trW) (F.map f) := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hMinusQis
  -- Proof comment: the bounded-above localization inverts exactly the denominators in
  -- `((Ac⁻(𝒜)).trW)`.
  exact Localization.inverts Qminus ((Ac⁻(𝒜)).trW) (F.map f) hMinusTrW

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor
`Qis^{b}(\mathcal A)^{-1}K^{b}(\mathcal A) ⥤ Qis^{-}(\mathcal A)^{-1}K^{-}(\mathcal A)`. -/
noncomputable abbrev boundedLocalizationToBoundedAboveLocalizationFunctor :
    ((Acᵇ(𝒜)).trW).Localization ⥤ ((Ac⁻(𝒜)).trW).Localization :=
  Localization.lift
    (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙
      ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization))
    boundedToBoundedAboveLocalization_inverts_acyclic_trW
    (((Acᵇ(𝒜)).trW).Q : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded
localization model to `D^{b}(\mathcal A)`. -/
noncomputable abbrev boundedLocalizationComparisonFunctor :
    ((Acᵇ(𝒜)).trW).Localization ⥤ Dᵇ(𝒜) :=
  Localization.lift mapBoundedHomotopyToDerivedBounded
    mapBoundedHomotopyToDerivedBounded_inverts_acyclic_trW
    (((Acᵇ(𝒜)).trW).Q : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)

/-- Helper for Lemma 13.11.6: the inclusion `K^{b}(\mathcal A) ⥤ K^{-}(\mathcal A)` is fully
faithful, so morphisms between bounded objects may be transported back from `K^{-}(\mathcal A)`.
-/
private noncomputable def boundedToBoundedAboveHomotopyFunctorFullyFaithful :
    (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)).FullyFaithful := by
  let F := boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)
  let ιminus : K⁻(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.minus 𝒜)
  let ιbounded : Kᵇ(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.bounded 𝒜)
  let eComp :
      F ⋙ ιminus ≅ ιbounded :=
    ObjectProperty.liftCompιIso
      (HomotopyCategory.minus 𝒜)
      ((HomotopyCategory.bounded 𝒜).ι)
      bounded_homotopy_obj_mem_minus
  let hFFminus : ιminus.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιminus
  let hFFbounded : ιbounded.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιbounded
  let _ : ιminus.Full := hFFminus.full
  let _ : ιminus.Faithful := hFFminus.faithful
  let _ : ιbounded.Full := hFFbounded.full
  let _ : ιbounded.Faithful := hFFbounded.faithful
  let _ : F.Full := Functor.Full.of_comp_faithful_iso (F := F) (G := ιminus) (H := ιbounded) eComp
  let _ : F.Faithful := Functor.Faithful.of_comp_iso (F := F) (G := ιminus) (H := ιbounded) eComp
  -- Proof comment: cancel the fully faithful inclusion `K^{-}(\mathcal A) ↪ K(\mathcal A)`
  -- against the canonical identification of the composite with `K^{b}(\mathcal A) ↪ K(\mathcal A)`.
  exact Functor.FullyFaithful.ofFullyFaithful F

/-- Helper for Lemma 13.11.6: any morphism in `K^{-}(\mathcal A)` between the images of bounded
objects has a unique bounded preimage. -/
private theorem boundedToBoundedAbove_preimage_hom
    {X Y : Kᵇ(𝒜)}
    (f :
      boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜).obj X ⟶
        boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜).obj Y) :
    ∃ g : X ⟶ Y, (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)).map g = f := by
  let hFF :
      (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)).FullyFaithful :=
    boundedToBoundedAboveHomotopyFunctorFullyFaithful (𝒜 := 𝒜)
  -- Proof comment: this packages the unique preimage provided by full faithfulness into the
  -- existential form convenient for the bounded left-fraction refinement arguments below.
  exact ⟨hFF.preimage f, hFF.map_preimage f⟩

/-- Helper for Lemma 13.11.6: the bounded comparison functor is essentially surjective. -/
theorem bounded_localization_comparison_essSurj
    :
    (boundedLocalizationComparisonFunctor (𝒜 := 𝒜)).EssSurj := by
  let F := boundedLocalizationComparisonFunctor (𝒜 := 𝒜)
  let j := boundedDerivedToDerivedAboveFunctor (𝒜 := 𝒜)
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  let ιbounded : Dᵇ(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.bounded : ObjectProperty (D(𝒜)))
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨Xminus, ⟨eXminus⟩⟩ :=
    (mapBoundedAboveHomotopyToDerivedAbove_essSurj (𝒜 := 𝒜)).mem_essImage (j.obj Y)
  let eminus :
      ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj Xminus) ≅
        DerivedCategory.Qh.obj Xminus.obj :=
    (ObjectProperty.liftCompιIso
      (t.minus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_minus).app Xminus
  let ej :
      ιminus.obj (j.obj Y) ≅ Y.obj :=
    (ObjectProperty.liftCompιIso
      (t.minus : ObjectProperty (D(𝒜)))
      ((t.bounded : ObjectProperty (D(𝒜))).ι)
      bounded_derived_obj_mem_minus).app Y
  have hYminusBounded :
      (t.bounded : ObjectProperty (D(𝒜))) (ιminus.obj (j.obj Y)) := by
    -- Proof comment: forgetting a bounded object to `D(\mathcal A)` preserves boundedness.
    exact (t.bounded : ObjectProperty (D(𝒜))).prop_of_iso ej.symm Y.property
  have hXminusBounded :
      (t.bounded : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj Xminus.obj) := by
    -- Proof comment: transport the boundedness of `j.obj Y` across the chosen bounded-above
    -- representative and the canonical inclusion-to-ambient comparison.
    exact
      (t.bounded : ObjectProperty (D(𝒜))).prop_of_iso
        ((ιminus.mapIso eXminus).symm ≪≫ eminus)
        hYminusBounded
  obtain ⟨Xbounded, tBounded, ht⟩ :=
    bounded_from_boundedAbove_derived_representative (𝒜 := 𝒜) Xminus hXminusBounded
  have hQt : IsIso (DerivedCategory.Qh.map tBounded) := by
    -- Proof comment: the bounded replacement map is a quasi-isomorphism, hence invertible in
    -- the ambient derived category.
    rw [DerivedCategory.isIso_Qh_map_iff]
    exact ht
  let ebounded :
      ιbounded.obj (mapBoundedHomotopyToDerivedBounded.obj Xbounded) ≅
        DerivedCategory.Qh.obj Xbounded.obj :=
    (ObjectProperty.liftCompιIso
      (t.bounded : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_bounded).app Xbounded
  let eAmbient :
      ιbounded.obj (mapBoundedHomotopyToDerivedBounded.obj Xbounded) ≅ Y.obj :=
    -- Route correction: essential surjectivity is cheaper than the roof arguments; first move to
    -- a bounded-above representative, then refine it to a bounded complex before descending.
    ebounded ≪≫ (asIso (DerivedCategory.Qh.map tBounded)).symm ≪≫
      eminus.symm ≪≫ ιminus.mapIso eXminus ≪≫ ej
  let hFF :
      ιbounded.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιbounded
  let eBounded :
      mapBoundedHomotopyToDerivedBounded.obj Xbounded ≅ Y :=
    hFF.preimageIso eAmbient
  refine ⟨(((Acᵇ(𝒜)).trW).Q.obj Xbounded), ⟨?_⟩⟩
  let eFac :
      F.obj (((Acᵇ(𝒜)).trW).Q.obj Xbounded) ≅
        mapBoundedHomotopyToDerivedBounded.obj Xbounded :=
    (Localization.fac
      mapBoundedHomotopyToDerivedBounded
      mapBoundedHomotopyToDerivedBounded_inverts_acyclic_trW
      ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)).app Xbounded
  exact eFac ≪≫ eBounded

/-- Helper for Lemma 13.11.6: if a morphism between bounded complexes becomes a quasi-isomorphism
after viewing it in `K^{-}(\mathcal A)`, then it was already a quasi-isomorphism in
`K^{b}(\mathcal A)`. -/
private theorem boundedToBoundedAbove_reflects_quasiIso
    {X Y : Kᵇ(𝒜)} (f : X ⟶ Y)
    (hf :
      Qis⁻(𝒜) ((boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)).map f)) :
    Qisᵇ(𝒜) f := by
  let F := boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)
  let ιminus : K⁻(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.minus 𝒜)
  let ιbounded : Kᵇ(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.bounded 𝒜)
  let eComp :
      F ⋙ ιminus ≅ ιbounded :=
    ObjectProperty.liftCompιIso
      (HomotopyCategory.minus 𝒜)
      ((HomotopyCategory.bounded 𝒜).ι)
      bounded_homotopy_obj_mem_minus
  have hMinus :
      IsIso (((F ⋙ ιminus) ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: `hf` says exactly that the image of `f` in the ambient homotopy category is
    -- inverted by `Qh`.
    change IsIso
      (DerivedCategory.Qh.map
        ((HomotopyCategory.minus 𝒜).ι.map (F.map f)))
    rw [DerivedCategory.isIso_Qh_map_iff]
    simpa [boundedAboveHomotopyQuasiIso] using hf
  have hBounded :
      IsIso (((ιbounded) ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: transport the invertibility statement across the comparison of the two
    -- ambient inclusion routes `Kᵇ ⥤ K`.
    exact
      ((NatIso.isIso_map_iff
        (Functor.isoWhiskerRight eComp DerivedCategory.Qh)
        f)).1 hMinus
  -- Proof comment: after canceling the ambient inclusion, the defining inverse-image condition
  -- for `Qisᵇ(\mathcal A)` is exactly the remaining ambient quasi-isomorphism statement.
  change HomotopyCategory.quasiIso 𝒜 (up ℤ) ((HomotopyCategory.bounded 𝒜).ι.map f)
  rw [← DerivedCategory.isIso_Qh_map_iff]
  simpa using hBounded

/-- Helper for Lemma 13.11.6: postcomposing a bounded-above left-fraction representative by a
further denominator in `Qis^{-}(\mathcal A)` does not change the represented localization
morphism. -/
private lemma boundedAboveLeftFraction_map_postcomp_eq
    {X Y Z : K⁻(𝒜)} (φ : ((Ac⁻(𝒜)).trW).LeftFraction X Y)
    (t : φ.Y' ⟶ Z) (ht : ((Ac⁻(𝒜)).trW) (φ.s ≫ t)) :
    φ.map
        ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
        (Localization.inverts
          ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
          ((Ac⁻(𝒜)).trW)) =
      (MorphismProperty.LeftFraction.mk (φ.f ≫ t) (φ.s ≫ t) ht).map
        ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
        (Localization.inverts
          ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
          ((Ac⁻(𝒜)).trW)) := by
  -- Proof comment: compare the original roof and its postcomposed refinement through the obvious
  -- common target `Z`.
  exact
    (MorphismProperty.LeftFraction.map_eq_iff
      (L := ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization))
      (W := ((Ac⁻(𝒜)).trW)) _ _).2 <| by
      refine ⟨Z, t, 𝟙 Z, ?_, ?_, ht⟩
      · simp
      · simp

/-- Helper for Lemma 13.11.6: passing a bounded roof through the comparison to the bounded-above
localization gives the corresponding bounded-above roof, conjugated by `Localization.fac`. -/
private theorem boundedLocalizationToBoundedAboveLocalization_map_leftFraction
    {X Y : Kᵇ(𝒜)} (φ : ((Acᵇ(𝒜)).trW).LeftFraction X Y) :
    (boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)).map
        (φ.map
          ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)
          (Localization.inverts
            ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)
            ((Acᵇ(𝒜)).trW))) =
      (Localization.fac
        ((boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)) ⋙
          ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization))
        boundedToBoundedAboveLocalization_inverts_acyclic_trW
        ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)).hom.app X ≫
        φ.map
          ((boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)) ⋙
            ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization))
          boundedToBoundedAboveLocalization_inverts_acyclic_trW ≫
        (Localization.fac
          ((boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)) ⋙
            ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization))
          boundedToBoundedAboveLocalization_inverts_acyclic_trW
          ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)).inv.app Y := by
  -- Proof comment: the bounded-to-bounded-above comparison is another localization lift, so the
  -- same left-fraction conjugation formula applies verbatim.
  simpa [boundedLocalizationToBoundedAboveLocalizationFunctor] using
    localization_lift_map_leftFraction
      ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)
      ((boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)) ⋙
        ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization))
      boundedToBoundedAboveLocalization_inverts_acyclic_trW
      φ

/-- Helper for Lemma 13.11.6: every morphism in the bounded-above localization between bounded
objects is represented by a left fraction whose intermediate object is bounded. -/
theorem bounded_localization_comparison_surjective_on_Q_obj_hom
    (X Y : Kᵇ(𝒜)) :
    Function.Surjective
      (fun g : (((Acᵇ(𝒜)).trW).Q.obj X ⟶ ((Acᵇ(𝒜)).trW).Q.obj Y) =>
        (boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)).map g) := by
  let Qbounded : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization := ((Acᵇ(𝒜)).trW).Q
  let Qminus : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := ((Ac⁻(𝒜)).trW).Q
  let F0 := boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)
  let F := boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)
  let G : Kᵇ(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := F0 ⋙ Qminus
  let eX :
      F.obj (Qbounded.obj X) ≅ G.obj X :=
    (Localization.fac G
      boundedToBoundedAboveLocalization_inverts_acyclic_trW
      Qbounded).app X
  let eY :
      F.obj (Qbounded.obj Y) ≅ G.obj Y :=
    (Localization.fac G
      boundedToBoundedAboveLocalization_inverts_acyclic_trW
      Qbounded).app Y
  intro h
  let hMinus :
      Qminus.obj (F0.obj X) ⟶ Qminus.obj (F0.obj Y) :=
    eX.inv ≫ h ≫ eY.hom
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction
    Qminus ((Ac⁻(𝒜)).trW) hMinus
  have hsMinusQis :
      Qis⁻(𝒜) φ.s := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using φ.hs
  obtain ⟨Z', t, ht⟩ :=
    quasiIso_to_bounded_refinement_of_bounded_above (𝒜 := 𝒜) Y φ.Y' φ.s.hom
      (by simpa [boundedAboveHomotopyQuasiIso] using hsMinusQis)
  let Zminus : K⁻(𝒜) := F0.obj Z'
  obtain ⟨tMinus, htMinuseq⟩ := boundedAbove_preimage_hom
    (𝒜 := 𝒜) (X := φ.Y') (Y := Zminus) t
  have htMinusQis :
      Qis⁻(𝒜) tMinus := by
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((HomotopyCategory.minus 𝒜).ι.map tMinus)
    rw [htMinuseq]
    exact ht
  obtain ⟨fZ, hfZeq⟩ := boundedToBoundedAbove_preimage_hom
    (𝒜 := 𝒜) (X := X) (Y := Z') (φ.f ≫ tMinus)
  obtain ⟨sZ, hsZeq⟩ := boundedToBoundedAbove_preimage_hom
    (𝒜 := 𝒜) (X := Y) (Y := Z') (φ.s ≫ tMinus)
  have hsImageQis :
      Qis⁻(𝒜) (F0.map sZ) := by
    rw [hsZeq]
    simpa [Category.assoc] using
      (Qis⁻(𝒜)).comp_mem _ _ hsMinusQis htMinusQis
  have hsZQis :
      Qisᵇ(𝒜) sZ := by
    exact boundedToBoundedAbove_reflects_quasiIso (𝒜 := 𝒜) (f := sZ) hsImageQis
  have hsZ :
      ((Acᵇ(𝒜)).trW) sZ := by
    simpa [boundedAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hsZQis
  let ψ : ((Acᵇ(𝒜)).trW).LeftFraction X Y :=
    MorphismProperty.LeftFraction.mk fZ sZ hsZ
  let ψMinus : ((Ac⁻(𝒜)).trW).LeftFraction (F0.obj X) (F0.obj Y) :=
    MorphismProperty.LeftFraction.mk
      (F0.map fZ)
      (F0.map sZ)
      (by
        simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using
          hsImageQis)
  have hsImageTrW :
      ((Ac⁻(𝒜)).trW) (φ.s ≫ tMinus) := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using
      (Qis⁻(𝒜)).comp_mem _ _ hsMinusQis htMinusQis
  have hψmap :
      ψ.map G boundedToBoundedAboveLocalization_inverts_acyclic_trW =
        ψMinus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) := by
    -- Proof comment: applying the comparison on the bounded roof just replaces its arrows by
    -- their images in `K^{-}(\mathcal A)`.
    rfl
  have hrefine :
      φ.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) =
        ψMinus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) := by
    -- Proof comment: postcomposing the bounded-above roof by the refined denominator does not
    -- change the represented localization morphism.
    let ψRefined : ((Ac⁻(𝒜)).trW).LeftFraction (F0.obj X) (F0.obj Y) :=
      MorphismProperty.LeftFraction.mk (φ.f ≫ tMinus) (φ.s ≫ tMinus) hsImageTrW
    have hrefine' :
        φ.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) =
          ψRefined.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) := by
      exact boundedAboveLeftFraction_map_postcomp_eq (𝒜 := 𝒜) φ tMinus hsImageTrW
    have hψMinusEq :
        ψRefined.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) =
          ψMinus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) := by
      exact
        (MorphismProperty.LeftFraction.map_eq_iff
          Qminus ((Ac⁻(𝒜)).trW) ψRefined ψMinus).2 <| by
            refine ⟨Zminus, 𝟙 _, 𝟙 _, ?_, ?_, ?_⟩
            · simpa [ψRefined, ψMinus] using hsZeq.symm
            · simpa [ψRefined, ψMinus] using hfZeq.symm
            · simpa [ψRefined] using hsImageTrW
    calc
      φ.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW))
          = ψRefined.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) := hrefine'
      _ = ψMinus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) := hψMinusEq
  refine ⟨ψ.map Qbounded (Localization.inverts Qbounded ((Acᵇ(𝒜)).trW)), ?_⟩
  calc
    F.map (ψ.map Qbounded (Localization.inverts Qbounded ((Acᵇ(𝒜)).trW)))
        = eX.hom ≫ ψ.map G boundedToBoundedAboveLocalization_inverts_acyclic_trW ≫ eY.inv := by
            simpa [F, Qbounded] using
              boundedLocalizationToBoundedAboveLocalization_map_leftFraction (𝒜 := 𝒜) ψ
    _ = eX.hom ≫ ψMinus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) ≫ eY.inv := by
          rw [hψmap]
          rfl
    _ = eX.hom ≫ hMinus ≫ eY.inv := by
          rw [← hrefine, hφ]
    _ = h := by
          calc
            eX.hom ≫ hMinus ≫ eY.inv
                = eX.hom ≫ (eX.inv ≫ h ≫ eY.hom) ≫ eY.inv := by rfl
            _ = (eX.hom ≫ eX.inv) ≫ h ≫ (eY.hom ≫ eY.inv) := by
                  simp [Category.assoc]
            _ = h := by
                  simp

/-- Helper for Lemma 13.11.6: if two bounded roofs become equal after passing to the
bounded-above localization, then they were already equal in the bounded localization. -/
theorem bounded_localization_comparison_injective_on_Q_obj_hom
    (X Y : Kᵇ(𝒜)) :
    Function.Injective
      (fun g : (((Acᵇ(𝒜)).trW).Q.obj X ⟶ ((Acᵇ(𝒜)).trW).Q.obj Y) =>
        (boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)).map g) := by
  let Qbounded : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization := ((Acᵇ(𝒜)).trW).Q
  let Qminus : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := ((Ac⁻(𝒜)).trW).Q
  let F0 := boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜)
  let F := boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)
  let G : Kᵇ(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization := F0 ⋙ Qminus
  let eX :
      F.obj (Qbounded.obj X) ≅ G.obj X :=
    (Localization.fac G
      boundedToBoundedAboveLocalization_inverts_acyclic_trW
      Qbounded).app X
  let eY :
      F.obj (Qbounded.obj Y) ≅ G.obj Y :=
    (Localization.fac G
      boundedToBoundedAboveLocalization_inverts_acyclic_trW
      Qbounded).app Y
  let hFF : F0.FullyFaithful := boundedToBoundedAboveHomotopyFunctorFullyFaithful (𝒜 := 𝒜)
  intro g₁ g₂ h
  obtain ⟨φ, hφ₁, hφ₂⟩ := Localization.exists_leftFraction₂
    Qbounded ((Acᵇ(𝒜)).trW) g₁ g₂
  have hsQis :
      Qisᵇ(𝒜) φ.s := by
    simpa [boundedAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using φ.hs
  have hsMinusQis :
      Qis⁻(𝒜) (F0.map φ.s) := by
    let ιminus : K⁻(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.minus 𝒜)
    let ιbounded : Kᵇ(𝒜) ⥤ K(𝒜) := ObjectProperty.ι (HomotopyCategory.bounded 𝒜)
    let eComp :
        F0 ⋙ ιminus ≅ ιbounded :=
      ObjectProperty.liftCompιIso
        (HomotopyCategory.minus 𝒜)
        ((HomotopyCategory.bounded 𝒜).ι)
        bounded_homotopy_obj_mem_minus
    have hBounded :
        IsIso (((ιbounded) ⋙ DerivedCategory.Qh).map φ.s) := by
      change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.bounded 𝒜).ι.map φ.s))
      rw [DerivedCategory.isIso_Qh_map_iff]
      simpa [boundedHomotopyQuasiIso] using hsQis
    have hMinus :
        IsIso (((F0 ⋙ ιminus) ⋙ DerivedCategory.Qh).map φ.s) := by
      exact
        ((NatIso.isIso_map_iff
          (Functor.isoWhiskerRight eComp DerivedCategory.Qh)
          φ.s)).2 hBounded
    change HomotopyCategory.quasiIso 𝒜 (up ℤ) ((HomotopyCategory.minus 𝒜).ι.map (F0.map φ.s))
    rw [← DerivedCategory.isIso_Qh_map_iff]
    simpa using hMinus
  let φ₁Minus : ((Ac⁻(𝒜)).trW).LeftFraction (F0.obj X) (F0.obj Y) :=
    MorphismProperty.LeftFraction.mk
      (F0.map φ.f)
      (F0.map φ.s)
      (by
        simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using
          hsMinusQis)
  let φ₂Minus : ((Ac⁻(𝒜)).trW).LeftFraction (F0.obj X) (F0.obj Y) :=
    MorphismProperty.LeftFraction.mk
      (F0.map φ.f')
      (F0.map φ.s)
      (by
        simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using
          hsMinusQis)
  have hmap₁ :
      F.map (φ.fst.map Qbounded (Localization.inverts Qbounded ((Acᵇ(𝒜)).trW))) =
        eX.hom ≫ φ₁Minus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) ≫ eY.inv := by
    -- Proof comment: the first bounded roof maps to its image roof in the bounded-above
    -- localization, again conjugated by the comparison isomorphisms.
    simpa [F, Qbounded, G, φ₁Minus] using
      boundedLocalizationToBoundedAboveLocalization_map_leftFraction (𝒜 := 𝒜) φ.fst
  have hmap₂ :
      F.map (φ.snd.map Qbounded (Localization.inverts Qbounded ((Acᵇ(𝒜)).trW))) =
        eX.hom ≫ φ₂Minus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) ≫ eY.inv := by
    -- Proof comment: the second bounded roof follows the identical transport pattern.
    simpa [F, Qbounded, G, φ₂Minus] using
      boundedLocalizationToBoundedAboveLocalization_map_leftFraction (𝒜 := 𝒜) φ.snd
  have hMinusMap :
      φ₁Minus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) =
        φ₂Minus.map Qminus (Localization.inverts Qminus ((Ac⁻(𝒜)).trW)) := by
    have h' :
        eX.inv ≫ F.map g₁ ≫ eY.hom =
          eX.inv ≫ F.map g₂ ≫ eY.hom := by
      exact congrArg (fun k ↦ eX.inv ≫ k ≫ eY.hom) h
    -- Proof comment: cancel the comparison isomorphisms to reduce equality to the two
    -- bounded-above roofs themselves.
    rw [hφ₁, hmap₁, hφ₂, hmap₂] at h'
    simpa [Category.assoc] using h'
  obtain ⟨Z, t₁, t₂, hst, hft, ht⟩ :=
    (MorphismProperty.LeftFraction.map_eq_iff
      Qminus ((Ac⁻(𝒜)).trW) φ₁Minus φ₂Minus).1 hMinusMap
  have htQis :
      Qis⁻(𝒜) (φ₁Minus.s ≫ t₁) := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using ht
  obtain ⟨Z', u, hu⟩ :=
    quasiIso_to_bounded_refinement_of_bounded_above
      (𝒜 := 𝒜) Y Z (φ₁Minus.s ≫ t₁).hom
      (by
        simpa [boundedAboveHomotopyQuasiIso] using htQis)
  let Zminus : K⁻(𝒜) := F0.obj Z'
  obtain ⟨uMinus, huMinuseq⟩ := boundedAbove_preimage_hom
    (𝒜 := 𝒜) (X := Z) (Y := Zminus) u
  have huMinusQis :
      Qis⁻(𝒜) uMinus := by
    change HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((HomotopyCategory.minus 𝒜).ι.map uMinus)
    rw [huMinuseq]
    exact hu
  obtain ⟨v₁, hv₁eq⟩ := boundedToBoundedAbove_preimage_hom
    (𝒜 := 𝒜) (X := φ.Y') (Y := Z') (t₁ ≫ uMinus)
  obtain ⟨v₂, hv₂eq⟩ := boundedToBoundedAbove_preimage_hom
    (𝒜 := 𝒜) (X := φ.Y') (Y := Z') (t₂ ≫ uMinus)
  have hsImageQis :
      Qis⁻(𝒜) (F0.map (φ.s ≫ v₁)) := by
    rw [Functor.map_comp, hv₁eq]
    simpa [φ₁Minus, Category.assoc] using
      (Qis⁻(𝒜)).comp_mem _ _ htQis huMinusQis
  have hsRefined :
      Qisᵇ(𝒜) (φ.s ≫ v₁) := by
    exact boundedToBoundedAbove_reflects_quasiIso (𝒜 := 𝒜) (f := φ.s ≫ v₁) hsImageQis
  have hsRefinedTrW :
      ((Acᵇ(𝒜)).trW) (φ.s ≫ v₁) := by
    simpa [boundedAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hsRefined
  have hrel :
      MorphismProperty.LeftFractionRel φ.fst φ.snd := by
    refine ⟨Z', v₁, v₂, ?_, ?_, hsRefinedTrW⟩
    · apply hFF.map_injective
      calc
        F0.map (φ.s ≫ v₁) = F0.map φ.s ≫ t₁ ≫ uMinus := by
          rw [Functor.map_comp, hv₁eq]
        _ = F0.map φ.s ≫ t₂ ≫ uMinus := by
          simpa [φ₁Minus, φ₂Minus, Category.assoc] using congrArg (fun k ↦ k ≫ uMinus) hst
        _ = F0.map (φ.s ≫ v₂) := by
          rw [Functor.map_comp, hv₂eq]
    · apply hFF.map_injective
      calc
        F0.map (φ.f ≫ v₁) = F0.map φ.f ≫ t₁ ≫ uMinus := by
          rw [Functor.map_comp, hv₁eq]
        _ = F0.map φ.f' ≫ t₂ ≫ uMinus := by
          simpa [φ₁Minus, φ₂Minus, Category.assoc] using congrArg (fun k ↦ k ≫ uMinus) hft
        _ = F0.map (φ.f' ≫ v₂) := by
          rw [Functor.map_comp, hv₂eq]
  have hfracEq :
      φ.fst.map Qbounded (Localization.inverts Qbounded ((Acᵇ(𝒜)).trW)) =
        φ.snd.map Qbounded (Localization.inverts Qbounded ((Acᵇ(𝒜)).trW)) := by
    exact
      (MorphismProperty.LeftFraction.map_eq_iff
        Qbounded ((Acᵇ(𝒜)).trW) φ.fst φ.snd).2 hrel
  rw [hφ₁, hφ₂]
  exact hfracEq

/-- Helper for Lemma 13.11.6: the comparison from the bounded localization model to the
bounded-above localization model is fully faithful. -/
theorem boundedLocalizationToBoundedAboveLocalization_fullyFaithful :
    Nonempty (boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)).FullyFaithful := by
  -- Proof comment: again, the localization source is generated up to isomorphism by `Q.obj`, so
  -- the explicit bounded roof bijections suffice for global full faithfulness.
  let F := boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)
  let Q : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization := ((Acᵇ(𝒜)).trW).Q
  letI : Q.EssSurj := Localization.essSurj Q ((Acᵇ(𝒜)).trW)
  letI : F.Full :=
    Functor.full_of_comp_essSurj F Q
      (by
        intro X Y
        exact bounded_localization_comparison_surjective_on_Q_obj_hom
          (𝒜 := 𝒜) X Y)
  letI : F.Faithful :=
    Functor.faithful_of_comp_essSurj F Q
      (by
        intro X Y
        exact bounded_localization_comparison_injective_on_Q_obj_hom
          (𝒜 := 𝒜) X Y)
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

/-- Helper for Lemma 13.11.6: the bounded route to `D^{-}(\mathcal A)` agrees with first passing
to the bounded-above localization model. -/
noncomputable def bounded_localization_comparison_to_derivedAbove_iso :
    (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙
        mapBoundedAboveHomotopyToDerivedAbove) ≅
      (mapBoundedHomotopyToDerivedBounded ⋙
        boundedDerivedToDerivedAboveFunctor (𝒜 := 𝒜)) :=
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  let eLeft :
      (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙
          mapBoundedAboveHomotopyToDerivedAbove) ⋙ ιminus ≅
        (HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh :=
    (Functor.associator
      (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜))
      mapBoundedAboveHomotopyToDerivedAbove
      ιminus) ≪≫
      Functor.isoWhiskerLeft
        (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜))
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_minus) ≪≫
      (Functor.associator
        (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜))
        ((HomotopyCategory.minus 𝒜).ι)
        DerivedCategory.Qh).symm ≪≫
      Functor.isoWhiskerRight
        (ObjectProperty.liftCompιIso
          (HomotopyCategory.minus 𝒜)
          ((HomotopyCategory.bounded 𝒜).ι)
          bounded_homotopy_obj_mem_minus)
        DerivedCategory.Qh
  let eRight :
      (mapBoundedHomotopyToDerivedBounded ⋙
          boundedDerivedToDerivedAboveFunctor (𝒜 := 𝒜)) ⋙ ιminus ≅
        (HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh :=
    (Functor.associator
      mapBoundedHomotopyToDerivedBounded
      (boundedDerivedToDerivedAboveFunctor (𝒜 := 𝒜))
      ιminus) ≪≫
      Functor.isoWhiskerLeft
        mapBoundedHomotopyToDerivedBounded
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(𝒜)))
          ((t.bounded : ObjectProperty (D(𝒜))).ι)
          bounded_derived_obj_mem_minus) ≪≫
      (ObjectProperty.liftCompιIso
        (t.bounded : ObjectProperty (D(𝒜)))
        ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh)
        qh_obj_mem_t_bounded)
  Functor.fullyFaithfulCancelRight ιminus (eLeft ≪≫ eRight.symm)

/-- Helper for Lemma 13.11.6: the bounded comparison functor is an equivalence. -/
theorem bounded_localization_comparison_isEquivalence
    :
    (boundedLocalizationComparisonFunctor (𝒜 := 𝒜)).IsEquivalence := by
  let F := boundedLocalizationComparisonFunctor (𝒜 := 𝒜)
  let G := boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)
  let H := boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)
  let Q : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization :=
    (((Acᵇ(𝒜)).trW).Q : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)
  let Qminus : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization :=
    ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)
  let j := boundedDerivedToDerivedAboveFunctor (𝒜 := 𝒜)
  let eRight :
      Q ⋙ (G ⋙ H) ≅
        boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙
          mapBoundedAboveHomotopyToDerivedAbove := by
    -- Proof comment: unfold both localization comparison functors on actual bounded complexes.
    exact
      (Functor.associator Q G H).symm ≪≫
        Functor.isoWhiskerRight
          (Localization.fac
            (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙ Qminus)
            boundedToBoundedAboveLocalization_inverts_acyclic_trW
            Q)
          H ≪≫
        (Functor.associator
          (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜))
          Qminus
          H) ≪≫
        Functor.isoWhiskerLeft
          (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜))
          (Localization.fac
            mapBoundedAboveHomotopyToDerivedAbove
            mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW
            Qminus)
  let eComp :
      F ⋙ j ≅ G ⋙ H :=
    Localization.liftNatIso Q ((Acᵇ(𝒜)).trW)
      (Q ⋙ (F ⋙ j))
      (Q ⋙ (G ⋙ H))
      (F ⋙ j)
      (G ⋙ H)
      ((Functor.associator Q F j).symm ≪≫
        Functor.isoWhiskerRight
          (Localization.fac
            mapBoundedHomotopyToDerivedBounded
            mapBoundedHomotopyToDerivedBounded_inverts_acyclic_trW
            Q)
          j ≪≫
        (bounded_localization_comparison_to_derivedAbove_iso (𝒜 := 𝒜)).symm ≪≫
        eRight.symm)
  obtain ⟨hFFG⟩ :
      Nonempty G.FullyFaithful :=
    boundedLocalizationToBoundedAboveLocalization_fullyFaithful (𝒜 := 𝒜)
  have hEqvAbove : H.IsEquivalence :=
    boundedAbove_localization_comparison_isEquivalence (𝒜 := 𝒜)
  let _ : G.Full := hFFG.full
  let _ : G.Faithful := hFFG.faithful
  let _ : H.Full := hEqvAbove.full
  let _ : H.Faithful := hEqvAbove.faithful
  let _ : (G ⋙ H).Full := inferInstance
  let _ : (G ⋙ H).Faithful := inferInstance
  let _ : F.Full := Functor.Full.of_comp_faithful_iso (F := F) (G := j) (H := G ⋙ H) eComp
  let _ : F.Faithful := Functor.Faithful.of_comp_iso eComp
  let _ : F.EssSurj := bounded_localization_comparison_essSurj (𝒜 := 𝒜)
  -- Proof comment: after comparing with the bounded-above equivalence, the bounded comparison
  -- functor inherits full faithfulness, and essential surjectivity was already established.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

-- Proof sketch: combine the bounded-above localization argument with the fact that bounded
-- denominators can be chosen inside `K^{b}(\mathcal A)`, again using the bounded replacement
-- statement from Lemma 13.11.5.
/-- Lemma 13.11.6 (9): the canonical functor `K^{b}(\mathcal A) ⟶ D^{b}(\mathcal A)` realizes
`D^{b}(\mathcal A)` as the localization of `K^{b}(\mathcal A)` at `Qis^{b}(\mathcal A)`. -/
@[stacks 05RW]
theorem mapBoundedHomotopyToDerivedBounded_isLocalization
    :
    Functor.IsLocalization
      mapBoundedHomotopyToDerivedBounded
      (Qisᵇ(𝒜)) := by
  let F := boundedLocalizationComparisonFunctor (𝒜 := 𝒜)
  have hEqv : F.IsEquivalence :=
    bounded_localization_comparison_isEquivalence (𝒜 := 𝒜)
  let _ : F.IsEquivalence := hEqv
  have hLoc :
      mapBoundedHomotopyToDerivedBounded.IsLocalization ((Acᵇ(𝒜)).trW) := by
    -- Proof comment: once the bounded comparison functor is an equivalence, the bounded derived
    -- functor inherits the universal property of the localization functor `Q`.
    exact
      Functor.IsLocalization.of_equivalence_target
        ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)
        ((Acᵇ(𝒜)).trW)
        mapBoundedHomotopyToDerivedBounded
        F.asEquivalence
        (Localization.fac
          mapBoundedHomotopyToDerivedBounded
          mapBoundedHomotopyToDerivedBounded_inverts_acyclic_trW
          ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization))
  simpa [boundedAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hLoc

end

end CategoryTheory

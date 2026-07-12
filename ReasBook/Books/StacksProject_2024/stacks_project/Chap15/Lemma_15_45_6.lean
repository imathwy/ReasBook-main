import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Lemma_10_39_3
import StacksProject_2024.Chap10.Lemma_10_163_9
import StacksProject_2024.Chap10.Lemma_10_164_3
import StacksProject_2024.Chap10.Lemma_10_37_17
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory Limits
open CategoryTheory.Under
open CommRingCat

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
* primary domain: normality for local rings under henselization and strict henselization;
* sampled owner-style declarations: `IsNormalRing`, `IsHenselizationOf`,
  `IsStrictHenselizationOf`, `isNormalRing_of_faithfullyFlat`,
  `isNormalRing_of_smooth`, and `isNormalRing_of_isColimit_filtered_system`;
* core/canonical owners: `IsNormalRing` for the property being compared, and
  `IsHenselizationOf` / `IsStrictHenselizationOf` for the chosen algebra objects;
* primitive vs. derived API: the primitive inputs are only the chosen henselization and strict
  henselization instances; faithful-flat descent via `isNormalRing_of_faithfullyFlat` and
  smooth/filtered-colimit ascent via `isNormalRing_of_smooth` and
  `isNormalRing_of_isColimit_filtered_system` are canonical derived chapter API and should not be
  repackaged locally;
* layer split: the three-way `List.TFAE` is the `source-facing` statement, and pairwise
  equivalences are derived canonically via `List.TFAE.out` rather than kept as parallel local
  wrappers.
-/
-- Proof sketch: the maps `R → Rh` and `R → Rsh` are faithfully flat local maps because
-- henselizations and strict henselizations are filtered colimits of étale algebras. Normality then
-- descends from `Rh` or `Rsh` to `R` by faithful flatness. Conversely, if `R` is normal, each
-- étale stage in the filtered-colimit presentations of `Rh` and `Rsh` is normal by smooth ascent,
-- and the directed colimit remains normal. For a local ring, `IsNormalRing` is equivalent to the
-- textbook phrase “normal domain”.
/-- Helper for Lemma 15.45.6: forget a commutative ring under `A` to its underlying `A`-module. -/
private abbrev under_forget_to_module (A : CommRingCat.{u}) : Under A ⥤ ModuleCat A where
  obj B := ModuleCat.of A B
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap

/-- Helper for Lemma 15.45.6: an object under `CommRingCat.of A` carries the canonical
`A`-module structure induced by its structure map. -/
private instance under_module (A : Type u) [CommRing A] (B : Under (CommRingCat.of A)) :
    Module A B := by
  let _ : Algebra A B.right := B.hom.hom.toAlgebra
  infer_instance

/-- Helper for Lemma 15.45.6: a filtered colimit in `Under (CommRingCat.of A)` is flat once
every stage is flat over the fixed base ring `A`. -/
lemma under_flat_of_isColimit_filtered_system {A : Type u} [CommRing A]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of A)) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat A (F.obj j)] :
    Module.Flat A c.pt.right := by
  let cM := (under_forget_to_module (CommRingCat.of A)).mapCocone c
  letI : ∀ j, Module.Flat A ((F ⋙ under_forget_to_module (CommRingCat.of A)).obj j) :=
    fun j ↦ by
      -- The transported module diagram has the same stage objects, so stagewise flatness is
      -- unchanged after forgetting from rings under `A` to `A`-modules.
      simpa [under_forget_to_module] using (inferInstance : Module.Flat A (F.obj j))
  have hcM : IsColimit cM := by
    -- Forget the under-diagram to additive groups, where the filtered colimit is preserved, and
    -- then reflect the colimit back to `ModuleCat`.
    apply isColimitOfReflects (forget₂ (ModuleCat A) AddCommGrpCat)
    simpa [under_forget_to_module] using
      (isColimitOfPreserves
        (CategoryTheory.Under.forget (CommRingCat.of A) ⋙
          forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) hc)
  -- The Chapter 10 filtered-colimit flatness theorem now applies directly to the module diagram.
  simpa using
    flat_of_isColimit_filtered_system
      (F := F ⋙ under_forget_to_module (CommRingCat.of A)) cM hcM

/-- Helper for Lemma 15.45.6: the stage maps in an `ind` presentation satisfy the under-category
compatibility relation coming from naturality. -/
private theorem ind_underFunctor_w {A : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    {i j : J} (g : i ⟶ j) :
    t.app i ≫ D.map g = t.app j := by
  -- The under-category compatibility is exactly the naturality square for the stage map `t`.
  simpa using (t.naturality g).symm

/-- Helper for Lemma 15.45.6: turn the stage maps in an ind-étale presentation into a functor to
the under-category over the fixed source ring. -/
private abbrev ind_underFunctor {A : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D) :
    J ⥤ Under A :=
  { obj := fun j ↦ Under.mk (t.app j)
    map := fun {i j} g ↦ Under.homMk (D.map g) (ind_underFunctor_w D t g) }

/-- Helper for Lemma 15.45.6: the stage map of the lifted cocone satisfies the defining
under-category compatibility relation. -/
private theorem ind_underCocone_app_w
    {A B : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    (s : D ⟶ (Functor.const J).obj B) (f : A ⟶ B)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f)
    (j : J) :
    ((ind_underFunctor (A := A) D t).obj j).hom ≫ s.app j = f := by
  -- This is just the stage compatibility relation, rewritten against the lifted under-object.
  simpa [ind_underFunctor] using hcompat j

/-- Helper for Lemma 15.45.6: the stage map of the lifted cocone as a morphism in the
under-category. -/
private abbrev ind_underCocone_app
    {A B : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    (s : D ⟶ (Functor.const J).obj B) (f : A ⟶ B)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f)
    (j : J) :
    (ind_underFunctor (A := A) D t).obj j ⟶ Under.mk f :=
  Under.homMk (s.app j) (ind_underCocone_app_w D t s f hcompat j)

/-- Helper for Lemma 15.45.6: the lifted cocone in the under-category satisfies the cocone
naturality relation inherited from the underlying ring cocone. -/
private theorem ind_underCocone_naturality
    {A B : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    (s : D ⟶ (Functor.const J).obj B) (f : A ⟶ B)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f)
    {i j : J} (g : i ⟶ j) :
    (ind_underFunctor (A := A) D t).map g ≫ ind_underCocone_app D t s f hcompat j =
      ind_underCocone_app D t s f hcompat i := by
  -- Equality of morphisms in `Under` is determined by the right component after forgetting.
  refine CategoryTheory.CommaMorphism.ext rfl ?_
  simpa using s.naturality g

/-- Helper for Lemma 15.45.6: the target cocone of an ind-étale presentation lifts canonically to
the corresponding cocone in the under-category. -/
private abbrev ind_underCocone {A B : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    (s : D ⟶ (Functor.const J).obj B) (f : A ⟶ B)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f) :
    Cocone (ind_underFunctor (A := A) D t) :=
  { pt := Under.mk f
    ι :=
      { app := fun j ↦ ind_underCocone_app D t s f hcompat j
        naturality := fun {_ _} g ↦
          ind_underCocone_naturality D t s f hcompat g } }

/-- Helper for Lemma 15.45.6: if the underlying cocone in `CommRingCat` is colimiting, then the
lifted cocone in the under-category is also colimiting. -/
noncomputable def ind_underCocone_isColimit_of_isColimit
    {A B : CommRingCat.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    (s : D ⟶ (Functor.const J).obj B) (f : A ⟶ B)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f)
    (hs : IsColimit (Cocone.mk B s)) :
    IsColimit (ind_underCocone D t s f hcompat) := by
  classical
  refine IsColimit.mk ?_ ?_ ?_
  · intro c
    let j₀ : J := Classical.choice (CategoryTheory.IsFiltered.nonempty (C := J))
    refine Under.homMk (hs.desc ((Under.forget A).mapCocone c)) ?_
    -- One stage equation identifies the source map after forgetting from `Under` to rings.
    change f ≫ hs.desc ((Under.forget A).mapCocone c) = c.pt.hom
    rw [← hcompat j₀]
    have hfac₀ :
        s.app j₀ ≫ hs.desc ((Under.forget A).mapCocone c) = (c.ι.app j₀).right := by
      simpa using hs.fac ((Under.forget A).mapCocone c) j₀
    have hdesc :
        (t.app j₀ ≫ s.app j₀) ≫ hs.desc ((Under.forget A).mapCocone c) =
          t.app j₀ ≫ (c.ι.app j₀).right := by
      calc
        (t.app j₀ ≫ s.app j₀) ≫ hs.desc ((Under.forget A).mapCocone c) =
            t.app j₀ ≫ (s.app j₀ ≫ hs.desc ((Under.forget A).mapCocone c)) := by
              simp [Category.assoc]
        _ = t.app j₀ ≫ (c.ι.app j₀).right := by
              exact congrArg (fun z ↦ t.app j₀ ≫ z) hfac₀
    exact hdesc.trans <| by
      simpa using (c.ι.app j₀).w.symm
  · intro c j
    -- After forgetting to rings, this is the usual colimit computation on the `j`-th stage.
    refine CategoryTheory.CommaMorphism.ext rfl ?_
    simpa using hs.fac ((Under.forget A).mapCocone c) j
  · intro c m hm
    -- Uniqueness is checked after forgetting to rings, where `hs` already gives the universal
    -- property.
    refine CategoryTheory.CommaMorphism.ext rfl ?_
    apply hs.hom_ext
    intro j
    have hmj :
        s.app j ≫ m.right = (c.ι.app j).right := by
      simpa [ind_underCocone] using congrArg CategoryTheory.CommaMorphism.right (hm j)
    have hfac :
        s.app j ≫ hs.desc ((Under.forget A).mapCocone c) = (c.ι.app j).right := by
      simpa using hs.fac ((Under.forget A).mapCocone c) j
    exact hmj.trans hfac.symm

/-- Helper for Lemma 15.45.6: normality transports across a ring equivalence. -/
lemma isNormalRing_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) [IsNormalRing A] :
    IsNormalRing B := by
  -- A ring equivalence is étale, hence smooth, so normality ascends across it.
  letI : Algebra A B := e.toRingHom.toAlgebra
  have het : (algebraMap A B).Etale := by
    exact RingHom.Etale.of_bijective e.bijective
  letI : Algebra.Etale A B := (RingHom.etale_algebraMap (R := A) (S := B)).mp het
  exact isNormalRing_of_smooth

/-- Helper for Lemma 15.45.6: a filtered colimit in `Under A` is normal once every stage is a
normal ring. -/
lemma under_isNormalRing_of_isColimit_filtered_system {A : CommRingCat.{u}}
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under A) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, IsNormalRing (F.obj j)) :
    IsNormalRing c.pt := by
  let cG := (Under.forget A).mapCocone c
  have hcG : IsColimit cG := Limits.isColimitOfPreserves (Under.forget A) hc
  -- Forgetting from `Under` to rings exposes the canonical Chapter 10 filtered-colimit theorem.
  letI : ∀ j, IsNormalRing ((F ⋙ Under.forget A).obj j) :=
    fun j ↦ by
      simpa using hF j
  simpa using
    isNormalRing_of_isColimit_filtered_system
      (F := F ⋙ Under.forget A) cG hcG

/-- Helper for Lemma 15.45.6: an ind-étale algebra map is flat over its base ring. -/
lemma flat_of_isFilteredColimitOfEtale {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale) :
    Module.Flat A B := by
  let _ : Algebra A (ULift B) := ULift.algebra
  let _ : Algebra (ULift.{u} A) (ULift B) := ULift.algebra' A (ULift B)
  -- Unpack the same-universe ind-étale witness hidden in the source-facing owner.
  dsimp [RingHom.IsFilteredColimitOfEtale] at hcolim
  rcases hcolim with ⟨J, _, _, D, t, s, hs, hstage⟩
  let F := ind_underFunctor (A := CommRingCat.of (ULift.{u} A)) D t
  let cUnder :=
    ind_underCocone D t s
      (CommRingCat.ofHom (algebraMap (ULift.{u} A) (ULift B)))
      (fun j ↦ (hstage j).2)
  have hsUnder :
      IsColimit
        cUnder := by
    -- The filtered colimit presentation lifts from rings to rings under the fixed base.
    exact ind_underCocone_isColimit_of_isColimit
      (D := D) (t := t) (s := s)
      (f := CommRingCat.ofHom (algebraMap (ULift.{u} A) (ULift B)))
      (hcompat := fun j ↦ (hstage j).2) hs
  letI : ∀ j, Module.Flat (ULift.{u} A) (F.obj j) :=
    fun j ↦ by
      let _ : Algebra (ULift.{u} A) (D.obj j) := (t.app j).hom.toAlgebra
      have hEtale : (t.app j).hom.Etale := by
        -- Each stage map in the chosen presentation is étale by construction.
        simpa [CommRingCat.etale] using (hstage j).1
      have hflatStageHom : (algebraMap (ULift.{u} A) (D.obj j)).Flat := by
        have hflat : (t.app j).hom.Flat :=
          (RingHom.Etale.iff_flat_and_formallyUnramified (f := (t.app j).hom)).mp hEtale |>.1
        simpa [RingHom.algebraMap_toAlgebra] using hflat
      have hflatStage : Module.Flat (ULift.{u} A) (D.obj j) :=
        RingHom.flat_algebraMap_iff.mp hflatStageHom
      simpa [F, ind_underFunctor] using hflatStage
  have hflatULiftUnder :
      Module.Flat (ULift.{u} A)
        cUnder.pt.right := by
    -- Stagewise étale flatness feeds into the under-category filtered-colimit flatness lemma.
    exact
      under_flat_of_isColimit_filtered_system
        (A := ULift.{u} A) F cUnder hsUnder
  let _ : Algebra (ULift.{u} A) cUnder.pt.right := cUnder.pt.hom.hom.toAlgebra
  have hflatUpUnder : (algebraMap (ULift.{u} A) cUnder.pt.right).Flat :=
    (RingHom.flat_algebraMap_iff (R := ULift.{u} A) (S := cUnder.pt.right)).mpr hflatULiftUnder
  have hflatUp : (algebraMap (ULift.{u} A) (ULift B)).Flat := by
    -- Unfold the cocone point once to identify its algebra map with the canonical `ULift` map.
    simpa [cUnder, ind_underCocone] using hflatUpUnder
  have hsource :
      ((ULift.ringEquiv.symm : A ≃+* ULift.{u} A).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv.symm : A ≃+* ULift.{u} A).bijective
  have htarget :
      ((ULift.ringEquiv : ULift B ≃+* B).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv : ULift B ≃+* B).bijective
  have hcomp :
      (((ULift.ringEquiv : ULift B ≃+* B).toRingHom).comp
        ((algebraMap (ULift.{u} A) (ULift B)).comp
          ((ULift.ringEquiv.symm : A ≃+* ULift.{u} A).toRingHom))).Flat := by
    -- Flatness is stable under composition with the two `ULift` equivalences.
    exact RingHom.Flat.comp (RingHom.Flat.comp hsource hflatUp) htarget
  have hEq :
      ((ULift.ringEquiv : ULift B ≃+* B).toRingHom).comp
        ((algebraMap (ULift.{u} A) (ULift B)).comp
          ((ULift.ringEquiv.symm : A ≃+* ULift.{u} A).toRingHom)) =
        algebraMap A B := by
    -- The transported composite is definitionally the original structure map.
    ext x
    rfl
  have hflatAB : (algebraMap A B).Flat := by
    rw [← hEq]
    exact hcomp
  exact RingHom.flat_algebraMap_iff.mp hflatAB

/-- Helper for Lemma 15.45.6: the canonical map to a henselization is faithfully flat. -/
lemma algebraMap_faithfullyFlat_of_isHenselizationOf :
    (algebraMap R Rh).FaithfullyFlat := by
  -- Once flatness is extracted from the ind-étale presentation, locality upgrades it to faithful
  -- flatness through the standard local-map criterion.
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  letI : Module.Flat R Rh :=
    flat_of_isFilteredColimitOfEtale IsHenselizationOf.isFilteredColimitOfEtale
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Helper for Lemma 15.45.6: the canonical map to a strict henselization is faithfully flat. -/
lemma algebraMap_faithfullyFlat_of_isStrictHenselizationOf :
    (algebraMap R Rsh).FaithfullyFlat := by
  -- The strict-henselization map has the same source-route shape as the henselization map.
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  letI : Module.Flat R Rsh :=
    flat_of_isFilteredColimitOfEtale IsStrictHenselizationOf.isFilteredColimitOfEtale
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Helper for Lemma 15.45.6: an ind-étale algebra over a normal base ring is normal. -/
lemma isNormalRing_of_isFilteredColimitOfEtale {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [IsNormalRing A]
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale) :
    IsNormalRing B := by
  let _ : Algebra A (ULift B) := ULift.algebra
  let _ : Algebra (ULift.{u} A) (ULift B) := ULift.algebra' A (ULift B)
  letI : IsNormalRing (ULift.{u} A) :=
    isNormalRing_of_ringEquiv (ULift.ringEquiv.symm : A ≃+* ULift.{u} A)
  -- Unpack the chosen ind-étale presentation once and keep it fixed for the rest of the proof.
  dsimp [RingHom.IsFilteredColimitOfEtale] at hcolim
  rcases hcolim with ⟨J, _, _, D, t, s, hs, hstage⟩
  let F := ind_underFunctor (A := CommRingCat.of (ULift.{u} A)) D t
  have hsUnder :
      IsColimit
        (ind_underCocone D t s
          (CommRingCat.ofHom (algebraMap (ULift.{u} A) (ULift B)))
          (fun j ↦ (hstage j).2)) := by
    -- The same under-category lift packages the colimit data needed by the Chapter 10 theorem.
    exact ind_underCocone_isColimit_of_isColimit
      (D := D) (t := t) (s := s)
      (f := CommRingCat.ofHom (algebraMap (ULift.{u} A) (ULift B)))
      (hcompat := fun j ↦ (hstage j).2) hs
  have hNormalULift : IsNormalRing (ULift B) := by
    -- Each étale stage over the normal base is smooth, hence normal; filtered colimits preserve
    -- normality in the under-category presentation.
    refine under_isNormalRing_of_isColimit_filtered_system
      (A := CommRingCat.of (ULift.{u} A)) F
      (ind_underCocone D t s
        (CommRingCat.ofHom (algebraMap (ULift.{u} A) (ULift B)))
        (fun j ↦ (hstage j).2))
      hsUnder
      (fun j ↦ ?_)
    let _ : Algebra (ULift.{u} A) (D.obj j) := (t.app j).hom.toAlgebra
    have hEtale : (t.app j).hom.Etale := by
      -- The stage map is one of the chosen étale generators of the ind-étale presentation.
      simpa [CommRingCat.etale] using (hstage j).1
    have hEtaleAlg : Algebra.Etale (ULift.{u} A) (D.obj j) := by
      refine (RingHom.etale_algebraMap (R := ULift.{u} A) (S := D.obj j)).mp ?_
      simpa [RingHom.algebraMap_toAlgebra] using hEtale
    letI : Algebra.Etale (ULift.{u} A) (D.obj j) := hEtaleAlg
    have hNormalStage : IsNormalRing (D.obj j) := by
      -- Etale algebras are smooth, so the Chapter 10 smooth-ascent theorem applies.
      exact isNormalRing_of_smooth
    simpa [F, ind_underFunctor] using hNormalStage
  -- Transport the normality instance back across the canonical `ULift` ring equivalence.
  exact isNormalRing_of_ringEquiv (ULift.ringEquiv : ULift B ≃+* B)

/-- Lemma 15.45.6: for a local ring `R`, the following are equivalent: `R` is a normal ring, a
henselization `Rh` of `R` is a normal ring, and a strict henselization `Rsh` of `R` is a normal
ring. For local rings this matches the textbook formulation in terms of normal domains. -/
theorem isNormalRing_tfae_henselization_strictHenselization :
    List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] := by
  -- The source proof is a two-map transfer argument: ind-étale ascent from `R` to each chosen
  -- henselian algebra, and faithfully flat descent back to `R`.
  tfae_have 1 → 2 := by
    -- Normality ascends from the base ring to the chosen henselization.
    intro hR
    letI : IsNormalRing R := hR
    exact isNormalRing_of_isFilteredColimitOfEtale
      (A := R) (B := Rh) IsHenselizationOf.isFilteredColimitOfEtale
  tfae_have 2 → 1 := by
    -- Faithfully flat descent recovers normality of the base from the henselization.
    intro hRh
    letI : IsNormalRing Rh := hRh
    exact isNormalRing_of_faithfullyFlat (algebraMap R Rh)
      algebraMap_faithfullyFlat_of_isHenselizationOf
  tfae_have 1 → 3 := by
    -- The same ind-étale ascent argument applies to the strict henselization.
    intro hR
    letI : IsNormalRing R := hR
    exact isNormalRing_of_isFilteredColimitOfEtale
      (A := R) (B := Rsh) IsStrictHenselizationOf.isFilteredColimitOfEtale
  tfae_have 3 → 1 := by
    -- The strict-henselization map is also faithfully flat, so the descent step repeats verbatim.
    intro hRsh
    letI : IsNormalRing Rsh := hRsh
    exact isNormalRing_of_faithfullyFlat (algebraMap R Rsh)
      algebraMap_faithfullyFlat_of_isStrictHenselizationOf
  tfae_finish

end

section

variable {R Rh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

-- The `0 ↔ 1` implication extracted from the source-facing `TFAE`.
/-- A local ring is normal if and only if any henselization is normal. -/
theorem isNormalRing_iff_isNormalRing_henselization :
    IsNormalRing R ↔ IsNormalRing Rh := by
  obtain ⟨Rsh, _, _, _⟩ := exists_strictHenselization R
  have hTFAE : List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] :=
    isNormalRing_tfae_henselization_strictHenselization
  exact hTFAE.out 0 1

end

section

variable {R Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- The `0 ↔ 2` implication extracted from the source-facing `TFAE`.
/-- A local ring is normal if and only if any strict henselization is normal. -/
theorem isNormalRing_iff_isNormalRing_strictHenselization :
    IsNormalRing R ↔ IsNormalRing Rsh := by
  obtain ⟨Rh, _, _, _⟩ := exists_henselization R
  have hTFAE : List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] :=
    isNormalRing_tfae_henselization_strictHenselization
  exact hTFAE.out 0 2

end

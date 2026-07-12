import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_3
import StacksProject_2024.Chap10.Lemma_10_106_8
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap10.Lemma_10_137_3
import StacksProject_2024.Chap10.Lemma_10_140_3
import StacksProject_2024.Chap10.Lemma_10_147_5
import StacksProject_2024.Chap10.Lemma_10_31_7
import StacksProject_2024.Chap15.Definition_15_41_1

open scoped TensorProduct

noncomputable section

universe u v

namespace RingHom

section LocalizationHelpers

variable {J : Type u} [Preorder J]
variable (B : J → Type v) [∀ j, CommRing (B j)]
variable (ρ : ∀ i j, i ≤ j → B i →+* B j) [DirectedSystem B (ρ · · ·)]
variable {A : Type v} [CommRing A]
variable (ι : ∀ j, B j →+* A)
variable (hcompat : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)

/-- Helper for Lemma 15.41.5: the prime of the target ring pulls back to a prime on each stage of
the directed system. -/
private abbrev localizationAtPrime_stagePrime (q : PrimeSpectrum A) (j : J) :
    PrimeSpectrum (B j) :=
  PrimeSpectrum.comap (ι j) q

/-- Helper for Lemma 15.41.5: localize each stage at the prime lying under the chosen target
prime. -/
private abbrev localizationAtPrime_stageRing (q : PrimeSpectrum A) (j : J) :
    Type v :=
  Localization.AtPrime ((localizationAtPrime_stagePrime B ι q j).asIdeal)

/-- Helper for Lemma 15.41.5: the pulled-back prime is compatible with the transition maps of the
directed system. -/
private lemma localizationAtPrime_stagePrime_comap
    (hcompat' : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)
    (q : PrimeSpectrum A) {i j : J} (hij : i ≤ j) :
    Ideal.comap (ρ i j hij) ((localizationAtPrime_stagePrime B ι q j).asIdeal) =
      (localizationAtPrime_stagePrime B ι q i).asIdeal := by
  -- Expand the pulled-back prime once and rewrite with the stage compatibility relation.
  ext x
  have hcomp : ι j (ρ i j hij x) = ι i x := by
    change ((ι j).comp (ρ i j hij)) x = (ι i) x
    rw [hcompat' hij]
  change ι j (ρ i j hij x) ∈ q.asIdeal ↔ ι i x ∈ q.asIdeal
  simpa [hcomp]

/-- Helper for Lemma 15.41.5: the localized transition map between two stages. -/
private abbrev localizationAtPrime_stageMap
    (hcompat' : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)
    (q : PrimeSpectrum A) {i j : J} (hij : i ≤ j) :
    localizationAtPrime_stageRing B ι q i →+*
      localizationAtPrime_stageRing B ι q j :=
  Localization.localRingHom
    (localizationAtPrime_stagePrime B ι q i).asIdeal
    (localizationAtPrime_stagePrime B ι q j).asIdeal
    (ρ i j hij)
    (localizationAtPrime_stagePrime_comap
      (B := B) (ρ := ρ) (ι := ι) hcompat' q hij).symm

/-- Helper for Lemma 15.41.5: each localized stage maps canonically to the localization of the
target at the chosen prime. -/
private abbrev localizationAtPrime_toTarget
    (q : PrimeSpectrum A) (j : J) :
    localizationAtPrime_stageRing B ι q j →+*
      Localization.AtPrime q.asIdeal :=
  Localization.localRingHom
    (localizationAtPrime_stagePrime B ι q j).asIdeal
    q.asIdeal
    (ι j)
    rfl

/-- Helper for Lemma 15.41.5: the localized stage maps to the target commute with the localized
transition maps. -/
private lemma localizationAtPrime_toTarget_comp_stageMap
    (hcompat' : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)
    (q : PrimeSpectrum A) {i j : J} (hij : i ≤ j) :
    (localizationAtPrime_toTarget B ι q j).comp
        (localizationAtPrime_stageMap B ρ ι hcompat' q hij) =
      localizationAtPrime_toTarget B ι q i := by
  -- Both localized maps are induced from the same composite `B i → A`, so uniqueness of
  -- `Localization.localRingHom` identifies the composite with the direct localized target map.
  symm
  refine Localization.localRingHom_unique
    (localizationAtPrime_stagePrime B ι q i).asIdeal q.asIdeal (ι i) rfl fun x ↦ ?_
  -- Rewrite both sides on the base ring `B i`; the compatibility relation collapses the stage map.
  simp only [localizationAtPrime_toTarget, localizationAtPrime_stageMap, RingHom.comp_apply,
    Localization.localRingHom_to_map]
  change algebraMap A (Localization.AtPrime q.asIdeal) (ι j (ρ i j hij x)) =
    algebraMap A (Localization.AtPrime q.asIdeal) (ι i x)
  rw [show ι j (ρ i j hij x) = ι i x by
    change ((ι j).comp (ρ i j hij)) x = (ι i) x
    rw [hcompat' hij]]

/-- Helper for Lemma 15.41.5: evaluate the commuting-square identity from
`localizationAtPrime_toTarget_comp_stageMap` on a localized element. -/
private lemma localizationAtPrime_toTarget_stageMap_apply
    (hcompat' : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)
    (q : PrimeSpectrum A) {i j : J} (hij : i ≤ j)
    (x : localizationAtPrime_stageRing B ι q i) :
    localizationAtPrime_toTarget B ι q j
        (localizationAtPrime_stageMap B ρ ι hcompat' q hij x) =
      localizationAtPrime_toTarget B ι q i x := by
  -- Evaluate the ring-hom equality pointwise so the later direct-limit lift can use a scalar
  -- compatibility theorem rather than re-unfolding the commuting square.
  have hcomp :
      ⇑((localizationAtPrime_toTarget B ι q j).comp
          (localizationAtPrime_stageMap B ρ ι hcompat' q hij)) =
        ⇑(localizationAtPrime_toTarget B ι q i) :=
    congrArg
      (fun g :
          localizationAtPrime_stageRing B ι q i →+* Localization.AtPrime q.asIdeal ↦
        (g : localizationAtPrime_stageRing B ι q i → Localization.AtPrime q.asIdeal)) <|
      localizationAtPrime_toTarget_comp_stageMap
      (B := B) (ρ := ρ) (ι := ι) hcompat' q hij
  simpa [RingHom.comp_apply] using
    congrFun hcomp x

/-- Helper for Lemma 15.41.5: the canonical comparison map from the direct limit of the localized
stages to the localization of the target ring at `q`. -/
private abbrev localizationAtPrime_directLimitToTarget
    (hcompat' : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)
    (q : PrimeSpectrum A) :
    Ring.DirectLimit
        (localizationAtPrime_stageRing B ι q)
        (fun i j hij ↦ localizationAtPrime_stageMap B ρ ι hcompat' q hij) →+*
      Localization.AtPrime q.asIdeal :=
  Ring.DirectLimit.lift
    (localizationAtPrime_stageRing B ι q)
    (fun i j hij ↦ localizationAtPrime_stageMap B ρ ι hcompat' q hij)
    (Localization.AtPrime q.asIdeal)
    (localizationAtPrime_toTarget B ι q)
    (fun i j hij x ↦
      localizationAtPrime_toTarget_stageMap_apply
        (B := B) (ρ := ρ) (ι := ι) hcompat' q hij x)

/-- Helper for Lemma 15.41.5: the direct-limit comparison map restricts on each stage to the
expected localized map into the target. -/
private lemma localizationAtPrime_directLimitToTarget_comp_of
    (hcompat' : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)
    (q : PrimeSpectrum A) (j : J) :
    (localizationAtPrime_directLimitToTarget B ρ ι hcompat' q).comp
        (Ring.DirectLimit.of
          (localizationAtPrime_stageRing B ι q)
          (fun i j hij ↦ localizationAtPrime_stageMap B ρ ι hcompat' q hij) j) =
      localizationAtPrime_toTarget B ι q j := by
  -- This is the direct-limit universal-property computation rule on the `j`-th stage.
  ext x
  simpa [localizationAtPrime_directLimitToTarget] using
    (Ring.DirectLimit.lift_of
      (G := localizationAtPrime_stageRing B ι q)
      (f := fun i j hij ↦ localizationAtPrime_stageMap B ρ ι hcompat' q hij)
      (P := Localization.AtPrime q.asIdeal)
      (g := localizationAtPrime_toTarget B ι q)
      (Hg := fun i j hij x ↦
        localizationAtPrime_toTarget_stageMap_apply
          (B := B) (ρ := ρ) (ι := ι) hcompat' q hij x)
      j x)

/-- Helper for Lemma 15.41.5: the localized transition maps are local ring homomorphisms. -/
private lemma localizationAtPrime_stageMap_isLocalHom
    (hcompat' : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)
    (q : PrimeSpectrum A) {i j : J} (hij : i ≤ j) :
    IsLocalHom (localizationAtPrime_stageMap B ρ ι hcompat' q hij) := by
  -- This is the canonical locality statement for `Localization.localRingHom`.
  simpa [localizationAtPrime_stageMap] using
    (Localization.isLocalHom_localRingHom
      (localizationAtPrime_stagePrime B ι q i).asIdeal
      (localizationAtPrime_stagePrime B ι q j).asIdeal
      (ρ i j hij)
      (localizationAtPrime_stagePrime_comap
        (B := B) (ρ := ρ) (ι := ι) hcompat' q hij).symm)

variable [Nonempty J] [IsDirectedOrder J]

/-- Helper for Lemma 15.41.5: if every element of the target ring already lifts from some stage,
then every element of the target localization lifts from the direct limit of the localized
stages. -/
private lemma localizationAtPrime_directLimitToTarget_surjective
    (hcompat' : ∀ ⦃i j⦄ (hij : i ≤ j), (ι j).comp (ρ i j hij) = ι i)
    (hsurj : Function.Surjective (fun x : Σ j, B j ↦ ι x.1 x.2))
    (q : PrimeSpectrum A) :
    Function.Surjective (localizationAtPrime_directLimitToTarget B ρ ι hcompat' q) := by
  intro z
  -- Present the localized target element by one numerator and one denominator in `A`.
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl z
  -- Lift both pieces to stages, then enlarge to a common upper stage.
  obtain ⟨⟨i, ai⟩, hai⟩ := hsurj a
  obtain ⟨⟨j, sj⟩, hsj⟩ := hsurj (s : A)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hnum :
      ι k (ρ i k hik ai) = a := by
    change ((ι k).comp (ρ i k hik)) ai = a
    rw [hcompat' hik]
    exact hai
  have hden :
      ι k (ρ j k hjk sj) = (s : A) := by
    change ((ι k).comp (ρ j k hjk)) sj = (s : A)
    rw [hcompat' hjk]
    exact hsj
  -- The lifted denominator still avoids the localized prime after moving to the common stage.
  have hs_stage_denom :
      ρ j k hjk sj ∈ (localizationAtPrime_stagePrime B ι q k).asIdeal.primeCompl := by
    change ι k (ρ j k hjk sj) ∉ q.asIdeal
    rw [hden]
    exact s.2
  let sk : (localizationAtPrime_stagePrime B ι q k).asIdeal.primeCompl :=
    ⟨ρ j k hjk sj, hs_stage_denom⟩
  let xk : localizationAtPrime_stageRing B ι q k :=
    IsLocalization.mk' (localizationAtPrime_stageRing B ι q k) (ρ i k hik ai) sk
  refine ⟨Ring.DirectLimit.of
      (localizationAtPrime_stageRing B ι q)
      (fun i j hij ↦ localizationAtPrime_stageMap B ρ ι hcompat' q hij) k xk, ?_⟩
  -- Evaluate the direct-limit comparison on the chosen stage fraction and rewrite it back to `z`.
  have hcomp :
      localizationAtPrime_directLimitToTarget B ρ ι hcompat' q
          (Ring.DirectLimit.of
            (localizationAtPrime_stageRing B ι q)
            (fun i j hij ↦ localizationAtPrime_stageMap B ρ ι hcompat' q hij) k xk) =
        localizationAtPrime_toTarget B ι q k xk := by
    simpa using
      congrArg
        (fun g :
            localizationAtPrime_stageRing B ι q k →+* Localization.AtPrime q.asIdeal ↦
          g xk)
        (localizationAtPrime_directLimitToTarget_comp_of
          (B := B) (ρ := ρ) (ι := ι) hcompat' q k)
  have hs_target_denom :
      (⟨ι k (ρ j k hjk sj), by
          change ι k (ρ j k hjk sj) ∉ q.asIdeal
          rw [hden]
          exact s.2⟩ : q.asIdeal.primeCompl) = s := by
    apply Subtype.ext
    simpa using hden
  calc
    localizationAtPrime_directLimitToTarget B ρ ι hcompat' q
        (Ring.DirectLimit.of
          (localizationAtPrime_stageRing B ι q)
          (fun i j hij ↦ localizationAtPrime_stageMap B ρ ι hcompat' q hij) k xk)
      = localizationAtPrime_toTarget B ι q k xk := hcomp
    _ = IsLocalization.mk' (Localization.AtPrime q.asIdeal) (ι k (ρ i k hik ai))
          (⟨ι k (ρ j k hjk sj), by
              change ι k (ρ j k hjk sj) ∉ q.asIdeal
              rw [hden]
              exact s.2⟩ : q.asIdeal.primeCompl) := by
        -- `localizationAtPrime_toTarget` is the canonical localized map on the `k`-th stage.
        simpa [localizationAtPrime_toTarget, xk, sk] using
          (Localization.localRingHom_mk'
            (localizationAtPrime_stagePrime B ι q k).asIdeal
            q.asIdeal
            (ι k)
            rfl
            (ρ i k hik ai)
            sk)
    _ = IsLocalization.mk' (Localization.AtPrime q.asIdeal) a
          (⟨(s : A), s.2⟩ : q.asIdeal.primeCompl) := by
        rw [hnum, hs_target_denom]
    _ = IsLocalization.mk' (Localization.AtPrime q.asIdeal) a s := by
        rfl

end LocalizationHelpers

section UnderFlat

open CategoryTheory Limits
open CategoryTheory.Under
open CommRingCat

/-- Helper for Lemma 15.41.5: turn the stage maps in an `ind` presentation into a functor to the
under-category over the fixed source ring. -/
private abbrev ind_underFunctor {A : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D) :
    J ⥤ Under A :=
  { obj := fun j ↦ Under.mk (t.app j)
    map := fun {i j} g ↦ Under.homMk (D.map g) (by
      -- The `Under`-morphism condition is exactly the naturality square for the stage map `t`.
      simpa using (t.naturality g).symm) }

/-- Helper for Lemma 15.41.5: the target cocone of an `ind` presentation lifts canonically to the
corresponding cocone in the under-category. -/
private abbrev ind_underCocone {A B : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    (s : D ⟶ (Functor.const J).obj B) (f : A ⟶ B)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f) :
    Cocone (ind_underFunctor (A := A) D t) :=
  { pt := Under.mk f
    ι :=
      { app := fun j ↦ Under.homMk (s.app j) (hcompat j)
        naturality := by
          intro i j g
          -- Equality of `Under` morphisms reduces to equality of their right components.
          refine CategoryTheory.CommaMorphism.ext rfl ?_
          simpa using s.naturality g } }

/-- Helper for Lemma 15.41.5: if the underlying cocone in `CommRingCat` is colimiting, then the
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
    -- The lifted desc morphism must respect the fixed source map; a single stage equation reduces
    -- this to the ordinary colimit computation after forgetting from `Under`.
    change f ≫ hs.desc ((Under.forget A).mapCocone c) = c.pt.hom
    rw [← hcompat j₀]
    have hfac₀ :
        s.app j₀ ≫ hs.desc ((Under.forget A).mapCocone c) = (c.ι.app j₀).right := by
      simpa using hs.fac ((Under.forget A).mapCocone c) j₀
    have hdesc :
        (t.app j₀ ≫ s.app j₀) ≫ hs.desc ((Under.forget A).mapCocone c) =
          t.app j₀ ≫ (c.ι.app j₀).right := by
      calc
        (t.app j₀ ≫ s.app j₀) ≫ hs.desc ((Under.forget A).mapCocone c)
            = t.app j₀ ≫ (s.app j₀ ≫ hs.desc ((Under.forget A).mapCocone c)) := by
                simp [Category.assoc]
        _ = t.app j₀ ≫ (c.ι.app j₀).right := by
              exact congrArg (fun z ↦ t.app j₀ ≫ z) hfac₀
    exact hdesc.trans <| by
      simpa using (c.ι.app j₀).w.symm
  · intro c j
    -- After forgetting to rings, this is exactly the usual colimit fac equation on the `j`-th
    -- stage, and equality of under-morphisms is determined by the right component.
    refine CategoryTheory.CommaMorphism.ext rfl ?_
    simpa using hs.fac ((Under.forget A).mapCocone c) j
  · intro c m hm
    -- Uniqueness is checked after forgetting to rings, where `hs` already supplies the universal
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

/-- Helper for Lemma 15.41.5: forget a commutative ring under `A` to its underlying `A`-module. -/
private abbrev under_forget_to_module (A : CommRingCat.{u}) : Under A ⥤ ModuleCat A where
  obj B := ModuleCat.of A B
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap

/-- Helper for Lemma 15.41.5: an object under `CommRingCat.of A` carries the canonical
`A`-module structure induced by its structure map. -/
private instance under_module (A : Type u) [CommRing A] (B : Under (CommRingCat.of A)) :
    Module A B := by
  let _ : Algebra A B.right := B.hom.hom.toAlgebra
  infer_instance

/-- Helper for Lemma 15.41.5: a filtered colimit in `Under (CommRingCat.of A)` is flat once
every stage is flat over the fixed base ring `A`. -/
private lemma under_colimit_flat_of_stagewise_flat {A : Type u} [CommRing A]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of A)) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat A (F.obj j)] :
    Module.Flat A c.pt.right := by
  let cM := (under_forget_to_module (CommRingCat.of A)).mapCocone c
  letI : ∀ j, Module.Flat A ((F ⋙ under_forget_to_module (CommRingCat.of A)).obj j) :=
    fun j ↦ by
      simpa [under_forget_to_module] using (inferInstance : Module.Flat A (F.obj j))
  have hcM : IsColimit cM := by
    -- Forget the under-diagram to additive groups, where the relevant filtered colimits are
    -- preserved, and then reflect the resulting colimit back to `ModuleCat`.
    apply isColimitOfReflects (forget₂ (ModuleCat A) AddCommGrpCat)
    simpa [under_forget_to_module] using
      (isColimitOfPreserves
        (CategoryTheory.Under.forget (CommRingCat.of A) ⋙
          forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) hc)
  -- Apply the Chapter 10 filtered-colimit flatness theorem to the transported module diagram.
  simpa using
    flat_of_isColimit_filtered_system
      (F := F ⋙ under_forget_to_module (CommRingCat.of A)) cM hcM

end UnderFlat

section FilteredColimitSmoothFlat

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Helper for Lemma 15.41.5: a filtered colimit of smooth algebras is flat over the base ring. -/
theorem IsFilteredColimitOfSmooth.flat
    (h : f.IsFilteredColimitOfSmooth) :
    f.Flat := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift S) := ULift.algebra' R (ULift S)
  -- Unpack the same-universe `ind` witness once and keep the chosen presentation fixed for the
  -- rest of the proof.
  dsimp [RingHom.IsFilteredColimitOfSmooth] at h
  rcases h with ⟨J, _, _, D, t, s, hs, hstage⟩
  let F := ind_underFunctor (A := CommRingCat.of (ULift.{v} R)) D t
  have hsUnder :
      CategoryTheory.Limits.IsColimit
        (ind_underCocone D t s
          (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift S)))
          (fun j ↦ (hstage j).2)) := by
    exact ind_underCocone_isColimit_of_isColimit
      (D := D) (t := t) (s := s)
      (f := CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift S)))
      (hcompat := fun j ↦ (hstage j).2) hs
  letI : ∀ j, Module.Flat (ULift.{v} R) (F.obj j) :=
    fun j ↦ by
      have hsmooth : (t.app j).hom.Smooth := (hstage j).1
      let _ : Algebra (ULift.{v} R) (D.obj j) := (t.app j).hom.toAlgebra
      have hflatStageHom :
          (algebraMap (ULift.{v} R) (D.obj j)).Flat := by
        simpa [RingHom.algebraMap_toAlgebra] using hsmooth.flat
      have hflatStage :
          Module.Flat (ULift.{v} R) (D.obj j) :=
        RingHom.flat_algebraMap_iff.mp hflatStageHom
      simpa [F, ind_underFunctor] using hflatStage
  have hflatULift : Module.Flat (ULift.{v} R) (ULift S) := by
    -- The `Under` colimit now matches the source-proof presentation exactly, so the stagewise
    -- smooth-flatness theorem applies without further reindexing.
    simpa [F, ind_underCocone] using
      under_colimit_flat_of_stagewise_flat
        (A := ULift.{v} R) F
        (ind_underCocone D t s
          (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift S)))
          (fun j ↦ (hstage j).2))
        hsUnder
  have hflatUp : (algebraMap (ULift.{v} R) (ULift S)).Flat :=
    RingHom.flat_algebraMap_iff.mpr hflatULift
  have hsource :
      ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).bijective
  have htarget :
      ((ULift.ringEquiv : ULift S ≃+* S).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv : ULift S ≃+* S).bijective
  have hcomp :
      (((ULift.ringEquiv : ULift S ≃+* S).toRingHom).comp
        ((algebraMap (ULift.{v} R) (ULift S)).comp
          ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom))).Flat := by
    exact RingHom.Flat.comp (RingHom.Flat.comp hsource hflatUp) htarget
  have hEq :
      ((ULift.ringEquiv : ULift S ≃+* S).toRingHom).comp
        ((algebraMap (ULift.{v} R) (ULift S)).comp
          ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom)) = f := by
    ext x
    rfl
  rw [← hEq]
  exact hcomp

end FilteredColimitSmoothFlat

section SmoothBaseChange

open CategoryTheory MorphismProperty
open CommRingCat

universe uR uS uR' uS'

private instance smooth_isStableUnderCobaseChange :
    (RingHom.toMorphismProperty
      (fun {A B} [CommRing A] [CommRing B] (g : A →+* B) ↦ g.Smooth)).IsStableUnderCobaseChange := by
  -- This is the smooth analogue of the ind-etale cobase-change instance from Chapter 10.
  simpa using
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2
      RingHom.Smooth.isStableUnderBaseChange

namespace IsFilteredColimitOfSmooth

/-- Helper for Lemma 15.41.5: filtered colimits of smooth ring maps are stable under base
change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.IsFilteredColimitOfSmooth := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hRS
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift R) (ULift S) := ULift.algebra' R (ULift S)
  let _ : Algebra R (ULift R') := ULift.algebra
  let _ : Algebra (ULift R) (ULift R') := ULift.algebra' R (ULift R')
  let _ : Algebra S (ULift S') := ULift.algebra
  let _ : Algebra (ULift S) (ULift S') := ULift.algebra' S (ULift S')
  let _ : Algebra R' (ULift S') := ULift.algebra
  let _ : Algebra (ULift R') (ULift S') := ULift.algebra' R' (ULift S')
  -- Mirror the Chapter 10 ind-etale base-change proof on the same `ULift` presentation hidden
  -- inside the source-facing owner `RingHom.IsFilteredColimitOfSmooth`.
  dsimp [RingHom.IsFilteredColimitOfSmooth] at hRS ⊢
  let sq₀ : IsPushout
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (algebraMap S S'))
      (CommRingCat.ofHom (algebraMap R' S')) :=
    CommRingCat.isPushout_of_isPushout R S R' S'
  let eR : CommRingCat.of R ≅ CommRingCat.of (ULift R) :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : R ≃+* ULift R)
  let eS : CommRingCat.of S ≅ CommRingCat.of (ULift S) :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : S ≃+* ULift S)
  let eR' : CommRingCat.of R' ≅ CommRingCat.of (ULift R') :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : R' ≃+* ULift R')
  let eS' : CommRingCat.of S' ≅ CommRingCat.of (ULift S') :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : S' ≃+* ULift S')
  let sq : IsPushout
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift S)))
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift R')))
      (CommRingCat.ofHom (algebraMap (ULift S) (ULift S')))
      (CommRingCat.ofHom (algebraMap (ULift R') (ULift S'))) :=
    sq₀.of_iso eR eS eR' eS'
      (by ext x; rfl) (by ext x; rfl) (by ext x; rfl) (by ext x; rfl)
  -- The categorical owner `MorphismProperty.ind` is already stable under cobase change, so the
  -- chosen pushout square upgrades the source `ind-smooth` presentation to the base-changed one.
  exact of_isPushout sq.flip hRS

end IsFilteredColimitOfSmooth

end SmoothBaseChange

section Main

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Helper for Lemma 15.41.5: a smooth algebra over a field remains regular local after
localizing at any prime lying under a target prime. -/
private theorem isRegularLocalRing_localizationAtPrime_comap_of_smooth
    {k : Type u} {B : Type v} {A : Type v}
    [Field k] [CommRing B] [CommRing A] [Algebra k B]
    (ι : B →+* A) (q : PrimeSpectrum A)
    (hsmooth : (algebraMap k B).Smooth) :
    IsRegularLocalRing (Localization.AtPrime ((PrimeSpectrum.comap ι q).asIdeal)) := by
  have hfp : (algebraMap k B).FinitePresentation := hsmooth.finitePresentation
  let _ : Algebra.FinitePresentation k B := (RingHom.finitePresentation_algebraMap).mp hfp
  let _ : Algebra.FiniteType k B := inferInstance
  have hisSmoothAt : Algebra.IsSmoothAt k ((PrimeSpectrum.comap ι q).asIdeal) := by
    let _ : Algebra.Smooth k B := (RingHom.smooth_algebraMap).1 hsmooth
    have hsmoothLocus : Algebra.smoothLocus k B = Set.univ := Algebra.smoothLocus_eq_univ
    -- Read off local smoothness of the pulled-back prime from the fact that the smooth locus is
    -- all of `Spec B`.
    simpa [Algebra.smoothLocus] using
      (Set.eq_univ_iff_forall.mp hsmoothLocus) (PrimeSpectrum.comap ι q)
  -- The field case of Lemma `10.140.3` upgrades local smoothness to regular-locality.
  simpa using
    (Algebra.isRegularLocalRing_of_isSmoothAt
      (k := k) (S := B) ((PrimeSpectrum.comap ι q).asIdeal) hisSmoothAt)

/-- Helper for Lemma 15.41.5: over a field, the proof reduces to comparing `A_q` with the direct
limit of the localized smooth stages and then invoking Lemma `10.106.8`. -/
private theorem localizationAtPrime_isRegularLocalRing_of_noetherian_filteredColimitOfSmooth_over_field
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [IsNoetherianRing A]
    (hA : (algebraMap k A).IsFilteredColimitOfSmooth)
    (q : PrimeSpectrum A) :
    IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  -- Route correction: the remaining work is the explicit identification of `Localization.AtPrime
  -- q.asIdeal` with the direct limit of the localized smooth stages in the chosen presentation of
  -- `hA`. Once that comparison is available, Lemma `10.106.8` closes the field case exactly in
  -- the source-proof style.
  have hstage_regular :
      ∀ {B : Type v} [CommRing B] [Algebra k B] (ι : B →+* A),
        (algebraMap k B).Smooth →
          IsRegularLocalRing (Localization.AtPrime ((PrimeSpectrum.comap ι q).asIdeal)) := by
    intro B _ _ ι hsmooth
    -- Package the stagewise regular-local statement once so the remaining blocker is only the
    -- direct-limit comparison with the chosen filtered presentation.
    simpa using
      isRegularLocalRing_localizationAtPrime_comap_of_smooth
        (k := k) (B := B) (A := A) ι q hsmooth
  -- Unpack the hidden filtered-colimit witness once so the remaining blocker is purely the
  -- localization/direct-limit comparison, not the stagewise smoothness input.
  dsimp [RingHom.IsFilteredColimitOfSmooth] at hA
  rcases hA with ⟨J, _, _, D, t, s, hs, hstage⟩
  have hstage_smooth : ∀ j : J, (t.app j).hom.Smooth := by
    intro j
    -- Record the stagewise smoothness from the `ind` witness now so the remaining gap is the
    -- passage from the filtered presentation to the localized direct limit.
    simpa [RingHom.toMorphismProperty] using (hstage j).1
  let _ := D
  let _ := t
  let _ := s
  let _ := hs
  let _ := hstage_smooth
  -- TODO for Lemma 15.41.5: choose a filtered smooth presentation of `A`, localize it stagewise
  -- at the primes under `q`, build the direct-limit comparison
  -- `Ring.DirectLimit ... → Localization.AtPrime q.asIdeal`, then construct the inverse map
  -- using the colimit presentation `hs` and prove these maps are mutually inverse before applying
  -- `Ring.DirectLimit.isRegularLocalRing`.
  -- The first concrete blocker is the directed reindexing of this filtered witness to the
  -- preorder-based `Ring.DirectLimit` API without importing the currently broken
  -- `Lemma_15_33_7` module.
  -- Once that bridge is available, the proof should compare its direct limit with
  -- `Localization.AtPrime q.asIdeal`, and then apply `Ring.DirectLimit.isRegularLocalRing`.
  sorry

-- Proof sketch: first prove flatness of the ind-smooth map. Then fix a prime `p ⊂ R` and use the
-- finite purely inseparable tensor-base-change criterion for geometric regularity. After base
-- change to the residue field and then to the chosen field extension, the resulting algebra is
-- still ind-smooth; the only missing ingredient is the field-case regularity theorem above.
/-- Helper for Lemma 15.41.5: finite tensor base change of a Noetherian fiber ring remains
Noetherian. -/
private theorem tensorBaseChange_isNoetherian_of_fiber_noetherian
    (p : PrimeSpectrum R)
    (hfiber_noetherian :
      let _ : Algebra R S := f.toAlgebra
      ∀ p : PrimeSpectrum R, IsNoetherianRing (p.asIdeal.Fiber S))
    (K : Type (max u v)) [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] :
    let _ : Algebra R S := f.toAlgebra
    IsNoetherianRing (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : IsNoetherianRing (p.asIdeal.Fiber S) := hfiber_noetherian p
  let _ : Module.Finite p.asIdeal.ResidueField K := inferInstance
  let _ : Algebra.FiniteType p.asIdeal.ResidueField K := Module.Finite.finiteType K
  -- The test field is finite type over the residue field, so base change preserves Noetherianity.
  simpa using
    (isNoetherianRing_baseChange
      (R := p.asIdeal.ResidueField)
      (S := p.asIdeal.Fiber S)
      (R' := K))

/-- Helper for Lemma 15.41.5: after tensoring a fiber with a field extension, the result should
still be a filtered colimit of smooth algebras over the new field. -/
private theorem tensorBaseChange_isFilteredColimitOfSmooth
    (hcolim : f.IsFilteredColimitOfSmooth)
    (p : PrimeSpectrum R)
    (K : Type (max u v)) [Field K] [Algebra p.asIdeal.ResidueField K]
    [FiniteDimensional p.asIdeal.ResidueField K] :
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber S) := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra K (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.leftAlgebra
    (algebraMap K (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S)).IsFilteredColimitOfSmooth := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber S) := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra K (K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.leftAlgebra
  -- TODO for Lemma 15.41.5: the abstract route is exactly two applications of
  -- `IsFilteredColimitOfSmooth.isStableUnderBaseChange`, first from `R` to `κ(p)` and then from
  -- `κ(p)` to `K`. The blocker is the explicit `ULift` transport needed because the source wrapper
  -- stores the ind-smooth witness on the same-universe map
  -- `ULift R → ULift S`, while the fiber ring lives in universe `max u v`.
  sorry

/-- Lemma 15.41.5: if a ring map `f : R →+* S` is a filtered colimit of smooth `R`-algebras and
every fiber ring `p.asIdeal.Fiber S = κ(p) ⊗[R] S` is Noetherian, then `f` is regular. -/
@[stacks 07EP]
theorem IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers
    (hcolim : f.IsFilteredColimitOfSmooth)
    (hfiber_noetherian :
      let _ : Algebra R S := f.toAlgebra
      ∀ p : PrimeSpectrum R, IsNoetherianRing (p.asIdeal.Fiber S)) :
    f.IsRegularRingMap := by
  let _ : Algebra R S := f.toAlgebra
  -- Route correction: the flatness half is now extracted directly from the chosen `ind` witness,
  -- so the only remaining source-proof work is the field-valued fiber regularity statement.
  rw [RingHom.isRegularRingMap_iff_flat_and_geometricallyRegular_fiber]
  constructor
  · exact hcolim.flat
  · intro p
    -- Geometric regularity is tested on finite purely inseparable tensor base changes.
    rw [Algebra.isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
    intro K _ _ _ _
    let T := K ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S
    let _ : Algebra p.asIdeal.ResidueField (p.asIdeal.Fiber S) := Algebra.TensorProduct.leftAlgebra
    let _ : Algebra K T := Algebra.TensorProduct.leftAlgebra
    letI : IsNoetherianRing T :=
      tensorBaseChange_isNoetherian_of_fiber_noetherian
        (f := f) p hfiber_noetherian K
    have hTcolim :
        (algebraMap K T).IsFilteredColimitOfSmooth :=
      tensorBaseChange_isFilteredColimitOfSmooth
        (f := f) hcolim p K
    refine ⟨fun q ↦ ?_⟩
    -- The unresolved field case now applies directly to the Noetherian ind-smooth `K`-algebra `T`.
    exact localizationAtPrime_isRegularLocalRing_of_noetherian_filteredColimitOfSmooth_over_field
      (k := K) (A := T) hTcolim q

end Main

end RingHom

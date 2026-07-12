import Mathlib
import StacksProject_2024.Chap10.Lemma_10_150_4
import StacksProject_2024.Chap10.Lemma_10_150_6
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_101_1
import StacksProject_2024.Chap10.Lemma_10_39_3
import StacksProject_2024.Chap10.Remark_10_155_4
import StacksProject_2024.Chap10.Lemma_10_97_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingHom
open CategoryTheory MorphismProperty Limits
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh]

local notation "mR" => maximalIdeal R
local notation "mRh" => maximalIdeal Rh
local notation "mRsh" => maximalIdeal Rsh

/-- Helper for Lemma 15.45.1: the maximal-ideal residue field agrees with the ambient residue
field of a local ring. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Lemma 15.45.1: quotienting by the maximal ideal gives the usual residue field. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    A ⧸ maximalIdeal A ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).trans
      (maximalIdealResidueFieldEquiv A)

/-- Helper for Lemma 15.45.1: under the quotient-to-residue-field identification, the quotient
class of `a` is exactly the residue class of `a`. -/
private theorem maximalIdealQuotientResidueFieldEquiv_apply_mk
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealQuotientResidueFieldEquiv A (Ideal.Quotient.mk (maximalIdeal A) a) =
      residue A a := by
  -- Both maps factor the same canonical quotient map into the residue field.
  change
    maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (residue A a) by rfl]
  change
    maximalIdealResidueFieldEquiv A ((maximalIdealResidueFieldEquiv A).symm (residue A a)) =
      residue A a
  exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)

/-- Helper for Lemma 15.45.1: the quotient maps to residue fields commute with any local
homomorphism. -/
private theorem maximalIdealQuotientResidueFieldEquiv_comp_quotientMap
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdealQuotientResidueFieldEquiv B).toRingHom.comp
        ((Ideal.Quotient.mk (maximalIdeal B)).comp f) =
      (ResidueField.map f).comp
        ((maximalIdealQuotientResidueFieldEquiv A).toRingHom.comp
          (Ideal.Quotient.mk (maximalIdeal A))) := by
  -- It is enough to compare both sides on representatives from the source ring.
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
  change
    maximalIdealQuotientResidueFieldEquiv B ((Ideal.Quotient.mk (maximalIdeal B)) (f a)) =
      (ResidueField.map f)
        (maximalIdealQuotientResidueFieldEquiv A ((Ideal.Quotient.mk (maximalIdeal A)) a))
  rw [maximalIdealQuotientResidueFieldEquiv_apply_mk,
    maximalIdealQuotientResidueFieldEquiv_apply_mk]
  exact IsLocalRing.ResidueField.map_residue f a

section IndEtaleFlat

open CategoryTheory.Under
open CommRingCat

/-- Helper for Lemma 15.45.1: an `ind` presentation of a ring map lifts canonically to the
under-category over the fixed source ring. -/
private abbrev ind_underFunctor {A : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D) :
    J ⥤ Under A :=
  { obj := fun j ↦ Under.mk (t.app j)
    map := fun {i j} g ↦ Under.homMk (D.map g) (by
      -- The `Under`-morphism condition is the naturality square for the chosen stage map.
      simpa using (t.naturality g).symm) }

/-- Helper for Lemma 15.45.1: the target cocone of an `ind` presentation lifts to the matching
under-category cocone. -/
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
          -- Equality in `Under` reduces to equality of the right components.
          refine CategoryTheory.CommaMorphism.ext rfl ?_
          simpa using s.naturality g } }

/-- Helper for Lemma 15.45.1: a colimit cocone in rings remains colimiting after lifting the same
`ind` presentation to the under-category. -/
private noncomputable def ind_underCocone_isColimit_of_isColimit
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
    -- One stage equation reduces the under-category condition to the ordinary colimit desc map.
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
    -- Forgetting to rings exposes the usual colimit fac equation on the chosen stage.
    refine CategoryTheory.CommaMorphism.ext rfl ?_
    simpa using hs.fac ((Under.forget A).mapCocone c) j
  · intro c m hm
    -- Uniqueness is checked after forgetting to rings, where `hs` already controls the desc map.
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

/-- Helper for Lemma 15.45.1: forgetting a commutative ring under `A` to its underlying
`A`-module. -/
private abbrev under_forget_to_module (A : CommRingCat.{u}) : Under A ⥤ ModuleCat A where
  obj B := ModuleCat.of A B
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap

/-- Helper for Lemma 15.45.1: an object under `CommRingCat.of A` carries the canonical
`A`-module structure induced by its structure map. -/
private instance under_module (A : Type u) [CommRing A] (B : Under (CommRingCat.of A)) :
    Module A B := by
  let _ : Algebra A B.right := B.hom.hom.toAlgebra
  infer_instance

/-- Helper for Lemma 15.45.1: a filtered colimit in `Under (CommRingCat.of A)` is flat once every
stage is flat over the fixed base ring `A`. -/
private theorem under_colimit_flat_of_stagewise_flat {A : Type u} [CommRing A]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of A)) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat A (F.obj j)] :
    Module.Flat A c.pt.right := by
  let cM := (under_forget_to_module (CommRingCat.of A)).mapCocone c
  letI : ∀ j, Module.Flat A ((F ⋙ under_forget_to_module (CommRingCat.of A)).obj j) :=
    fun j ↦ by
      simpa [under_forget_to_module] using (inferInstance : Module.Flat A (F.obj j))
  have hcM : IsColimit cM := by
    -- Forget to additive groups, preserve the filtered colimit there, then reflect it back.
    apply isColimitOfReflects (forget₂ (ModuleCat A) AddCommGrpCat)
    simpa [under_forget_to_module] using
      (isColimitOfPreserves
        (CategoryTheory.Under.forget (CommRingCat.of A) ⋙
          forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) hc)
  -- Apply the Chapter 10 filtered-colimit flatness theorem to the transported module diagram.
  simpa using
    flat_of_isColimit_filtered_system
      (F := F ⋙ under_forget_to_module (CommRingCat.of A)) cM hcM

/-- Helper for Lemma 15.45.1: a filtered colimit of étale algebras is flat over the base ring. -/
private theorem flat_of_isFilteredColimitOfEtale
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (h : (algebraMap A B).IsFilteredColimitOfEtale) :
    Module.Flat A B := by
  let _ : Algebra A (ULift B) := ULift.algebra
  let _ : Algebra (ULift.{u} A) (ULift B) := ULift.algebra' A (ULift B)
  -- Unpack the same-universe ind-étale witness hidden in the source-facing owner.
  dsimp [RingHom.IsFilteredColimitOfEtale] at h
  rcases h with ⟨J, _, _, D, t, s, hs, hstage⟩
  let F := ind_underFunctor (A := CommRingCat.of (ULift.{u} A)) D t
  let cUnder :=
    ind_underCocone D t s
      (CommRingCat.ofHom (algebraMap (ULift.{u} A) (ULift B)))
      (fun j ↦ (hstage j).2)
  have hsUnder : IsColimit cUnder := by
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
  have hflatULiftUnder : Module.Flat (ULift.{u} A) cUnder.pt.right := by
    -- Stagewise étale flatness feeds into the under-category filtered-colimit flatness lemma.
    exact under_colimit_flat_of_stagewise_flat (A := ULift.{u} A) F cUnder hsUnder
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

end IndEtaleFlat

/-
Domain-style sampling:
- primary domain: local henselization and strict henselization maps of local rings, together with
  their maximal-ideal and Artinian-quotient behavior;
- sampled owner declarations of the same kind:
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `IsHenselizationOf.map_maximalIdeal`,
  `IsStrictHenselizationOf.map_maximalIdeal`,
  `RingHom.formallyEtale_quotientMap_pow_bijective`,
  `strictHenselization_over_henselization_isStrictHenselizationOf`;
- best owner abstraction: the primitive source data is carried by `IsHenselizationOf` and
  `IsStrictHenselizationOf`; weakly étale and formally étale consequences, faithful flatness,
  maximal-ideal extension, and quotient comparison are derived API from those owners;
- primitive data: locality of the structural map, filtered-colimit-of-etale presentation,
  maximal-ideal image, and for henselizations the residue-field bijectivity;
- derived API: faithful flatness of the structural maps and the induced comparison on quotients by
  powers of the maximal ideal.

Layer triage:
- `source-facing`: parts (4), (6), and (7) of Lemma 15.45.1;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`,
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `RingHom.formallyEtale_quotientMap_pow_bijective`;
- `bridge/view`: parts (1), (2), (3), and (5) as direct owner specializations, together with
  `strictHenselization_over_henselization_isStrictHenselizationOf`.
-/

section Henselization

variable [IsHenselizationOf R Rh]

/-- Helper for Lemma 15.45.1: the closed-fiber map `R → Rh / maximalIdeal Rh` of a henselization
is surjective because the induced residue-field map is bijective. -/
private theorem henselization_closedFiber_surjective :
    Function.Surjective
      (((Ideal.Quotient.mk mRh).comp (algebraMap R Rh)) : R →+* Rh ⧸ mRh) := by
  intro z
  let zκ : ResidueField Rh := maximalIdealQuotientResidueFieldEquiv Rh z
  -- Pull the target residue class back through the residue-field bijection of a henselization.
  obtain ⟨wκ, hwκ⟩ :=
    (IsHenselizationOf.residueField_bijective :
      Function.Bijective (ResidueField.map (algebraMap R Rh))).surjective zκ
  obtain ⟨r, hr⟩ :=
    Ideal.Quotient.mk_surjective ((maximalIdealQuotientResidueFieldEquiv R).symm wκ)
  refine ⟨r, ?_⟩
  apply (maximalIdealQuotientResidueFieldEquiv Rh).injective
  -- The quotient-to-residue comparison commutes with the local ring map `R → Rh`.
  calc
    maximalIdealQuotientResidueFieldEquiv Rh
        ((((Ideal.Quotient.mk mRh).comp (algebraMap R Rh)) : R →+* Rh ⧸ mRh) r) =
      ResidueField.map (algebraMap R Rh)
        (maximalIdealQuotientResidueFieldEquiv R (Ideal.Quotient.mk mR r)) := by
          simpa [RingHom.comp_apply] using
            DFunLike.congr_fun
              (maximalIdealQuotientResidueFieldEquiv_comp_quotientMap
                (A := R) (B := Rh) (f := algebraMap R Rh)) r
    _ = ResidueField.map (algebraMap R Rh)
          (maximalIdealQuotientResidueFieldEquiv R
            ((maximalIdealQuotientResidueFieldEquiv R).symm wκ)) := by
          rw [hr]
    _ = ResidueField.map (algebraMap R Rh) wκ := by
          rw [(maximalIdealQuotientResidueFieldEquiv R).apply_symm_apply]
    _ = zκ := hwκ
    _ = maximalIdealQuotientResidueFieldEquiv Rh z := rfl

/-- Lemma 15.45.1 (1): the canonical map from a local ring to its henselization is faithfully
flat. -/
theorem henselizationMap_faithfullyFlat :
    (algebraMap R Rh).FaithfullyFlat := by
  -- Replace the broken weakly-étale wrapper import by the direct flatness owner theorem.
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  letI : Module.Flat R Rh :=
    flat_of_isFilteredColimitOfEtale IsHenselizationOf.isFilteredColimitOfEtale
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

section StrictHenselization

variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh]
variable [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.1 (2): the canonical map from a local ring to its strict henselization is
faithfully flat. -/
theorem strictHenselizationMap_faithfullyFlat :
    (algebraMap R Rsh).FaithfullyFlat := by
  -- The strict-henselization map has the same source-faithful flat/local route.
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  letI : Module.Flat R Rsh :=
    flat_of_isFilteredColimitOfEtale IsStrictHenselizationOf.isFilteredColimitOfEtale
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end StrictHenselization

section StrictOverHenselization
variable [Algebra Rh Rsh] [IsScalarTower R Rh Rsh]

-- Proof sketch: this is one of the defining properties of `IsHenselizationOf`.
/- Lemma 15.45.1 (3): the maximal ideal of a henselization is the extension of the maximal ideal
of the base local ring. -/
recall IsHenselizationOf.map_maximalIdeal

-- Proof sketch:
-- `strictHenselization_over_henselization_isStrictHenselizationOf` upgrades `R → Rsh` to a strict
-- henselization, so both sides identify with `maximalIdeal Rsh` via the owner theorem
-- `IsStrictHenselizationOf.map_maximalIdeal`.
/-- Lemma 15.45.1 (4): if `Rh` is a henselization of `R` and `Rsh` is a strict henselization of
`Rh`, then the image of the maximal ideal of `R` in `Rsh` is the image of the maximal ideal of
`Rh`. -/
theorem strictHenselizationOverHenselization_map_baseMaximalIdeal :
    Ideal.map (algebraMap R Rsh) mR = Ideal.map (algebraMap Rh Rsh) mRh := by
  calc
    Ideal.map (algebraMap R Rsh) mR =
        Ideal.map (algebraMap Rh Rsh) (Ideal.map (algebraMap R Rh) mR) := by
      simpa [Ideal.map_map, IsScalarTower.algebraMap_eq R Rh Rsh]
    _ = Ideal.map (algebraMap Rh Rsh) mRh := by
      rw [IsHenselizationOf.map_maximalIdeal]

variable [IsStrictHenselizationOf Rh Rsh]

-- Proof sketch: this is one of the defining properties of `IsStrictHenselizationOf` applied to
-- the henselian local ring `Rh`.
/- Lemma 15.45.1 (5): the maximal ideal of a strict henselization over `Rh` is the extension of
the maximal ideal of `Rh`. -/
recall IsStrictHenselizationOf.map_maximalIdeal

end StrictOverHenselization

-- Proof sketch: `RingHom.formallyEtale_of_isFilteredColimitOfEtale` makes the henselization map
-- `R → Rh` formally étale, and the induced map on closed fibers `R → Rh / maximalIdeal Rh` is
-- surjective because the residue-field map of a henselization is bijective. Apply the owner
-- theorem `RingHom.formallyEtale_quotientMap_pow_bijective` with `J = maximalIdeal Rh`.
/-- Lemma 15.45.1 (6): for every `n`, the canonical map
`R / maximalIdeal R ^ n → Rh / maximalIdeal Rh ^ n` is bijective. -/
theorem henselizationQuotientPowMap_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap (mRh ^ n) (algebraMap R Rh)
        (pow_maximalIdeal_le_comap_pow_maximalIdeal (algebraMap R Rh) n)) := by
  let f : R →+* Rh := algebraMap R Rh
  let qPow :
      R ⧸ (Ideal.comap f mRh ^ n) →+* Rh ⧸ mRh ^ n :=
    Ideal.quotientMap (mRh ^ n) f ((maximalIdeal Rh).le_comap_pow f n)
  have hqPow :
      Function.Bijective qPow :=
    RingHom.formallyEtale_quotientMap_pow_bijective f mRh n
  let hcomapPow :
      Ideal.comap f mRh ^ n = mR ^ n := by
    -- The local henselization map pulls back the maximal ideal of `Rh` to the maximal ideal of
    -- `R`, hence the same is true after taking powers.
    simpa [f, IsLocalRing.maximalIdeal_comap (algebraMap R Rh)]
  let eSource : R ⧸ (Ideal.comap f mRh ^ n) ≃+* R ⧸ mR ^ n :=
    Ideal.quotEquivOfEq hcomapPow
  have hEq :
      Ideal.quotientMap (mRh ^ n) (algebraMap R Rh)
          (pow_maximalIdeal_le_comap_pow_maximalIdeal (algebraMap R Rh) n) =
        qPow.comp eSource.symm.toRingHom := by
    -- Compare both quotient maps on representatives from `R`.
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp [qPow, eSource, f, RingHom.comp_apply, Ideal.quotientMap_mk]
  rw [hEq]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply eSource.symm.injective
    exact hqPow.injective hxy
  · intro z
    obtain ⟨w, hw⟩ := hqPow.surjective z
    refine ⟨eSource w, ?_⟩
    simpa [RingHom.comp_apply] using hw

end Henselization

section StrictHenselizationQuotients

-- For part `(7)`, use the canonical quotient owner
-- `Ideal.Quotient.algebraQuotientOfLEComap` as local instance data rather than a named local
-- wrapper.
local instance [IsStrictHenselizationOf R Rsh] (n : ℕ) :
    Algebra (R ⧸ mR ^ n) (Rsh ⧸ mRsh ^ n) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (pow_maximalIdeal_le_comap_pow_maximalIdeal (algebraMap R Rsh) n)

/-- Helper for Lemma 15.45.1: every positive power of the maximal ideal remains proper. -/
private theorem quotient_pow_maximalIdeal_ne_top (n : ℕ) :
    mR ^ (n + 1) ≠ (⊤ : Ideal R) := by
  intro hpow
  have htop : (⊤ : Ideal R) ≤ mR := by
    calc
      (⊤ : Ideal R) = mR ^ (n + 1) := hpow.symm
      _ ≤ mR := Ideal.pow_le_self (I := mR) (Nat.succ_ne_zero n)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp htop)

local instance quotient_pow_maximalIdeal_nontrivial (n : ℕ) :
    Nontrivial (R ⧸ mR ^ (n + 1)) :=
  Ideal.Quotient.nontrivial_iff.2 (quotient_pow_maximalIdeal_ne_top (R := R) n)

local instance quotient_pow_maximalIdeal_isLocalRing (n : ℕ) :
    IsLocalRing (R ⧸ mR ^ (n + 1)) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (mR ^ (n + 1))) Ideal.Quotient.mk_surjective

/-- Helper for Lemma 15.45.1: flatness survives quotienting a ring map by the induced ideal. -/
private theorem quotientMap_flat_of_flat
    {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (I : Ideal A) (hφ : φ.Flat) :
    (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map).Flat := by
  let _ : Algebra A B := φ.toAlgebra
  let e : B ⧸ Ideal.map φ I ≃+* ((A ⧸ I) ⊗[A] B) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toRingEquiv).trans
      (Algebra.TensorProduct.comm A B (A ⧸ I)).toRingEquiv
  -- First base change the flat map `A → B` to the quotient ring `A ⧸ I`.
  have hφ_alg : (algebraMap A B).Flat := by
    simpa [RingHom.algebraMap_toAlgebra] using hφ
  have hbaseModule : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] B) := by
    let _ : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hφ_alg
    simpa using (Module.Flat.baseChange (R := A) (S := A ⧸ I) (M := B))
  have hbase :
      (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr hbaseModule
  -- Then transport that flatness across the standard tensor/quotient equivalence.
  have he : e.symm.toRingHom.Flat := RingHom.Flat.of_bijective e.symm.bijective
  have hcomp :
      (e.symm.toRingHom.comp (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B))).Flat :=
    RingHom.Flat.comp hbase he
  have hEq :
      e.symm.toRingHom.comp (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)) =
        Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map := by
    apply Ideal.Quotient.ringHom_ext
    rw [Ideal.quotientMap_comp_mk]
    ext x
    change
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm
          ((Algebra.TensorProduct.comm A B (A ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[A] (1 : B))) =
        (Ideal.Quotient.mk (Ideal.map φ I)) (φ x)
    have hcomm :
        (Algebra.TensorProduct.comm A B (A ⧸ I)).symm
            ((Ideal.Quotient.mk I) x ⊗ₜ[A] (1 : B)) =
          (1 : B) ⊗ₜ[A] (Ideal.Quotient.mk I x) := by
      simpa using
        (Algebra.TensorProduct.comm_symm_tmul (R := A) (a := (1 : B))
          (b := Ideal.Quotient.mk I x))
    rw [hcomm, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    have hs : x • (1 : B) = φ x := by
      change (algebraMap A B x) * 1 = φ x
      simpa [RingHom.algebraMap_toAlgebra]
    simpa [RingHom.algebraMap_toAlgebra, hs]
  rw [← hEq]
  exact hcomp

/-- Helper for Lemma 15.45.1: the `(n + 1)`st strict-henselization quotient stays flat over the
matching quotient of the base local ring. -/
private theorem strictHenselization_quotient_flat
    [IsStrictHenselizationOf R Rsh] (n : ℕ) :
    Module.Flat (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)) := by
  let qComp :
      (R ⧸ mR ^ (n + 1)) →+*
        (Rsh ⧸ Ideal.map (algebraMap R Rsh) (mR ^ (n + 1))) :=
    Ideal.quotientMap (Ideal.map (algebraMap R Rsh) (mR ^ (n + 1)))
      (algebraMap R Rsh) Ideal.le_comap_map
  let hmap :
      Ideal.map (algebraMap R Rsh) (mR ^ (n + 1)) = mRsh ^ (n + 1) := by
    -- The strict-henselization map carries the maximal ideal to the maximal ideal, so the same
    -- holds for every positive power.
    simpa [IsStrictHenselizationOf.map_maximalIdeal] using
      (Ideal.map_pow (algebraMap R Rsh) mR (n + 1))
  let eTarget :
      (Rsh ⧸ Ideal.map (algebraMap R Rsh) (mR ^ (n + 1))) ≃+*
        (Rsh ⧸ mRsh ^ (n + 1)) :=
    Ideal.quotEquivOfEq hmap
  -- First quotient the flat map `R → Rˢʰ` by the mapped power of the maximal ideal.
  have hqComp_flat : qComp.Flat :=
    quotientMap_flat_of_flat (algebraMap R Rsh) (mR ^ (n + 1))
      strictHenselizationMap_faithfullyFlat.flat
  -- Then transport flatness across the quotient equivalence coming from `map_maximalIdeal`.
  have heTarget_flat : eTarget.toRingHom.Flat :=
    RingHom.Flat.of_bijective eTarget.bijective
  have htransport :
      (eTarget.toRingHom.comp qComp).Flat :=
    RingHom.Flat.comp hqComp_flat heTarget_flat
  have hEq :
      eTarget.toRingHom.comp qComp =
        algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)) := by
    -- Compare both quotient maps on representatives coming from `R`.
    apply Ideal.Quotient.ringHom_ext
    ext x
    change
      eTarget
          ((Ideal.Quotient.mk (Ideal.map (algebraMap R Rsh) (mR ^ (n + 1))))
            ((algebraMap R Rsh) x)) =
        (Ideal.Quotient.mk (mRsh ^ (n + 1))) ((algebraMap R Rsh) x)
    rw [Ideal.quotEquivOfEq_mk]
  have halgebraMap :
      (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1))).Flat := by
    rw [← hEq]
    exact htransport
  exact RingHom.flat_algebraMap_iff.mp halgebraMap

/-- Helper for Lemma 15.45.1: on the `(n + 1)`st quotient, the maximal ideal of the source
quotient maps to the image of `maximalIdeal Rˢʰ`. -/
private theorem strictHenselization_quotient_maximalIdeal_image
    [IsStrictHenselizationOf R Rsh] (n : ℕ) :
    let A := R ⧸ mR ^ (n + 1)
    let S := Rsh ⧸ mRsh ^ (n + 1)
    Ideal.map (algebraMap A S) (maximalIdeal A) =
      Ideal.map (Ideal.Quotient.mk (mRsh ^ (n + 1))) mRsh := by
  dsimp
  have hmax :
      maximalIdeal (R ⧸ mR ^ (n + 1)) =
        Ideal.map (Ideal.Quotient.mk (mR ^ (n + 1))) mR := by
    -- The maximal ideal of a quotient local ring is the image of the upstairs maximal ideal.
    symm
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (mR ^ (n + 1))) Ideal.Quotient.mk_surjective
  -- Rewrite the source maximal ideal as an image from `R`, then push it across the quotient map.
  calc
    Ideal.map (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
        (maximalIdeal (R ⧸ mR ^ (n + 1))) =
      Ideal.map (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
        (Ideal.map (Ideal.Quotient.mk (mR ^ (n + 1))) mR) := by
          rw [hmax]
    _ = Ideal.map
          ((algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1))).comp
            (Ideal.Quotient.mk (mR ^ (n + 1)))) mR := by
          rw [Ideal.map_map]
    _ = Ideal.map (((Ideal.Quotient.mk (mRsh ^ (n + 1))).comp (algebraMap R Rsh))) mR := by
          congr 1
    _ = Ideal.map (Ideal.Quotient.mk (mRsh ^ (n + 1)))
          (Ideal.map (algebraMap R Rsh) mR) := by
          rw [Ideal.map_map]
    _ = Ideal.map (Ideal.Quotient.mk (mRsh ^ (n + 1))) mRsh := by
          rw [IsStrictHenselizationOf.map_maximalIdeal]

/-- Helper for Lemma 15.45.1: reducing the `(n + 1)`st quotient of `Rˢʰ` modulo the mapped
maximal ideal recovers the closed fiber `Rˢʰ / maximalIdeal Rˢʰ`. -/
private noncomputable def strictHenselization_quotient_closedFiber_ringEquiv
    [IsStrictHenselizationOf R Rsh] (n : ℕ) :
    let A := R ⧸ mR ^ (n + 1)
    let S := Rsh ⧸ mRsh ^ (n + 1)
    (S ⧸ Ideal.map (algebraMap A S) (maximalIdeal A)) ≃+* (Rsh ⧸ mRsh) := by
  -- Route correction: separate the ideal-image computation from the quotient-of-a-quotient
  -- equivalence so the reduction map is a stable named object.
  dsimp
  let hmap :
      Ideal.map (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
          (maximalIdeal (R ⧸ mR ^ (n + 1))) =
        Ideal.map (Ideal.Quotient.mk (mRsh ^ (n + 1))) mRsh :=
    strictHenselization_quotient_maximalIdeal_image (R := R) (Rsh := Rsh) n
  exact
    (Ideal.quotEquivOfEq hmap).trans
      (DoubleQuot.quotQuotEquivQuotOfLE
        (R := Rsh)
        (I := mRsh ^ (n + 1))
        (J := mRsh)
        (Ideal.pow_le_self (I := mRsh) (Nat.succ_ne_zero n)))

/-- Helper for Lemma 15.45.1: quotienting the Artinian source quotient by its maximal ideal
recovers the residue quotient `R / maximalIdeal R`. -/
private noncomputable def quotient_pow_maximalIdeal_quotient_ringEquiv (n : ℕ) :
    let A := R ⧸ mR ^ (n + 1)
    (A ⧸ maximalIdeal A) ≃+* (R ⧸ mR) := by
  -- Match the source maximal ideal with the image of `mR`, then use the quotient-of-a-quotient
  -- equivalence exactly as on the strict-henselization side.
  dsimp
  let hmax :
      maximalIdeal (R ⧸ mR ^ (n + 1)) =
        Ideal.map (Ideal.Quotient.mk (mR ^ (n + 1))) mR := by
    symm
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (mR ^ (n + 1))) Ideal.Quotient.mk_surjective
  exact
    (Ideal.quotEquivOfEq hmax).trans
      (DoubleQuot.quotQuotEquivQuotOfLE
        (R := R)
        (I := mR ^ (n + 1))
        (J := mR)
        (Ideal.pow_le_self (I := mR) (Nat.succ_ne_zero n)))

/-- Helper for Lemma 15.45.1: the scalar-side quotient-of-quotient equivalence sends a nested
quotient class to the original class modulo `maximalIdeal R`. -/
private theorem quotient_pow_maximalIdeal_quotient_ringEquiv_apply_mk
    (n : ℕ) (a : R) :
    quotient_pow_maximalIdeal_quotient_ringEquiv (R := R) n
        (Ideal.Quotient.mk (maximalIdeal (R ⧸ mR ^ (n + 1)))
          (Ideal.Quotient.mk (mR ^ (n + 1)) a)) =
      Ideal.Quotient.mk mR a := by
  -- Compute first across the ideal-transport, then across the quotient-of-a-quotient equivalence.
  dsimp [quotient_pow_maximalIdeal_quotient_ringEquiv]
  rfl

/-- Helper for Lemma 15.45.1: the target closed-fiber equivalence sends a nested quotient class to
its original class modulo `maximalIdeal Rˢʰ`. -/
private theorem strictHenselization_quotient_closedFiber_ringEquiv_apply_mk
    [IsStrictHenselizationOf R Rsh] (n : ℕ) (a : Rsh) :
    strictHenselization_quotient_closedFiber_ringEquiv (R := R) (Rsh := Rsh) n
        (Ideal.Quotient.mk
          (Ideal.map
            (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
            (maximalIdeal (R ⧸ mR ^ (n + 1))))
          (Ideal.Quotient.mk (mRsh ^ (n + 1)) a)) =
      Ideal.Quotient.mk mRsh a := by
  -- The strict-henselization closed-fiber comparison uses the same two-step normalization.
  dsimp [strictHenselization_quotient_closedFiber_ringEquiv]
  rfl

/-- Helper for Lemma 15.45.1: after passing to the `(n + 1)`st Artinian quotient, quotienting by
the mapped maximal ideal is the same as quotienting the ambient module by
`maximalIdeal A • ⊤`. -/
private noncomputable abbrev strictHenselization_idealQuotient_equiv_module_quotient
    [IsStrictHenselizationOf R Rsh]
    (n : ℕ) :
    let A := R ⧸ mR ^ (n + 1)
    let S := Rsh ⧸ mRsh ^ (n + 1)
    (S ⧸ Ideal.map (algebraMap A S) (maximalIdeal A)) ≃ₗ[A]
      (S ⧸ ((maximalIdeal A • (⊤ : Submodule A S)) : Submodule A S)) := by
  dsimp
  -- Route correction: isolate the quotient-model change `Ideal.map = maximalIdeal A • ⊤`
  -- before the later scalar descent to the residue field.
  exact
    (Submodule.Quotient.restrictScalarsEquiv
      (R ⧸ mR ^ (n + 1))
      (Ideal.map
        (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
        (maximalIdeal (R ⧸ mR ^ (n + 1))))).symm.trans
      (Submodule.quotEquivOfEq
        (Submodule.restrictScalars
          (R ⧸ mR ^ (n + 1))
          ((Ideal.map
            (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
            (maximalIdeal (R ⧸ mR ^ (n + 1)))) : Submodule
              (Rsh ⧸ mRsh ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1))))
        (((maximalIdeal (R ⧸ mR ^ (n + 1))) •
            (⊤ : Submodule (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))) : Submodule
              (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
        (Ideal.smul_top_eq_map (maximalIdeal (R ⧸ mR ^ (n + 1)))).symm)

/-- Helper for Lemma 15.45.1: the ideal-quotient/module-quotient bridge sends a nested quotient
class to the corresponding module quotient class represented by the same lift. -/
private theorem strictHenselization_idealQuotient_equiv_module_quotient_mk
    [IsStrictHenselizationOf R Rsh]
    (n : ℕ) (a : Rsh) :
    let A := R ⧸ mR ^ (n + 1)
    let S := Rsh ⧸ mRsh ^ (n + 1)
    strictHenselization_idealQuotient_equiv_module_quotient (R := R) (Rsh := Rsh) n
        ((Ideal.Quotient.mk
          (Ideal.map (algebraMap A S) (maximalIdeal A)))
          (Ideal.Quotient.mk (mRsh ^ (n + 1)) a)) =
      (((maximalIdeal A • (⊤ : Submodule A S)) : Submodule A S).mkQ
        (Ideal.Quotient.mk (mRsh ^ (n + 1)) a)) := by
  dsimp [strictHenselization_idealQuotient_equiv_module_quotient]
  have hrestrict :
      (Submodule.Quotient.restrictScalarsEquiv
          (R ⧸ mR ^ (n + 1))
          ((Ideal.map
            (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
            (maximalIdeal (R ⧸ mR ^ (n + 1)))) : Ideal (Rsh ⧸ mRsh ^ (n + 1)))).symm
          ((Ideal.Quotient.mk
            (Ideal.map
              (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
              (maximalIdeal (R ⧸ mR ^ (n + 1)))))
            (Ideal.Quotient.mk (mRsh ^ (n + 1)) a)) =
        Submodule.Quotient.mk (Ideal.Quotient.mk (mRsh ^ (n + 1)) a) := by
    -- First forget from the ring quotient to the matching module quotient over `A`.
    rfl
  -- Then compute across the quotient transport given by `Ideal.smul_top_eq_map`.
  calc
    strictHenselization_idealQuotient_equiv_module_quotient (R := R) (Rsh := Rsh) n
        ((Ideal.Quotient.mk
          (Ideal.map
            (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
            (maximalIdeal (R ⧸ mR ^ (n + 1)))))
          (Ideal.Quotient.mk (mRsh ^ (n + 1)) a))
      = (Submodule.quotEquivOfEq
          (Submodule.restrictScalars
            (R ⧸ mR ^ (n + 1))
            ((Ideal.map
              (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
              (maximalIdeal (R ⧸ mR ^ (n + 1)))) : Submodule
                (Rsh ⧸ mRsh ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1))))
          (((maximalIdeal (R ⧸ mR ^ (n + 1))) •
              (⊤ : Submodule (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))) : Submodule
                (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
          (Ideal.smul_top_eq_map (maximalIdeal (R ⧸ mR ^ (n + 1)))).symm)
          ((Submodule.Quotient.restrictScalarsEquiv
              (R ⧸ mR ^ (n + 1))
              ((Ideal.map
                (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
                (maximalIdeal (R ⧸ mR ^ (n + 1)))) : Ideal (Rsh ⧸ mRsh ^ (n + 1)))).symm
            ((Ideal.Quotient.mk
              (Ideal.map
                (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
                (maximalIdeal (R ⧸ mR ^ (n + 1)))))
              (Ideal.Quotient.mk (mRsh ^ (n + 1)) a))) := by
            rfl
    _ = (Submodule.quotEquivOfEq
          (Submodule.restrictScalars
            (R ⧸ mR ^ (n + 1))
            ((Ideal.map
              (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
              (maximalIdeal (R ⧸ mR ^ (n + 1)))) : Submodule
                (Rsh ⧸ mRsh ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1))))
          (((maximalIdeal (R ⧸ mR ^ (n + 1))) •
              (⊤ : Submodule (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))) : Submodule
                (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
          (Ideal.smul_top_eq_map (maximalIdeal (R ⧸ mR ^ (n + 1)))).symm)
          (Submodule.Quotient.mk (Ideal.Quotient.mk (mRsh ^ (n + 1)) a)) := by
            rw [hrestrict]
    _ = (((maximalIdeal (R ⧸ mR ^ (n + 1))) •
            (⊤ : Submodule (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))) : Submodule
              (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1))).mkQ
          (Ideal.Quotient.mk (mRsh ^ (n + 1)) a) := by
            simpa using
              (Submodule.quotEquivOfEq_mk
                (Submodule.restrictScalars
                  (R ⧸ mR ^ (n + 1))
                  ((Ideal.map
                    (algebraMap (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
                    (maximalIdeal (R ⧸ mR ^ (n + 1)))) : Submodule
                      (Rsh ⧸ mRsh ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1))))
                (((maximalIdeal (R ⧸ mR ^ (n + 1))) •
                    (⊤ : Submodule (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))) : Submodule
                      (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)))
                (Ideal.smul_top_eq_map (maximalIdeal (R ⧸ mR ^ (n + 1)))).symm
                (Ideal.Quotient.mk (mRsh ^ (n + 1)) a))

/-- Helper for Lemma 15.45.1: the maximal ideal of `R / maximalIdeal R ^ (n + 1)` is nilpotent. -/
private theorem quotient_pow_maximalIdeal_nilpotent (n : ℕ) :
    IsNilpotent (maximalIdeal (R ⧸ mR ^ (n + 1))) := by
  -- The quotient maximal ideal is the image of `mR`, so its `(n + 1)`st power vanishes because
  -- the quotient map kills `mR ^ (n + 1)`.
  let π : R →+* R ⧸ mR ^ (n + 1) := Ideal.Quotient.mk (mR ^ (n + 1))
  have hmax :
      maximalIdeal (R ⧸ mR ^ (n + 1)) = Ideal.map π mR := by
    symm
    exact IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective
  refine ⟨n + 1, ?_⟩
  calc
    maximalIdeal (R ⧸ mR ^ (n + 1)) ^ (n + 1) = Ideal.map π mR ^ (n + 1) := by
      rw [hmax]
    _ = Ideal.map π (mR ^ (n + 1)) := by
      rw [Ideal.map_pow]
    _ = ⊥ := by
      apply (Ideal.map_eq_bot_iff_le_ker π).2
      simpa [π, Ideal.mk_ker]

/-- Helper for Lemma 15.45.1: the closed-fiber module quotient carries the canonical residue-field
scalar action inherited from the quotient by the maximal ideal. -/
noncomputable local instance
    (A : Type u) [CommRing A] [IsLocalRing A]
    (M : Type u) [AddCommGroup M] [Module A M] :
    Module (ResidueField A) (M ⧸ (maximalIdeal A • (⊤ : Submodule A M))) :=
  inferInstanceAs
    (Module (A ⧸ maximalIdeal A) (M ⧸ (maximalIdeal A • (⊤ : Submodule A M))))

/-- Helper for Lemma 15.45.1: quotienting an `A`-algebra by the image of `maximalIdeal A`
inherits the residue-field scalar action from `A ⧸ maximalIdeal A`. -/
private noncomputable local instance residueFieldModuleIdealMapQuotient
    (A : Type u) [CommRing A] [IsLocalRing A]
    (S : Type u) [CommRing S] [Algebra A S] :
    Module (ResidueField A) (S ⧸ Ideal.map (algebraMap A S) (maximalIdeal A)) :=
  inferInstanceAs
    (Module (A ⧸ maximalIdeal A) (S ⧸ Ideal.map (algebraMap A S) (maximalIdeal A)))

/-- Helper for Lemma 15.45.1: the fixed closed fiber `Rˢʰ / maximalIdeal Rˢʰ` carries the
residue-field action coming from each Artinian quotient `R / maximalIdeal R ^ (n + 1)`. -/
private noncomputable local instance strictHenselizationClosedFiberResidueFieldModule
    [IsStrictHenselizationOf R Rsh] (n : ℕ) :
    Module (ResidueField (R ⧸ mR ^ (n + 1))) (Rsh ⧸ mRsh) :=
  let eκ : (R ⧸ mR) ≃+* ResidueField (R ⧸ mR ^ (n + 1)) :=
    (quotient_pow_maximalIdeal_quotient_ringEquiv (R := R) n).symm.trans
      (maximalIdealQuotientResidueFieldEquiv (R ⧸ mR ^ (n + 1)))
  Module.compHom (Rsh ⧸ mRsh) eκ.symm.toRingHom

/-- Helper for Lemma 15.45.1: the closed fiber of the successor Artinian quotient, presented as a
module quotient over the source Artinian quotient. -/
private abbrev strictHenselizationSuccessorClosedFiberModule
    [IsStrictHenselizationOf R Rsh] (n : ℕ) :=
  let A := R ⧸ mR ^ (n + 1)
  let S := Rsh ⧸ mRsh ^ (n + 1)
  S ⧸ ((maximalIdeal A • (⊤ : Submodule A S)) : Submodule A S)

/-- Helper for Lemma 15.45.1: a basis of `Rˢʰ / maximalIdeal Rˢʰ` admits a chosen family of lifts
in `Rˢʰ`. -/
private theorem strictHenselization_exists_basis_lifts
    [IsStrictHenselizationOf R Rsh] {ι : Type u}
    (b0 : Module.Basis ι (R ⧸ mR) (Rsh ⧸ mRsh)) :
    ∃ x : ι → Rsh, ∀ i, Ideal.Quotient.mk mRsh (x i) = b0 i := by
  classical
  let x : ι → Rsh := fun i ↦ Classical.choose (Ideal.Quotient.mk_surjective (b0 i))
  refine ⟨x, ?_⟩
  intro i
  exact Classical.choose_spec (Ideal.Quotient.mk_surjective (b0 i))

/-- Helper for Lemma 15.45.1: the zeroth quotients are subsingleton, so any fixed family gives a
trivial basis. -/
private theorem zero_power_quotient_basis_of_subsingleton
    [IsStrictHenselizationOf R Rsh]
    {ι : Type u} (x : ι → Rsh) :
    ∃ b : Module.Basis ι (R ⧸ mR ^ 0) (Rsh ⧸ mRsh ^ 0),
      ∀ i, b i = Ideal.Quotient.mk (mRsh ^ 0) (x i) := by
  haveI : Subsingleton (R ⧸ mR ^ 0) := by
    simpa using (inferInstance : Subsingleton (R ⧸ (⊤ : Ideal R)))
  haveI : Subsingleton (Rsh ⧸ mRsh ^ 0) := by
    simpa using (inferInstance : Subsingleton (Rsh ⧸ (⊤ : Ideal Rsh)))
  let b : Module.Basis ι (R ⧸ mR ^ 0) (Rsh ⧸ mRsh ^ 0) :=
    Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _)
  refine ⟨b, ?_⟩
  intro i
  exact Subsingleton.elim _ _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Helper for Lemma 15.45.1: once the closed fiber is normalized, Lemma `10.101.1` lifts the
fixed family to a basis on every successor Artinian quotient. -/
private theorem strictHenselization_successor_basis_of_fixed_lifts
    [IsStrictHenselizationOf R Rsh] {ι : Type u}
    (b0 : Module.Basis ι (R ⧸ mR) (Rsh ⧸ mRsh))
    (x : ι → Rsh)
    (hx : ∀ i, Ideal.Quotient.mk mRsh (x i) = b0 i)
    (n : ℕ) :
    ∃ b : Module.Basis ι (R ⧸ mR ^ (n + 1)) (Rsh ⧸ mRsh ^ (n + 1)),
      ∀ i, b i = Ideal.Quotient.mk (mRsh ^ (n + 1)) (x i) := by
  let A := R ⧸ mR ^ (n + 1)
  let S := Rsh ⧸ mRsh ^ (n + 1)
  let P : Submodule A S := ((maximalIdeal A • (⊤ : Submodule A S)) : Submodule A S)
  letI : Module.Flat A S := strictHenselization_quotient_flat (R := R) (Rsh := Rsh) n
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  let eκ : (R ⧸ mR) ≃+* ResidueField A :=
    (quotient_pow_maximalIdeal_quotient_ringEquiv (R := R) n).symm.trans
      (maximalIdealQuotientResidueFieldEquiv A)
  let bκ : Module.Basis ι (ResidueField A) (Rsh ⧸ mRsh) :=
    b0.mapCoeffs eκ fun c y ↦ by
      -- The coefficient transport changes only the scalar ring, not the underlying vectors.
      change (eκ.symm (eκ c)) • y = c • y
      simp
  let eRing := strictHenselization_quotient_closedFiber_ringEquiv (R := R) (Rsh := Rsh) n
  let q := strictHenselization_idealQuotient_equiv_module_quotient (R := R) (Rsh := Rsh) n
  let e : (Rsh ⧸ mRsh) ≃ₗ[ResidueField A] (S ⧸ P) := by
    let quotientModule : Module (A ⧸ maximalIdeal A) (S ⧸ P) :=
      inferInstanceAs (Module (A ⧸ maximalIdeal A) (S ⧸ P))
    letI : Module (A ⧸ maximalIdeal A) (S ⧸ P) := quotientModule
    let smulP : A ⧸ maximalIdeal A → S ⧸ P → S ⧸ P := fun c z ↦ c • z
    refine
      { toFun := fun z ↦ q (eRing.symm z)
        invFun := fun z ↦ eRing (q.symm z)
        left_inv := by
          intro z
          change eRing (q.symm (q (eRing.symm z))) = z
          rw [q.symm_apply_apply]
          exact eRing.apply_symm_apply z
        right_inv := by
          intro z
          change q (eRing.symm (eRing (q.symm z))) = z
          rw [eRing.symm_apply_apply]
          exact q.apply_symm_apply z
        map_add' := by
          intro y z
          rw [eRing.symm.map_add]
          exact q.map_add _ _
        map_smul' := by
          intro (c : ResidueField A) z
          obtain ⟨c₀, rfl⟩ := (maximalIdealQuotientResidueFieldEquiv A).surjective c
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c₀
          obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective r
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
          have h_target :
              q
                  (eRing.symm
                    ((maximalIdealQuotientResidueFieldEquiv A
                        (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))) •
                      (Ideal.Quotient.mk mRsh a))) =
                smulP
                  (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))
                  (q (eRing.symm (Ideal.Quotient.mk mRsh a))) := by
            have h_dom :
                (maximalIdealQuotientResidueFieldEquiv A
                    (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))) •
                    (Ideal.Quotient.mk mRsh a : Rsh ⧸ mRsh) =
                  Ideal.Quotient.mk mRsh ((algebraMap R Rsh r₀) * a) := by
              have h_scalar :
                  eκ.symm
                      (maximalIdealQuotientResidueFieldEquiv A
                        (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))) =
                    Ideal.Quotient.mk mR r₀ := by
                dsimp [eκ]
                rw [(maximalIdealResidueFieldEquiv A).symm_apply_apply]
                let eQ :
                    (A ⧸ maximalIdeal A) ≃+* (maximalIdeal A).ResidueField :=
                  RingEquiv.ofBijective
                    (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
                    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))
                have h_eQ :
                    eQ.symm
                        (algebraMap A (maximalIdeal A).ResidueField
                          (Ideal.Quotient.mk (mR ^ (n + 1)) r₀)) =
                      Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀) := by
                  change
                    eQ.symm (eQ (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))) =
                      Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀)
                  exact eQ.symm_apply_apply _
                rw [h_eQ]
                exact quotient_pow_maximalIdeal_quotient_ringEquiv_apply_mk (R := R) n r₀
              change
                (eκ.symm
                    (maximalIdealQuotientResidueFieldEquiv A
                      (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀)))) •
                  (Ideal.Quotient.mk mRsh a : Rsh ⧸ mRsh) =
                Ideal.Quotient.mk mRsh ((algebraMap R Rsh r₀) * a)
              rw [h_scalar]
              rw [Algebra.smul_def]
              rfl
            have h_symm_apply (x : Rsh) :
                eRing.symm (Ideal.Quotient.mk mRsh x) =
                  Ideal.Quotient.mk
                    (Ideal.map (algebraMap A S) (maximalIdeal A))
                    (Ideal.Quotient.mk (mRsh ^ (n + 1)) x) := by
              exact eRing.symm_apply_eq.2
                (strictHenselization_quotient_closedFiber_ringEquiv_apply_mk
                  (R := R) (Rsh := Rsh) n x)
            have h_q :
                q (eRing.symm (Ideal.Quotient.mk mRsh a)) =
                  P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) a) := by
              rw [h_symm_apply]
              simpa [P] using
                (strictHenselization_idealQuotient_equiv_module_quotient_mk
                  (R := R) (Rsh := Rsh) n a)
            have h_q_mul :
                q (eRing.symm (Ideal.Quotient.mk mRsh ((algebraMap R Rsh r₀) * a))) =
                  P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) ((algebraMap R Rsh r₀) * a)) := by
              rw [h_symm_apply]
              simpa [P] using
                (strictHenselization_idealQuotient_equiv_module_quotient_mk
                  (R := R) (Rsh := Rsh) n ((algebraMap R Rsh r₀) * a))
            have h_cod :
                smulP
                    (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))
                    (P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) a) : S ⧸ P) =
                  P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) ((algebraMap R Rsh r₀) * a)) := by
              have h_cod_quotient :
                  ((Ideal.Quotient.mk (maximalIdeal A)
                        (Ideal.Quotient.mk (mR ^ (n + 1)) r₀)) : A ⧸ maximalIdeal A) •
                      (P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) a) : S ⧸ P) =
                    P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) ((algebraMap R Rsh r₀) * a)) := by
                change
                  P.mkQ
                      (((Ideal.Quotient.mk (mR ^ (n + 1)) r₀) : A) •
                        (Ideal.Quotient.mk (mRsh ^ (n + 1)) a : S)) =
                    P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) ((algebraMap R Rsh r₀) * a))
                rw [Algebra.smul_def]
                rfl
              simpa [smulP] using h_cod_quotient
            calc
              q
                  (eRing.symm
                    ((maximalIdealQuotientResidueFieldEquiv A
                        (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))) •
                      (Ideal.Quotient.mk mRsh a))) =
                q (eRing.symm (Ideal.Quotient.mk mRsh ((algebraMap R Rsh r₀) * a))) := by
                  rw [h_dom]
              _ = P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) ((algebraMap R Rsh r₀) * a)) := h_q_mul
              _ =
                  smulP
                    (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))
                    (P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) a) : S ⧸ P) := by
                  symm
                  exact h_cod
              _ =
                  smulP
                    (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀))
                    (q (eRing.symm (Ideal.Quotient.mk mRsh a))) := by
                  rw [h_q]
          convert h_target using 1
          simpa using
            congrArg
              (fun t : A ⧸ maximalIdeal A ↦ t • q (eRing.symm (Ideal.Quotient.mk mRsh a)))
              ((maximalIdealQuotientResidueFieldEquiv A).symm_apply_apply
                (Ideal.Quotient.mk (maximalIdeal A) (Ideal.Quotient.mk (mR ^ (n + 1)) r₀)))
      }
  have h_e_apply (a : Rsh) :
      e (Ideal.Quotient.mk mRsh a) = P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) a) := by
    dsimp [e]
    have h_symm_apply :
        eRing.symm (Ideal.Quotient.mk mRsh a) =
          Ideal.Quotient.mk
            (Ideal.map (algebraMap A S) (maximalIdeal A))
            (Ideal.Quotient.mk (mRsh ^ (n + 1)) a) := by
      exact eRing.symm_apply_eq.2
        (strictHenselization_quotient_closedFiber_ringEquiv_apply_mk
          (R := R) (Rsh := Rsh) n a)
    rw [h_symm_apply]
    simpa [P] using
      (strictHenselization_idealQuotient_equiv_module_quotient_mk
        (R := R) (Rsh := Rsh) n a)
  let bbar : Module.Basis ι (ResidueField A) (S ⧸ P) := bκ.map e
  have hbbar : ∀ i, bbar i = P.mkQ (Ideal.Quotient.mk (mRsh ^ (n + 1)) (x i)) := by
    intro i
    -- The chosen lifts survive the coefficient transport and the closed-fiber comparison unchanged.
    dsimp [bbar]
    rw [Module.Basis.mapCoeffs_apply, ← hx i]
    simpa using h_e_apply (x i)
  have h_basisbar :
      ∃ bbar' : @Module.Basis ι (ResidueField A)
          (S ⧸ ((maximalIdeal A • (⊤ : Submodule A S)) : Submodule A S))
          _ _
          (inferInstanceAs
            (Module (A ⧸ maximalIdeal A)
              (S ⧸ ((maximalIdeal A • (⊤ : Submodule A S)) : Submodule A S)))),
        ∀ i,
          bbar' i =
            ((maximalIdeal A • (⊤ : Submodule A S)) : Submodule A S).mkQ
              (Ideal.Quotient.mk (mRsh ^ (n + 1)) (x i)) := by
    refine ⟨by simpa [P] using bbar, ?_⟩
    intro i
    simpa [P] using hbbar i
  -- Then Lemma `10.101.1` lifts that closed-fiber basis through the nilpotent Artinian quotient.
  obtain ⟨b, hb⟩ :=
    (basis_iff_basis_mod_maximalIdeal_of_flat_of_nilpotent_maximalIdeal
      (R := A)
      (M := S)
      (A := ι)
      (h_nil := quotient_pow_maximalIdeal_nilpotent (R := R) n)
      (x := fun i ↦ Ideal.Quotient.mk (mRsh ^ (n + 1)) (x i))).mp
      h_basisbar
  exact ⟨b, hb⟩

/-- Lemma 15.45.1 (7): there is a single family of elements of `Rˢʰ` whose classes modulo
`maximalIdeal Rˢʰ ^ n` form a basis of `Rˢʰ / maximalIdeal Rˢʰ ^ n` over
`R / maximalIdeal R ^ n` for every `n`. -/
theorem strictHenselization_exists_basis_lift_family [IsStrictHenselizationOf R Rsh] :
    ∃ (ι : Type u) (x : ι → Rsh), ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ mR ^ n) (Rsh ⧸ mRsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i) := by
  classical
  letI : Field (R ⧸ mR) := Ideal.Quotient.field (maximalIdeal R)
  let ι := Module.Free.ChooseBasisIndex (R ⧸ mR) (Rsh ⧸ mRsh)
  let b0 : Module.Basis ι (R ⧸ mR) (Rsh ⧸ mRsh) := Module.Free.chooseBasis (R ⧸ mR) (Rsh ⧸ mRsh)
  -- Choose one lift of each closed-fiber basis vector; this family is kept fixed for all `n`.
  obtain ⟨x, hx⟩ :=
    strictHenselization_exists_basis_lifts (R := R) (Rsh := Rsh) b0
  refine ⟨ι, x, ?_⟩
  intro n
  cases n with
  | zero =>
      -- The zeroth quotient is the trivial ring/module pair, so any fixed family gives a basis.
      simpa using zero_power_quotient_basis_of_subsingleton (R := R) (Rsh := Rsh) x
  | succ k =>
      -- For positive powers, apply the Artinian lifting step to the fixed closed-fiber lifts.
      simpa using
        strictHenselization_successor_basis_of_fixed_lifts
          (R := R) (Rsh := Rsh) b0 x hx k

end StrictHenselizationQuotients

end
